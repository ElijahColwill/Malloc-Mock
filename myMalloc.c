#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t object_left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);
static inline int get_idx(header * block);
static inline int get_idx_int(int size);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);
static inline size_t get_actual_size(size_t raw_size);
static inline header * get_free_block(size_t block_size);
static inline header * split_block(header * block, size_t request_size);
static inline void insert_block(header * block);
static inline int chunk_manager(size_t mem_req);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized = false;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_object_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->object_left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param object_left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t object_left_size) {
	set_object_state(fp,FENCEPOST);
	set_object_size(fp, ALLOC_HEADER_SIZE);
	fp->object_left_size = object_left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size); 
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_object_state(hdr, UNALLOCATED);
  set_object_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->object_left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // Error Case: Malloc not initialized
  if (!isMallocInitialized) {
  	init();
  }

  // Error Case: Request of size 0 bytes
  if (raw_size == 0) {
  	return NULL;
  }

  // Get the actual request size of memory that is required for the request.
  size_t actual_size = get_actual_size(raw_size);
   
  // Get the correct block from the freelists to allocate
  header * block = get_free_block(actual_size);

  // Case 1: Block was not found. Call chunk manager to get new memory,
  // then run again and move to Cases 2 and 3.
  if (block == NULL) {
	// Call chunk manager and run get_free_block again to 
	// grab the new free block. If the chunk_manager returns
	// one, return NULL will an error.
	int attempt_chunk = chunk_manager(actual_size);
	if (attempt_chunk == 1) {
		fprintf(stdout, "Malloc Failed: Cannot allocate memory\n");
		errno = ENOMEM;
		exit(1);
	}
	block = get_free_block(actual_size);
  }

  // Case 2: Block is exactly the requested size or too small to be allocated
  if (get_object_size(block) < (actual_size + MIN_ALLOCATION)) { 
  // Allocate and return block
	block->next->prev = block->prev;
	block->prev->next = block->next;
	set_object_state(block, ALLOCATED);
	return get_header_from_offset(block, ALLOC_HEADER_SIZE);	
  // Case 3: Block large enough to be split, with both greater than MIN_ALLOCATION
  } else {
  	return split_block(block, actual_size);
  }
}

/**
 * @brief Helper fuction to calculate the real size that allocate_object will use
 *
 * @param raw_size the number of bytes that the user needs
 *
 * @return the actual number of bytes that will be requested
*/
static inline size_t get_actual_size(size_t raw_size) {
	// Initalized local variable to hold returned actual size
	size_t actual_size = raw_size;

	// Step 1: Check if requested Size is less then minimum allocation size required
	// Action: Set actual_size to MIN_ALLOCATION and run the rest of the function
	// for any further adjustments.
	if (raw_size < MIN_ALLOCATION) {
		actual_size = MIN_ALLOCATION;	
	}

	// Step 2: Check if the current value of actual_size is not  multiple of 8, and 
	// round up if it is not.
	if (actual_size % 8 != 0) {
		actual_size += (8 - (actual_size % 8));
	}

	// Step 3: Add the size of the metadata to the request size
	actual_size += ALLOC_HEADER_SIZE;

	// Return Step: Return calculated actual_size
	return actual_size > sizeof(header) ? actual_size : sizeof(header);
}

/** 
 * @brief Helper function to find a block that is free to allocate with the correct size
 *
 * @param block_size the number of bytes of the block portion that will detemine the free
 * list the block is located in, including metadata
 *
 * @return a pointer to the block that is the correct size for the requested allocation
 */ 
static inline header * get_free_block(size_t block_size) {
	// Step 1: Calculate index to access initial correct free list
	int idx = get_idx_int(block_size);

	// Step 2: Locate the block we want to allocate in the free lists.
	while(idx < N_LISTS) {
		// Create pointer to the sentinel node
		header * current_list = &freelistSentinels[idx];
		// If we are at the last free list, we need to check every block
		if (idx == N_LISTS - 1) {
			// Store the address of the sentinel node
			header * sentinel = current_list;
			// Check if the last free list is empty, in which case
			// just return.
			if (sentinel->next == sentinel) {
				return NULL;
			}
			// Move to the first block that is not a sentinel
			current_list = current_list->next;
			// Iterate through the list to see if a block exists that is large enough
			while (current_list != sentinel) {
				if (get_object_size(current_list) >= block_size) {
					return current_list;
				}
				current_list = current_list->next;
			}
		// If we are not at the last free list, just check if a block is available
		} else if (current_list->next != current_list) {
			return current_list->next;
		}
		idx++;
	}
	
	// Return Step: Return NULL if no satisfying block was found.
	return NULL;
}

/**
 * @brief Helper function to split block into two and allocate the rightmost block
 *
 * @param block the block to be split, passed as a header pointer
 * @param request_size the size of the memory request, including metadata
 *
 * @return pointer to the block that has been allocated
 */
static inline header * split_block(header * block, size_t request_size) {	
	// Get the new size of the block to allow us to use it throughout the function.
	size_t new_block_size = get_object_size(block) - request_size;

	// Step 1: Create a new header for a new block at the correct distance from the original block.
	// Set the size, state, and left_size of this new block to create it.
	header * new_block = get_header_from_offset(block, new_block_size);
	set_block_object_size_and_state(new_block, request_size, ALLOCATED);
	new_block->object_left_size = new_block_size;
	
	// Step 2: Correct the object size and left object size of the neighboring blocks
	set_object_size(block, new_block_size);
	get_header_from_offset(new_block, get_object_size(new_block))->object_left_size = get_object_size(new_block);

	// Step 3: If the remaining deallocated block no longer begins in the (N_LISTS)th free list,
	// then by design it no longer belongs in its current list and needs to be reinserted.
	if (new_block_size < ((N_LISTS - 1) * 8 + 1)) {
		// Adjust pointers to delete from current free list
		block->next->prev = block->prev;
		block->prev->next = block->next;
		
		// Insert block into free list
		insert_block(block);
	}

	// Return Step: Return a pointer to the header of the new block;
	return get_header_from_offset(new_block, ALLOC_HEADER_SIZE);	
}

/**
 * @breif Helper function to find the correct free list for a given block
 *
 * @param block the block in memory to be inserted
 */
static inline void insert_block(header * block) {
	// Step 1: Find the correct list and insert the block into that list.
	
	// Create the index for the list the block belongs in, capping at 
	// the variable sized free list.
	int idx = get_idx(block);

	// Step 3: Insert the block into the correct list.
	header * sentinel = &freelistSentinels[idx];
	// Case A: There are data nodes in the free list beyond the sentinal.
	if (sentinel->next != sentinel) {
		// Store the next block that the new block will be inserted before
		header * next_node = sentinel->next;
		
		// Adjust next and previous pointers for block, sentinel, and next node
		sentinel->next = block;
		block->prev = sentinel;

		next_node->prev = block;
		block->next = next_node;
	// Case B: The sentinel is the only node in the free list.
	} else {
		sentinel->next = block;
		sentinel->prev = block;

		block->next = sentinel;
		block->prev = sentinel;
	}
}

/**
 * @brief Helper function to manage and request new chunks from the OS
 *
 * @param the amount of memory (in bytes) that needs to be requested and handled
 *
 * @return integer indicating success of the OS call and function, returns 1
 * in an error state
 */
static inline int chunk_manager(size_t mem_req) {
	// Step 1: Store size yet to be allocated in case request takes more then
	// one system call.
	int remaining = mem_req;

	// Error Case: If we are at the maximum OS chunk allocation, return an error state
	if (numOsChunks >= MAX_OS_CHUNKS) {
		return 1;
	}

	// Step 2: Repeat allocation process until request is filled or there is an error
	while (remaining > 0) {
		// Error Case: If allocating a chunk would put us above maximum, return an error state
		if (numOsChunks + 1 > MAX_OS_CHUNKS) {
			return 1;
		}
		// Allocate chunk.
		header * chunk = allocate_chunk(ARENA_SIZE);
		// Error Case: If chunk allocation fails, return exit status and leave function
		if (chunk == NULL) {
			return 1;
		}
		// Set up and insert fence posts as an os_chunk
		header * prevFencePost = get_header_from_offset(chunk, -ALLOC_HEADER_SIZE);
		insert_os_chunk(prevFencePost);

		// Set up pointer to check if this chunk is adjacent to the previous chunk in memory
		header * adjacent = get_header_from_offset(prevFencePost, -ALLOC_HEADER_SIZE);

		// Case A: Chunks are not adjacent, chunk can be inserted as a new entry in free lists
		if (adjacent != lastFencePost) {
			insert_block(chunk);
		// Case B: Chunks are adjacent and need to be coalesed.
		} else {
			// Get the header of the lastBLock and decrememnt numOsChunks
			header * last_block = get_header_from_offset(adjacent, -adjacent->object_left_size);
			numOsChunks--;
			// Case I: lastBlock is allocated, we only need to delete the fenceposts and insert the 
			// new, larger block.
			if (get_object_state(last_block) == ALLOCATED) {
				// Calculate the new size of the block and update fencepost left size
				size_t new_size = get_object_size(chunk) + (2 * ALLOC_HEADER_SIZE);
				get_header_from_offset(chunk, get_object_size(chunk))->object_left_size = new_size;
				// Get the header of the fencepost that will now act as the unallocated chunk
				chunk = get_header_from_offset(chunk, -(2 * ALLOC_HEADER_SIZE));
				// Set the chunk size and state and insert it into the free lists
				set_block_object_size_and_state(chunk, new_size, UNALLOCATED);
				insert_block(chunk);
			// Case II: Block to the left is unallocated and needs to me merged	
			} else {
				// Calculate new size of last_block to include both fenceposts and the size of the new chunk
				// Additionally, store the old size to see if we need to reinsert.
				size_t new_size = get_object_size(last_block) + (2 * ALLOC_HEADER_SIZE) + get_object_size(chunk);
				size_t old_size = get_object_size(last_block);

				// Adjust current and neighboring values
				set_object_size(last_block, new_size);
				get_header_from_offset(last_block, new_size)->object_left_size = new_size;

				// Check if the last_block was not in the largest free_list, in which case remove it from its
				// current free list.
				if (old_size < ((N_LISTS - 1) * 8) + 1) {
					// Adjust pointers and call insert_block
					last_block->next->prev = last_block->prev;
					last_block->prev->next = last_block->next;
					insert_block(last_block);
				}
			}
		}

		// Subtract size of memory grabbed from size of remaining request
		remaining -= ARENA_SIZE;

		// After checking for adjacent chunk, update lastFencePost
		lastFencePost = get_header_from_offset(chunk, get_object_size(chunk));
	}

	// Return Step: Return zero when memory has been successfully handled and inserted into free lists
	return 0;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // Error State: if p is null, return from function (no-op)
  if (p == NULL) {
	errno = ENOMEM;
  	return;
  }

  // Store a pointer to the head of the block passed to us.
  header * p_head = ptr_to_header(p);
  // Error State: p is UNALLOCATED (called on unallocated block or previously freed)
  // Return from function.
  if (get_object_state(p_head) == UNALLOCATED) {
	fprintf(stderr, "Double Free Detected\n");
	errno = ENOMEM;
	assert(false);
	exit(1);
  }
  // Set p_head to unallocated to protect against double frees even if 
  // it ends up being merged.
  set_object_state(p_head, UNALLOCATED);

  // Store pointers to the left and right neightbors of p_head
  header * right = get_header_from_offset(p_head, get_object_size(p_head));
  header * left = get_header_from_offset(p_head, -p_head->object_left_size);


  // Case 1: right and left are allocated, insert this block into the free list
  if (get_object_state(left) != UNALLOCATED && get_object_state(right) != UNALLOCATED) {
  	// Set the object state and insert in the free lists
	insert_block(p_head);
  // Case 2: Left is unallocated and should be merged, right is allocated
  } else if (get_object_state(left) == UNALLOCATED && get_object_state(right) != UNALLOCATED) {
	// Update the size of the old block and check if it's index has changed.
  	int old_idx = get_idx(left);
	set_object_size(left, get_object_size(left) + get_object_size(p_head));
	get_header_from_offset(left, get_object_size(left))->object_left_size = get_object_size(left);
	int new_idx = get_idx(left);
	// If the index is different, re-insert the left block
	if (old_idx != new_idx) {
		// Adjust pointers to delete from current free list
		left->next->prev = left->prev;
	        left->prev->next = left->next;
		insert_block(left);	
	}
  // Case 3: Left is allocated, right is unallocated and should be merged
  } else if (get_object_state(left) != UNALLOCATED && get_object_state(right) == UNALLOCATED) {
	//  Computer old and new index for comparison and update size and state of p_head
	int old_idx = get_idx(right);
	set_block_object_size_and_state(p_head, get_object_size(p_head) + get_object_size(right), UNALLOCATED);
	get_header_from_offset(p_head, get_object_size(p_head))->object_left_size = get_object_size(p_head);
	int new_idx = get_idx(p_head);
	// Case A: New indicies are equal: update pointers and remove right
	if (old_idx == new_idx) {
		p_head->next = right->next;
		p_head->prev = right->prev;
		right->next->prev = right->prev;
		right->prev->next = right->next;
	// Case B: Indicies are not equal: update pointers are insert p_head
	} else {
		right->next->prev = right->prev;
		right->prev->next = right->next;
		insert_block(p_head);
	}
  // Case 4: Both are unallocated
  } else {
	// Calculate the new indicies for comparison and update size of left to include everything
	int old_idx = get_idx(left);
	set_object_size(left, get_object_size(left) + get_object_size(p_head) + get_object_size(right));
	get_header_from_offset(left, get_object_size(left))->object_left_size = get_object_size(left);
	int new_idx = get_idx(right);
	// Delete right from the free lists
	right->next->prev = right->prev;
	right->prev->next = right->next;
	// If the index has changed, delete and reinsert left in the free lists
	if (old_idx != new_idx) {
		// Adjust pointers to delete from current free list
		left->next->prev = left->prev;
		left->prev->next = left->next;
		insert_block(left);
	}	
  }

}

/**
 * @brief Helper to return the index the block belongs to in the free list
 *
 * @param block header pointer to calculate index from
 *
 * @return integer of the index a block of that size will have
 */
static inline int get_idx(header * block) {
	int test_size = ((get_object_size(block) - ALLOC_HEADER_SIZE) / 8) - 1;
	return test_size < N_LISTS - 1 ? test_size : N_LISTS - 1;
}

/**
 * @breif Helper function to return the index from an int size
 *
 * @param size integer giving the size to be calculated
 *
 * @return integer of the index a block of that size will have
 */
static inline int get_idx_int(int size) {
	int test_size = ((size - ALLOC_HEADER_SIZE) / 8) - 1;
	return test_size < N_LISTS - 1 ? test_size : N_LISTS - 1;
}


/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_object_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_object_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_object_size(chunk)  != get_right_header(chunk)->object_left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);	

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_object_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;

  isMallocInitialized = true;

}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
