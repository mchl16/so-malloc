/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

typedef struct {
  uint32_t header;
  /*
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array.  This allow us to obtain a
   * pointer to the start of the payload.
   */
  uint8_t payload[];
} block_t;

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

//static uint32_t root; // compressed pointer to the root of the splay tree

/* Functions for setting boundary tags (size, allocation status etc) */

static const uint32_t allocated_mask = 0x40000000;
static const uint32_t prev_mask = 0x80000000;

static inline uint32_t get_size(block_t *bl) {
  uint32_t mask = !(allocated_mask | prev_mask);
  return (*(uint32_t *)bl) & mask;
}

static inline void set_size(block_t *bl, uint32_t size) {
  *(uint32_t *)bl = (size | allocated_mask | prev_mask);
}

/* Splay tree functions */
static inline block_t *splay_find(uint32_t size) {
  return NULL;
}

static inline void splay_insert(block_t *node) {
}

static inline void splay_remove(block_t *node) {
}

/* Create a new (unallocated) block and insert it into the tree */
static inline void create_bl(block_t *ptr,uint32_t size){
  *(uint32_t*)ptr=size;
  splay_insert(ptr);
}

/* Utility functions for finding next blocks
 * (or NULL for allocated/non-existent blocks)
 */

static inline block_t *next_bl(block_t *bl) {
  block_t *res = bl + get_size(bl);
  return (void *)res < mem_heap_hi() ? res : NULL;
}

static inline block_t *prev_bl(block_t *bl) {
  if ((*(uint32_t *)bl) | prev_mask)
    return NULL; // previous block allocated or non-existent
  block_t *ptr = bl - 1;
  uint32_t s = get_size(ptr); // empty blocks have 2 boundary tags
  return ptr - (s - 1);
}

/* Merge a newly free block with its free neighbors (if possible) */
static inline block_t *maybe_merge(block_t *bl) {
  block_t *next = next_bl(bl);
  if (next) {
    splay_remove(next);
    set_size(bl, get_size(bl) + get_size(next));
  }
  block_t *prev = prev_bl(bl);
  if (prev) {
    splay_remove(prev);
    set_size(prev, get_size(prev) + get_size(bl));
    bl = prev;
  }
  return bl;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((long)mem_sbrk(ALIGNMENT - offsetof(block_t, payload)) < 0)
    return -1;
  return 0;
}

/*
 * malloc - If a block of desired size (or larger) is in the splay tree of free
 * blocks, remove it, allocate its part and readd the rest (first fit, best fit
 * seems to be too hard to implement using splay trees). Otherwise allocate a
 * new block using mem_sbrk (if possible).
 */
void *malloc(size_t size) {
  size = round_up(4 + size);
  block_t *bl = splay_find(size);

  //printf("%lx\n",(long)mem_sbrk(0));
  //fflush(stdout);
  if (!bl) {
    block_t *ptr = mem_sbrk(size);
    return ptr < 0 ? NULL : (void*)(ptr+1);
  } else {
    splay_remove(bl);
    int s = get_size(bl);
    if (s > size) {
      create_bl(bl + size, s - size);
      set_size(bl, size);
    }
    return (void*)(bl+1);
  }
}

/*
 * free - If the block being freed has free neighbors,
 *        remove them from the splay tree, merge into one free block
 *        and add it back to the tree.
 */
void free(void *ptr) {
  block_t *bl = ptr;
  bl = maybe_merge(bl - 1);
  splay_insert(bl);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  block_t *block = old_ptr - offsetof(block_t, payload);
  size_t old_size = get_size(block);
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
}
