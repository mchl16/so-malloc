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

/* This memory manager algorithm uses splay trees to search for
 * blocks of interesting size (using the first-fit policy).
 * The memory layout is as follows:
 * beginning | tree root ptr | last block ptr | padding | blocks | ... | end
 * Block sizes are multiples of 16 bytes (as required by ABI),
 * their structure is as follows:
 * Allocated block: tag (4 B) | data | padding
 * Unallocated block: tag (4 B) | compressed ptrs to l and r subtrees (2x4 B) |
 * padding | 2nd boundary tag (4 B) Tags contain information about the block's
 * size and whether it or its left neighbor is allocated. Blocks are coalesced
 * with their free neighbors immediately upon being freed. If the splay tree
 * doesn't contain a free block of desired size and the last block is
 * unallocated, it can be expanded to the requested size (saving a bit of
 * memory). A similar thing may happen if we want to realloc a block with free
 * neighbors.
 */

/* Declaration of block_t
 * (untouched, it is fine for my needs)
 */

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

/* Functions for setting boundary tags (size, allocation status etc) */

static const uint32_t allocated_mask = 0x1;
static const uint32_t prev_mask = 0x2;

static inline bool get_allocated(block_t *bl) {
  return (*(uint32_t *)bl) & allocated_mask;
}

static inline void set_allocated(block_t *bl,bool val){
  if(val) *(uint32_t*)bl|=allocated_mask;
  else *(uint32_t*)bl&=~allocated_mask;
}

static inline bool get_prev(block_t *bl) {
  return (*(uint32_t *)bl) & prev_mask;
}

static inline void set_prev(block_t *bl,bool val){
  if(val) *(uint32_t*)bl|=prev_mask;
  else *(uint32_t*)bl&=~prev_mask;
}

static inline uint32_t get_size(block_t *bl) {
  uint32_t mask = ~(allocated_mask | prev_mask);
  return (*(uint32_t *)bl) & mask;
}

static inline void set_size(block_t *bl, uint32_t size) {
  *(uint32_t *)bl &= 3;
  *(uint32_t *)bl |= size;
  memcpy(bl + size / 4 - 1, bl, 4);
}

/* Get pointer to the splay tree root */
static inline block_t **root() {
  return (block_t **)mem_heap_lo();
}

/* Get pointer to the last allocated block */
static inline block_t **last() {
  return (block_t **)(mem_heap_lo() + 8);
}

/* My splay tree implementation */

/* Pointer manipulation functions */
static inline uint32_t get_offset(block_t *ptr) {
  return ((uint64_t)ptr - (uint64_t)mem_heap_lo());
}

static inline block_t *get_ptr(uint32_t offset) {
  return (block_t *)((uint64_t)mem_heap_lo() + offset);
}

static inline bool is_nullptr(block_t *bl) {
  return bl == (block_t *)mem_heap_lo();
}

/* Splay tree functions */
static inline block_t *get_left(block_t *bl) {
  return get_ptr(*(uint32_t *)(bl + 1));
}

static inline block_t *get_right(block_t *bl) {
  return get_ptr(*(uint32_t *)(bl + 2));
}

static inline void set_left(block_t *bl, block_t *bl2) {
  *(uint32_t *)(bl + 1) = get_offset(bl2);
}

static inline void set_right(block_t *bl, block_t *bl2) {
  *(uint32_t *)(bl + 2) = get_offset(bl2);
}

static inline block_t *rotate_left(block_t *bl) {
  block_t *tmp = get_right(bl);
  set_right(bl, get_left(tmp));
  set_left(tmp, bl);
  return tmp;
}

static inline block_t *rotate_right(block_t *bl) {
  block_t *tmp = get_left(bl);
  set_left(bl, get_right(tmp));
  set_right(tmp, bl);
  return tmp;
}

static inline int compare(block_t *lhs, block_t *rhs) {
  if (get_size(lhs) < get_size(rhs))
    return 1;
  else if (get_size(lhs) > get_size(rhs))
    return -1;
  else
    return lhs < rhs ? 1 : (lhs == rhs ? 0 : -1);
}

static inline block_t *splay(block_t *root, block_t *node) {
  int cmp = compare(node, root);
  if (cmp == 1) {
    if (is_nullptr(get_left(root)))
      return root;
    set_left(root, splay(get_left(root), node));
    return rotate_right(root);
  } else if (cmp == -1) {
    if (is_nullptr(get_right(root)))
      return root;
    set_right(root, splay(get_right(root), node));
    return rotate_left(root);
  } else
    return root;
}

/* Greedy first-fit search */
static inline block_t *splay_find(uint32_t size) {
  if(is_nullptr(*root())) return NULL;
  if (get_size(*root()) >= size)
    return *root();
  while (!is_nullptr(get_right(*root()))) {
    *root() = rotate_left(*root());
    if (get_size(*root()) >= size)
      return *root();
  }
  return NULL;
}

static inline block_t *_splay_insert(block_t *root, block_t *node) {
  if (is_nullptr(root))
    return node;

  printf("Kupa\n");
  printf("%lx %lx\n",(long)root,(long)node);
  if (compare(node, root) == 1) {
    if ((is_nullptr(get_left(root))))
      set_left(root, node);
    else
      set_left(root, _splay_insert(get_left(root), node));
    return rotate_right(root);
  } else {
    if ((is_nullptr(get_right(root))))
      set_right(root, node);
    else
      set_right(root, _splay_insert(get_right(root), node));
    return rotate_left(root);
  }
}

static inline block_t *_splay_remove(block_t *root, block_t *node) {
  if (is_nullptr(root))
    return root;
  root = splay(root, node);
  if (compare(node, root))
    return root;

  block_t *bl = get_left(root);
  if (is_nullptr(bl))
    return get_right(root);
  bl=splay(bl, node);
  set_right(bl, get_right(root));
  return bl;
}

/* Wrappers */
static inline void splay_insert(block_t *node){
  *root()=_splay_insert(*root(),node);
}

/* Wrappers */
static inline void splay_remove(block_t *node){
  *root()=_splay_remove(*root(),node);
}

/* Return a pointer to the next block (no matter if allocated or not) */
static inline block_t *next_bl(block_t *bl) {
  block_t *res = bl + get_size(bl)/4;
  if ((void *)res >= mem_heap_hi()) return mem_heap_lo();
  return res;
}

/* If the previous block is allocated, return a pointer to it */
static inline block_t *prev_bl(block_t *bl) {
  if (get_prev(bl))
    return mem_heap_lo(); // previous block allocated or non-existent
  block_t *ptr = bl - 1;
  uint32_t s = get_size(ptr) / 4; // empty blocks have 2 boundary tags
  return ptr - (s - 1);
}

/* Create a new (unallocated) block and insert it into the tree */
static inline void create_bl(block_t *ptr, uint32_t size, bool allocated,
                             bool prev) {
  if (allocated)
    size |= allocated_mask;
  if (prev)
    size |= prev_mask;
  *(uint32_t *)ptr = size;
  if (!allocated) {
    *(uint32_t *)(ptr + size / 4 - 1) = *(uint32_t *)ptr;
    memset(ptr + 1, 0, 8);
    splay_insert(ptr);
  }
  block_t *bl=next_bl(ptr);
  if(!is_nullptr(bl)){
    set_prev(bl,allocated);
  }
}

/* Merge a newly free block with its free neighbors (if possible) */
static inline block_t *maybe_merge(block_t *bl) {
  block_t *next = next_bl(bl);
  if (!is_nullptr(next) && !get_allocated(next)) {
    splay_remove(next);
    set_size(bl, get_size(bl) + get_size(next));
  }
  block_t *prev = prev_bl(bl);
  if (!is_nullptr(prev)) {
    splay_remove(prev);
    set_size(prev, get_size(prev) + get_size(bl));
    bl = prev;
  }
  create_bl(bl,get_size(bl),false,get_prev(bl));
  return bl;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Allocate memory for splay tree root and last block pointers */
  if ((long)mem_sbrk(16) < 0)
    return -1;
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((long)mem_sbrk(ALIGNMENT - offsetof(block_t, payload)) < 0)
    return -1;

  /* Set up the splay tree (initially with one block of size 16) */
  block_t *bl = mem_sbrk(16);
  *root()=mem_heap_lo();
  *last()=bl;
  create_bl(bl, 16, false, true);
  return 0;
}

/*
 * malloc - If a block of desired size (or larger) is in the splay tree of free
 * blocks, remove it, allocate its part and readd the rest (first fit, best fit
 * seems to be too hard to implement using splay trees). Otherwise allocate a
 * new block using mem_sbrk (if possible).
 */
void *malloc(size_t size) {
  debug("%ld!!\n", size);
  size = round_up(4 + size);
  block_t *bl = splay_find(size);
  if (!bl) {
    block_t *ptr = mem_sbrk(size);
    if (ptr < 0)
      return NULL;
    debug("%lx?!\n", (long)*last());
    create_bl(ptr, size, true, get_allocated(*last()));
    *last() = ptr;
    return (void *)(ptr + 1);
  } else {
    debug("Eureka!\n");
    splay_remove(bl);
    printf("%lx",(long)*root());
    uint32_t s = get_size(bl);
    if (s > size) {
      create_bl(bl + size / 4, s - size, false, true);
    }
    else{
      block_t *bl2=next_bl(bl);
      printf("Kot\n");
      if(!is_nullptr(bl2)){
        printf("kocha\n");
        set_prev(bl2,true);
      }
    }
    create_bl(bl,size,true,get_prev(bl));
    return (void *)(bl + 1);
  }
}

/*
 * free - If the block being freed has free neighbors,
 *        remove them from the splay tree, merge into one free block
 *        and add it back to the tree.
 */
void free(void *ptr) {
  debug("free %lx???\n",(long)ptr);
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

  block_t *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  block_t *block = old_ptr - 1;
  size_t old_size = get_size(block) - 4;
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

/* Attempts to perform DFS on the splay tree (without splaying)
 * To be used to mm_checkheap
 */

void check_tree(block_t *bl, int verbose) {
  if(is_nullptr(bl)) return;
  if (verbose >= 2)
    debug("->%lx\n", (long)bl);
  if (get_allocated(bl)) {
    if (verbose) {
      printf("Zaalokowany blok w drzewie\n");
    }
    exit(1);
  }
  block_t *l = get_left(bl);
  if (!is_nullptr(l)) {
    if (l < (block_t *)mem_heap_lo() || l >= (block_t *)mem_heap_hi() ||
        ((uint64_t)l & 15) != 12 || l==bl) {
      if (verbose) {
        printf("Popsuty pointer w bloku w drzewie\n");
        printf("%x %x %x\n",*(uint32_t*)bl,*(uint32_t*)(bl+1),*(uint32_t*)(bl+2));
      }
      exit(1);
    }
    if (verbose >= 2)
      printf("l->%lx\n", (long)l);
    check_tree(l, verbose);
  }
  block_t *r = get_right(bl);
  if (!is_nullptr(r)) {
    if (r < (block_t *)mem_heap_lo() || r >= (block_t *)mem_heap_hi() ||
        ((uint64_t)r & 15) != 12 || r==bl) {
      if (verbose) {
        printf("Popsuty pointer w bloku w drzewie\n");
        printf("%x %x %x\n",*(uint32_t*)bl,*(uint32_t*)(bl+1),*(uint32_t*)(bl+2));
      }
      exit(1);
    }
    if (verbose >= 2)
      printf("r->%lx\n", (long)r);
    check_tree(r, verbose);
  }
}

/*
 * mm_checkheap - Check the block list first,
 *                then try to check the splay tree
 */
void mm_checkheap(int verbose) {
  /* Check the block list from left to right */
  if (verbose)
    printf("\nSprawdzanie listy:\n");
  block_t *ptr = (block_t *)((uint64_t)mem_heap_lo() + 16 +
                             (ALIGNMENT - offsetof(block_t, payload)));
  block_t *limit = (block_t *)*last();
  bool prev = true;
  while (ptr <= limit) {
    if (verbose) {
      printf("%lx %d %s %s!\n", (long)ptr, get_size(ptr), get_allocated(ptr) ? "TAK" : "NIE", get_prev(ptr) ? "TAK" : "NIE");
    }
    uint32_t size = get_size(ptr);
    if (verbose >= 2)
      printf("%d\n", size);
    if (get_prev(ptr) != prev) {
      if (verbose) {
        printf("Popsute dane o poprzednim bloku\n");
        printf("%lx %x %d %d\n", (long)ptr, *(uint32_t *)ptr, get_prev(ptr),
               prev);
      }

      exit(1);
    }
    uint32_t size2 = size / 4;
    prev = get_allocated(ptr);
    if (!get_allocated(ptr)) {
      if(verbose>=2) printf("%x %x %x\n",*(uint32_t*)ptr,*(uint32_t*)(ptr+1),*(uint32_t*)(ptr+2));
      if (*(uint32_t *)(ptr + size2 - 1) != *(uint32_t *)ptr) {
        if (verbose) {
          printf("Popsute boundary tagi w niezaalokowanym bloku\n");
          printf("%d %x %x\n", size, *(uint32_t *)ptr,
                 *(uint32_t *)(ptr + size2 - 1));
        }
        exit(1);
      }
      else if(get_left(ptr)==ptr || get_right(ptr)==ptr){
        if(verbose){
          printf("Popsuty pointer w bloku w drzewie\n");
          printf("%x %x %x\n",*(uint32_t*)ptr,*(uint32_t*)(ptr+1),*(uint32_t*)(ptr+2));
        }
        exit(1);
      }
    }
    ptr += size2;
  }

  /* Check the splay tree */
  if (verbose)
    printf("Sprawdzanie drzewa:\n");
  check_tree(*root(), verbose);
  if (verbose)
    printf("Nie stwierdzono usterek\n");
}
