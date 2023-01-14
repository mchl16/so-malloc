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

/* Declaration of block_t
 * (untouched, it is fine)
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

static inline uint32_t get_size(block_t *bl) {
  uint32_t mask = !(allocated_mask | prev_mask);
  return (*(uint32_t *)bl) & mask;
}

static inline void set_size(block_t *bl, uint32_t size) {
  *(uint32_t *)bl = (size | allocated_mask | prev_mask);
  memcpy(bl+size/4-1,bl,4);
}

/* Get pointer to the splay tree root */
static inline block_t **root(){
  return (block_t**)mem_heap_lo();
}

/* Get pointer to the last allocated block */
static inline block_t **last(){
  return (block_t**)(mem_heap_lo()+8);
}

/* Splay tree functions */
static inline block_t *get_left(block_t *bl){
	return (block_t*)((uint32_t*)mem_heap_lo()+*(uint32_t*)(bl+1));
}

static inline block_t *get_right(block_t *bl){
  fprintf(stderr,"%lx %lx ",(long)mem_heap_lo(),(long)mem_sbrk(0));
  fflush(stderr);
	return (block_t*)((uint32_t*)mem_heap_lo()+*(uint32_t*)(bl+2));
}

static inline void set_left(block_t *bl,block_t *bl2){
	uint32_t val=(uint32_t)((uint32_t*)bl2-(uint32_t*)mem_heap_lo());
	*(uint32_t*)(bl+1)=val;
}

static inline void set_right(block_t *bl,block_t *bl2){
	uint32_t val=(uint32_t)((uint32_t*)bl2-(uint32_t*)mem_heap_lo());
	*(uint32_t*)(bl+2)=val;
}

/* My splay tree implementation */
static inline bool is_nullptr(block_t *bl){
  return bl==(block_t*)mem_heap_lo();
}

static inline block_t *rotate_left(block_t *bl){
	block_t *tmp=get_right(bl);
	set_right(bl,get_left(tmp));
	set_left(tmp,bl);
	return tmp;
}

static inline block_t *rotate_right(block_t *bl){
	block_t *tmp=get_left(bl);
	set_left(bl,get_right(tmp));
	set_right(tmp,bl);
	return tmp;
}

static inline int compare(block_t *lhs,block_t *rhs){
  if(get_size(lhs)<get_size(rhs)) return 1;
  else if(get_size(lhs)>get_size(rhs)) return -1;
  else return lhs<rhs;
}

static inline block_t *splay(block_t *root,block_t *node){
  int cmp=compare(node,root);
  if(cmp==1){
    if(is_nullptr(get_left(root))) return root;
    set_left(root,splay(get_left(root),node));
    return rotate_right(root);
  }
  else if(cmp==-1){
    if(is_nullptr(get_right(root))) return root;
    set_right(root,splay(get_right(root),node));
    return rotate_left(root);
  }
  else return root;
}

/* Greedy first-fit search */
static inline block_t *splay_find(uint32_t size) {
  if(get_size(*root())>=size) return *root();
  while(!is_nullptr(get_right(*root()))){
    *root()=rotate_left(*root());
    if(get_size(*root())>=size) return *root();
  }
  return NULL;
}

static inline block_t *splay_insert(block_t *root,block_t *node) {
  if(!root) return node;
  if(compare(node,root)==1){
    if((is_nullptr(get_left(root)))) set_left(root,node);
    else set_left(root,splay_insert(get_left(root),node));
    return rotate_right(root);
  }
  else{
    if((is_nullptr(get_right(root)))) set_right(root,node);
    else set_right(root,splay_insert(get_right(root),node));
    return rotate_left(root);
  }
}

static inline block_t *splay_remove(block_t *root,block_t *node) {
  if(!root) return root;
  root=splay(root,node);
  if(compare(node,root)) return root;

  block_t *bl=get_left(root);
  if(is_nullptr(bl)) return get_right(root);
  set_left(root,splay(bl,node));
  set_right(bl,get_right(root));
  return bl;
  
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
  uint32_t s = get_size(ptr)/4; // empty blocks have 2 boundary tags
  return ptr - (s - 1);
}

/* Create a new (unallocated) block and insert it into the tree */
static inline void create_bl(block_t *ptr,uint32_t size,bool allocated){
  *(uint32_t*)ptr=size | (prev_bl(ptr) ? prev_mask : 0) | (allocated ? allocated_mask : 0);
  if(!allocated){
    *(uint32_t*)(ptr+size/4-1)=*(uint32_t*)ptr;
    memset(ptr+1,0,8);
    splay_insert(*root(),ptr);
  }
}

/* Merge a newly free block with its free neighbors (if possible) */
static inline block_t *maybe_merge(block_t *bl) {
  block_t *next = next_bl(bl);
  if (next) {
    splay_remove(*root(),next);
    set_size(bl, get_size(bl) + get_size(next));
  }
  block_t *prev = prev_bl(bl);
  if (prev) {
    splay_remove(*root(),prev);
    set_size(prev, get_size(prev) + get_size(bl));
    bl = prev;
  }
  return bl;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Allocate memory for splay tree root and last block pointers */
  if((long)mem_sbrk(16)<0) return -1;
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((long)mem_sbrk(ALIGNMENT - offsetof(block_t, payload)) < 0)
    return -1;

  /* Set up the splay tree (initially with one block of size 16) */
  *root()=mem_sbrk(16);
  create_bl(*root(),16,false);
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
  if (!bl) {
    block_t *ptr = mem_sbrk(size);
    if(ptr<0) return NULL;
    create_bl(ptr,size,true);
    return (void*)(ptr+1);
  } else {
    splay_remove(*root(),bl);
    int s = get_size(bl);
    if (s > size) {
      create_bl(bl + size/4, s - size,false);
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
  splay_insert(*root(),bl);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  //fprintf(stderr,"!");
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
  size_t old_size = get_size(block)-4;
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
