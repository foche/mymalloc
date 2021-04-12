/*
 * mm.c
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "contracts.h"
#include "memlib.h"

#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SEARCH_DEPTH 8 /* search depth for block search */

/* macros for constants (in bytes) */
#define WSIZE     4            /* word, header and footer size */
#define DWSIZE    8            /* double word size */
#define MINSIZE   (3 * DWSIZE) /* minimum block size */
#define LRG_LO    (1 << 7)     /* smallest large size (incl) */
#define LRG_HI    (1 << 13)    /* largest large size (excl) */

/* minimum number of bytes per
 * heap expansion request
 */
#define CHUNKSIZE        (1 << 10)

/* include overhead and align the size */
#define ROUNDSIZE(size)  ((unsigned)ALIGN((size) + WSIZE))

/* status flags */
#define NONE       0x0
#define MALL       0x1 /* current is malloced */
#define PREV_M     0x2 /* prev is malloced */
#define SEEN       0x4 /* indicates a reachable block */

/* number of bins */
#define SML_BIN_N ((LRG_LO-MINSIZE) / ALIGNMENT)
#define LRG_BIN_N (13 - 7 + 1)

/* max of two numbers */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* footer or header manipulation macros */
#define PACK(size, flags) ((unsigned)(size) | (unsigned)(flags))
#define GET(p)            (*(unsigned *)(p))
#define GET_PREV_M(p)     (GET(p) & PREV_M)
#define GET_MALL(p)       (GET(p) & MALL)
#define GET_SIZE(p)       (GET(p) & ~0x7)
#define SET(p, v)         (GET(p) = (v))
#define SET_SIZE(p, size) (GET(p) = (GET(p) & 0x7) | (size))
#define CHG_MALL(p)       (GET(p) ^= MALL)
#define CHG_PREV_M(p)     (GET(p) ^= PREV_M)
#define CHG_SEEN(p)       (GET(p) ^= SEEN)

/* macros for finding and manipulating metadata from block pointers */
#define HDRP(bp)           ((char *)(bp) - WSIZE)
#define SET_H(bp, v)       SET(HDRP(bp), (v))
#define GET_H(bp)          GET(HDRP(bp))
#define GET_HSIZE(bp)      GET_SIZE(HDRP(bp))
#define GET_HMALL(bp)      GET_MALL(HDRP(bp))
#define GET_HPREV_M(bp)    GET_PREV_M(HDRP(bp))
#define GET_HSEEN(bp)      (GET(HDRP(bp)) & SEEN)
#define CHG_HMALL(bp)      CHG_MALL(HDRP(bp))
#define CHG_HPREV_M(bp)    CHG_PREV_M(HDRP(NEXT(bp)))
#define SET_HSIZE(bp, size) SET_SIZE(HDRP(bp), (size))
#define CHG_HSEEN(bp)      CHG_SEEN(HDRP(bp))
#define NEXT(bp)           ((char *)(bp) + GET_HSIZE(bp))
#define FTRP(bp)           ((char *)NEXT(bp) - DWSIZE)
#define SET_F(bp, v)       SET(FTRP(bp), (v))
#define BP_FROM_FTRP(ftrp) ((char *)(ftrp) - GET_SIZE(ftrp) + DWSIZE)
#define PREV(bp)           BP_FROM_FTRP((char *)(bp) - DWSIZE)
#define COPY_H(bp)         SET(FTRP(bp), GET(HDRP(bp)))

#define EXPERIMENTAL /* use experimental realloc implementation */

/* linked list element */
typedef struct link
{
  struct link *next, /* pointers to other links */
              *prev;
} link_t;

/* map of free lists */
typedef struct listmap
{
  link_t *sml_bin[SML_BIN_N], /* bins for exact sizes */
         *lrg_bin[LRG_BIN_N]; /* bins for a range of bigger sizes */
} listmap_t;

/* global variables */

static listmap_t *LIST_MAP; /* pointer to a list map */
static char      *HEAP_HEAD, /* pointer to the first block */
                 *HEAP_TAIL; /* pointer to the last block */

/* helper function prototypes */
static bool     in_heap(const void *p);
static bool     aligned(const void *p);
static void     place(link_t *ptr, unsigned asize);
static void    *malloc_tail(unsigned asize);
static void     insert(link_t *ptr);
static void     pop(link_t *ptr);
static link_t  *findfit(unsigned asize);
static unsigned intlog2(unsigned asize);
static void     error(const char *msg, int lineno);
static void     check_list(link_t *head, unsigned min,
                           unsigned max, int lineno);
static void     printheap(unsigned start, unsigned end);

/*
 * Initialize: return -1 on error, 0 on success.
 *
 * Allocate data structures and initial heap area
 *
 */
int mm_init(void)
{
  unsigned list_size = (unsigned)sizeof(listmap_t); /* size of the map struct */
  void    *p; /* pointer to initial heap */
  if ((p = mem_sbrk(CHUNKSIZE)) == (void *)-1)
    return -1; /* mem_sbrk failed */
  LIST_MAP = (listmap_t *)p;
  memset(LIST_MAP, 0, list_size);
  HEAP_HEAD = (char *)LIST_MAP + list_size + 2*DWSIZE;
  HEAP_TAIL = HEAP_HEAD;
  SET_H(HEAP_HEAD - DWSIZE, PACK(8, MALL | PREV_M)); /* prologue */
  COPY_H(HEAP_HEAD - DWSIZE);
  /* create tail meta data */
  SET_H(HEAP_TAIL, PACK(CHUNKSIZE - list_size - DWSIZE, MALL | PREV_M));
#ifdef DEBUG
  mm_checkheap(__LINE__);
#endif
  return 0;
}

/*
 * malloc
 */
void *malloc (size_t size)
{
  unsigned asize, /* adjusted size */
           bin;   /* bin index */
  link_t  *p;     /* pointer to the allocated block */
  if (size == 0)
    return NULL;
  if (LIST_MAP == NULL)
    mm_init();
  if (size <= MINSIZE - WSIZE) /* factor in overhead */
    asize = MINSIZE;
  else
    asize = ROUNDSIZE(size);
  if (asize < LRG_LO) {
    bin = (asize-MINSIZE) / ALIGNMENT;
    if ((p = LIST_MAP->sml_bin[bin]) != NULL) {
      place(p, asize); /* found a free block in one of the small bins */
      if (GET_HSIZE(p) < MINSIZE)
        error("wrong size", __LINE__);
      return (void *)p;
    }
    else {
      for (bin = 0; bin < LRG_BIN_N; bin++) {
        if ((p = LIST_MAP->lrg_bin[bin]) != NULL) {
          place(p, asize); /* look at larger bins next */
          if (GET_HSIZE(p) < MINSIZE)
            error("wrong size", __LINE__);
          return (void *)p;
        }
      }
    }
  }
  else if (asize < LRG_HI && (p = findfit(asize)) != NULL) {
    place(p, asize); /* handle large requests from one
                      * of the variable-sized bins
                      */
    if (GET_HSIZE(p) < MINSIZE)
      error("wrong size", __LINE__);
    return (void *)p;
  }
  /* everything failed, so satisfy request from the tail,
   * also handles huge requests directly from the tail
   */
  return malloc_tail(asize);
}

/*
 * free
 */
void free (void *ptr)
{
  /* pointer to the leftmost block that will become
   * the final block
   */
  link_t *bp = (link_t *)ptr,
         *prev = NULL,
         *next;
  unsigned total_size;
  if (ptr == NULL)
    return;
  if (LIST_MAP == NULL)
    mm_init();
  next = (link_t *)NEXT(ptr);
  total_size = GET_HSIZE(ptr);
  if ((char *)next == HEAP_TAIL) {
    /* handle heap tail separately */
    total_size += GET_HSIZE(HEAP_TAIL);
    if (!GET_HPREV_M(ptr)) {
      /* previous block is free */
      prev = (link_t *)PREV(ptr);
      pop(prev);
      total_size += GET_HSIZE(prev);
      bp = prev;
    }
    HEAP_TAIL = (char *)bp;
    SET_H(HEAP_TAIL, PACK(total_size, MALL | PREV_M));
  }
  else {
    ASSERT(next != HEAP_TAIL);
    if (!GET_HMALL(next) && !GET_HPREV_M(ptr)) {
      /* previous and next blocks are free */
      prev = (link_t *)PREV(ptr);
      pop(next);
      pop(prev);
      total_size += GET_HSIZE(next) + GET_HSIZE(prev);
      SET_H(prev, PACK(total_size, PREV_M));
      COPY_H(prev);
      insert(prev);
    }
    else if (!GET_HMALL(next) && GET_HPREV_M(ptr)) {
      /* only the next block is free */
      pop(next);
      total_size += GET_HSIZE(next);
      SET_H(ptr, PACK(total_size, PREV_M));
      COPY_H(ptr);
      insert(ptr);
    }
    else if (GET_HMALL(next) && !GET_HPREV_M(ptr)) {
      /* only the previous block is free */
      prev = (link_t *)PREV(ptr);
      pop(prev);
      total_size += GET_HSIZE(prev);
      SET_H(prev, PACK(total_size, PREV_M));
      COPY_H(prev);
      CHG_HPREV_M(prev);
      insert(prev);
    }
    else {
      /* none of the adjacent blocks are free */
      SET_H(ptr, PACK(total_size, PREV_M));
      COPY_H(ptr);
      CHG_HPREV_M(ptr);
      insert(ptr);
    }
  }
}

/*
 * realloc - you may want to look at mm-naive.c
 */
#ifdef EXPERIMENTAL
void *realloc(void *oldptr, size_t size)
{
  void    *newptr = NULL;
  link_t  *next = NULL;
  unsigned oldsize,
           asize,
           adjsize;
  if (LIST_MAP == NULL)
    mm_init();
  if (size == 0) {
    free(oldptr);
    return NULL;
  }
  if (oldptr == NULL)
    return malloc(size);
  if (size <= MINSIZE - WSIZE)
    asize = MINSIZE;
  else
    asize = ROUNDSIZE(size);
  oldsize = GET_HSIZE(oldptr);
  if (asize + MINSIZE <= oldsize) {
    /* split off a block and free it */
    SET_HSIZE(oldptr, asize);
    next = (link_t *)NEXT(oldptr);
    SET_H(next, PACK(oldsize - asize, MALL | PREV_M));
    free(next);
    return oldptr;
  }
  else if (asize <= oldsize)
    return oldptr;
  else {
    ASSERT(asize > oldsize);
    next = (link_t *)NEXT(oldptr);
    if ((char *)next == HEAP_TAIL) {
      /* next is the tail */
      if (malloc_tail(asize - oldsize) != NULL) {
        SET_HSIZE(oldptr, asize); /* attemp to get space from tail */
        return oldptr;
      }
      else
        return NULL; /* malloc from tail failed */
    }
    else if (GET_HMALL(next)) {
      /* next is not free */
      if ((newptr = malloc(size)) != NULL) {
        memcpy(newptr, oldptr, size);
        free(oldptr);
      }
      return newptr;
    }
    else {
      /* next is free */
      adjsize = oldsize + GET_HSIZE(next);
      if (asize + MINSIZE <= adjsize) {
        /* enough space for two blocks */
        pop(next);
        SET_HSIZE(oldptr, asize);
        next = (link_t *)NEXT(oldptr);
        SET_H(next, PACK(adjsize - asize, PREV_M));
        COPY_H(next);
        insert(next);
        return oldptr;
      }
      else if (asize <= adjsize) {
        /* incorporate the whole next block */
        pop(next);
        SET_HSIZE(oldptr, adjsize);
        CHG_HPREV_M(oldptr);
        return oldptr;
      }
      else {
        /* not enough space */
        if ((newptr = malloc(size)) != NULL) {
          memcpy(newptr, oldptr, size);
          free(oldptr);
        }
        return newptr;
      }
    }
  }
}
#else
void *realloc(void *oldptr, size_t size)
{
  void *newptr;
  unsigned asize, oldsize;
  if (LIST_MAP == NULL)
    mm_init();
  if (size == 0) {
    free(oldptr);
    return NULL;
  }
  if (oldptr == NULL)
    return malloc(size);
  if (size <= MINSIZE - WSIZE)
    asize = MINSIZE;
  else
    asize = ROUNDSIZE(size);
  oldsize = GET_HSIZE(oldptr);
  if (asize == size)
    return oldptr;
  else if ((newptr = malloc(size)) != NULL) {
    memcpy(newptr, oldptr, oldsize - WSIZE);
    free(oldptr);
  }
  return newptr;
}
#endif

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t size_full = nmemb * size; /* calculate actual size */
  void *p;                         /* pointer to allocated memory */
  if (size_full == 0)
    return NULL;
  if (LIST_MAP == NULL)
    mm_init();
  if ((p = malloc(size_full)) != NULL)
    memset(p, 0, size_full); /* reset memory on success */
  return p;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p)
{
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p)
{
  return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno)
{
  link_t *head;
  unsigned i, min, max, bin;
  void   *p;
  char    buf[128];
  if (!aligned(LIST_MAP) || !in_heap(LIST_MAP)
      || (void *)LIST_MAP != mem_heap_lo())
    error("free list map is corrupted", lineno);
  if (!aligned(HEAP_HEAD) || !in_heap(HEAP_HEAD)
      || !GET_HPREV_M(HEAP_HEAD) || HEAP_HEAD > HEAP_TAIL)
    error("heap head is corrupted", lineno);
  if (!aligned(HEAP_TAIL) || !in_heap(HEAP_TAIL)
      || (char *)NEXT(HEAP_TAIL) != (char *)mem_heap_hi() + 1 + DWSIZE
      || !GET_HPREV_M(HEAP_TAIL) || !GET_HMALL(HEAP_TAIL)) {
    error("heap tail is corrupted", lineno);
  }
  /* check every free list */
  for (i = 0; i < SML_BIN_N + LRG_BIN_N; i++) {
    if (i < SML_BIN_N) {
      bin = i;
      min = MINSIZE + bin*DWSIZE;
      max = min;
      head = LIST_MAP->sml_bin[bin];
    }
    else if (i < SML_BIN_N + LRG_BIN_N - 1) {
      bin = i - SML_BIN_N;
      min = 1 << (bin + 7);
      max = 1 << (bin + 8);
      head = LIST_MAP->lrg_bin[bin];
    }
    else {
      bin = i - SML_BIN_N;
      min = LRG_HI;
      max = 0U - 1;
      head = LIST_MAP->lrg_bin[bin];
    }
    if (head != NULL)
      check_list(head, min, max, lineno);
  }
  /* check every block */
  for (p = HEAP_HEAD; p != HEAP_TAIL; p = NEXT(p)) {
    if (!aligned(p) || !in_heap(p))
      error("block is misaligned", lineno);
    if (!GET_HMALL(p)) {
      if (!GET_HSEEN(p)) {
        sprintf(buf, "unreachable block at %p of size %u; flags: %#x\n",
                p, GET_HSIZE(p), GET_H(p) & 0x7);
        error(buf, lineno);
      }
      CHG_HSEEN(p);
    }
    else {
      ASSERT(GET_HMALL(p));
      if (GET_HSIZE(p) < MINSIZE || (char *)p < HEAP_HEAD
          || (char *)p >= HEAP_TAIL) {
        sprintf(buf, "block at %p of size %u is corrupted, flags: %#x\n",
                p, GET_HSIZE(p), GET_H(p) & 0x7);
        error(buf, lineno);
      }
    }
  }
}

static void place(link_t *ptr, unsigned asize)
{
  unsigned old_size = GET_HSIZE(ptr),
           new_size = old_size - asize;
  link_t  *new_block = NULL;
  pop((link_t *)ptr);
  if (new_size < MINSIZE) {
    /* the new block would not be big enough
     * for splitting
     */
    CHG_HMALL(ptr);
    CHG_HPREV_M(ptr);
  }
  else {
    ASSERT(new_size >= MINSIZE);
    SET_H(ptr, PACK(asize, MALL | PREV_M));
    new_block = (link_t *)NEXT(ptr);
    SET_H(new_block, PACK(new_size, PREV_M));
    COPY_H(new_block);
    insert(new_block);
  }
}

static void *malloc_tail(unsigned asize)
{
  unsigned old_size = GET_HSIZE(HEAP_TAIL), /* old size of the tail */
           new_size;                        /* new size of the tail */
  void    *bp       = (void *)HEAP_TAIL;    /* pointer to be returned */
  /* expand heap if necessary */
  if (asize + MINSIZE > old_size) {
    if (mem_sbrk((int)(MAX(CHUNKSIZE, asize + MINSIZE))) == (void *)-1)
      return NULL;
  }
  SET_H(bp, PACK(asize, MALL | PREV_M));
  HEAP_TAIL = NEXT(bp);
  if (HEAP_TAIL > (char *)mem_heap_hi() + 1 - WSIZE)
    error("heap tail out of range", __LINE__);
  new_size = (unsigned)((size_t)mem_heap_hi() + 1 + DWSIZE - (size_t)HEAP_TAIL);
  SET_H(HEAP_TAIL, PACK(new_size, MALL | PREV_M));
  if (!GET_HMALL(bp) || !GET_HPREV_M(bp))
    error("block failed to allocate", __LINE__);
  if ((char *)NEXT(HEAP_TAIL) != mem_heap_hi() + 1 + DWSIZE
      || new_size < MINSIZE)
    error("tail size is wrong", __LINE__);
  return bp;
}

/*
 * insert
 *
 * inserts the item into a free list, updating
 * the necessary links
 *
 */
static void insert(link_t *ptr)
{
  REQUIRES(ptr != NULL && LIST_MAP != NULL);
  unsigned asize = GET_HSIZE(ptr),
           bin;
  link_t **head;
  if (ptr == NULL)
    error("tried to insert a NULL block", __LINE__);
  ASSERT(0 <= bin && bin < LRG_BIN_N + SML_BIN_N);
  /* find the appropriate bin */
  if (asize < LRG_LO) {
    bin = (asize-MINSIZE) / ALIGNMENT;
    head = &(LIST_MAP->sml_bin[bin]);
  }
  else {
    if (asize < LRG_HI)
      bin = intlog2(asize) - intlog2(LRG_LO);
    else
      bin = LRG_BIN_N - 1;
    head = &(LIST_MAP->lrg_bin[bin]);
  }
  if (head == NULL)
    error("head is NULL", __LINE__);
  ptr->next = *head;          /* sets next to first element */
  ptr->prev = (link_t *)head; /* sets prev to bin */
  *head = ptr;                /* sets bin to ptr */
  if (ptr->next != NULL)      /* if next is not null, */
    ptr->next->prev = ptr;    /* set its prev to ptr */
  if (!in_heap(ptr->prev))
    error("prev ptr is not in heap", __LINE__);
  if (ptr->next != NULL && !in_heap(ptr->next))
    error("next ptr is invalid", __LINE__);
  ENSURES(*head == ptr && ptr->prev == (link_t *)head
      && (ptr->next == NULL || ptr->next->prev == ptr));
}

/*
 * pop
 *
 * disconnects the block from its list and clears the next
 * block's flag
 *
 */
static void pop(link_t *ptr)
{
  REQUIRES(ptr != NULL && ptr->prev != NULL);
  link_t *next = ptr->next,
         *prev = ptr->prev;
  if (next != NULL)
    next->prev = prev;
  prev->next = next;
  ptr->next = NULL;
  ptr->prev = NULL;
  ENSURES((ptr->next == NULL || ptr->next->prev != ptr)
        && ptr->prev->next != ptr);
}

/* look for a good fit to place a block */
static link_t *findfit(unsigned asize)
{
  link_t *p; /* pointer to the returned block */
  unsigned bin,
           searched = 0,
           best_size = 0U - 1,
           bl_size;
  link_t  *best_p = NULL;
  if (asize < LRG_LO)
    bin = 0;
  else if (asize < LRG_HI)
    bin = intlog2(asize) - intlog2(LRG_LO); /* first bin to look at */
  else
    bin = LRG_BIN_N - 1;
  for (; bin < LRG_BIN_N; bin++) {
    for (p = LIST_MAP->lrg_bin[bin]; p != NULL; p = p->next) {
      if (asize == GET_HSIZE(p)) {
        return (void *)p; /* found a fit */
      }
      else if (searched >= SEARCH_DEPTH && best_p != NULL)
        return best_p;
      else if (asize < (bl_size = GET_HSIZE(p))
            && bl_size < best_size) {
        best_size = bl_size;
        best_p = p;
      }
      searched++;
    }
  }
  return best_p; /* failed to find a fit */
}

/* log base 2 of a number */
static unsigned intlog2(unsigned asize)
{
  REQUIRES(asize > 0);
  unsigned log = 0,
           shift;
  for (shift = 32; shift > 0; shift /= 2) {
    if (asize >= 0x1U << shift) {
      log += shift;
      asize >>= shift;
    }
  }
  ASSERT(asize == 1);
  return log;
}

/* print an error message and quit */
static void error(const char *msg, int lineno)
{
  printheap(0, ~0U);
  fprintf(stderr, "Error: %s (line %d)\n", msg, lineno);
  exit(1);
}

static void check_list(link_t *head, unsigned min,
                     unsigned max, int lineno)
{
  link_t *block;
  char    buf[128];
  /* traverse the list and set the seen flag */
  for (block = head; block != NULL; block = block->next) {
    if (!in_heap(block) || !aligned(block)
        ||  GET(HDRP(block)) != GET(FTRP(block))
        || (char *)block < HEAP_HEAD || (char *)block >= HEAP_TAIL
        ||  block->prev->next != block
        || (block->next != NULL && block->next->prev != block)
        || GET_HMALL(block)
        || !GET_HPREV_M(block) || GET_HPREV_M(NEXT(block))
        || (min == max && GET_HSIZE(block) != min)
        || (min != max && (GET_HSIZE(block) < min
                        || GET_HSIZE(block) >= max))) {
      sprintf(buf, "block of size %u at %p is corrupted; flags: %#x;\
                    min: %u, max: %u",
              GET_HSIZE(block), block, GET_H(block) & 0x7, min, max);
      error(buf, lineno);
    }
    CHG_HSEEN(block); /* mark as seen */
  }
}

static void printheap(unsigned start, unsigned end)
{
  void *p;
  unsigned count = 0;
  printf("\n\n********************\n");
  for (p = HEAP_HEAD; p != HEAP_TAIL; p = NEXT(p)) {
    if (count >= start && count < end) {
      printf("\nBlock: %u\n", count);
      printf("Address: %p\n", p);
      printf("Size: %u\n", GET_HSIZE(p));
      printf("Malloced: %s\n", GET_HMALL(p) ? "true" : "false");
      printf("Previous Mall.: %s\n", GET_HPREV_M(p) ? "true" : "false");
    }
    count++;
  }
  printf("\n********************\n\n");
  printf("Heap tail: %p, size: %u\n",
          HEAP_TAIL, GET_HSIZE(HEAP_TAIL));
  printf("mem hi: %p\n", mem_heap_hi() + 1 + DWSIZE);
}

