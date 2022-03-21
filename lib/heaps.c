/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <stdlib.h>
#include <limits.h>
#include "xalloc.h"
#include "contracts.h"
#include "heaps.h"

typedef struct heap_header heap;
struct heap_header {
  int limit;                      // limit = capacity+1
  int next;                       // 1 <= next && next <= limit
  elem* data;                     // \length(data) == limit
  has_higher_priority_fn* prior;  // != NULL
  elem_free_fn* fr;
};

/* Just checks the basic invariants described above, none
 * of the ordering invariants. */
bool is_heap_safe(heap* H) {
  return H != NULL
      && (1 < H->limit && H->limit < INT_MAX/2)
      && (1 <= H->next && H->next <= H->limit)
      && H->prior != NULL;
}


/****** Utility functions ******/

/* Returns true if the element in H->data[i] can
 * correctly be placed above H->data[j] in the heap. */
bool ok_above(heap* H, int i, int j) {
  REQUIRES(is_heap_safe(H));
  REQUIRES(1 <= i && i < H->next);
  REQUIRES(1 <= j && j < H->next);

  return !(*H->prior)(H->data[j], H->data[i]);
}

/* Swaps H->data[i] with its parent. */
void swap_up(heap* H, int i) {
  REQUIRES(is_heap_safe(H));
  REQUIRES(2 <= i && i < H->next);
  REQUIRES(!ok_above(H, i/2, i));

  elem tmp = H->data[i];
  H->data[i] = H->data[i/2];
  H->data[i/2] = tmp;

  ENSURES(ok_above(H, i/2, i));
}


/****** Data structure invariants ******/

bool is_heap_ordered(heap* H) {
  REQUIRES(is_heap_safe(H));

  for (int i = 2; i < H->next; i++)
  //@loop_invariant 2 <= i;
  {
    if (!ok_above(H, i/2, i)) return false;
  }

  return true;
}

bool is_heap(heap* H) {
  return is_heap_safe(H) && is_heap_ordered(H);
}


/****** Partial invariants ******/

/* Valid heap except at n, looking up the tree */
bool is_heap_except_up(heap* H, int n) {
  REQUIRES(is_heap_safe(H));
  REQUIRES(1 <= n && n < H->next);

  for (int i = 2; i < H->next; i++)
  //@loop_invariant 2 <= i;
  {
    if (!(i == n || ok_above(H, i/2, i))) return false;
  }

  return true;
}

/* Valid heap except at n, looking down the tree */
bool is_heap_except_down(heap* H, int n) {
  REQUIRES(is_heap_safe(H));
  REQUIRES(1 <= n && n < H->next);

  for (int i = 2; i < H->next; i++)
  //@loop_invariant 2 <= i;
  {
    if (!(i/2 == n || ok_above(H, i/2, i))) return false;
  }

  return true;
}

bool grandparent_check(heap* H, int i) {
  REQUIRES(is_heap_safe(H));
  REQUIRES(1 <= i && i < H->next);

  if (i == 1) return true; // Root
  if (i*2 >= H->next) return true; // No children
  if (i*2 + 1 == H->next && ok_above(H, i/2, i*2)) return true; // Left only
  return i*2 + 1 < H->next
      && ok_above(H, i/2, i*2)
      && ok_above(H, i/2, i*2+1);
}


/****** Implementation ******/

bool pq_empty(heap* H) {
  REQUIRES(is_heap(H));
  return H->next == 1;
}

bool pq_full(heap* H) {
  REQUIRES(is_heap(H));

  return H->next == H->limit;
}

heap* pq_new(int capacity, has_higher_priority_fn* prior, elem_free_fn* fr) {
  REQUIRES(0 < capacity && capacity < INT_MAX/2 - 1);
  REQUIRES(prior != NULL);

  heap* H = xmalloc(sizeof(heap));
  H->next = 1;
  H->data = xcalloc(sizeof(elem), capacity + 1);
  H->limit = capacity + 1;
  H->prior = prior;
  H->fr = fr;

  ENSURES(is_heap(H));
  ENSURES(pq_empty(H));
  return H;
}

void pq_add(heap* H, elem e) {
  REQUIRES(is_heap(H));
  REQUIRES(!pq_full(H));
  REQUIRES(e != NULL);

  int i = H->next;
  H->data[H->next] = e;
  (H->next)++;

  while (i > 1)
  //@loop_invariant 1 <= i && i < H->next;
  //@loop_invariant is_heap_except_up(H, i);
  //@loop_invariant grandparent_check(H, i);
  {
    if (ok_above(H, i/2, i)) return; // No more violations

    swap_up(H, i);
    i = i/2;
  }
  ASSERT(i == 1);

  ENSURES(is_heap(H));
}

void sift_down(heap* H) {
  REQUIRES(is_heap_safe(H));
  REQUIRES(H->next > 1);
  REQUIRES(is_heap_except_down(H, 1));

  int i = 1;

  while (2*i < H->next)
  //@loop_invariant 1 <= i && i < H->next;
  //@loop_invariant is_heap_except_down(H, i);
  //@loop_invariant grandparent_check(H, i);
  {
    int left = 2*i;
    int right = left+1;

    if (ok_above(H, i, left)                // all good on the left, and
        && (right >= H->next ||             // no right child or
            ok_above(H, i, right))) {       // all good on the right too
      // Nothing to do: invariant is restored already!
      ENSURES(is_heap(H));
      return;
    } else if (right >= H->next ||          // No right child, or
               ok_above(H, left, right)) {  // all good on the right
      // We need to push the new element down to the left
      swap_up(H, left);
      i = left;
    } else {                                // right child needs fixing
      ASSERT(right < H->next && ok_above(H, right, left));
      swap_up(H, right);
      i = right;
    }
  }

  ASSERT(i < H->next && 2*i >= H->next);
  ASSERT(is_heap_except_down(H, i));
  ENSURES(is_heap(H));
}

elem pq_rem(heap* H) {
  REQUIRES(is_heap(H));
  REQUIRES(!pq_empty(H));

  elem min = H->data[1];
  (H->next)--;

  if (H->next > 1) {
    H->data[1] = H->data[H->next];  // Swap last element in
    /* H is no longer a heap! */
    sift_down(H);
  }

  ENSURES(min != NULL);
  ENSURES(is_heap(H));
  return min;
}

elem pq_peek(heap* H) {
  REQUIRES(is_heap(H));
  REQUIRES(!pq_empty(H));

  elem result = H->data[1];

  ENSURES(result != NULL && is_heap(H));
  return result;
}


void pq_free(heap* H) {
  REQUIRES(is_heap(H));

  if (H->fr != NULL) {
    for (int i = 1; i < H->next; i++)
      (*H->fr)(H->data[i]);
  }
  free(H->data);
  free(H);
}
