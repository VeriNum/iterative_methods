#include "../sparse/sparse.h"

void exit(int code);

struct coo_matrix *create_coo_matrix (unsigned maxn, unsigned rows, unsigned cols) {
  struct coo_matrix *p = surely_malloc (sizeof (*p));
  p->row_ind = (unsigned *)surely_malloc(maxn * sizeof(unsigned));
  p->col_ind = (unsigned *)surely_malloc(maxn * sizeof(unsigned));
  p->val = (double *)surely_malloc(maxn * sizeof(double));
  p->n=0;
  p->maxn=maxn;
  p->rows=rows; p->cols=cols;
  return p;
}

void add_to_coo_matrix(struct coo_matrix *p, unsigned i, unsigned j, double x) {
  unsigned n = p->n;
  if (n>=p->maxn) exit(2);
  p->row_ind[n]=i;
  p->col_ind[n]=j;
  p->val[n]=x;
  p->n = n+1;
}


void swap(struct coo_matrix *p, unsigned a, unsigned b) {
  unsigned i,j; double x;
  i=p->row_ind[a];
  j=p->col_ind[a];
  x=p->val[a];
  p->row_ind[a]=p->row_ind[b];
  p->col_ind[a]=p->col_ind[b];
  p->val[a]=p->val[b];
  p->row_ind[b]=i;
  p->col_ind[b]=j;
  p->val[b]=x;
}

int coo_less (struct coo_matrix *p, unsigned a, unsigned b) {
  unsigned ra = p->row_ind[a], rb = p->row_ind[b];
  if (ra<rb) return 1;
  if (ra>rb) return 0;
  return p->col_ind[a] < p->col_ind[b];
}

/* adapted from qsort3 in cbench:
   https://github.com/cverified/cbench/blob/master/src/qsort/qsort3.c */

/* sort the coordinate elements of a coo_matrix */
void coo_quicksort(struct coo_matrix *p, unsigned base, unsigned n)
{
  unsigned lo, hi, left, right, mid;

  if (n == 0)
    return;
  lo = base;
  hi = lo + n - 1;
  while (lo < hi) {
    mid = lo + ((hi - lo) >> 1);
    
    if (coo_less(p,mid,lo))
      swap(p, mid, lo);
    if (coo_less(p,hi,mid)) {
      swap(p, mid, hi);
      if (coo_less(p,mid,lo))
        swap(p, mid, lo);
    }
    left = lo + 1;
    right = hi - 1;
    do {
      while (coo_less(p,left,mid))
        left++;
      while (coo_less(p,mid,right))
        right--;
      if (left < right) {
	swap(p, left, right);
        if (mid == left)
          mid = right;
        else if (mid == right)
          mid = left;
        left++;
        right--;
      } else if (left == right) {
        left++;
        right--;
        break;
      }
    } while (left <= right);
    if (right - lo > hi - left) {
      coo_quicksort(p, left, hi - left + 1);
      hi = right;
    } else {
      coo_quicksort(p, lo, right - lo + 1);
      lo = left;
    }
  }
}

/* Count the number of distinct row/col entries in a sorted coordinate list */
unsigned coo_count (struct coo_matrix *p) {
  unsigned i;
  unsigned n = p->n;
  if (n==0) return 0;
  unsigned count=1;
  for (i=1; i<n; i++) {
    if (p->row_ind[i-1]!=p->row_ind[i] || p->col_ind[i-1]!=p->col_ind[i])
      count++;
  }
  return count;
}

struct csr_matrix *coo_to_csr_matrix(struct coo_matrix *p) {
  struct csr_matrix *q;
  unsigned count, i;
  unsigned r,c, ri, ci, cols, k, l, rows;
  unsigned *col_ind, *row_ptr, *prow_ind, *pcol_ind;
  double x, *val, *pval;
  unsigned n = p->n;
  coo_quicksort(p, 0, n);
  k = coo_count(p);
  rows = p->rows;
  prow_ind=p->row_ind;
  pcol_ind=p->col_ind;
  pval = p->val;
  q = surely_malloc(sizeof(struct csr_matrix));
  val = surely_malloc(k * sizeof(double));
  col_ind = surely_malloc(k * sizeof(unsigned));
  row_ptr = surely_malloc ((rows+1) * sizeof(unsigned));
  r=-1;
  c=0; /* this line is unnecessary for correctness but simplifies the proof */
  l=0;
  /* partial_csr_0 */
  for (i=0; i<n; i++) {
    ri = prow_ind[i];
    ci = pcol_ind[i];
    x = pval[i];
    if (ri==r)
      if (ci==c)
	val[l-1] += x; /* partial_CSR_duplicate */
      else {
	c=ci;
	col_ind[l] = ci;
	val[l] = x;
	l++;           /* partial_CSR_newcol */
      }
    else {
      while (r+1<=ri) row_ptr[++r]=l; /* partial_CSR_skiprow */
      c= ci;
      col_ind[l] = ci;
      val[l] = x;
      l++;            /* partial_CSR_newrow */
    }
  }
  cols = p->cols;
  while (r+1<=rows) row_ptr[++r]=l;  /* partial_CSR_lastrows */
  q->val = val;
  q->col_ind = col_ind;
  q->row_ptr = row_ptr;
  q->rows = rows;
  q->cols = cols;
  return q;          /* partial_CSR_properties */
}
