#include <stdlib.h>
#include <math.h>
#include "sparse.h"

void *surely_malloc(size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

double csr_row_vector_multiply(struct csr_matrix *m, double *v, unsigned i) {
  double *val = m->val;
  unsigned *col_ind = m->col_ind;
  unsigned *row_ptr = m->row_ptr;
  unsigned h, hi=row_ptr[i+1];
  double s=0.0;
  for (h=row_ptr[i]; h<hi; h++) {
      double x = val[h];
      unsigned j = col_ind[h];
      double y = v[j];
      s = fma(x,y,s);
  }
  return s;
}

void csr_matrix_vector_multiply_byrows (struct csr_matrix *m, double *v, double *p) {
  unsigned i, rows=csr_matrix_rows(m);
  for (i=0; i<rows; i++)
    p[i]=csr_row_vector_multiply(m,v,i);
}

/* csr_matrix_vector_multiply(m,v,p)
      multiplies a sparse matrix m by a dense vector v,
      putting the result into the (already allocated) dense vector p
*/
void csr_matrix_vector_multiply (struct csr_matrix *m, double *v, double *p) {
  unsigned i, rows=m->rows;
  double *val = m->val;
  unsigned *col_ind = m->col_ind;
  unsigned *row_ptr = m->row_ptr;
  unsigned next=row_ptr[0];
  for (i=0; i<rows; i++) {
    double s=0.0;
    unsigned h=next;
    next=row_ptr[i+1];
    for (; h<next; h++) {
      double x = val[h];
      unsigned j = col_ind[h];
      double y = v[j];
      s = fma(x,y,s);
    }
    p[i]=s;
  }
}

/* Let D be a diagonal matrix, whose diagonal is represented
   as the vector diag.  Let A be a matrix with number of rows equal
   to dimension of D.  let m represent A.
   Then diag_mult(diag,m) sets m to represent D*A */
void diag_mult(double *diag, struct csr_matrix *m) {
  unsigned i, h, rows=m->rows;
  for (i=0; i<rows; i++) {
    unsigned k=m->row_ptr[i+1];
    unsigned x = diag[i];
    for (h=m->row_ptr[i]; h<k; h++)
      m->val[h] *= x;
  }
}

unsigned csr_matrix_rows (struct csr_matrix *m) {
  return m->rows;
}

extern struct csr_matrix *coo_to_csr_matrix(struct coo_matrix *p);

struct csr_matrix *coo_to_csr_matrix_hack (struct coo_matrix *p) {
  return coo_to_csr_matrix(p);
}

