#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"

void vector_add(double *x, double *y, double *r, unsigned N) {
  unsigned i;
  for (i=0; i<N; i++) r[i] = x[i]+y[i];
}

/* vector A1 represents the diagonal of NxN matrix A.
   matrix A2 is A-A1.
   b and x are vectors of length N.
 */
void jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, unsigned k) {
  unsigned N=A2->rows;
  unsigned i;
  double *y = (double *)surely_malloc(N*sizeof(double));
  for (i=0; i<N; i++) A1[i] = 1.0/A1[i];
  for (i=0; i<N; i++) b[i] *= A1[i];
  diag_mult(A1,A2);
  for (i=0; i<k; i++) {
    crs_matrix_vector_multiply(A2,x,y);
    vector_add(y,b,x,N);
  }
}

    
