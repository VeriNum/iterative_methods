#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include "jacobi.h"

int main (int argc, char **argv) {
  struct csr_matrix *A2; double *A1, *b, *x;
  unsigned N, D, K, T, i;
  struct timeval start,finish,diff;
  if (argc!=5) {
   fprintf(stderr, "Usage: test N D K T\n\
   makes a random NxN matrix A with D nonzeros per row in addition\n\
   to 1 on the diagonal; then computes (A^K)I, using T threads.\n");
   exit(1);
  }
  N=atoi(argv[1]);
  D=atoi(argv[2]);
  K=atoi(argv[3]);
  T=atoi(argv[4]);
  A2 = make_example(N, D, 0.0);
  A1 = (double *)surely_malloc(N * sizeof(double));
  b = (double *)surely_malloc(N * sizeof(double));
  x = (double *)surely_malloc(N * sizeof(double));
  for (i=0; i<N; i++) A1[i]=1.0;
  for (i=0; i<N; i++) b[i]=1.0;
  for (i=0; i<N; i++) x[i]=1.0;
  jacobi(A1,A2,b,x,0.001);
  for (i=0; i<N; i++) printf("%8.4f ", x[i]);
  return 0;
}
