#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <sys/time.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"
#include <assert.h>

int main (int argc, char **argv) {
  struct crs_matrix *m; double *v;
  unsigned N, D, K, T;
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
  m = make_example(N, D, 1.0);
  /*  dump_crs_matrix(m);
  printf("\n");
  print_crs_matrix(m); */
  gettimeofday(&start,NULL);
  v=par_eigenvector(m,K,T);  
  gettimeofday(&finish,NULL);
  printf("Time: %f\n", timediff(&start,&finish));
  return 0;
}
