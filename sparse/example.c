#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <sys/time.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"
#include <assert.h>

void dump_crs_matrix  (struct crs_matrix *m) {
  int i,j;
  printf("    val: ");
  for (i=0; i<m->row_ptr[m->rows]; i++) printf ("xx ");
  printf("\ncol_ind: ");
  for (i=0; i<m->row_ptr[m->rows]; i++) printf ("%2d ",m->col_ind[i]);
  printf("\nrow_ptr:");
  for (i=0; i<=m->rows; i++) printf ("%2d ",m->row_ptr[i]);
  printf("\n");
}

void print_crs_matrix (struct crs_matrix *m) {
  unsigned i,j;
  for (i=0; i<m->rows; i++) {
    unsigned j=0;
    unsigned h, k=m->row_ptr[i+1];
    for (h=m->row_ptr[i]; h<k; h++) {
      while (j++ < m->col_ind[h]) printf(". ");
      if (m->val[h]<1.0) printf("x ");
      else printf("1 ");
    }
    while (j++ < m->cols) printf(". ");
    printf("\n");
  }
}

struct crs_matrix *make_example(unsigned N, unsigned D) {
  unsigned entries = N*(D+1);
  struct crs_matrix *m = (struct crs_matrix*)surely_malloc(sizeof (*m));
  double *val = (double *)surely_malloc(entries*sizeof(double));
  unsigned *col_ind = (unsigned *)surely_malloc(entries*sizeof(unsigned));
  unsigned *row_ptr = (unsigned *)surely_malloc((N+1)*sizeof(unsigned));
  m->val=val; m->col_ind=col_ind; m->row_ptr=row_ptr; m->rows=N; m->cols=N;
  unsigned i,h=0,k;
  for (i=0;i<N;i++) {
    unsigned j;
    row_ptr[i]=h;
    assert (h<entries);
    val[h]=1.0;
    col_ind[h]=i;
    h++;
    for (j=0; j<D; j++) {
      double x = drand48()/(4*D);
      unsigned c = lrand48()%N;
      unsigned k;
      for (k=row_ptr[i]; k<h; k++)
	if (col_ind[k]==c) {
	  val[k]+=x;
	  goto Done;
	}
      assert (h<entries);
      k=h++;
      while (k>row_ptr[i] && col_ind[k-1]>c) {
	col_ind[k]=col_ind[k-1];
	val[k]=val[k-1];
	k--;
      }
      col_ind[k]=c;
      val[k]=x;
    Done:
    }
  }
  row_ptr[i]=h;
  return m;
}

double *eigenvector(struct crs_matrix *m, unsigned iterations) {
  unsigned N=m->rows;
  unsigned i;
  double *vec1 = (double *)surely_malloc(N*sizeof(double));
  double *vec2 = (double *)surely_malloc(N*sizeof(double));
  double *p;
  for (i=0; i<N; i++) vec1[i]=1.0;
  for (i=0; i<iterations; i++) {
    crs_matrix_vector_multiply(m,vec1,vec2);
    p=vec1; vec1=vec2; vec2=p;
  }
  free(vec2);
  return vec1;
}

double *par_eigenvector(struct crs_matrix *m, unsigned iterations, unsigned T) {
  unsigned N=m->rows;
  unsigned i;
  double *vec1 = (double *)surely_malloc(N*sizeof(double));
  double *vec2 = (double *)surely_malloc(N*sizeof(double));
  double *p;
  struct task *jobs = make_multiply_tasks(m,vec1,vec2,T);
  for (i=0; i<N; i++) vec1[i]=1.0;
  for (i=0; i<iterations; i++) {
    /* BUG: This doesn't swap the vectors, so each iteration
       computes the same thing over again; but still useful
       for measuing timing*/
    do_tasks(jobs,T);
  }
  free(vec2);
  return vec1;
}


double timediff(struct timeval *start, struct timeval *finish) {
  return (finish->tv_sec-start->tv_sec)+
    (((double)finish->tv_usec)-((double)start->tv_usec))/1000000.0;
}

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
  m = make_example(N, D);
  /*  dump_crs_matrix(m);
  printf("\n");
  print_crs_matrix(m); */
  gettimeofday(&start,NULL);
  v=par_eigenvector(m,K,T);  
  gettimeofday(&finish,NULL);
  printf("Time: %f\n", timediff(&start,&finish));
  return 0;
}
