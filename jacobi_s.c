#include <math.h>
#include <stdio.h>
#include <stdlib.h>

float fma_dot
  (int n, float *Ai, float *x) {
    if (n == 1) return Ai[0]*x[0];
    return fmaf(Ai[n-1],x[n-1],fma_dot(n-1,Ai,x));
}

void jacobi_method
  (int n, float **A, float *b, float *x,
    double eps, int max_it)
{
  for  (int k = 0; k < max_it; k++) {
    float y = 0.0f;
    double res = 0.0;
    for (int i = 0; i < n; i++) {
      y = b[i] - fma_dot(n,A[i],x);
      res += fabs(y);
      y /= A[i][i];
      x[i] += y;
    }
    printf("res = %.6f\n",res);
    if (res <= eps) break;
  }
}

void read_Abx (int n, const char* filename,
  float **A, float *b, float *x) {
  FILE *read_file;
  read_file = fopen(filename, "r");
  for (int i=0; i<n; i++) {
    for (int j=0; j<n; j++) {
      fscanf(read_file, "%f", &A[i][j]);
    }
  }
  for (int i=0; i<n; i++) {
      fscanf(read_file, "%f", &b[i]);
    }
  for (int i=0; i<n; i++) {
      fscanf(read_file, "%f", &x[i]);
    }
  printf("\n");
  printf("coefficient matrix A: \n");
  for (int i=0; i<n; i++) {
    for (int j=0; j<n; j++) {
      printf("%f     ", A[i][j]);
    }
    printf("\n");
  }
  printf("\n");
  printf("RHS b: \n");
  for (int i=0; i<n; i++) {
      printf("%f     ", b[i]);
      printf("\n");
  }
  printf("\n");
  printf("initial guess x: \n");
  for (int i=0; i<n; i++) {
      printf("%f     ", x[i]);
      printf("\n");
  }
  printf("\n");
}

int main (int argc, char **argv) {
  if (argc!=5) {
   fprintf(stderr, "requires 4 arguments: dimension of system, \n\
   desired residual, max iterations, and the name of file \n\
   containing the coefficient matrix A, RHS b, and initial guess x0.\n");
   exit(1);
  }
  int n = atoi(argv[1]);
  float eps = atof(argv[2]);
  int max_it = atoi(argv[3]);
  const char *filename = argv[4];

  float **A;
  float *b, *x;
  A = (float**) calloc(n,sizeof(float*));
  for (int i = 0; i < n; i++) {
    A[i] = (float*) calloc(n,sizeof(float));
  }
  b = (float*) calloc(n,sizeof(float));
  x = (float*) calloc(n,sizeof(float));

  read_Abx(n,filename,A,b,x);

  jacobi_method(n,A,b,x,eps,max_it);
  printf("\n");a
  printf("solution x: \n");
  for (int i = 0; i < n; i++) {printf("%.6f\n",x[i]);}

  free(A);
  free(b);
  free(x);
  return 0;
}
