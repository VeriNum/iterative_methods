#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"
#include "jacobi.h"

void vector_add(double *x, double *y, double *r, unsigned N) {
  unsigned i;
  for (i=0; i<N; i++) r[i] = x[i]+y[i];
}


void block_inverse(double *A, double *B, unsigned left, unsigned right, unsigned N)
{
  int i, j, k;
  double t;

  for (i = left; i < right; i++) {
    for (j = left; j < right; j++) {
      if (i == j) {
        B[i*N + j] = 1.0;
      } else {
        B[i*N + j] = 0.0;
      }
    }
  }

  for (i = left; i < right; i++) {
    t = A[i*N + i];
    for (j = left; j < right; j++) {
      A[i*N + j] /= t;
      B[i*N + j] /= t;
    }

    for (j = left; j < right; j++) {
      if (i == j) continue;
      t = A[j*N + i];
      for (k = left; k < right; k++) {
        A[j*N + k] -= t * A[i*N + k];
        B[j*N + k] -= t * B[i*N + k];
      }
    }
  }
}

void block_matrix_inverse(double *A, double *B, unsigned *block_idx, unsigned N, unsigned block_num)
{
  int i;
  for (i = 0; i < block_num; i++) {
    if (i == block_num - 1) {
      block_inverse(A, B, block_idx[i], N, N);
    } else {
      block_inverse(A, B, block_idx[i], block_idx[i+1], N);
    }
  }
}

int main()
{
  unsigned N = 5;
  double A[N * N];
  double B[N * N];
  unsigned block_idx[2] = {0, 2};
  for (int i = 0; i < 5; i++){
    for (int j = 0; j < 5; j++) {
      A[i*5+j] = 1.0 / (i + j + 1.0);
      B[i*5+j] = 0.0;
    }
  }

  // output matrix A
  printf("Matrix A:\n");
  for (int i = 0; i < 5; i++){
    for (int j = 0; j < 5; j++) {
      printf("%.4f ", A[i*5+j]);
    }
    printf("\n");
  }

  block_matrix_inverse(A, B, block_idx, 5, 2);

  // output matrix B
  printf("Matrix B:\n");
  for (int i = 0; i < 5; i++){
    for (int j = 0; j < 5; j++) {
      printf("%.4f ", B[i*5+j]);
    }
    printf("\n");
  }

}
