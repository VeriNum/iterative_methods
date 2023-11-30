#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "parsplit.h"
#include "sparse.h"
#include "parsparse.h"
#include "jacobi.h"

void vector_add(double *x, double *y, double *r, unsigned N) 
{
  unsigned i;
  for (i=0; i<N; i++) r[i] = x[i]+y[i];
}

void matrix_vector_multiplication(double *A, double *v, double *res, unsigned N) 
{
  int i, j;
  double t;
  for (i = 0; i < N; i++) {
    t = 0.0;
    for (j = 0; j < N; j++) {
      t = fma(A[i*N + j], v[j], t);
    }
    res[i] = t;
  }
}

void vector_linear_comb(double a1, double *v1, double a2, double *v2, double *res, unsigned N)
{
  int i;
  for (i = 0; i < N; i++) {
    res[i] = fma(a1, v1[i], 0);
    res[i] = fma(a2, v2[i], res[i]);
  }
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
  int i, j;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
        B[i*N + j] = 0.0;
    }
  }

  for (i = 0; i < block_num; i++) {
    if (i == block_num - 1) {
      block_inverse(A, B, block_idx[i], N, N);
    } else {
      block_inverse(A, B, block_idx[i], block_idx[i+1], N);
    }
  }
}

void block_diagonal_partition (double *A, double *A1, double *A2, unsigned *block_idx, unsigned N, unsigned block_num)
{
  int i, j, k;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      A1[i*N + j] = 0.0;
      A2[i*N + j] = A[i*N + j];
    }
  }

  for (i = 0; i < block_num; i++) {
    if (i == block_num - 1) {
      for (j = block_idx[i]; j < N; j++) {
        for (k = block_idx[i]; k < N; k++) {
          A1[j*N + k] = A[j*N + k];
          A2[j*N + k] = 0.0;
        }
      }
    } else {
      for (j = block_idx[i]; j < block_idx[i+1]; j++) {
        for (k = block_idx[i]; k < block_idx[i+1]; k++) {
          A1[j*N + k] = A[j*N + k];
          A2[j*N + k] = 0.0;
        }
      }
    }
  }
}

// x^(k+1) := A1^(-1) (b - A2 x^(k))

void block_jacobi_oneiter(double *A1inv, double *A2, double *b, double *x, unsigned N)
{
  double t1[N];
  double t2[N];

  matrix_vector_multiplication(A2, x, t1, N);
  vector_linear_comb(1.0, b, -1.0, t1, t2, N);
  matrix_vector_multiplication(A1inv, t2, x, N);

}

double l2norm(double *x, unsigned N)
{
  double s = 0.0;
  for (int i = 0; i < N; i++) {
    s = fma(x[i], x[i], s);
  }
  return sqrt(s);
}

double residual(double *A, double *b, double *x, unsigned N)
{
  double s = 0.0;
  double t1[N];
  matrix_vector_multiplication(A, x, t1, N);

  // output t
  // printf("t = [");
  // for (int i = 0; i < N; i++) {
  //   printf("%.3f ", t[i]);
  // }
  // printf("]\n");

  double t2[N];
  vector_linear_comb(1.0, b, -1.0, t1, t2, N);

  s = l2norm(t2, N);
  return s;
}

void block_jacobi(double *A, double *b, double *x0, unsigned *block_idx, unsigned N, unsigned block_num, double acc, unsigned max_iter) 
{
  double A1[N * N];
  double A2[N * N];
  block_diagonal_partition(A, A1, A2, block_idx, N, block_num);

  double A1inv[N * N];
  block_matrix_inverse(A1, A1inv, block_idx, N, block_num);

  double x[N];
  for (int i = 0; i < N; i++) {
    x[i] = x0[i];
  }

  double res = 2 * acc;
  unsigned iter = 0;

  while (res > acc && iter < max_iter) {
    block_jacobi_oneiter(A1inv, A2, b, x, N);

    printf("Iteration %d:\n", iter);
    res = residual(A, b, x, N);
    iter++;
    printf("x = [");
    for (int i = 0; i < N; i++) {
      printf("%.4f ", x[i]);
    }
    printf("]\n");
    printf("residual = %.6f\n", res);

  }
}


int main()
{
  unsigned N = 50;
  double A[N * N];

  unsigned block_idx[5] = {0, 10, 20, 30, 40};
  for (int i = 0; i < N; i++){
    for (int j = 0; j < N; j++) {
      if (i == j) {
        A[i * N + j] = 2.0 * N + 1;
      } else {
        A[i * N + j] = 1.0;
      }
    }
  }


  double tempx[N];
  for (int i = 0; i < N; i++) tempx[i] = 1.0;

  double b[N];
  matrix_vector_multiplication(A, tempx, b, N);

  double x[N];
  for (int i = 0; i < N; i++) x[i] = 100.0;

  block_jacobi(A, b, x, block_idx, N, 5, 1e-6, 100);

  // output matrix A
  // printf("Matrix A:\n");
  // for (int i = 0; i < N; i++){
  //   for (int j = 0; j < N; j++) {
  //     printf("%.3f ", A[i*N+j]);
  //   }
  //   printf("\n");
  // }

  // double v[N];
  // for (int i = 0; i < N; i++) v[i] = i;
  // double res[N];
  // matrix_vector_multiplication(A, v, res, N);

  // printf("Matrix-vector multiplication result:\n");
  // for (int i = 0; i < N; i++) {
  //   printf("%.3f ", res[i]);
  // }

  // block_matrix_inverse(A, B, block_idx, 5, 2);

  // output matrix B
  // printf("Matrix B:\n");
  // for (int i = 0; i < N; i++){
  //   for (int j = 0; j < N; j++) {
  //     printf("%.4f ", B[i*N+j]);
  //   }
  //   printf("\n");
  // }

}
