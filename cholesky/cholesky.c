extern double sqrt(double);
extern float sqrtf(float);

#define N 1000

void cholesky (unsigned n, double A[N][N], double R[N][N]) {
  unsigned i,j,k; double s;
  for (j=0; j<n; j++) {
     for (i=0; i<j; i++) {
       s = A[i][j];
       for (k=0; k<i; k++)
       	   s = s - R[k][i]*R[k][j];
       R[i][j]=s/R[i][i];
     }
     s = A[j][j];
     for (k=0; k<j; k++) {
     	 double rkj = R[k][j];
     	 s = s - rkj*rkj;
     }
     R[j][j] = sqrt(s);
  }
}

void choleskyf (unsigned n, float A[N][N], float R[N][N]) {
  unsigned i,j,k; float s;
  for (j=0; j<n; j++) {
     for (i=0; i<j; i++) {
       s = A[i][j];
       for (k=0; k<i; k++)
       	   s = s - R[k][i]*R[k][j];
       R[i][j]=s/R[i][i];
     }
     s = A[j][j];
     for (k=0; k<j; k++) {
     	 float rkj = R[k][j];
     	 s = s - rkj*rkj;
     }
     R[j][j] = sqrtf(s);
  }
}

     	  
