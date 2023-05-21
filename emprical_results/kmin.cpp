#include<bits/stdc++.h>
using namespace std;

#define N 10

double* matrix_vector_multiply (double** A, double* v, double* res){
    for (int i = 0; i < N; i++){
        for (int j = 0; j < N; j++){
            res[i] = res[i] + A[i][j] * v[j];
        }
    }

    return res;
}

double** matrix_matrix_sub(double **A1, double** A2, double** res){
    for (int i = 0; i < N; i++){
            for (int j = 0; j < N; j++){
                res[i][j] = A1[i][j]- A2[i][j];
            }
        }
    return res;
}

double* vector_sub(double* v1, double* v2, double* res){

    for (int i =0; i<N; i++){
        res[i] = v1[i] - v2[i];
    }
    return res;
}

void print_vector(double* v){
    for (int i = 0; i< N; i++){
        printf("%lf \n", v[i]);
    }
}

void print_matrix(double** A){
    for (int i = 0; i< N; i++){
        for (int j = 0; j < N; j++)
            printf("%lf \t", A[i][j]);
        printf("\n");
    }

}

double jacobi_oneiter(double** A1, double** A2, double* b, double* x, double* y){

    double s = 0.0;
    double* res = (double*)malloc(N * sizeof(double));
    for (int i = 0; i < N ; i++){ 
        double sum = 0.0;
        for(int j = 0; j < N; j++){
            sum = sum + A2[i][j] * x[j];
        }
        y[i] = b[i] - sum;
        double a1 = A1[i][i];
        double res = (1/a1) * y[i];
        double r = a1 * (res - x[i]);
        s = fma(r,r,s);
        y[i] = res;
    }
    print_vector(y);
    return s;
}




double* jacobi(double** A1, double** A2, double* b, double acc, double* x, int maxiter){

    double s = 1.0;
    double *y = (double*)malloc(N * sizeof(double));
    for(int i = 0; i<N; i++){
        y[i] = 0.0;
    }

    int k = 0;
    while(s*0 == 0.0 && s >= acc && maxiter){
        s = jacobi_oneiter(A1, A2, b, x, y);
        //print_vector(y);
        printf("%lf \n", s);
        for(int i = 0; i< N; i++){
            x[i] = y[i];
        }
        k++;
        maxiter--;
    }

    printf("Final iteration count is: %d \n", k);
    return x;
    
}


int main(){

    double **A = (double**)malloc(N * sizeof(double*));
    for (int i = 0; i < N; i++){
        A[i] = (double*)malloc(N * sizeof(double));
    }


    double* b = (double*)malloc(N* sizeof(double));

    // Initialize A
    for (int i = 0; i< N; i++){
        for (int j = 0; j< N; j++){
            A[i][j] = 0.0;
        }
    }

    A[0][0] = -3.0; A[0][1] = 1.0;
    A[N-1][N-1] = -3.0; A[N-1][N-2] = 1.0;
    for (int i = 1; i < N-1; i++){
        A[i][i] = -3.0;
        A[i][i-1] = 1.0;
        A[i][i+1] = 1.0;
    }



    // Initialize b
    for (int i = 0; i< N ; i++){
        b[i] = -1.0;
    }

    // Define A_1 matrix
    double **A1 = (double**)malloc(N * sizeof(double*));
    for (int i = 0; i < N; i++){
        A1[i] = (double*)malloc(N * sizeof(double));
    }

    for (int i = 0; i< N; i++){
        for (int j = 0; j < N; j++){
            A1[i][j] = 0.0;
        }
    }

    for (int i = 0; i< N; i++){
        A1[i][i] = A[i][i];
    }


    //print_matrix(A1);


    // Define A2 matrix
    double **A2= (double**)malloc(N * sizeof(double*));
    for (int i = 0; i < N; i++){
        A2[i] = (double*)malloc(N * sizeof(double));
    }
    for (int i = 0; i< N; i++){
        for (int j = 0; j < N; j++){
            A2[i][j] = 0.0;
        }
    }

    A2 = matrix_matrix_sub(A, A1, A2);
    


    // define accuracy
    double acc = 1e-3;
    
    // define initial vector
    double* x0 = (double*)malloc(N * sizeof(double));
    for (int i =0; i<N; i++){
        x0[i] = 0.0;
    }

    // Define maxiter
    int maxiter = INT_MAX;

    // define solution vector
    double* sol = (double*)malloc(N * sizeof(double));
    print_matrix(A2);
    sol = jacobi(A1, A2, b, acc, x0, maxiter);

    print_vector(sol);
    return 0;
}