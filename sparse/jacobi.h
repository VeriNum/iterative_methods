#include "sparse.h"

/* make_example(N,D,diag) creates a random NxN matrix where every
    diagonal element = diag, and each row has D random nondiagonal elements
    with values picked uniformaly between 0 and 1/4D; except that
    if two or more of these collide, their values will be added. */
struct crs_matrix *make_example(unsigned N, unsigned D, double diag);

/* vector A1 represents the diagonal of NxN matrix A.
   matrix A2 is A-A1.
   b and x are vectors of length N.
   At start, x is initialized to some arbitraryish vector.
   At finish, x is some vector that's within acc^2 Euclidean distance 
   of (A x - b).


 */
void jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, double acc);

extern unsigned threads;  /* how many threads should par_jacobi use */

/* same interface as jacobi, but computes in parallel */
void par_jacobi(double *A1, struct crs_matrix *A2, double *b, double *x, double acc);
