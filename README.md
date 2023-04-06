# Verified Error Analysis for Stationary Iterative Methods

This repository contains an end-to-end Coq formalization of accuracy and correctness of a Stationary iterative method called the Jacobi method.
Some important results in this formalization are summarized as follows:

## Formalization of FMA dot product:
The directory `StationaryMethods` contains formal definition of both a naive dot product and fma dot product, and results on finiteness of fma dot product.

- `dotprod_model.v` defines both naive or vanilla dot product, and the fma dot product.
- `fma_dot_acc.v` formalizes a result on the forward error bound (rounding error between a real model and a floating point model for the fma dot product) 
`fma_dotprod_forward_error_3` assuming that the fma dot product operation does not overflow.
- `fma_is_finite.v` formalizes conditions for which no overflow happens in the fma dot product operation. This lemma is called `finite_fma_from_bounded`.


## Proof of accuracy of the Jacobi iteration algorithm
The main results are summarized as follows:
- `fma_jacobi_forward_error.v`: This file contains a formalization of the forward error bound of the Jacobi iteration : `jacobi_forward_error_bound`, and defines a set of
conditions `forward_error_cond` for the lemma `jacobi_forward_error_bound` to hold.
- `jacobi_preconditions.v` : This file defines a set of conditions that need to hold for the convergence of a Jacobi iteration algorithm. These conditions are defined as
`jacobi_preconditions_Rcompute`. 
- `jacobi_iteration_bound.v`: This file contains the main proof of accuracy: `jacobi_iteration_bound_lowlevel`. This theorem uses the `jacobi_forward_error_bound` and `jacobi_preconditions_Rcompute` to prove that the residual converges to a values less than the user-defined tolerance with in `k_min` iterations which we define in the `jacobi_preconditions.v` file.
- `inf_norm_properties.v` : This file contains formalization of infinity norms of vectors and matrices.
- `fma_matrix_vec_mult.v` : This file contains results on forward error bound for a matrix-vector multiplication and connects to the fma dot product forward error bounds formalized in `fma_dot_acc.v`.
- `jacob_list_fun_model.v` : Defines a floating point functional model for the Jacobi ieration algorithm. `jacobi_n` defines a vector obtained after n Jacobi iterations, and `jacobi` defines the resulting vector from Jacobi iterations equipped with a stopping condition.
- `fma_dot_mat_model.v` : This file defines an equivalence (`func_model_equiv`) between the mathcomp definition of matrix and vector with a list definition of a matrix and vector. The mathcomp definitions are used in accuracy analysis and leverages the powerful analysis infrastructure provided by the mathcomp library in Coq. The list
definitons are needed to connect to data structures used in the correctness proof that uses powerful infrasture provided by the VST tool for C program verification.


## Proof of correctness of a C program implementing the Jacobi iteration
The `sparse` directory contains a sparse implentaion of the Jacobi iteration algorithm, proof of correctness of this implementation with respect to a functional model 
of Jacobi iteration, and connects the proof of accuracy with the proof of correctness to get an end-to-end verification of the Jacobi iteration.

- `jacobi.c` : a C program implementing Jacobi iteration algorithm using the sparse matrix vector multiplication defined in `sparse.c`.
- `spec_jacobi.v` : Defines specification for correctness of a Jacobi iteration algorithm. `jacobi2_spec` specifies that the C program refines the functional model, and 
`jacobi2_highspec` specifies that the C program converges to a result vector with norm below the defined threshold if it satifies `jacobi_preconditions`.
- `verif_jacobi2.v` : contains the proof of correctness of a C implementation of jacobi iteration with respect to the functional model. This proof of correctness is
formalized in the lemma `body_jacobi2`. Another important result in this file is the lemma `subsume_jacobi2` which states that if the C program respects `jacobi2_spec` then it respects the `jacobi2_highspec`.
- `main.v` : contains the main theorem `main_jacobi` that connects the proof of accuracy with the proof of correctness.

This repository also contains results on the forward error bound for naive or vanilla dot product. These files are contained in the repo: `naive_dot_product`.

# Building instructions
To build this project, install the latest release of [Coq platform](https://github.com/coq/platform), [VCFloat](https://github.com/VeriNum/vcfloat), and [VST](https://github.com/PrincetonUniversity/VST). Details on building the files in the `sparse` directory are mentioned in the README file in the `sparse` directory itself.

Then do:
```
git clone https://github.com/VeriNum/iterative_methods.git
cd iterative_methods
make
```


