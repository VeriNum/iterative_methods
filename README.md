# Verified Error Analysis for Stationary Iterative Methods

This repository contains an end-to-end Coq formalization of accuracy and correctness of a Stationary iterative method called the Jacobi method.
Some important results in this formalization are summarized as follows:

## Formalization of FMA dot product:
The directory `StationaryMethods` contains formal definition of both a naive dot product and fma dot product, and results on finiteness of fma dot product.

- `dotprod_model.v` defines both naive or vanilla dot product, and the fma dot product.
- `fma_dot_acc.v` formalizes a result on the forward error bound (rounding error between a real model and a floating point model for the fma dot product) 
`fma_dotprod_forward_error_3` assuming that the fma dot product operation does not overflow.
- `fma_is_finite.v` formalizes conditions for which no overflow happens in the fma dot product operation. This lemma is called `finite_fma_from_bounded`.

## Proof of correctness of a C program implementing the Jacobi iteration
This directory contains a sparse implentaion of the Jacobi iteration algorithm, proof of correctness of this implementation with respect to a functional model 
of Jacobi iteration, and connects the proof of accuracy with the proof of correctness to get an end-to-end verification of the Jacobi iteration.

- `jacobi.c` : a C program implementing Jacobi iteration algorithm using the sparse matrix vector multiplication defined in `sparse.c`.
- `spec_jacobi.v` : Defines specification for correctness of a Jacobi iteration algorithm. `jacobi2_spec` specifies that the C program refines the functional model, and 
`jacobi2_highspec` specifies that the C program converges to a result vector with norm below the defined threshold if it satifies some conditions formalized in the proof 
of accuracy for the Jacobi iteration algorithm.
- `verif_jacobi2.v` : contains the proof of correctness of a C implementation of jacobi iteration with respect to the functional model. This proof of correctness is
formalized in the lemma `body_jacobi2`. Another important result in this file is the lemma `subsume_jacobi2` which states that if the C program respects `jacobi2_spec` then it respects the `jacobi2_highspec`.
- `main.v` : contains the main theorem `main_jacobi` that connects the proof of accuracy with the proof of correctness.










This repository contains the Coq formalization described in the paper *[Towards Verified Rounding Error Analysis for
Stationary Iterative Methods](https://github.com/VeriNum/iterative_methods/blob/main/correctness_workshop_paper.pdf)*, which appeared at Correctness 2022: Sixth International Workshop on Software Correctness for HPC Applications.

The main theorem for iterative round-off error is found in the file global_float_error.v. In order to run the proof script, you will need to have installed the [Coq platform](https://github.com/coq/platform) and [VCFloat](https://github.com/VeriNum/vcfloat).
