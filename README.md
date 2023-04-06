# Verified Error Analysis for Stationary Iterative Methods

This repository contains an end-to-end Coq formalization of accuracy and correctness of a Stationary iterative method called the Jacobi method.
Some important results in this formalization are summarized as follows:

## Formalization of FMA dot product:
The directory `StationaryMethods` contains formal definition of both a naive dot product and fma dot product, and results on finiteness of fma dot product.

- `dotprod_model.v` defines both naive or vanilla dot product, and the fma dot product.
- `fma_dot_acc.v` formalizes a result on the forward error bound (rounding error between a real model and a floating point model for the fma dot product) 
`fma_dotprod_forward_error_3` assuming that the fma dot product operation does not overflow.
- `fma_is_finite.v` formalizes conditions for which no overflow happens in the fma dot product operation. This lemma is called `finite_fma_from_bounded`.









This repository contains the Coq formalization described in the paper *[Towards Verified Rounding Error Analysis for
Stationary Iterative Methods](https://github.com/VeriNum/iterative_methods/blob/main/correctness_workshop_paper.pdf)*, which appeared at Correctness 2022: Sixth International Workshop on Software Correctness for HPC Applications.

The main theorem for iterative round-off error is found in the file global_float_error.v. In order to run the proof script, you will need to have installed the [Coq platform](https://github.com/coq/platform) and [VCFloat](https://github.com/VeriNum/vcfloat).
