# Sparse matrix-vector multiply, proved correct in VST

## How to build

(These instructions don't quite work on an M1 Mac, because of configuration path issues.  This will be fixed in the next Coq Platform release expected
 approximately December 2022.  Until then there are workarounds available,
 consult the author if necessary.)

In a Coq Platform that already has CompCert and VST installed, you must also install vcfloat and VSTlib (in that order!).
1. Clone the repo https://github.com/VeriNum/vcfloat # (or git pull latest version!)
2. cd vcfloat
3. make -j
4. make install # This will put things in your-coq-installation/coq/user-contrib/vcfloat
5. Clone the repo https://github.com/PrincetonUniversity/VST # (or git pull latest version!)
6. cd lib
7. make -j
8. make install # This will put things in your-coq-installation/coq/user-contrib/VSTlib

Now, in the current directory `sparse` :
- make run-clightgen  # this produces sparse.v
- make -j  # this builds verif_sparse.vo

## What is proved

The program `sparse.c` is proved correct with respect to the
specification `crs_matrix_vector_multiply_spec`
by lemma `body_crs_matrix_vector_multiply`.

You can find the specification in `spec_sparse.v`, supported
by the definition `crs_rep_aux` in `sparse_model.v`.

You can find the proof of the main lemma at the end of `verif_sparse.v`.
