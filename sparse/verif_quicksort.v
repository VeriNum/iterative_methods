Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import build_csr sparse_model spec_sparse spec_build_csr distinct partial_csr.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := Build_CSR_ASI ++ SparseASI ++ MathASI.


Lemma body_coo_to_csr_matrix: semax_body Vprog Gprog f_coo_quicksort coo_quicksort_spec.
Proof.
start_function.