Require Import vcfloat.VCFloat vcfloat.FPLib.
From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp.analysis Require Import Rstruct.
Require Import fma_is_finite dotprod_model.
Require Import floatlib jacob_list_fun_model.
Require Import fma_real_func_model fma_floating_point_model.
Require Import inf_norm_properties common.
Require Import norm_compat.

Require Import Coq.Lists.List. Import ListNotations.
Set Bullet Behavior "Strict Subproofs".

Require Import lemmas.
Require Import fma_dot_acc fma_matrix_vec_mult.
From Flocq Require Import Binary.
Require Import finite_lemmas_additional.
Require Import fma_jacobi_forward_error.
Require Import float_acc_lems.
Require Import vec_sum_inf_norm_rel.
Require Import fma_dot_mat_model.
Require Import jacobi_preconditions.
Require Import jacobi_iteration_bound.

Section WITH_NANS.

Context {NANS: Nans}.

Definition jacobi_accuracy_preconditions {t} (A: matrix t) (b: vector t)  (tau: ftype t) := False.

Definition bound_jacobi_accuracy {t} (A: matrix t) (b: vector t)  (tau: ftype t) : R. 
Admitted.

Definition jacobi_accuracy {t: type}  (A: matrix t) (b: vector t) (y: vector t) : R :=
     let n := (length A).-1 in
    let A' := @matrix_inj _ A n.+1 n.+1 in
    let b' := @vector_inj _ b n.+1 in
    let x:= (FT2R_mat A')^-1 *m (FT2R_mat b') in
    vec_inf_norm ((FT2R_mat (@vector_inj _ y n.+1 )) - x).

Lemma jacobi_accurate {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (j: nat),
   jacobi_accuracy_preconditions A b acc ->
   let x0 := (repeat  (Zconst t 0) (length b)) in
   let y :=  jacobi_n A b x0 j in
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
    (forall i, (i <= j)%nat -> finite (norm2 (resid (jacobi_n A b x0 i)))) ->
    BCMP Lt false (norm2 (resid y)) (BMULT acc acc) = false  ->
    jacobi_accuracy A b y <= bound_jacobi_accuracy A b (norm2 (resid y)).
Admitted.

Lemma jacobi_accurate_alt {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (y: vector t),
   jacobi_accuracy_preconditions A b acc ->
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
    BCMP Lt false (norm2 (resid y)) (BMULT acc acc) = false  ->
    jacobi_accuracy A b y <= bound_jacobi_accuracy A b (norm2 (resid y)).
Abort.


End WITH_NANS.
