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


Definition bridge_safety_preconditions := False.

Search Bcompare.
Lemma bridge_is_not_falling_ever {t: type} :
 forall (A: matrix t) (b: vector t) (acc: ftype t) (k: nat),
   bridge_safety_preconditions ->
   let acc2 := BMULT acc acc in
   let x0 := (repeat  (Zconst t 0) (length b)) in
   let resid := jacobi_residual (diag_of_matrix A) (remove_diag A) b in
   (exists j,
    (j <= k)%nat /\
    let y :=  jacobi_n A b x0 j in
    let r2 := norm2 (resid y) in
    (forall i, (i <= j)%nat -> finite (norm2 (resid (jacobi_n A b x0 i)))) /\
    BCMP Lt false (norm2 (resid (jacobi_n A b x0 j))) acc2 = true ) ->
    exists (j:nat) (bnd:R),
    let y :=  jacobi_n A b x0 j in
    let n := (length A).-1 in
    let A' := @matrix_inj _ A n.+1 n.+1 in
    let b' := @vector_inj _ b n.+1 in
    (0 < length A)%coq_nat ->
    length A = length b ->
    let x:= (FT2R_mat A')^-1 *m (FT2R_mat b') in
    vec_inf_norm ((FT2R_mat (@vector_inj _ y n.+1 )) - x) <= bnd.
Admitted.
    





End WITH_NANS.