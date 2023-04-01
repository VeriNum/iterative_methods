From mathcomp Require Import all_ssreflect ssralg  ssrnat all_algebra seq matrix .
From mathcomp.analysis Require Import Rstruct sequences normedtype landau topology.
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
From Coquelicot Require Import Coquelicot.


From mathcomp.classical Require Import boolp classical_sets functions.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope classical_set_scope.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Section WITH_NANS.

Context {NANS: Nans}.

Print series.


(** Check (series (fun n: nat => (vec_inf_norm x1))). **)


(** Define the solution vector at k-th iteration **)
Fixpoint x_k {n:nat} (k: nat) 
  (x0 b : 'cV[R]_n.+1) (A: 'M[R]_n.+1):= 
  match k with 
  | O => x0
  | p.+1 => x_fix (x_k p x0 b A ) b A
  end.
  
(*
Lemma x_bounded_by_x_k {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) :
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let x0 := (\col_(j < n.+1) 0%Re) in 
  (vec_inf_norm x1 <= 
      (lim (series (fun k : nat => vec_inf_norm (x_k k x0 b_real A_real)))))%Re.
Proof.

intros.  
pose proof (@limr_ge nat \oo eventually_filter).
apply /RleP.
apply H.
+

assert (ProperFilter \oo).
{ apply eventually_filter. }



by []. Locate "ProperFilter".




Print lim_id.
assert (vec_inf_norm x1 = lim (series ( fun _ => vec_inf_norm x1))).
{ rewrite lim_id.



rewrite -[in X in (X <= _)%Re]lim_id.


Admitted.
*)

Lemma Rbar_le_real:
  forall (x y :R),
  Rbar_le x y ->
  (x <= y)%Re.
Proof.
intros. 
by unfold Rbar_le in H.
Qed.


Lemma x_bounded_by_x_k {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) :
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let x0 := (\col_(j < n.+1) 0%Re) in
  let R_def := (vec_inf_norm ( A1_diag A_real) * 
                 matrix_inf_norm (A2_J_real A_real))%Re in 
  (R_def < 1)%Re ->
  Rbar_le (vec_inf_norm x1) 
    (Lim_seq (fun k: nat =>  vec_inf_norm (x_k k x0 b_real A_real))).
Proof.
intros.
assert (Lim_seq (fun k:nat => vec_inf_norm x1) = 
        vec_inf_norm x1).
{ by rewrite Lim_seq_const. } rewrite -H0.
apply Lim_seq_le_loc.
unfold eventually.
assert (is_lim_seq (fun n => ((R_def ^ n) * vec_inf_norm x1)%Re) 0%Re).
{ assert (0%Re = (0 * vec_inf_norm x1)%Re) by nra.
  rewrite H1. apply is_lim_seq_mult'.
  + apply is_lim_seq_geom. 
    rewrite Rabs_right. apply H.
    unfold R_def. apply Rle_ge. apply Rmult_le_pos.
    apply /RleP. apply vec_norm_pd.
    apply /RleP. apply matrix_norm_pd.
  + apply is_lim_seq_const.
} rewrite <-is_lim_seq_spec in H1. 


unfold is_lim_seq' in H1.
assert ((0 < 1)%Re) by nra.
specialize (H1 (mkposreal 1%Re H2)).
unfold eventually in H1. 
destruct H1 as [N H1].
exists N. intros.
specialize (H1 n0). specialize (H1 H3).
simpl in H1.
apply RIneq.Rminus_le. apply /RleP.
apply reverse_triang_ineq. apply /RleP.
apply Rle_trans wtih 







  (vec_inf_norm x1 <= 
      (Lim_seq (fun k: nat =>  vec_inf_norm (x_k k x0 b_real A_real))%Re))%Re.
Proof.
intros.
apply Rbar_le_real.
assert (Lim_seq (fun k:nat => vec_inf_norm x1) = 
        vec_inf_norm x1).
{ by rewrite Lim_seq_const. } rewrite -H.
pose proof Lim_seq_le_loc.
specialize (H0 (fun=> vec_inf_norm x1)
               (fun k : nat =>
                    vec_inf_norm (x_k k x0 b_real A_real))).

apply (@Lim_seq_le_loc (fun=> vec_inf_norm x1) 
         (fun k : nat =>
            vec_inf_norm (x_k k x0 b_real A_real))).


).









(** bound for ||x|| **)
Lemma x_bound_exists {t} {n:nat}
  (A : 'M[ftype t]_n.+1) (b : 'cV[ftype t]_n.+1) :
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := A_real^-1 *m b_real in
  let x1 := x_fix x b_real A_real in
  let A1_inv_real := FT2R_mat (A1_inv_J A) in 
  let A2_real := FT2R_mat (A2_J A) in
  let R_def := (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
                     matrix_inf_norm (A2_real))%Re in
  (R_def < 1)%Re ->
   (vec_inf_norm x1 <= 
      (((vec_inf_norm (FT2R_mat (A1_inv_J A)) + default_abs t) / (1 - default_rel t)) * 
        vec_inf_norm (b_real)) / (1 - R_def))%Re.
Proof.
intros.
remember (\col_(j < n.+1) 0%Re) as x0.
apply Rle_trans with
  (Lim_seq (fun k: nat =>  vec_inf_norm (x_k k x0 b_real A_real))).
+





apply Rle_trans with
  (lim (series (fun k : nat => vec_inf_norm (x_k k x0 b_real A_real)))).
+ (** ||x|| <= lim ||x_k|| **)
   admit.
+ 



Admitted.



End WITH_NANS.



