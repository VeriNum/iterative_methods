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

Lemma Rbar_le_real:
  forall (x y :R),
  Rbar_le x y ->
  (x <= y)%Re.
Proof.
intros. 
by unfold Rbar_le in H.
Qed.


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
assert ((Lim_seq (fun k: nat =>  vec_inf_norm (x_k k x0 b_real A_real)))
          = vec_inf_norm x1).
{ apply is_lim_seq_unique.
  apply is_lim_seq_ext with
  (fun k : nat =>
     (vec_inf_norm x1 + 
       (vec_inf_norm
         (x_k k x0 b_real A_real) - vec_inf_norm x1))%Re).
  intros. nra.
  assert (vec_inf_norm x1 = (vec_inf_norm x1 + 0)%Re).
  { nra. } rewrite [in X in (is_lim_seq _ X)]H0.
  apply is_lim_seq_plus'. 
  apply is_lim_seq_const.
  admit.
} apply Rbar_le_real.
rewrite -H0.


Admitted.

End WITH_NANS.




