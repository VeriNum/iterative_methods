From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify 
                            Float_notations Automate.

Require Import floatlib jacob_list_fun_model fma_dot_mat_model 
               inf_norm_properties fma_matrix_vec_mult.

Require Import common fma_dot_acc float_acc_lems dotprod_model.
Require Import fma_matrix_vec_mult vec_sum_inf_norm_rel.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas fma_is_finite.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section WITHNANS.
Context {NANS: Nans}. 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).


(** Define forward error **)

Fixpoint vec_to_list_real {n:nat} (m:nat) (v :'cV[R]_n.+1)
   : list R := 
   match m with 
   | O => []
   | S p => [v (@inord n p) ord0] ++ vec_to_list_real p v
   end.


Definition A1_diag {n: nat} (A: 'M[R]_n.+1) : 'cV[R]_n.+1:=
  \col_i (1 / (A i i))%Re.

Definition diag_matrix_vec_mult_R {n:nat} (v1 v2 : 'cV[R]_n.+1)
  : 'cV[R]_n.+1 :=
  \col_i ((nth (n.+1.-1 -i) (vec_to_list_real n.+1 v1) 0%Re) * 
          (nth (n.+1.-1 -i) (vec_to_list_real n.+1 v2) 0%Re)).

Definition A2_J_real {n:nat} (A: 'M[R]_n.+1): 
  'M[R]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then 0%Re else A i j.

(** Define real real functional model **)
Definition x_fix {n:nat} x b (A: 'M[R]_n.+1) :
  'cV[R]_n.+1 :=
  let r := b - ((A2_J_real A) *m x) in
  diag_matrix_vec_mult_R (A1_diag A) r.

Definition f_error {ty} {n:nat} m b x0 x (A: 'M[ftype ty]_n.+1):=
  let x_k := X_m_jacobi m x0 b A in 
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x := x_fix x b_real A_real in
  vec_inf_norm (FT2R_mat x_k - x).


Definition matrix_of_diag_A1 {ty} {n:nat} (A: 'M[ftype ty]_n.+1) :
 'M[ftype ty]_n.+1 :=
 \matrix_(i, j) 
    (if (i == j :> nat) then (A1_inv_J A i ord0) else (Zconst ty 0)).


Lemma rho_ge_0 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let R := vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real) in
  let delta := default_rel ty in
  let rho := ((g ty n.+1 * (1+ delta) * (1+ g ty n.+1) + delta + delta * g ty n.+1 + g ty n.+1) * R)%Re in
  (0 <= rho)%Re.
Proof.
intros.
unfold rho.
repeat apply Rmult_le_pos.
+ apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    * apply Rplus_le_le_0_compat.
      ++ admit.
      ++ unfold delta. apply default_rel_ge_0.
    * apply Rmult_le_pos.
      ++ unfold delta. apply default_rel_ge_0.
      ++ apply g_pos.
  - apply g_pos.
+ apply /RleP. apply vec_norm_pd.
+ apply /RleP. apply matrix_norm_pd.
Admitted.



(** State the forward error theorem **)
Theorem jacobi_forward_error_bound {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  x != 0 ->
  (forall (A: 'M[ftype ty]_n.+1) (v: 'cV[ftype ty]_n.+1)
          (xy : ftype ty * ftype ty) (i : 'I_n.+1),
    In xy
      (combine
         (vec_to_list_float n.+1
            (\row_j A (inord i) j)^T)
         (vec_to_list_float n.+1 v)) ->
    is_finite (fprec ty) (femax ty) xy.1 = true /\
    is_finite (fprec ty) (femax ty) xy.2 = true /\ 
      Rabs (FT2R (fst (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1) - default_abs ty) /\
      Rabs (FT2R (snd (xy))) <= sqrt (F' ty / (INR n.+1 * (1 + default_rel ty)^n.+1) - default_abs ty)) ->
  
   let R := vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real) in
   let delta := default_rel ty in
   let rho := ((g ty n.+1 * (1+ delta) * (1+ g ty n.+1) + delta + delta * g ty n.+1 + g ty n.+1) * R)%Re in
   let d_mag := ( g ty n.+1 * (1 + delta) * (1 + g ty n.+1) * R * vec_inf_norm x +
                  (delta + delta * g ty n.+1 + g ty n.+1) * R * vec_inf_norm x +
                  g ty n.+1 * (1 + delta) * vec_inf_norm (A1_diag A_real) * vec_inf_norm b_real  +
                  g ty n.+1 * g1 ty n.+1 (n.+1 - 1)%nat * (1 + delta) * vec_inf_norm (A1_diag A_real) +
                  g1 ty n.+1 (n.+1 - 1)%nat * (1+ delta) * vec_inf_norm (A1_diag A_real) +
                  delta * vec_inf_norm (A1_diag A_real) * vec_inf_norm b_real)%Re in

  (rho < 1)%Re ->
  (A =  ((matrix_of_diag_A1 A) +f (A2_J A))) ->
  forall x0: 'cV[ftype ty]_n.+1, 
  forall k:nat,
  (f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + ((1 - rho^k) / (1 - rho))* d_mag)%Re.
Proof.
induction k.
+ simpl. nra.
+ simpl.
  assert (((1 - rho * rho ^ k) / (1 - rho))%Re = 
           (rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re).
  { assert ((rho * ((1 - rho ^ k) / (1 - rho)) + 1)%Re = 
            (rho * ((1 - rho ^ k) / (1 - rho)) + (1 - rho) * / (1 - rho))%Re).
    { rewrite Rinv_r; nra. } rewrite H3. clear H3.
    Search ((_ + _ ) * _ )%Re.
    assert ((rho * ((1 - rho ^ k) / (1 - rho)) +
                  (1 - rho) * / (1 - rho))%Re = 
             (( (rho * (1 - rho ^ k)) * / (1 - rho))%Re + 
              (1 - rho) * / (1 - rho))%Re).
    { nra. } rewrite H3. clear H3.
    rewrite -Rmult_plus_distr_r. nra.
  } rewrite H3. 
  Search ( (_ + _ ) * _)%Re.
  rewrite Rmult_plus_distr_r.
  assert ((rho * rho ^ k * f_error 0 b x0 x A +
            (rho * ((1 - rho ^ k) / (1 - rho)) * d_mag + 1 * d_mag))%Re = 
           (rho * (rho ^ k * f_error 0 b x0 x A +
                        (1 - rho ^ k) / (1 - rho) * d_mag) + d_mag)%Re).
  { nra. } rewrite H4.
  apply Rle_trans with (rho * f_error k b x0 x A + d_mag)%Re.
  - admit.
  - apply Rplus_le_compat_r. apply Rmult_le_compat_l.
    * admit.
    * nra.
Admitted. 
  












End WITHNANS.