From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp Require Import Rstruct.
Import List ListNotations.


From vcfloat Require Import RAux FPStdLib.

Require Import floatlib inf_norm_properties.

Require Import common fma_dot_acc float_acc_lems dotprod_model.
Require Import fma_matrix_vec_mult vec_sum_inf_norm_rel.
Require Import fma_real_func_model fma_floating_point_model.
Require Import fma_jaboci_forward_error.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas fma_is_finite finite_lemmas_additional.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section WITHNANS.
Context {NANS: FPCore.Nans}. 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).

Lemma rho_sparse_ge_0 {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1) (r : nat):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel ty in
  let rho := ((((1 + g ty r.+1) * (1 + delta) *
                  g ty r.+1 + delta * (1 + g ty r.+1) +
                  g ty r.+1) * (1 + delta) + delta) * R +
                (((1 + g ty r.+1) * (1 + delta) *
                  g ty r.+1 + delta * (1 + g ty r.+1) +
                  g ty r.+1) * default_abs ty +
                 default_abs ty) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re in
 (0 <= rho)%Re.
Proof.
 intros.
 unfold rho.
 repeat apply Rplus_le_le_0_compat.
 + apply Rmult_le_pos.
   - apply Rplus_le_le_0_compat.
     * apply Rmult_le_pos.
       ++ apply Rplus_le_le_0_compat; last by apply g_pos.
          repeat apply Rplus_le_le_0_compat; apply Rmult_le_pos. 
          -- apply Rmult_le_pos; try apply Rplus_le_le_0_compat; 
             try nra; try apply g_pos. unfold delta. 
             apply default_rel_ge_0.
          -- apply g_pos.
          -- unfold delta. 
             apply default_rel_ge_0.
          -- apply Rplus_le_le_0_compat; last by apply g_pos. nra. 
       ++ apply Rplus_le_le_0_compat. nra.  
          unfold delta. 
          apply default_rel_ge_0.
     * unfold delta. 
       apply default_rel_ge_0.
   - unfold R2. apply Rmult_le_pos.
     * apply /RleP. apply vec_norm_pd.
     * apply /RleP. apply matrix_norm_pd.
 + apply Rmult_le_pos.
   - repeat apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
     apply Rmult_le_pos; last by apply default_abs_ge_0.
     apply Rplus_le_le_0_compat; last by apply g_pos.
     apply Rplus_le_le_0_compat. 
     * repeat apply Rmult_le_pos.
       ++ apply Rplus_le_le_0_compat; last by apply g_pos. nra. 
       ++ apply Rplus_le_le_0_compat. nra.  
          unfold delta. 
          apply default_rel_ge_0.
       ++ apply g_pos.
     * apply Rmult_le_pos.
       ++ unfold delta. 
          apply default_rel_ge_0.
       ++ apply Rplus_le_le_0_compat; last by apply g_pos. nra.
   - apply /RleP. apply matrix_norm_pd.
 + unfold R2. apply Rmult_le_pos.
     * apply /RleP. apply vec_norm_pd.
     * apply /RleP. apply matrix_norm_pd.
Qed.

Definition rho_def_sparse  {t: type} {n:nat} 
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) 
  (r : nat) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in  
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel t in
  ((((1 + g t r.+1) * (1 + delta) *
                  g t r.+1 + delta * (1 + g t r.+1) +
                  g t r.+1) * (1 + delta) + delta) * R +
                (((1 + g t r.+1) * (1 + delta) *
                  g t r.+1 + delta * (1 + g t r.+1) +
                  g t r.+1) * default_abs t +
                 default_abs t) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re.

Definition d_mag_def_sparse {t: type} {n:nat} 
  (A: 'M[ftype t]_n.+1) (b: 'cV[ftype t]_n.+1) 
  (r : nat) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in  
  let x:= mulmx (A_real^-1) b_real in
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
  let delta := default_rel t in
  ((g t r.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_diag A_real) *
                      (1 + delta) + default_abs t) *
                     vec_inf_norm b_real) +
                    (1 + g t r.+1) * g1 t r.+1 (r.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_diag A_real) *
                     (1 + delta) + default_abs t) +
                    g1 t r.+1 (r.+1 - 1) +
                    (vec_inf_norm (A1_diag A_real) * delta +
                     default_abs t) * vec_inf_norm b_real +
                    ((((1 + g t r.+1) * (1 + delta) *
                       g t r.+1 + delta * (1 + g t r.+1) +
                       g t r.+1) * (1 + delta) + delta) * R +
                     (((1 + g t r.+1) * (1 + delta) *
                       g t r.+1 + delta * (1 + g t r.+1) +
                       g t r.+1) * default_abs t +
                      default_abs t) *
                     matrix_inf_norm (A2_J_real A_real)) *
                    vec_inf_norm (x_fix x b_real A_real))%Re.

Lemma d_mag_sparse_ge_0 {t: type} {n:nat} (A: 'M[ftype t]_n.+1) 
  (b: 'cV[ftype t]_n.+1) (r : nat) :
  (0 <= d_mag_def_sparse A b r)%Re.
Proof.
  unfold d_mag_def_sparse.
  repeat apply Rplus_le_le_0_compat.
  + repeat try apply Rmult_le_pos; try repeat apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; try apply g_pos.
      apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
    - apply default_rel_ge_0.
    - apply Rmult_le_pos. 
      apply /RleP. apply vec_norm_pd.
      apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
    - apply default_abs_ge_0.
    - apply /RleP. apply vec_norm_pd.
  + repeat try apply Rmult_le_pos.
    - apply Rplus_le_le_0_compat. nra. apply g_pos.
    - apply pos_INR.
    - nra.
    - apply bpow_ge_0.
    - apply Rplus_le_le_0_compat. nra. apply g_pos.
    - apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0. 
    - apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
      apply Rmult_le_pos; last by (apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0).
      apply /RleP. apply vec_norm_pd.
  + apply g1_pos.
  + apply Rmult_le_pos; last by (apply /RleP; try apply vec_norm_pd).
    apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
    apply Rmult_le_pos; last by apply default_rel_ge_0.
    apply /RleP. apply vec_norm_pd.
  + repeat apply Rmult_le_pos; last by (apply /RleP; try apply vec_norm_pd).
    repeat apply Rplus_le_le_0_compat.
    - repeat apply Rmult_le_pos.
      * repeat apply Rplus_le_le_0_compat; last by apply default_rel_ge_0.
        repeat apply Rmult_le_pos.
        ++ apply Rplus_le_le_0_compat; last by apply g_pos.
           apply Rplus_le_le_0_compat.
           -- repeat apply Rmult_le_pos;last by apply g_pos.
              apply Rplus_le_le_0_compat; try nra; try apply g_pos.
              apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
           -- apply Rmult_le_pos; first by apply default_rel_ge_0.
              apply Rplus_le_le_0_compat; try nra; try apply g_pos.
        ++ apply Rplus_le_le_0_compat. nra. apply default_rel_ge_0.
      * apply /RleP. apply vec_norm_pd.
      * apply /RleP. apply matrix_norm_pd.
    - repeat apply Rmult_le_pos; last by (apply /RleP; apply matrix_norm_pd).
      repeat apply Rplus_le_le_0_compat; last by apply default_abs_ge_0.
      repeat apply Rmult_le_pos; last by apply bpow_ge_0.
      * apply Rplus_le_le_0_compat;last by apply g_pos.
        apply Rplus_le_le_0_compat.
        ++ repeat apply Rmult_le_pos;last by apply g_pos.
           apply Rplus_le_le_0_compat; try nra; try apply g_pos.
           apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
        ++ apply Rmult_le_pos; first by apply default_rel_ge_0.
           apply Rplus_le_le_0_compat. nra. apply g_pos.
      * nra.
Qed.

Lemma x_k_bound_sparse {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) 
  (r : nat) (HA : is_r_sparse_mat A r) k i:
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def_sparse A b r in 
  let d_mag := d_mag_def_sparse A b r in 
   (f_error k b x0 x A <=
       rho ^ k * f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) * d_mag)%Re ->
    (Rabs (FT2R (X_m_jacobi k x0 b A i ord0)) <= 
      vec_inf_norm
         (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       rho ^ k * f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) * d_mag)%Re.
Proof.
intros.
rewrite [in X in (X <= _)%Re]/f_error in H.
apply Rle_trans with 
  (vec_inf_norm (FT2R_mat (X_m_jacobi k x0 b A))).
  - unfold vec_inf_norm.
    apply Rle_trans with 
     [seq Rabs
          (FT2R_mat (X_m_jacobi k x0 b A)
             i0 0)
          | i0 <- enum 'I_n.+1]`_i.
    * rewrite seq_equiv. rewrite nth_mkseq; 
      last by apply ltn_ord.
      rewrite mxE. rewrite inord_val. apply Rle_refl.
    * apply /RleP.
      apply (@bigmaxr_ler  _ 0%Re [seq Rabs
                                   (FT2R_mat (X_m_jacobi k x0 b A) i0 0)
                               | i0 <- enum 'I_n.+1] i).
      rewrite size_map size_enum_ord.
      by apply ltn_ord.
  - assert (forall x y z d: R, (x - y <= z + d)%Re -> (x <= y + z + d)%Re).
    { intros. nra. } apply H0.
    apply /RleP. apply reverse_triang_ineq.
    by apply /RleP.
Qed.

Lemma bound_1_sparse  {t: type} {n:nat}
  (A : 'M[ftype t]_n.+1) (x0 b : 'cV[ftype t]_n.+1) (k:nat) m
  (r : nat) (HA : is_r_sparse_mat A r):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def_sparse A b r in 
  let d_mag := d_mag_def_sparse A b r in 
  input_bound A x0 b ->
  (rho < 1)%Re ->
  (0 < f_error 0 b x0 x A -
         d_mag_def A b * / (1 - rho_def_sparse A b r))%Re ->
  (Rabs (FT2R (A (inord m) (inord m))) *
   (rho ^ k * (1 + rho) *
    (f_error 0 b x0 x A -
     d_mag * / (1 - rho)) +
    2 * d_mag * / (1 - rho) +
    2 *
    vec_inf_norm
      (x_fix x (FT2R_mat b) (FT2R_mat A))) <
   (sqrt (fun_bnd t n.+1) - default_abs t) /
   (1 + default_rel t) /
   (1 + default_rel t))%Re.
Proof.
intros.
unfold input_bound in H.
destruct H as [bnd1 H]. clear H.
apply Rle_lt_trans with 
(Rabs (FT2R (A (inord m) (inord m))) *
        (1 * (1 + rho_def_sparse A b r) *
         (f_error 0 b x0
            ((FT2R_mat A)^-1 *m 
             FT2R_mat b) A -
          d_mag_def A b *
          / (1 - rho_def_sparse A b r)) +
         2 * d_mag_def A b *
         / (1 - rho_def_sparse A b r) +
         2 *
         vec_inf_norm
           (x_fix
              ((FT2R_mat A)^-1 *m FT2R_mat b)
              (FT2R_mat b) (FT2R_mat A))))%Re.
+ apply Rmult_le_compat_l. apply Rabs_pos.
  change (_ *m _) with x.
 (* unfold d_mag.*)
  fold rho in H1|-*.
  set v := vec_inf_norm _.
  replace (d_mag_def _ _) with d_mag in H1|- * by admit.
  replace rho with (rho_def A b) in * by admit. clear rho.
  repeat apply Rplus_le_compat_r.
  apply Rmult_le_compat_r. apply Rlt_le. apply H1.
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat. nra. 
 by apply rho_ge_0.
  assert ( 1%Re = (1 ^ k)%Re) by (rewrite pow1; nra).
  rewrite H. apply pow_incr.
  split. by apply rho_ge_0.
  apply Rlt_le. apply H0.
+ fold rho.
  replace rho with (rho_def A b) by admit. 
 apply bnd1.
Admitted.

Lemma bound_2_sparse {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) k
  (r : nat) (HA : is_r_sparse_mat A r):
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def_sparse A b r in 
  let d_mag := d_mag_def_sparse A b r in 
  input_bound_sparse A x0 b r ->
  (rho < 1)%Re ->
  (vec_inf_norm
   (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       rho ^ k *
       f_error 0 b x0 x A +
       (1 - rho ^ k) / (1 - rho) *
       d_mag < sqrt (fun_bnd ty r.+1))%Re.
Proof. 
intros.
unfold input_bound in H.
destruct H as [_ [bnd2 H]]. clear H.
apply Rle_lt_trans with
(vec_inf_norm
          (x_fix
             ((FT2R_mat A)^-1 *m 
              FT2R_mat b)
             (FT2R_mat b)
             (FT2R_mat A)) +
        1 * f_error 0 b x0
          ((FT2R_mat A)^-1 *m 
           FT2R_mat b) A +
        1 / (1 - rho_def_sparse A b r) * d_mag_def_sparse A b r)%Re.
+ unfold x. unfold A_real, b_real. rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l. unfold rho, d_mag.
  apply Rplus_le_compat.
  - apply Rmult_le_compat_r.
    * unfold f_error. apply /RleP.
      apply vec_norm_pd.
    * assert ( 1%Re = (1 ^ k)%Re) by (rewrite pow1; nra).
      rewrite H. apply pow_incr.
      split. by apply rho_sparse_ge_0.
      apply Rlt_le. apply H0.
  - apply Rmult_le_compat_r.
    apply d_mag_sparse_ge_0. apply Rmult_le_compat_r.
    apply Rlt_le. apply Rinv_0_lt_compat.
    apply Rlt_Rminus. apply H0.
    apply Rcomplements.Rle_minus_l.
    assert (forall a b:R, (0 <= b)%Re -> (a <= a + b)%Re).
    { intros. nra. } apply H.
    apply pow_le. by apply rho_sparse_ge_0.
+ apply bnd2.
Qed.

Lemma bound_3_sparse {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) (r : nat):
  input_bound_sparse A x0 b r ->
  forall i j, 
  (Rabs (FT2R (A2_J A i j )) <
    sqrt (fun_bnd ty r.+1))%Re.
Proof.
intros. unfold input_bound_sparse in H.
destruct H as [_ [_ [bnd3 H]]]. clear H.
apply bnd3. 
Qed.

Definition forward_error_cond_sparse {ty} {n:nat} 
  (A: 'M[ftype ty]_n.+1) (x0 b: 'cV[ftype ty]_n.+1) (r : nat) :=
  let rho := rho_def_sparse A b r in
  let d_mag := d_mag_def_sparse A b r in
   let A_real := FT2R_mat A in
  (forall i, finite (A i i)) /\
  (rho < 1)%Re /\
  A_real \in unitmx /\
  (forall i : 'I_n.+1, finite (BDIV (Zconst ty 1) (A i i))) /\
  (forall i : 'I_n.+1, finite (x0 i ord0)) /\
  (forall i, finite  (A1_inv_J A i ord0)) /\
  (forall i j, finite (A2_J A i j)) /\ 
  (forall i, finite (b i ord0)) /\
  @size_constraint ty n /\
  input_bound_sparse A x0 b r.

  Theorem jacobi_forward_error_bound_sparse_aux {ty} {n : nat}
  (A: 'M[ftype ty]_n.+1) (b: 'cV[ftype ty]_n.+1)
  (r : nat) (HA : is_r_sparse_mat A r):
  let A_real := FT2R_mat A in 
  let b_real := FT2R_mat b in 
  let x := A_real^-1 *m b_real in 
  let R := (vec_inf_norm (A1_diag A_real) * matrix_inf_norm (A2_J_real A_real))%Re in
   let delta := default_rel ty in
   let rho := ((((1 + g ty r.+1) * (1 + delta) *
                  g ty r.+1 + delta * (1 + g ty r.+1) +
                  g ty r.+1) * (1 + delta) + delta) * R +
                (((1 + g ty r.+1) * (1 + delta) *
                  g ty r.+1 + delta * (1 + g ty r.+1) +
                  g ty r.+1) * default_abs ty +
                 default_abs ty) *
                matrix_inf_norm (A2_J_real A_real) + R)%Re in
   let d_mag := ((g ty r.+1 * (1 + delta) + delta) *
                    ((vec_inf_norm (A1_diag A_real) *
                      (1 + delta) + default_abs ty) *
                     vec_inf_norm b_real) +
                    (1 + g ty r.+1) * g1 ty r.+1 (r.+1 - 1) *
                    (1 + delta) *
                    (vec_inf_norm (A1_diag A_real) *
                     (1 + delta) + default_abs ty) +
                    g1 ty r.+1 (r.+1 - 1) +
                    (vec_inf_norm (A1_diag A_real) * delta +
                     default_abs ty) * vec_inf_norm b_real +
                    ((((1 + g ty r.+1) * (1 + delta) *
                       g ty r.+1 + delta * (1 + g ty r.+1) +
                       g ty r.+1) * (1 + delta) + delta) * R +
                     (((1 + g ty r.+1) * (1 + delta) *
                       g ty r.+1 + delta * (1 + g ty r.+1) +
                       g ty r.+1) * default_abs ty +
                      default_abs ty) *
                     matrix_inf_norm (A2_J_real A_real)) *
                    vec_inf_norm (x_fix x b_real A_real))%Re in
  forall x0: 'cV[ftype ty]_n.+1,
  forward_error_cond_sparse A x0 b r ->
  (forall k:nat, 
   (forall i, finite (X_m_jacobi k x0 b A i ord0)) /\
   (f_error k b x0 x A <= rho^k * (f_error 0 b x0 x A) + ((1 - rho^k) / (1 - rho))* d_mag)%Re).
Proof.
  intros ? ? ? ? ? ? ? ? Hcond.
  unfold forward_error_cond_sparse in Hcond.
  destruct Hcond as [HAf [H [H0 [Hdivf [Hx0 [Ha1_inv [HfA2 [Hb [size_cons Hinp]]]]]]]]].
  assert (forall i : 'I_n.+1, FT2R (A i i) <> 0%Re).
  { intros. by apply BDIV_FT2R_sep_zero. }
  induction k.
  { split; simpl; try nra. intros. apply Hx0. }
  assert (Hfin: (forall i : 'I_n.+1, finite (X_m_jacobi k.+1 x0 b A i ord0))).
  { intros. simpl.
    unfold jacobi_iter.
    rewrite mxE.
    rewrite nth_vec_to_list_float; last by apply ltn_ord.
    assert (finite 
              (let l1 :=
                 vec_to_list_float n.+1
                   (\row_j A2_J A (inord i) j)^T in
               let l2 :=
                 vec_to_list_float n.+1
                   (\col_j X_m_jacobi k x0 b A j
                             ord0) in
               dotprod_r l1 l2)).
    { pose proof (@finite_fma_from_bounded _ ty).
      specialize (H2 (vec_to_list_float n.+1
                         (\row_j A2_J A (inord i) j)^T)
                      ( vec_to_list_float n.+1
                          (\col_j X_m_jacobi k x0 b A j ord0))).
      rewrite combine_length !length_veclist Nat.min_id in H2.
      specialize (H2 (dotprod_r 
                            (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                            (vec_to_list_float n.+1
                                 (\col_j X_m_jacobi k x0 b A j  ord0)))).
      specialize (H2 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                          (\col_j X_m_jacobi k x0 b A j ord0))).

      (* modifications start here! *)
      assert ((g1 ty (n.+2 +1)%coq_nat n.+2 <= fmax ty)%Re).
      { by apply g1_constraint_Sn. } specialize (H2 H3).
      apply H2. intros.
      repeat split.
      + destruct x1. simpl. apply in_combine_l in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev (vec_to_list_float n.+1
                                 (\row_j A2_J A (inord i) j)^T)) f (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite mxE in H52. rewrite -H52. apply HfA2.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_r in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev
                                (vec_to_list_float n.+1
                                   (\col_j X_m_jacobi k x0 b A j ord0))) f0 (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite -H52. apply IHk.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_l in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev (vec_to_list_float n.+1
                                 (\row_j A2_J A (inord i) j)^T)) f (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite mxE in H52. rewrite -H52. 
          apply bound_3_sparse with x0 b.
          admit.
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
      + destruct x1. simpl. apply in_combine_r in H4.
        apply in_rev in H4.
        pose proof (@In_nth _ (rev
                                (vec_to_list_float n.+1
                                   (\col_j X_m_jacobi k x0 b A j ord0))) f0 (Zconst ty 0) H4).
        destruct H5 as [m [H51 H52]]. rewrite rev_nth in H52.
        rewrite length_veclist in H52.
        assert ((n.+1 - m.+1)%coq_nat = (n.+1.-1 - m)%coq_nat) by lia.
        rewrite H5 in H52. rewrite nth_vec_to_list_float  in H52.
        - rewrite mxE in H52. rewrite -H52.
          destruct IHk as [IHk1 IHk2].
          apply (x_k_bound_sparse HA (@inord n m)) in IHk2.
          eapply Rle_lt_trans.
          apply IHk2. admit. (*by apply bound_2_sparse.*)
        - rewrite rev_length length_veclist in H51. by apply /ssrnat.ltP. 
        - rewrite rev_length in H51. apply H51.
    }
    assert (finite 
            (BMINUS (b (inord i) ord0)
               ((A2_J A *f X_m_jacobi k x0 b A)
                  (inord i) ord0))).
    { apply Bplus_bminus_opp_implies.
      apply BPLUS_no_overflow_is_finite.
        + apply Hb.
        + rewrite finite_BOPP. rewrite mxE. apply H2.
        + unfold Bplus_no_overflow. 
          pose proof (@generic_round_property ty).
          specialize (H3 (FT2R (b (inord i) ord0) +
                             FT2R
                               (BOPP
                                  ((A2_J A *f
                                    X_m_jacobi k x0 b A)
                                     (inord i) ord0)))%Re).
          destruct H3 as [d1 [e1 [Hde1 [Hd1 [He1 H3]]]]].
          rewrite H3.
          eapply Rle_lt_trans. apply Rabs_triang.
          eapply Rle_lt_trans. apply Rplus_le_compat_l.
          apply He1. apply Rcomplements.Rlt_minus_r.
          rewrite Rabs_mult.
          eapply Rle_lt_trans.
          apply Rmult_le_compat_l. apply Rabs_pos.
          eapply Rle_trans. apply Rabs_triang.
          rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1.
          apply Rcomplements.Rlt_div_r.
          apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
          eapply Rle_lt_trans. apply Rabs_triang.
          rewrite [in X in (_ + X < _)%Re]/FT2R B2R_Bopp Rabs_Ropp.
          fold (@FT2R ty). rewrite mxE.
          pose proof (@fma_dotprod_forward_error _ ty).
          specialize (H4 (vec_to_list_float n.+1
                                  (\row_j A2_J A (inord i) j)^T)
                         (vec_to_list_float n.+1
                            (\col_j X_m_jacobi k x0 b A j  ord0))).
          rewrite !length_veclist in H4.
          assert (n.+1 = n.+1). { lia. } specialize (H4 H5). 
          clear H5.
          specialize (H4 (dotprod_r 
                            (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                            (vec_to_list_float n.+1
                                 (\col_j X_m_jacobi k x0 b A j  ord0)))).
          specialize (H4 
                     (\sum_j ( (FT2R (A2_J A (inord i) j)) * 
                               (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
          specialize (H4
                     (\sum_j (Rabs (FT2R (A2_J A (inord i) j)) * 
                              Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
          specialize (H4 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                          (\col_j X_m_jacobi k x0 b A j ord0))).
          assert (\sum_j
                     (FT2R
                        (A2_J A (inord i) j) *
                      FT2R
                        (X_m_jacobi k x0 b
                           A j ord0))%Re = 
                  \sum_(j < n.+1)
                          FT2R_mat (A2_J A) (inord i) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                          FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
          { apply eq_big. intros. by []. intros.
            assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
            { unfold widen_ord. 
              apply val_inj. by simpl. 
            } rewrite H6. by rewrite !mxE.
          } rewrite H5 in H4.
          specialize (H4 (@R_dot_prod_rel_holds _ _  n.+1 i (leqnn n.+1) (A2_J A)
                        (\col_j X_m_jacobi k x0 b A j ord0))). 
          assert (\sum_j
                     (Rabs
                        (FT2R
                           (A2_J A 
                              (inord i) j)) *
                      Rabs
                        (FT2R
                           (X_m_jacobi k
                              x0 b A j ord0))) =  
                  sum_fold
                    (map (uncurry Rmult)
                       (map Rabsp
                          (map FR2
                             (combine
                                (vec_to_list_float n.+1
                                   (\row_j (A2_J A) (inord i) j)^T)
                                (vec_to_list_float n.+1 
                                  (\col_j X_m_jacobi k x0 b A j ord0))))))).
          { rewrite -sum_fold_mathcomp_equiv.
            apply eq_big. by []. intros.
            assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
            { unfold widen_ord. 
              apply val_inj. by simpl. 
            } rewrite H7. by rewrite !mxE.
          } rewrite H6 in H4.
          specialize (H4 (R_dot_prod_rel_abs_holds    n.+1 i (A2_J A)
                        (\col_j X_m_jacobi k x0 b A j ord0))).
          rewrite -H6 in H4. rewrite -H5 in H4. clear H5 H6.
          specialize (H4 H2). 
          eapply Rle_lt_trans. apply Rplus_le_compat_l. 
          apply Rle_trans with 
          ((1 + g ty n.+1) * 
            Rabs  (\sum_j
                      Rabs (FT2R (A2_J A (inord i) j)) *
                      Rabs (FT2R (X_m_jacobi k x0 b A j ord0))) + 
            g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
          * apply Rle_trans with 
            (Rabs ( \sum_j
                      (FT2R (A2_J A (inord i) j) *
                       FT2R(X_m_jacobi k x0 b A j ord0)))  +
              (g ty n.+1 *
                  Rabs
                    (\sum_j
                        Rabs
                          (FT2R (A2_J A (inord i) j)) *
                        Rabs
                          (FT2R
                             (X_m_jacobi k x0 b A j
                                ord0))) +
                  g1 ty n.+1 (n.+1 - 1)%coq_nat))%Re.
            rewrite Rplus_comm.
            apply Rcomplements.Rle_minus_l.
            eapply Rle_trans. apply Rabs_triang_inv.
            apply H4. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
            rewrite Rmult_plus_distr_r. apply Rplus_le_compat_r.
            rewrite Rmult_1_l. rewrite Rabs_sum_in.
            rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
            apply /RleP. apply Rabs_ineq.
          * apply Rle_refl.
          * rewrite Rabs_sum_in. rewrite sum_abs_eq; last by (intros; apply Rabs_pos).
            eapply Rle_lt_trans. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
            apply Rplus_le_compat_l.
            apply Rmult_le_compat_l.
            apply Rplus_le_le_0_compat; try nra; try apply g_pos.
            apply Rle_trans with 
            ((vec_inf_norm
                 (x_fix x (FT2R_mat b) (FT2R_mat A)) +
                     rho ^ k * f_error 0 b x0 x A +
                     (1 - rho ^ k) / (1 - rho) * d_mag) * 
              \sum_j (Rabs ( FT2R (A2_J A (inord i) j))))%Re.
            ++ apply /RleP. rewrite RmultE.
               rewrite big_distrr /=.
               apply big_sum_ge_ex_abstract.
               intros. rewrite -RmultE.
               rewrite Rabs_mult. rewrite Rmult_comm.
               apply Rmult_le_compat_r. apply Rabs_pos.
               admit. (* apply x_k_bound. apply IHk. *)
            ++ apply Rle_refl.
            ++ admit. (* by apply bound_4. *)
    }
    apply BMULT_no_overflow_is_finite.
    + apply Ha1_inv.
    + rewrite nth_vec_to_list_float; last by apply ltn_ord.
      rewrite mxE. apply H3.
    + rewrite nth_vec_to_list_float; last by apply ltn_ord.
      unfold Bmult_no_overflow.
      unfold rounded.
      pose proof (@generic_round_property ty 
                  (FT2R (A1_inv_J A (inord i) ord0) *
                     FT2R
                       ((b -f
                         A2_J A *f X_m_jacobi k x0 b A)
                          (inord i) ord0))).
      destruct H4 as [d [e [Hde [Hd [He H4]]]]].
      rewrite H4. 
      eapply Rle_lt_trans.
      apply Rabs_triang. eapply Rle_lt_trans.
      apply Rplus_le_compat_l. apply He.
      apply Rcomplements.Rlt_minus_r. rewrite Rabs_mult.
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rle_trans with (Rabs 1 + Rabs d)%Re.
      apply Rabs_triang. rewrite Rabs_R1.
      apply Rplus_le_compat_l. apply Hd. 
      apply Rcomplements.Rlt_div_r.
      apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
      rewrite Rabs_mult. rewrite [in X in (_ * X < _)%Re]mxE. 
      rewrite Bminus_bplus_opp_equiv.
      pose proof (@BPLUS_accurate' _ ty).
      specialize (H5 (b (inord i) ord0) (BOPP 
            ((A2_J A *f X_m_jacobi k x0 b A)
                          (inord i) ord0))).
      assert (finite
               (BPLUS (b (inord i) ord0)
                  (BOPP
                     ((A2_J A *f
                       X_m_jacobi k x0 b A)
                        (inord i) ord0)))).
      { by apply Bminus_bplus_opp_implies . }
      specialize (H5 H6).
      destruct H5 as [d1 [Hd1 H5]].
      rewrite H5.
      - rewrite Rabs_mult. eapply Rle_lt_trans.
        apply Rmult_le_compat_l. apply Rabs_pos.
        apply Rmult_le_compat_l. apply Rabs_pos.
        apply Rle_trans with (Rabs 1 + Rabs d1)%Re.
        apply Rabs_triang. rewrite Rabs_R1. apply Rplus_le_compat_l.
        apply Hd1. rewrite -Rmult_assoc.
        apply Rcomplements.Rlt_div_r.
        apply Rplus_lt_le_0_compat; try nra; try apply default_rel_ge_0.
        eapply Rle_lt_trans. apply Rmult_le_compat_l.
        apply Rabs_pos. apply Rabs_triang.
        rewrite [in X in (_ * (_ + X) < _)%Re]/FT2R B2R_Bopp.
        rewrite Rabs_Ropp. fold (@FT2R ty).
        rewrite [in X in (_ * (_ + X) < _)%Re]mxE.
        pose proof (@fma_dotprod_forward_error _ ty).
        specialize (H7 (vec_to_list_float n.+1
                                (\row_j A2_J A (inord i) j)^T)
                       (vec_to_list_float n.+1
                          (\col_j X_m_jacobi k x0 b A j  ord0))).
        rewrite !length_veclist in H7.
        assert (n.+1 = n.+1). { lia. } specialize (H7 H8). 
        clear H8.
        specialize (H7 (dotprod_r 
                          (vec_to_list_float n.+1
                              (\row_j A2_J A (inord i) j)^T)
                          (vec_to_list_float n.+1
                               (\col_j X_m_jacobi k x0 b A j  ord0)))).
       specialize (H7 
                   (\sum_j ( (FT2R (A2_J A (inord i) j)) * 
                             (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
      specialize (H7 
                   (\sum_j (Rabs (FT2R (A2_J A (inord i) j)) * 
                            Rabs (FT2R (X_m_jacobi k x0 b A j ord0)))%Re)).
      specialize (H7 (@fma_dot_prod_rel_holds _ _ _ n.+1 i (A2_J A) 
                        (\col_j X_m_jacobi k x0 b A j ord0))).
      assert (\sum_j
                 (FT2R
                    (A2_J A (inord i) j) *
                  FT2R
                    (X_m_jacobi k x0 b
                       A j ord0))%Re = 
              \sum_(j < n.+1)
                      FT2R_mat (A2_J A) (inord i) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) * 
                      FT2R_mat (\col_j X_m_jacobi k x0 b A j ord0) (@widen_ord n.+1 n.+1 (leqnn n.+1) j) ord0).
      { apply eq_big. intros. by []. intros.
        assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
        { unfold widen_ord. 
          apply val_inj. by simpl. 
        } rewrite H9. by rewrite !mxE.
      } rewrite H8 in H7.
      specialize (H7 (@R_dot_prod_rel_holds _ _  n.+1 i (leqnn n.+1) (A2_J A)
                    (\col_j X_m_jacobi k x0 b A j ord0))). 
      assert (\sum_j
                 (Rabs
                    (FT2R
                       (A2_J A 
                          (inord i) j)) *
                  Rabs
                    (FT2R
                       (X_m_jacobi k
                          x0 b A j ord0))) =  
              sum_fold
                (map (uncurry Rmult)
                   (map Rabsp
                      (map FR2
                         (combine
                            (vec_to_list_float n.+1
                               (\row_j (A2_J A) (inord i) j)^T)
                            (vec_to_list_float n.+1 
                              (\col_j X_m_jacobi k x0 b A j ord0))))))).
      { rewrite -sum_fold_mathcomp_equiv.
        apply eq_big. by []. intros.
        assert ((widen_ord (m:=n.+1) (leqnn n.+1) i0) = i0).
        { unfold widen_ord. 
          apply val_inj. by simpl. 
        } rewrite H10. by rewrite !mxE.
      } rewrite H9 in H7.
      specialize (H7 (R_dot_prod_rel_abs_holds    n.+1 i (A2_J A)
                    (\col_j X_m_jacobi k x0 b A j ord0))).
      rewrite -H9 in H7. rewrite -H8 in H7. clear H8 H9.
      specialize (H7 H2). 
      eapply Rle_lt_trans. apply Rmult_le_compat_l. apply Rabs_pos.
      apply Rplus_le_compat_l.
      apply Rle_trans with 
      ((1 + g ty n.+1) * 
        Rabs  (\sum_j
                  Rabs (FT2R (A2_J A (inord i) j)) *
                  Rabs (FT2R (X_m_jacobi k x0 b A j ord0))) + 
        g1 ty n.+1 (n.+1 - 1)%coq_nat)%Re.
      * apply Rle_trans with 
        (Rabs ( \sum_j
                  (FT2R (A2_J A (inord i) j) *
                   FT2R(X_m_jacobi k x0 b A j ord0)))  +
          (g ty n.+1 *
              Rabs
                (\sum_j
                    Rabs
                      (FT2R (A2_J A (inord i) j)) *
                    Rabs
                      (FT2R
                         (X_m_jacobi k x0 b A j
                            ord0))) +
              g1 ty n.+1 (n.+1 - 1)%coq_nat))%Re.
        rewrite Rplus_comm.
        apply Rcomplements.Rle_minus_l.
        eapply Rle_trans. apply Rabs_triang_inv.
        apply H7. rewrite -Rplus_assoc. apply Rplus_le_compat_r.
        rewrite Rmult_plus_distr_r. apply Rplus_le_compat_r.
        rewrite Rmult_1_l. rewrite Rabs_sum_in.
        rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
        apply /RleP. apply Rabs_ineq.
      * apply Rle_refl.
      * rewrite  Rabs_sum_in.
        rewrite sum_abs_eq ; last by (intros; apply Rabs_pos).
        (** This gives us information about conditions in terms of 
            conditions on input
        **)
        eapply Rle_lt_trans. apply Rmult_le_compat_l.
        apply Rabs_pos. rewrite -Rplus_assoc.
        apply Rplus_le_compat_r. apply Rplus_le_compat_l.
        apply Rmult_le_compat_l.
        apply Rplus_le_le_0_compat; try nra; try apply g_pos.
        apply Rle_trans with 
            ((vec_inf_norm
                 (x_fix x (FT2R_mat b) (FT2R_mat A)) +
                     rho ^ k * f_error 0 b x0 x A +
                     (1 - rho ^ k) / (1 - rho) * d_mag) * 
              \sum_j (Rabs ( FT2R (A2_J A (inord i) j))))%Re.
            ++ apply /RleP. rewrite RmultE.
               rewrite big_distrr /=.
               apply big_sum_ge_ex_abstract.
               intros. rewrite -RmultE.
               rewrite Rabs_mult. rewrite Rmult_comm.
               apply Rmult_le_compat_r. apply Rabs_pos.
               admit. (* apply x_k_bound. apply IHk. *)
            ++ apply Rle_refl.
            ++ admit. (* by apply bound_5. *)
   - by apply Bminus_bplus_opp_implies .
 }

Admitted.

Definition input_bound_sparse {t} {n:nat} 
  (A: 'M[ftype t]_n.+1) (x0 b: 'cV[ftype t]_n.+1) (r : nat) :=
  let A_real := FT2R_mat A in
  let b_real := FT2R_mat b in
  let x:= A_real^-1 *m b_real in
  let rho := rho_def_sparse A b r in 
  let d_mag := d_mag_def_sparse A b r in
  (forall i,
    (Rabs (FT2R (A i i)) *
     (1 * (1 + rho) *
      (f_error 0 b x0 x A -
       d_mag * / (1 - rho)) +
      2 * d_mag * / (1 - rho) +
      2 *
      vec_inf_norm
        (x_fix x (FT2R_mat b) (FT2R_mat A))) <
     (sqrt (fun_bnd t r.+1) - default_abs t) /
     (1 + default_rel t) /
     (1 + default_rel t))%Re) /\ 
  (vec_inf_norm
   (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       1 *
       f_error 0 b x0 x A +
       1 / (1 - rho) *
       d_mag < sqrt (fun_bnd t r.+1))%Re /\
  (forall i j, 
      (Rabs (FT2R (A2_J A i j )) <
        sqrt (fun_bnd t r.+1))%Re) /\
  (forall i,
     (Rabs (FT2R (b i ord0)) +
     (1 + g t r.+1) *
     ((vec_inf_norm
         (x_fix x (FT2R_mat b) (FT2R_mat A)) +
       1 * f_error 0 b x0 x A +
       1 / (1 - rho) * d_mag) *
      (\sum_j
          Rabs (FT2R (A2_J A i j)))) +
     g1 t r.+1 (r.+1 - 1)%coq_nat <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t))%Re) /\
  (forall i,
    (Rabs (FT2R (A1_inv_J A (inord i) ord0)) *
     (Rabs (FT2R (b (inord i) ord0)) +
      (1 + g t r.+1) *
      ((vec_inf_norm
          (x_fix x (FT2R_mat b) (FT2R_mat A)) +
        1 * f_error 0 b x0 x A +
        1 / (1 - rho) * d_mag) *
       (\sum_j
           Rabs (FT2R (A2_J A (inord i) j)))) +
      g1 t r.+1 (r.+1 - 1)%coq_nat) <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t) /
     (1 + default_rel t))%Re) /\
  (1 * (1 + rho) *
     ((f_error 0 b x0 x A) - d_mag * / (1 - rho)) +
     2 * d_mag * / (1 - rho) +
     2 *
     vec_inf_norm
       (x_fix x (FT2R_mat b) (FT2R_mat A)) <
     (bpow Zaux.radix2 (femax t) -
      default_abs t) / (1 + default_rel t))%Re.