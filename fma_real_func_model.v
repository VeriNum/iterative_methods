From Coq Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect ssralg 
              ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas inf_norm_properties.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

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

Lemma nth_vec_to_list_real_sub {n:nat} i m (v1 v2 :'cV[R]_n.+1) d:
  (i < m)%nat ->
  nth (m.-1 -i) (@vec_to_list_real n m (v1 - v2)) d = 
  nth (m.-1 -i) (@vec_to_list_real n m v1) d - 
  nth (m.-1 -i) (@vec_to_list_real n m v2) d.
Proof.
intros.
induction m.
+ by rewrite ltn0 in H.
+ simpl. rewrite -subn_gt0 in IHm. rewrite -predn_sub in IHm.
  destruct (m-i)%nat.
  - by rewrite !mxE /=.
  - simpl in IHm. by apply IHm.
Qed.

Lemma diag_matrix_vec_mult_diff {n:nat} (v1 v2 v3 : 'cV[R]_n.+1):
  diag_matrix_vec_mult_R v1 v2 - diag_matrix_vec_mult_R v1 v3 = 
  diag_matrix_vec_mult_R v1 (v2 - v3).
Proof.
apply /matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite nth_vec_to_list_real_sub.
+ rewrite -!RmultE -!RminusE. field_simplify. auto.
+ apply ltn_ord.
Qed.



Lemma diag_matrix_vec_mult_diff_r {n:nat} (v1 v2 v3 : 'cV[R]_n.+1):
  diag_matrix_vec_mult_R v1 v3 - diag_matrix_vec_mult_R v2 v3 = 
  diag_matrix_vec_mult_R (v1 - v2) v3.
Proof.
apply /matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite nth_vec_to_list_real_sub.
+ rewrite -!RmultE -!RminusE. field_simplify. auto.
+ apply ltn_ord.
Qed.



Lemma nth_vec_to_list_real {n:nat} i m (v :'cV[R]_n.+1) d:
  (i < m)%nat ->
  nth (m.-1 -i) (@vec_to_list_real n m v) d = v (@inord n i) ord0.
Proof.
intros.
elim: m i H => [ | m IHm] i H.
+ by [].
+ simpl.
  rewrite leq_eqVlt in H.
  assert ((i == m) \/ (i < m)%nat).
  { by apply /orP. } destruct H0.
  - assert (i = m). { by apply /eqP. }
    rewrite H1. simpl.
    assert ((m - m)%nat = 0%N). 
    { apply /eqP. rewrite subn_eq0. by []. } by rewrite H2 /=.
  - assert (nth (m.-1 - i) (vec_to_list_real m v)
                d = v (inord i) ord0).
    { by apply IHm. } 
    rewrite -H1. rewrite -[in RHS]predn_sub.
    rewrite -subn_gt0 in H0. rewrite -predn_sub in H1.
    by destruct (m - i)%nat.
Qed.


Definition A2_J_real {n:nat} (A: 'M[R]_n.+1): 
  'M[R]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then 0%Re else A i j. 


(** Define real real functional model **)

Definition x_fix {n:nat} x b (A: 'M[R]_n.+1) : 
  'cV[R]_n.+1 :=
  let r := b - ((A2_J_real A) *m x) in
  diag_matrix_vec_mult_R (A1_diag A) r.

Lemma vec_inf_norm_diag_matrix_vec_mult_R {n:nat} (v1 v2 : 'cV[R]_n.+1):
  vec_inf_norm (diag_matrix_vec_mult_R v1 v2) <= 
  vec_inf_norm v1 * vec_inf_norm v2.
Proof.
unfold vec_inf_norm, diag_matrix_vec_mult_R.
rewrite -bigmaxr_mulr.
+ apply /RleP. apply lemmas.bigmax_le.
  - by rewrite size_map size_enum_ord.
  - intros. rewrite seq_equiv. rewrite nth_mkseq; 
    last by rewrite size_map size_enum_ord in H.
    apply Rle_trans with 
    [seq (bigmaxr 0%Re
           [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
         Rabs (v2 i0 0))%Ri
      | i0 <- enum 'I_n.+1]`_i.
    * assert ([seq bigmaxr 0%Re
                    [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
                  Rabs (v2 i0 0)
                | i0 <- enum 'I_n.+1] = 
               mkseq (fun i: nat => bigmaxr 0%Re
                            [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
                            Rabs (v2 (@inord n i) 0))
                             n.+1).
      { by rewrite !seq_equiv. } rewrite H0.
      rewrite nth_mkseq; 
      last by rewrite size_map size_enum_ord in H.
      rewrite !mxE. rewrite -!RmultE. rewrite Rabs_mult.
      rewrite !nth_vec_to_list_real; try rewrite inord_val.
      ++ apply Rmult_le_compat_r; try apply Rabs_pos.
         apply Rle_trans with 
         [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1]`_i.
         -- rewrite seq_equiv. rewrite nth_mkseq; 
            last by rewrite size_map size_enum_ord in H.
            apply Rle_refl.
         -- apply /RleP.
            apply (@bigmaxr_ler _ 0%Re [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] i).
            rewrite size_map size_enum_ord.
            by rewrite size_map size_enum_ord in H.
      ++ by rewrite size_map size_enum_ord in H.
      ++ by rewrite size_map size_enum_ord in H.
    * apply /RleP.
      apply (@bigmaxr_ler _ 0%Re [seq bigmaxr 0%Re
                     [seq Rabs (v1 i1 0) | i1 <- enum 'I_n.+1] *
                   Rabs (v2 i0 0)
                 | i0 <- enum 'I_n.+1] i).
       rewrite size_map size_enum_ord.
       by rewrite size_map size_enum_ord in H.
+ apply bigmax_le_0.
  - apply /RleP. apply Rle_refl.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    apply /RleP. apply Rabs_pos.
Qed.



Lemma x_fixpoint {n:nat} x b (A: 'M[R]_n.+1):
  A *m x = b ->
  (forall i, A i i <> 0%Re) ->
  x = x_fix x b A.
Proof.
intros.
unfold x_fix. unfold diag_matrix_vec_mult_R.
apply /matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite !nth_vec_to_list_real.
+ rewrite !mxE. 
  assert (x x0 y = ((1 / A (inord x0) (inord x0)) *
                    (A (inord x0) (inord x0) * x x0 y))%Re).
  { assert (((1 / A (inord x0) (inord x0)) *
                    (A (inord x0) (inord x0) * x x0 y))%Re = 
             ((A (inord x0) (inord x0) * / A (inord x0) (inord x0))*
              x x0 y)%Re).
    { nra. } rewrite H1. rewrite Rinv_r.
    nra.  apply H0.
  } rewrite H1.
  assert ((((A (inord x0) (inord x0)) * x x0 y))%Re  = 
           (b (inord x0) ord0 -
              \sum_j A2_J_real (A) (inord x0) j * x j ord0)%Re).   
  { assert (forall x y z:R, (x + y = z)%Re -> (x = z - y)%Re).
    { intros. nra. } apply H2.
    assert (( (A (inord x0) (inord x0)) * x x0 y +
              \sum_j A2_J_real A (inord x0) j * x j ord0)%Re = 
              \sum_j (A x0 j * x j ord0)%Re).
    { unfold A2_J_real. rewrite [in RHS](bigD1 x0) /=.
      rewrite inord_val. 
      assert (y = ord0). { by apply ord1. } rewrite H3. 
      apply Rplus_eq_compat_l. 
      assert (\sum_(i < n.+1 | i != x0)
                    (A x0 i * x i ord0)%Re = 
               \sum_(i < n.+1)
                   (if (~~ (i == x0 :> nat)) then 
                      (A x0 i * x i ord0)%Re else 0%Re)).
      { by rewrite big_mkcond /=. } rewrite H4.
      apply eq_big.
      by []. intros. rewrite !mxE. rewrite eq_sym.
      destruct (i == x0 :>nat).
      + simpl. by rewrite mul0r.
      + simpl. by rewrite -RmultE.
      + by [].
    } rewrite H3. apply matrixP in H. unfold eqrel in H.
    specialize (H x0 y). rewrite !mxE in H.
    assert (y = ord0). { by apply ord1. } rewrite H4 in H.
    rewrite inord_val. by apply H.
  } rewrite H2. by [].
+ apply ltn_ord.
+ apply ltn_ord.
Qed.



