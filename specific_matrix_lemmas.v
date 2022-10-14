From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.

Set Bullet Behavior "Strict Subproofs". 


Require Import infinity_norm_properties error_real lemmas float_model vcfloat_lemmas.

Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.



From mathcomp Require Import matrix bigop all_algebra all_ssreflect.
From mathcomp.analysis Require Import Rstruct.
From Coquelicot Require Import Lub Rbar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** We will open the real scope and the Ring scope 
  separately **)

Open Scope ring_scope.

(** We instantiate the ring scope with real scope using
  Delimit Scope ... **)
Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

(** We next import the ring theory so that we can use
  it for reals **)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.



Lemma vec_inf_norm_all_le :
  forall E k x b h len,
  (0 < len)%N ->
  @vec_inf_norm len (@listR_to_vecR len (FT2R_list (X_m k x b h))) <= E ->
  forall i, (i < len)%nat ->
  Rabs (List.nth i (FT2R_list (X_m k x b h)) 0%R) <= E.
Proof.
intros. rewrite /vec_inf_norm in H.
assert ((bigmaxr 0
          [seq Rabs
               (listR_to_vecR
                  (FT2R_list (X_m k x b h)) i ord0)
            | i <- enum 'I_len] <= E)%Re). 
{ by apply /RleP. } 
assert ((0 < size ([seq Rabs
               (listR_to_vecR
                  (FT2R_list (X_m k x b h)) i ord0)
            | i <- enum 'I_len]))%N).
{ by rewrite size_map size_enum_ord. }
assert (forall i:nat, 
          let lr := [seq Rabs
               (listR_to_vecR
                  (FT2R_list (X_m k x b h)) i ord0)
            | i <- enum 'I_len] in 
         (i < size lr)%N -> ((nth 0 lr i) <= E)%Re).
{ by apply bigmax_le_implies. }
specialize (H4 i). simpl in H4.
rewrite size_map size_enum_ord in H4.
specialize (H4 H1).
assert ([seq Rabs
               (listR_to_vecR
                  (FT2R_list (X_m k x b h)) i ord0)
           | i <- enum 'I_len] = 
         mkseq (fun i => Rabs (listR_to_vecR (FT2R_list (X_m k x b h)) (@inord len.-1 i) ord0)) len).
{ unfold mkseq. rewrite -val_enum_ord.
  rewrite -[in RHS]map_comp.
  apply eq_map. unfold eqfun. intros. simpl. 
  assert (len = len.-1.+1).
  { by rewrite prednK. } move: x0. rewrite H5. intros.
  assert (x0 = (@inord len.-1 x0)).
  { by rewrite inord_val. } by rewrite -H6.
} rewrite H5 in H4. clear H5.
rewrite nth_mkseq in H4.
+ assert (listR_to_vecR (FT2R_list (X_m k x b h))
           (@inord len.-1 i) ord0 = 
          List.nth i (FT2R_list (X_m k x b h)) 0).
  { rewrite !mxE. rewrite inordK.
    + by destruct i.
    + by rewrite prednK.
  } rewrite H5 in H4.
  by apply /RleP.
+ apply H1.
Qed.


Lemma S_mat_norm_eq_1 (h:R): 
  (0 < h)%Re -> 
  @matrix_inf_norm 3%N (S_mat _ h) = 1%Re.
Proof.
intros. rewrite /S_mat /matrix_inf_norm.
assert ([seq row_sum (- inv_A1 3 h *m A2 3 h) i
          | i <- enum 'I_3] = 
        [seq (fun i: 'I_3 => nth 0 [(1/2)%Re; 1%Re; (1/2)%Re] i) i | i <-  enum 'I_3]).
{ apply eq_map. unfold eqfun. intros.
  rewrite /row_sum. rewrite !big_ord_recr //= big_ord0 add0r.
  rewrite !mxE. rewrite !big_ord_recr //= !big_ord0 !add0r//=.
  rewrite !mxE.
  assert (widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max) = 0).
  { by apply /eqP. } rewrite H0 //=. rewrite !subr0 !mulr0.
  assert (((2 / (h * (h * 1)))%Re - (2 / (h * (h * 1)))%Re) = 0%Re).
  { rewrite -RminusE. nra. } rewrite H1. rewrite !addr0 !mulr0 !add0r.
  assert ((x < 3)%N). { apply ltn_ord. } 
  assert ((x = 0%N :> nat) \/ (x = 1%N :> nat) \/ (x = 2%N :> nat)) .
    { rewrite leq_eqVlt in H2.
      assert ((x.+1 == 3%N) \/ (x.+1 < 3)%N). { by apply /orP. }
      destruct H3.
      + by right;right;apply /eqP.
      + rewrite leq_eqVlt in H3.
        assert ((x.+2 == 3%N) \/ (x.+2 < 3)%N). { by apply /orP. }
        destruct H4.
        - right. left. by apply /eqP.
        - left. rewrite !ltnS in H4. rewrite leqn0 in H4. by apply /eqP.
    } 
    destruct H3.
    - rewrite H3 //=.  rewrite -!RmultE -!RoppE.
      assert ( (- 0 * (-1 / (h * (h * 1))))%Re = 0%Re).
      { nra. } rewrite H4 add0r Rabs_R0 !add0r !addr0. 
      assert ((- (1 * (2 / (h * (h * 1)))%Re^-1) *
                  (-1 / (h * (h * 1))))%Re =  (1 / 2)%Re).
      { assert ((-1 / (h * (h * 1)))%Re = (- (1 / h^2))%Re).
        { rewrite Rmult_1_r. 
          assert ((h^2)%Re = (h*h)%Re). { nra. } rewrite H5. nra.
        } rewrite H5. rewrite Rmult_1_r.
        assert ((2 / (h * h))%Re^-1 = (h^2 / 2)%Re).
        { rewrite -div1r. rewrite -RdivE.
          + assert ((1 / (2 / (h * h)))%Re = ( / (2 / (h* h)))%Re).
            { nra. } rewrite H6. rewrite Rinv_mult_distr.
            - rewrite Rinv_involutive; nra.  
            - nra.
            - apply Rinv_neq_0_compat. nra.
          + apply /eqP. apply Rmult_integral_contrapositive.
            split.
            - nra.
            - apply Rinv_neq_0_compat. nra.
        } rewrite H6.
        assert ((- (1 * (h ^ 2 / 2)) * - (1 / h ^ 2))%Re = 
                 ((h^2 * / (h^2)) * (/2))%Re).
        { nra. } rewrite H7. 
        assert ((h^2 * / (h^2))%Re = 1%Re).
        { by rewrite Rinv_r; nra. } by rewrite H8.
      } rewrite H5. rewrite Rabs_right; nra.
    - destruct H3.
    * rewrite H3 //=.  rewrite !addr0.
      rewrite -!RmultE -!RoppE.
      assert ( (- 0 * (-1 / (h * (h * 1))))%Re = 0%Re).
      { nra. } rewrite H4 add0r Rabs_R0 !addr0.
      assert ((- (1 * (2 / (h * (h * 1)))%Re^-1) *
                (-1 / (h * (h * 1))))%Re =  (1 / 2)%Re).
      { assert ((-1 / (h * (h * 1)))%Re = (- (1 / h^2))%Re).
        { rewrite Rmult_1_r. 
          assert ((h^2)%Re = (h*h)%Re). { nra. } rewrite H5. nra.
        } rewrite H5. rewrite Rmult_1_r.
        assert ((2 / (h * h))%Re^-1 = (h^2 / 2)%Re).
        { rewrite -div1r. rewrite -RdivE.
          + assert ((1 / (2 / (h * h)))%Re = ( / (2 / (h* h)))%Re).
            { nra. } rewrite H6. rewrite Rinv_mult_distr.
            - rewrite Rinv_involutive; nra.  
            - nra.
            - apply Rinv_neq_0_compat. nra.
          + apply /eqP. apply Rmult_integral_contrapositive.
            split.
            - nra.
            - apply Rinv_neq_0_compat. nra.
        } rewrite H6.
        assert ((- (1 * (h ^ 2 / 2)) * - (1 / h ^ 2))%Re = 
                 ((h^2 * / (h^2)) * (/2))%Re).
        { nra. } rewrite H7. 
        assert ((h^2 * / (h^2))%Re = 1%Re).
        { by rewrite Rinv_r; nra. } by rewrite H8.
      } rewrite H5. rewrite Rabs_right.
      rewrite -RplusE. 
      assert ((1 / 2 + 1 / 2)%Re = 1%Re). { nra. } rewrite H6. nra. nra.
    * rewrite H3 //=.  rewrite !addr0.
      rewrite -!RmultE -!RoppE.
      assert ( (- 0 * (-1 / (h * (h * 1))))%Re = 0%Re).
      { nra. } rewrite H4 add0r Rabs_R0 !addr0 !add0r.
      assert ((- (1 * (2 / (h * (h * 1)))%Re^-1) *
                (-1 / (h * (h * 1))))%Re =  (1 / 2)%Re).
      { assert ((-1 / (h * (h * 1)))%Re = (- (1 / h^2))%Re).
        { rewrite Rmult_1_r. 
          assert ((h^2)%Re = (h*h)%Re). { nra. } rewrite H5. nra.
        } rewrite H5. rewrite Rmult_1_r.
        assert ((2 / (h * h))%Re^-1 = (h^2 / 2)%Re).
        { rewrite -div1r. rewrite -RdivE.
          + assert ((1 / (2 / (h * h)))%Re = ( / (2 / (h* h)))%Re).
            { nra. } rewrite H6. rewrite Rinv_mult_distr.
            - rewrite Rinv_involutive; nra.  
            - nra.
            - apply Rinv_neq_0_compat. nra.
          + apply /eqP. apply Rmult_integral_contrapositive.
            split.
            - nra.
            - apply Rinv_neq_0_compat. nra.
        } rewrite H6.
        assert ((- (1 * (h ^ 2 / 2)) * - (1 / h ^ 2))%Re = 
                 ((h^2 * / (h^2)) * (/2))%Re).
        { nra. } rewrite H7. 
        assert ((h^2 * / (h^2))%Re = 1%Re).
        { by rewrite Rinv_r; nra. } by rewrite H8.
     } rewrite H5. rewrite Rabs_right; nra.
} rewrite H0.
apply bigmaxrP.
split.
+ rewrite seq_equiv.
  assert (1%Re = (fun i => nth 0  [:: (1 / 2)%Re; 1; (1 / 2)%Re] (@inord 2 i)) 1%N).
  { rewrite inordK //=.  } rewrite H1.
  rewrite inE //=. rewrite inordK //=. apply /orP. right.
  rewrite inordK //=.  rewrite inE //=. apply /orP. by left.
+ intros. 
  rewrite size_map size_enum_ord in H1.
  assert (i = 0%N \/ i = 1%N \/ i = 2%N).
  { rewrite leq_eqVlt in H1. 
    assert ((i.+1 == 3%N) \/ (i.+1 < 3)%N).
    { by apply /orP. } destruct H2.
    + by right;right; apply /eqP.
    + rewrite leq_eqVlt in H2.
      assert ((i.+2 == 3%N) \/ (i.+2 < 3)%N).
      { by apply /orP. } destruct H3.
      - by right;left; apply /eqP.
      - left. rewrite !ltnS leqn0 in H3. by apply /eqP.
  }
  destruct H2.
  * rewrite H2. rewrite seq_equiv. rewrite nth_mkseq //=. rewrite inordK //=. by apply /RleP; nra.
  * destruct H2; rewrite H2; rewrite seq_equiv; rewrite nth_mkseq //=; rewrite inordK //=; apply /RleP; nra.
Qed.



Lemma sol_up_bound_exists_aux:
  forall k x0 b,
  @vec_inf_norm 3 (X_m_real k.+1 x0 b 1%Re) <=
  (@vec_inf_norm 3 x0 + (1/2) * k.+1%:R * 
    @vec_inf_norm 3 b)%Re.
Proof.
intros. rewrite X_m_ind.
apply /RleP.
apply Rle_trans with 
(vec_inf_norm (S_mat 3 1 ^+ k.+1 *m x0) + 
 vec_inf_norm (\sum_(j < k.+1) S_mat 3 1 ^+ j *m (inv_A1 3 1 *m b)))%Re.
+ apply /RleP. apply triang_ineq.
+ apply Rle_trans with 
  (matrix_inf_norm (S_mat 3 1 ^+ k.+1) * vec_inf_norm x0 +
   matrix_inf_norm (\sum_(j < k.+1)  S_mat 3 1 ^+ j) * 
   vec_inf_norm (inv_A1 3 1 *m b))%Re.
  - apply Rplus_le_compat.
    * apply /RleP. apply submult_prop.
    * rewrite mulmx_distrl. apply /RleP. apply submult_prop.
  - apply Rle_trans with 
    (vec_inf_norm x0 + matrix_inf_norm
      (\sum_(j < k.+1) S_mat 3 1 ^+ j) * (matrix_inf_norm (inv_A1 3 1) *
       vec_inf_norm b))%Re.
    * apply Rplus_le_compat.
      ++ apply Rle_trans with 
          (1 * vec_inf_norm x0)%Re.
         -- apply Rmult_le_compat.
            ** apply /RleP. apply matrix_norm_pd.
            ** apply /RleP. apply vec_norm_pd.
            ** apply /RleP. apply mat_inf_norm_S_pow.
            ** nra.
         -- nra.
      ++ apply Rmult_le_compat.
         -- apply /RleP. apply matrix_norm_pd.
         -- apply /RleP. apply vec_norm_pd.
         -- nra.
         -- apply /RleP. apply submult_prop.
    * apply Rplus_le_compat.
      ++ nra. 
      ++ assert ((1 / 2 * k.+1%:R * vec_inf_norm b)%Re = 
                  ( k.+1%:R  * (1 / 2  * vec_inf_norm b))%Re).
         { nra. } rewrite H.
         apply Rmult_le_compat.
        -- apply /RleP. apply matrix_norm_pd.
        -- apply Rmult_le_pos.
           +++ apply /RleP. apply matrix_norm_pd.
           +++ apply /RleP. apply vec_norm_pd.
        -- apply Rle_trans with 
            (\sum_(j < k.+1) (matrix_inf_norm (S_mat 3 1 ^+j))).
           ** apply /RleP. apply matrix_norm_sum.
           ** apply Rle_trans with 
              (\sum_(j < k.+1) matrix_inf_norm (S_mat 3 1) ^+ j).
              +++ apply /RleP. apply big_sum_ge_ex_abstract.
                  intros. apply matrix_inf_norm_pow.
              +++ assert (\sum_(j < k.+1) matrix_inf_norm (S_mat 3 1) ^+ j  = 
                           \sum_(j < k.+1) 1%Re).
                  { apply eq_big. by []. intros. rewrite S_mat_norm_eq_1.
                    + by rewrite expr1n.
                    + nra.
                  } rewrite H0. rewrite sum_1_eq. apply Rle_refl.
        -- apply Rmult_le_compat.
           +++ apply /RleP. apply matrix_norm_pd.
           +++ apply /RleP. apply vec_norm_pd.
           +++ apply /RleP. apply matrix_norm_A1_lt_2.
           +++ nra.
Qed.

Lemma sol_up_bound_exists:
  forall x0 b k,
  ( k <= 100)%nat -> 
  @vec_inf_norm 3 x0 <= 48 -> @vec_inf_norm 3 b <= 1 -> 
  @vec_inf_norm 3 (X_m_real k.+1 x0 b 1%Re) <= 99.
Proof.
intros.
rewrite_scope.
eapply Rle_trans.
rewrite_scope. 
apply sol_up_bound_exists_aux.
eapply Rle_trans. 
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
rewrite_scope; apply mulr_ge0.
apply /RleP. 
assert ((1 / 2)%Re = (/2)%Re). { nra. } rewrite H2.
apply Rlt_le. apply Rinv_0_lt_compat. nra.
apply /RleP. apply nat_ge_0.
rewrite_scope; apply H1.
eapply Rle_trans. 
apply Rplus_le_compat_r.
rewrite_scope; apply H0.
rewrite Rmult_1_r.
eapply Rle_trans. 
apply Rplus_le_compat_l.
apply Rmult_le_compat_l; try nra.
assert (k.+1%:R <= 101)%Re.
{ rewrite -addn1. rewrite natrD -RplusE. 
  assert (101%Re = (100 + 1)%Re).
  { nra. } rewrite H2. apply Rplus_le_compat.
  + assert (100%Re = 100%:R). 
    { rewrite real_cast. simpl. nra. }
    rewrite H3. by apply m_ge_n.
  + apply Rle_refl.
}
apply H2.
try interval.
Qed.



End WITHNANS.

