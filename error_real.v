From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From mathcomp.analysis Require Import Rstruct.
From mathcomp Require Import matrix all_ssreflect all_algebra ssralg ssrnum bigop.

Set Bullet Behavior "Strict Subproofs". 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import lemmas.
Import List ListNotations.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

(*** Functional model for the iterative solution ***)

(** Specialized to the Jacobi iterate for the symmetric tridiagonal
    matrix:
    (1'h^2) [2 -1 0; -1 2 -1; 0 -1 2]
**)
(** define a tridiagonal system **)
Definition A (n:nat) (h:R) := \matrix_(i<n, j<n)
   if (i==j :> nat) then (2 / h^2) %Re else
      (if ((i-j)%N==1%N :>nat) then (-1 / h^2)%Re else
            (if ((j-i)%N==1%N :>nat) then (-1/ h^2)%Re else 0)).

Definition A1 (n:nat) (h:R) := \matrix_(i < n, j < n)
      if (i == j :> nat) then (A n h) i j else 0.

Definition A2 (n:nat) (h:R) := \matrix_(i < n, j < n)
  ((A n h) i j - (A1 n h) i j).
  
Definition inv_A1 (n:nat) (h:R) := \matrix_(i < n, j < n)
      if (i == j :> nat) then (1/ (A1 n h) i j) else 0.


Definition S_mat (n:nat) (h:R) := -(inv_A1 n h) *m (A2 n h).

Definition b_real : list R := [1;1;1].


Fixpoint X_m_real (m n:nat) (x0 b: 'cV[R]_n) (h:R) : 'cV[R]_n:=
  match m with
  | O => x0
  | S p => S_mat n h *m (X_m_real p x0 b h) + inv_A1 n h *m b
  end.

Lemma X_m_real_iter {n:nat} (k: nat) (x0 b: 'cV[R]_n) (h:R) :
    let xkr := X_m_real k x0 b h in
    X_m_real k.+1 x0 b h = X_m_real 1 xkr b h.
Proof. simpl; auto. Qed.

Lemma matrix_norm_submult {n:nat}:
 (0 < n)%nat ->
 forall x y b: 'cV[R]_n, forall h : R,
    vec_inf_norm (X_m_real 1 x b h - X_m_real 1 y b h) <=
    matrix_inf_norm (S_mat n h) * vec_inf_norm( x - y).
Proof.
intros. 
assert ((X_m_real 1 x b h - X_m_real 1 y b h ) = 
            (S_mat n h) *m (x - y)).
-
rewrite /X_m_real. 
assert (S_mat n h *m y + inv_A1 n h *m b = 
            inv_A1 n h *m b + S_mat n h *m y) by (rewrite addrC; auto).
+
rewrite H0.
rewrite addrKA.
rewrite mulmxBr.
auto.
-
rewrite H0.
assert (n = n.-1.+1) by (rewrite prednK; auto) .
generalize dependent x.
generalize dependent y.
generalize dependent b.
rewrite H1.
intros;
apply submult_prop.
Qed.


Lemma S_mat_norm_lt_1 (h:R): 
  (0 < h)%Re -> 
  @matrix_inf_norm 3%N (S_mat _ h) <= 1%Re.
Proof.
intros. rewrite /S_mat /matrix_inf_norm. apply /RleP.
apply bigmax_le.
+ by rewrite size_map size_enum_ord.
+ intros. 
  rewrite size_map size_enum_ord in H0.
  assert ( [seq row_sum (- inv_A1 3 h *m A2 3 h) i0
              | i0 <- enum 'I_3] = 
           mkseq (fun i => row_sum (- inv_A1 3 h *m A2 3 h) (@inord 2 i)) 3).
  { unfold mkseq. rewrite -val_enum_ord.
    rewrite -[in RHS]map_comp.
    apply eq_map. unfold eqfun. intros.
    by rewrite //= inord_val //=.
  } rewrite H1 nth_mkseq; last by apply H0.
  rewrite /row_sum. rewrite !big_ord_recr //= big_ord0 !add0r //=.
  rewrite !mxE. rewrite !big_ord_recr //= !big_ord0 !add0r//=.
  rewrite !mxE.
  assert (widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max) = 0).
  { by apply /eqP. } rewrite H2 //=. rewrite !subr0 !mulr0.
  assert (((2 / (h * (h * 1)))%Re - (2 / (h * (h * 1)))%Re) = 0%Re).
  { rewrite -RminusE. nra. } rewrite H3. rewrite !addr0 !mulr0 !add0r.
  assert (i = 0%N \/ i = 1%N \/ i = 2%N).
  { rewrite leq_eqVlt in H0.
    assert ((i.+1 == 3%N) \/ (i.+1 < 3)%N). { by apply /orP. }
    destruct H4.
    + by right;right;apply /eqP.
    + rewrite leq_eqVlt in H4.
      assert ((i.+2 == 3%N) \/ (i.+2 < 3)%N). { by apply /orP. }
      destruct H5.
      - right. left. by apply /eqP.
      - left. rewrite !ltnS in H5. rewrite leqn0 in H5. by apply /eqP.
  } 
  destruct H4.
  - rewrite H4 //=. rewrite inordK //=. rewrite -!RmultE -!RoppE.
    assert ( (- 0 * (-1 / (h * (h * 1))))%Re = 0%Re).
    { nra. } rewrite H5 add0r Rabs_R0 !add0r !addr0. 
    assert ((- (1 * (2 / (h * (h * 1)))%Re^-1) *
                (-1 / (h * (h * 1))))%Re =  (1 / 2)%Re).
    { assert ((-1 / (h * (h * 1)))%Re = (- (1 / h^2))%Re).
      { rewrite Rmult_1_r. 
        assert ((h^2)%Re = (h*h)%Re). { nra. } rewrite H6. nra.
      } rewrite H6. rewrite Rmult_1_r.
      assert ((2 / (h * h))%Re^-1 = (h^2 / 2)%Re).
      { rewrite -div1r. rewrite -RdivE.
        + assert ((1 / (2 / (h * h)))%Re = ( / (2 / (h* h)))%Re).
          { nra. } rewrite H7. rewrite Rinv_mult_distr.
          - rewrite Rinv_involutive; nra.  
          - nra.
          - apply Rinv_neq_0_compat. nra.
        + apply /eqP. apply Rmult_integral_contrapositive.
          split.
          - nra.
          - apply Rinv_neq_0_compat. nra.
      } rewrite H7.
      assert ((- (1 * (h ^ 2 / 2)) * - (1 / h ^ 2))%Re = 
               ((h^2 * / (h^2)) * (/2))%Re).
      { nra. } rewrite H8. 
      assert ((h^2 * / (h^2))%Re = 1%Re).
      { by rewrite Rinv_r; nra. } by rewrite H9.
    } rewrite H6. rewrite Rabs_right; nra.
  - destruct H4.
    * rewrite H4 //=. rewrite inordK //=. rewrite !addr0.
      rewrite -!RmultE -!RoppE.
      assert ( (- 0 * (-1 / (h * (h * 1))))%Re = 0%Re).
      { nra. } rewrite H5 add0r Rabs_R0 !addr0.
      assert ((- (1 * (2 / (h * (h * 1)))%Re^-1) *
                (-1 / (h * (h * 1))))%Re =  (1 / 2)%Re).
      { assert ((-1 / (h * (h * 1)))%Re = (- (1 / h^2))%Re).
        { rewrite Rmult_1_r. 
          assert ((h^2)%Re = (h*h)%Re). { nra. } rewrite H6. nra.
        } rewrite H6. rewrite Rmult_1_r.
        assert ((2 / (h * h))%Re^-1 = (h^2 / 2)%Re).
        { rewrite -div1r. rewrite -RdivE.
          + assert ((1 / (2 / (h * h)))%Re = ( / (2 / (h* h)))%Re).
            { nra. } rewrite H7. rewrite Rinv_mult_distr.
            - rewrite Rinv_involutive; nra.  
            - nra.
            - apply Rinv_neq_0_compat. nra.
          + apply /eqP. apply Rmult_integral_contrapositive.
            split.
            - nra.
            - apply Rinv_neq_0_compat. nra.
        } rewrite H7.
        assert ((- (1 * (h ^ 2 / 2)) * - (1 / h ^ 2))%Re = 
                 ((h^2 * / (h^2)) * (/2))%Re).
        { nra. } rewrite H8. 
        assert ((h^2 * / (h^2))%Re = 1%Re).
        { by rewrite Rinv_r; nra. } by rewrite H9.
      } rewrite H6. rewrite Rabs_right.
      rewrite -RplusE. 
      assert ((1 / 2 + 1 / 2)%Re = 1%Re). { nra. } rewrite H7.
      apply Rle_refl. nra.
    * rewrite H4 //=. rewrite inordK //=. rewrite !addr0.
      rewrite -!RmultE -!RoppE.
      assert ( (- 0 * (-1 / (h * (h * 1))))%Re = 0%Re).
      { nra. } rewrite H5 add0r Rabs_R0 !addr0 !add0r.
      assert ((- (1 * (2 / (h * (h * 1)))%Re^-1) *
                (-1 / (h * (h * 1))))%Re =  (1 / 2)%Re).
      { assert ((-1 / (h * (h * 1)))%Re = (- (1 / h^2))%Re).
        { rewrite Rmult_1_r. 
          assert ((h^2)%Re = (h*h)%Re). { nra. } rewrite H6. nra.
        } rewrite H6. rewrite Rmult_1_r.
        assert ((2 / (h * h))%Re^-1 = (h^2 / 2)%Re).
        { rewrite -div1r. rewrite -RdivE.
          + assert ((1 / (2 / (h * h)))%Re = ( / (2 / (h* h)))%Re).
            { nra. } rewrite H7. rewrite Rinv_mult_distr.
            - rewrite Rinv_involutive; nra.  
            - nra.
            - apply Rinv_neq_0_compat. nra.
          + apply /eqP. apply Rmult_integral_contrapositive.
            split.
            - nra.
            - apply Rinv_neq_0_compat. nra.
        } rewrite H7.
        assert ((- (1 * (h ^ 2 / 2)) * - (1 / h ^ 2))%Re = 
                 ((h^2 * / (h^2)) * (/2))%Re).
        { nra. } rewrite H8. 
        assert ((h^2 * / (h^2))%Re = 1%Re).
        { by rewrite Rinv_r; nra. } by rewrite H9.
     } rewrite H6. rewrite Rabs_right; nra.
Qed.



Lemma matrix_norm_A1_lt_2:
  matrix_inf_norm (inv_A1 3 1) <= (1 / 2)%Re.
Proof.
unfold matrix_inf_norm.  apply /RleP.
apply bigmax_le. 
+ by rewrite size_map size_enum_ord.
+ intros. rewrite seq_equiv. rewrite nth_mkseq.
  - rewrite /row_sum. rewrite !big_ord_recr //= !big_ord0 !add0r //=.
    rewrite !mxE //=.
    assert ((i < 3)%N). { by rewrite size_map size_enum_ord in H. }
    rewrite leq_eqVlt in H0.
    assert ((i == 2%N) \/ (i < 2)%N). { by apply /orP. } destruct H1.
    * assert (i = 2%N). { by apply /eqP. } rewrite H2.
      rewrite !inordK //=. rewrite Rabs_R0 !add0r. rewrite !Rmult_1_r.
      assert ((2 / 1)%Re = 2%Re). { nra. } rewrite H3. rewrite -RdivE.
      ++ rewrite Rabs_right. 
         -- apply Rle_refl.
         -- apply Rle_ge, Rlt_le. 
            assert ((1 / 2)%Re = (/2)%Re). { nra. } rewrite H4. 
            apply Rinv_0_lt_compat; nra.
      ++ apply /eqP. apply two_not_zero.
    * rewrite leq_eqVlt in H1.
      assert ((i == 1%N) \/ (i < 1)%N). { by apply /orP. } destruct H2.
      ++ assert (i = 1%N). { by apply /eqP. } rewrite H3.
         rewrite !inordK //=. rewrite Rabs_R0 !add0r addr0. rewrite !Rmult_1_r.
         assert ((2 / 1)%Re = 2%Re). { nra. } rewrite H4. rewrite -RdivE.
         -- rewrite Rabs_right. 
            ** apply Rle_refl.
            ** apply Rle_ge, Rlt_le. 
                assert ((1 / 2)%Re = (/2)%Re). { nra. } rewrite H5. 
                apply Rinv_0_lt_compat; nra.
         -- apply /eqP. apply two_not_zero.
      ++ rewrite ltnS leqn0 in H2.  assert (i = 0%N). { by apply /eqP. } rewrite H3.
         rewrite !inordK //=. rewrite Rabs_R0 !addr0. rewrite !Rmult_1_r.
         assert ((2 / 1)%Re = 2%Re). { nra. } rewrite H4. rewrite -RdivE.
         -- rewrite Rabs_right. 
            ** apply Rle_refl.
            ** apply Rle_ge, Rlt_le. 
                assert ((1 / 2)%Re = (/2)%Re). { nra. } rewrite H5. 
                apply Rinv_0_lt_compat; nra.
         -- apply /eqP. apply two_not_zero.
  - by rewrite size_map size_enum_ord in H.
Qed.


Lemma X_m_ind:
  forall k x0 b,
  X_m_real k.+1 x0 b 1 = 
  ((S_mat _ 1%Re)^+k.+1 *m x0) + 
  \sum_(j < k.+1) ((S_mat _ 1%Re)^+j *m ((inv_A1 3 1%Re) *m b)).
Proof.
intros.
induction k.
+ simpl. rewrite expr1. 
  rewrite !big_ord_recr //= big_ord0. rewrite expr0 add0r mul1mx //=.
+ assert (X_m_real k.+2 x0 b 1 = 
          (S_mat _ 1%Re) *m X_m_real k.+1 x0 b 1 + ((inv_A1 3 1%Re) *m b)).
  { by simpl. } rewrite H.
  rewrite IHk. rewrite !mulmxDr.
  assert (S_mat 3 1 *m (S_mat 3 1 ^+ k.+1 *m x0) = 
          S_mat 3 1 ^+ k.+2 *m x0 ).
  { rewrite [in RHS]exprS. by rewrite mulmxA. } rewrite H0.
  assert (\sum_(j < k.+2) S_mat 3 1 ^+ j *m (inv_A1 3 1 *m b) =
          S_mat 3 1 *m (\sum_(j < k.+1)
                 S_mat 3 1 ^+ j *m 
              (inv_A1 3 1 *m b)) + inv_A1 3 1 *m b).
  { rewrite big_ord_recl //=. rewrite expr0 mul1mx. rewrite addrC.
    assert (\sum_(i < k.+1) S_mat 3 1 ^+ bump 0 i *m (inv_A1 3 1 *m b) = 
                S_mat 3 1 *m (\sum_(j < k.+1)
                 S_mat 3 1 ^+ j *m  (inv_A1 3 1 *m b))).
    { rewrite /bump //=. 
      assert (\sum_(i < k.+1)
                S_mat 3 1 ^+ (1 + i) *m (inv_A1 3 1 *m b) = 
               \sum_(i < k.+1) (S_mat 3 1) *m ((S_mat 3 1)^+i *m (inv_A1 3 1 *m b))).
      { apply eq_big. by []. intros. rewrite [in LHS]exprS.
        by rewrite !mulmxA.
      } rewrite H1. 
      by rewrite (@mulmx_distrr 3 (S_mat 3 1) (fun i => (S_mat 3 1 ^+ i *m 
                 (inv_A1 3 1 *m b))) k).
    } by rewrite H1 //=.
  } rewrite H1. by rewrite -addrA.
Qed. 


Lemma mat_inf_norm_S_pow:
  forall k,
  matrix_inf_norm (S_mat 3 1 ^+ k.+1) <= 1%Re.
Proof.
intros. induction k.
+ rewrite expr1.  by apply S_mat_norm_lt_1; nra.
+ assert ( S_mat 3 1 ^+ k.+2 = S_mat 3 1 *m S_mat 3 1 ^+k.+1).
  { rewrite exprS //=. } rewrite H. apply /RleP.
  apply Rle_trans with 
  (matrix_inf_norm (S_mat 3 1) * matrix_inf_norm (S_mat 3 1 ^+ k.+1))%Re.
  - apply /RleP. apply matrix_norm_le.
  - assert (1%Re = (1 * 1)%Re). { nra. } rewrite H0.
    apply Rmult_le_compat.
    * apply /RleP. apply matrix_norm_pd.
    * apply /RleP. apply matrix_norm_pd.
    * rewrite -H0. apply /RleP. by apply S_mat_norm_lt_1; nra.
    * rewrite -H0. by apply /RleP.
Qed.
  

(* 
Definition f_bound {n:nat} (x1 b : 'cV[R]_n) (x2 : nat -> 'cV[R]_n) (m:nat) (u eps h: R) :=
  bigmaxr 0%Re [seq (Finite (theta_x x1 x2 m) * 
                    \big[+%R/0]_(j < n) ((n+1)%:R * Rabs (A2 n h i j) * Rabs (x1 j ord0) * u) + 
                        2 * n.-1%:R * eps * (1 + u)^+n + 
                        eps * (1 + u) + Rabs (b i ord0) * u + eps + 
                     ( (((n.+1)^2)%:R * ((n+1)^(n-2) - 1)%:R) / 2`!%:R) * 
                    \big[+%R/0]_(j < n) (Rabs (A2 n h i j) * Rabs (x1 j ord0)) * u^+2)%Re |  i <- enum 'I_n].


*)

Close Scope R_scope. 
