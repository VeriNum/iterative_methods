From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

Set Bullet Behavior "Strict Subproofs". 


From Iterative Require Import   lemmas.


From mathcomp Require Import matrix bigop all_algebra all_ssreflect.
From mathcomp Require Import Rstruct.
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


(** Infinity norm of a vector is the maximum of 
    absolute values of the entries of a vector 
**)

Definition vec_inf_norm {n : nat} (v : 'cV[R]_n) :=
  let s := [seq (Rabs (v i 0)) | i <- enum 'I_n] in 
  \big[maxr / 0%Re]_(i <- s) i.

(* bigmaxr deprecated*)
(* Definition vec_inf_norm {n:nat} (v : 'cV[R]_n) :=
 bigmaxr 0%Re [seq (Rabs (v i 0)) | i <- enum 'I_n]. *)

(** Infinity norm of a matrix is the maximum of the columm sums **)
Definition matrix_inf_norm {n : nat} (A : 'M[R]_n) :=
  let s := [seq (row_sum A i) | i <- enum 'I_n] in 
  \big[maxr / 0%Re]_(i <- s) i.

(* bigmaxr deprecated *)
(* Definition matrix_inf_norm {n:nat} (A: 'M[R]_n) :=
  bigmaxr 0%Re [seq (row_sum A i) | i <- enum 'I_n]. *)

Lemma vec_inf_norm_nonneg {n : nat} (v : 'cV[R]_n.+1):
  0 <= vec_inf_norm v.
Proof.
  rewrite /vec_inf_norm. 
  apply bigmax_le_0_0head. intros.
  rewrite (@nth_map _ 0).
  + apply /RleP. apply Rabs_pos.
  + rewrite size_map in H. auto.
Qed.

Lemma matrix_inf_norm_nonneg {n : nat} (A : 'M[R]_n.+1):
  0 <= matrix_inf_norm A.
Proof.
  rewrite /matrix_inf_norm.
  apply bigmax_le_0_0head. intros.
  rewrite (@nth_map _ 0).
  + rewrite /row_sum. apply sum_of_pos. intros.
    apply /RleP. apply Rabs_pos.
  + rewrite size_map in H. auto.
Qed.


Lemma vec_inf_norm_0_is_0 {n:nat}: 
  @vec_inf_norm n.+1 0 = 0%Re.
Proof.
  rewrite /vec_inf_norm.
  (* rewrite seq_equiv /mkseq. *)
  assert ([seq Rabs ((GRing.zero : 'cV[R]_n.+1) (i : 'I_n.+1) 0) | i <- enum 'I_n.+1] = 
    [seq 0%Re | i <- enum 'I_n.+1]).
  { apply eq_map. intros i. rewrite zero_vec_entry Rabs_R0 //=. } 
  assert ([seq 0%Re | _ <- enum 'I_n.+1] = nseq n.+1 0%Re). 
  { apply seq_const_nseq. by rewrite size_enum_ord. } 
  rewrite H H0 big_nseq.
  clear H H0. induction n as [|n'].
  + rewrite //=. unfold maxr. replace (0%Re < 0%Re) with false by auto. by [].
  + rewrite //=. rewrite //= in IHn'. rewrite IHn'.
    rewrite /maxr. replace (0%Re < 0%Re) with false by auto. by [].
Qed.


Lemma triang_ineq {n:nat} : forall a b: 'cV[R]_n.+1,
  vec_inf_norm(a + b) <= vec_inf_norm a + vec_inf_norm b.
Proof.
  intros. rewrite /vec_inf_norm. apply /RleP. apply bigmax_le_0head.
  + rewrite size_map size_enum_ord //=.
  + intros. rewrite size_map size_enum_ord in H. 
    assert (nth 0 [seq Rabs ((a + b)%Ri i0 0)  | i0 <- enum 'I_n.+1] i = 
            Rabs ((a + b)%Ri (@inord n i) 0)).
    { rewrite seq_equiv. rewrite nth_mkseq; auto. }
    rewrite H0.
    apply Rle_trans with (Rabs (a (@inord n i) ord0) + Rabs (b (@inord n i) ord0))%Re.
    { rewrite !mxE //=. rewrite -!RplusE. apply Rabs_triang. }
    rewrite -!RplusE. apply Rplus_le_compat.
    - apply bigmax_ler_0head.
      { rewrite seq_equiv /mkseq. 
        apply (@map_f _ _ (fun i => Rabs (a (inord i) ord0)) (iota 0 n.+1) i).
        rewrite mem_iota. rewrite //=. }
      { intros. move /mapP in H1. destruct H1 as [ix H1 H2]. rewrite H2.
        apply /RleP. apply Rabs_pos. }
    - apply bigmax_ler_0head.
      { rewrite seq_equiv /mkseq. 
        apply (@map_f _ _ (fun i => Rabs (b (inord i) ord0)) (iota 0 n.+1) i).
        rewrite mem_iota. rewrite //=. }
      { intros. move /mapP in H1. destruct H1 as [ix H1 H2]. rewrite H2.
        apply /RleP. apply Rabs_pos. }
  + intros. move /mapP in H. destruct H as [ix H1 H2]. rewrite H2.
    apply /RleP. apply Rabs_pos.
Qed.



Lemma submult_prop {n:nat} (A: 'M[R]_n.+1) (v : 'cV[R]_n.+1):
  vec_inf_norm (A *m v) <=
  matrix_inf_norm A * vec_inf_norm v.
Proof.
  rewrite /vec_inf_norm /matrix_inf_norm mulrC.
  rewrite -!RmultE.
  rewrite bigmax_mulr_0head.
  2:{ rewrite size_map size_enum_ord //=. } 
  2:{ intros. move /mapP in H. destruct H as [ix H1 H2]. rewrite H2.
      rewrite /row_sum. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rabs_pos. }
  2:{ pose proof (vec_inf_norm_nonneg v). rewrite /vec_inf_norm in H. auto. } 
  remember (\big[maxr/0%Re]_(i <- [seq Rabs (v i 0)  | i <- enum 'I_n.+1])  i) as vnorm.
  apply /RleP. apply bigmax_le_0head.
  { rewrite size_map size_enum_ord //=. } 
  2:{ intros. move /mapP in H. destruct H as [ix H1 H2]. rewrite H2. apply /RleP. apply Rabs_pos. }
  intros. rewrite (@nth_map _ 0).
  2:{ rewrite size_map size_enum_ord in H. rewrite size_enum_ord. auto. }
  rewrite enum_inord.
  2:{ rewrite size_map size_enum_ord in H. auto. }
  rewrite mxE. eapply Rle_trans.
  { apply /RleP. apply Rabs_ineq. } 
  rewrite //=. 
  assert ([seq (vnorm * x)%Ri  | x <- [seq row_sum A i0  | i0 <- enum 'I_n.+1]] =
    [seq vnorm * row_sum A i0  | i0 <- enum 'I_n.+1]).
  { rewrite -map_comp //=. } rewrite {}H0.
  assert (\sum_(j < n.+1) Rabs (A (inord i) j * v j 0) <= 
          \sum_(j < n.+1) Rabs (A (inord i) j) * vnorm).
  { apply sum_all_terms_le. intros. rewrite -!RmultE.
    rewrite !Rabs_mult. apply Rmult_le_compat_l.
    apply Rabs_pos. rewrite Heqvnorm. apply bigmax_ler_0head.
    { apply (@map_f _ _ (fun i0 => Rabs (v i0 0)) (enum 'I_n.+1) i0).
      apply mem_enum. }
    intros. move /mapP in H0. destruct H0. rewrite H1. apply /RleP. apply Rabs_pos. }
  eapply Rle_trans. { apply /RleP. apply H0. } clear H0.
  rewrite sum_mult_distrr -!RmultE Rmult_comm.
  assert (vnorm * (\sum_(i0 < n.+1)  Rabs (A (inord i) i0)) <=
    vnorm * row_sum A (inord i)).
  { rewrite /row_sum. auto. } 
  eapply Rle_trans. { apply /RleP. apply H0. } clear H0.
  remember (inord i) as i0.
  apply bigmax_ler_0head.
  { apply (@map_f _ _ (fun i0 => vnorm * row_sum A i0) (enum 'I_n.+1) i0).
    apply mem_enum. } 
  intros. move /mapP in H0. destruct H0. rewrite H1. apply /RleP.
  rewrite -!RmultE. apply Rmult_le_pos.
  + rewrite Heqvnorm. apply /RleP. apply vec_inf_norm_nonneg.
  + rewrite /row_sum. apply /RleP. apply sum_of_pos. intros.
    apply /RleP. apply Rabs_pos.
Qed.



Lemma matrix_norm_pd {n:nat} (A : 'M[R]_n.+1):
  0 <= matrix_inf_norm A.
Proof.
  apply matrix_inf_norm_nonneg.
Qed.




Lemma vec_norm_pd {n:nat} (v : 'cV[R]_n.+1):
  0 <= vec_inf_norm v.
Proof.
  apply vec_inf_norm_nonneg.
Qed.



Lemma reverse_triang_ineq {n : nat} (a b: 'cV[R]_n.+1) (c : R):
  @vec_inf_norm n.+1 (a - b) <= c -> 
  @vec_inf_norm n.+1 (a) - @vec_inf_norm n.+1 (b) <= c.
Proof.
intros. apply /RleP. rewrite -RminusE.
apply Rle_trans with (vec_inf_norm (a - b)).
+ assert (forall x y z:R, (x  <= y + z)%Re -> (x  - y <= z)%Re).
  { intros. nra. } apply H0.
  apply Rle_trans with (vec_inf_norm (b + (a - b))).
  - assert (a = b + (a - b)).
    { apply matrixP. unfold eqrel. intros. rewrite !mxE. 
      rewrite -RplusE -RminusE.
      assert ((b x y + (a x y - b x y))%Re = a x y).
      { nra. } by rewrite H1.
    } rewrite -H1. apply Rle_refl.
  - apply /RleP. apply triang_ineq. 
+ by apply /RleP.
Qed.


Lemma vec_inf_norm_opp {n:nat}:
  forall v: 'cV[R]_n,  
  vec_inf_norm v = vec_inf_norm (-v).
Proof.
intros. rewrite /vec_inf_norm. 
assert ([seq Rabs (v i 0) | i <- enum 'I_n] = 
        [seq Rabs ((- v)%Ri i 0) | i <- enum 'I_n]).
{ apply eq_map. unfold eqfun. intros.
  rewrite! mxE. rewrite -RoppE. by rewrite  Rabs_Ropp.
} by rewrite H.
Qed.




Lemma cs_ineq_vec_inf_norm :
forall len, forall a b c d: 'cV[R]_len,
(0 < len)%N -> 
vec_inf_norm(a - b + c -d) <= vec_inf_norm(a - b) + vec_inf_norm(c -d).
Proof.
intros.
  assert ((a - b + c -d) = (a - b) + (c - d)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE. 
    rewrite -!RplusE -!RoppE. nra.
  } rewrite H0.
  assert (len = len.-1.+1).
  {  rewrite prednK; auto. }
  move: a  b c d H0. rewrite H1. intros. by apply triang_ineq.
Qed.


Lemma matrix_norm_le {n:nat}:
  forall (A B : 'M[R]_n.+1),
  matrix_inf_norm (A *m B) <= matrix_inf_norm A * matrix_inf_norm B.
Proof.
  intros. rewrite /matrix_inf_norm.
  apply /RleP. apply bigmax_le_0head.
  { rewrite size_map size_enum_ord //=. } 
  2:{ intros. move /mapP in H. destruct H as [ix H1 H2]. rewrite H2.
      rewrite /row_sum. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rabs_pos. }
  intros. rewrite (@nth_map _ 0).
  2:{ rewrite size_map size_enum_ord in H. rewrite size_enum_ord. auto. }
  rewrite enum_inord.
  2:{ rewrite size_map size_enum_ord in H. auto. }
  rewrite /row_sum.
  apply Rle_trans with (\sum_(j < n.+1) (\sum_(k < n.+1) (Rabs (A (inord i) k) * Rabs (B k j))%Re)).
  { apply /RleP. apply big_sum_ge_ex_abstract. intros. 
    rewrite !mxE. apply Rle_trans with (\sum_j (Rabs ((A (inord i) j) * B j i0))).
    { apply /RleP. apply Rabs_ineq. }
    assert (\sum_j Rabs (A (inord i) j * B j i0) = 
                  \sum_(k < n.+1) (Rabs (A (inord i) k) * Rabs (B k i0))%Re).
    { apply eq_big; auto. intros. apply Rabs_mult. }
    rewrite {}H1. nra. } 
  assert (\sum_(j < n.+1) \sum_(k < n.+1) (Rabs (A (inord i) k) * Rabs (B k j))%Re = 
          \sum_(k < n.+1) \sum_(j < n.+1) (Rabs (A (inord i) k) * Rabs (B k j))%Re).
  { apply exchange_big. } rewrite {}H0.
  rewrite mulrC. rewrite -RmultE. 
  remember (\big[maxr/0]_(i0 <- [seq \sum_(j < n.+1)  Rabs (B i0 j)  | i0 <- enum 'I_n.+1])  i0) as Bnorm.
  rewrite -HeqBnorm. rewrite bigmax_mulr_0head.
  2:{ rewrite size_map size_enum_ord //=. }
  2:{ intros. move /mapP in H0. destruct H0 as [ix H1 H2]. rewrite H2.
      apply /RleP. apply /RleP. apply sum_of_pos. intros. apply /RleP. apply Rabs_pos. }
  2:{ rewrite HeqBnorm. apply matrix_inf_norm_nonneg. }
  
  assert ([seq (Bnorm * x)%Ri  | x <- [seq \sum_(j < n.+1)  Rabs (A i0 j)  | i0 <- enum 'I_n.+1]] = 
          [seq Bnorm * \sum_(j < n.+1) Rabs (A i0 j)  | i0 <- enum 'I_n.+1]).
  { rewrite -map_comp //=. } rewrite {}H0.
  assert (\sum_(k < n.+1)  \sum_(j < n.+1)  (Rabs (A (inord i) k) * Rabs (B k j)) = 
          \sum_(k < n.+1) (Rabs (A (inord i) k) * (\sum_(j < n.+1) Rabs (B k j)))).
  { apply eq_big; auto. intros. rewrite sum_mult_distrl. auto. } rewrite {}H0.
  assert (forall k, \sum_(j < n.+1)  Rabs (B k j) <= Bnorm).
  { intros. rewrite HeqBnorm. apply /RleP. apply bigmax_ler_0head.
    apply (@map_f _ _ (fun k => \sum_(j < n.+1) Rabs (B k j)) ).
    apply mem_enum. intros. move /mapP in H0. destruct H0. rewrite H1.
    apply sum_of_pos. intros. apply /RleP. apply Rabs_pos. } 
  assert (\sum_(k < n.+1)  Rabs (A (inord i) k) * (\sum_(j < n.+1)  Rabs (B k j)) <= 
          \sum_(k < n.+1) Rabs (A (inord i) k) * Bnorm).  
  { apply sum_all_terms_le. intros. rewrite -!RmultE.
    apply Rmult_le_compat_l. apply Rabs_pos. apply /RleP. apply H0. }
  eapply Rle_trans. { apply /RleP. apply H1. } clear H0 H1.
  assert (\sum_(k < n.+1)  Rabs (A (inord i) k) * Bnorm  = 
    Bnorm * \sum_(k < n.+1)  Rabs (A (inord i) k)).
  { rewrite sum_mult_distrr. rewrite -!RmultE Rmult_comm. auto. } rewrite {}H0.
  apply bigmax_ler_0head.
  { apply (@map_f _ _ (fun i0 => Bnorm * (\sum_(k < n.+1) Rabs (A i0 k))) (enum 'I_n.+1)).
    apply mem_enum. }
  intros. move /mapP in H0. destruct H0. rewrite H1. apply mulr_ge0.
  + rewrite HeqBnorm. pose proof @matrix_inf_norm_nonneg. apply H2.
  + apply sum_of_pos. intros. apply /RleP. apply Rabs_pos.
Qed.


Lemma matrix_norm_add {n:nat}:
  forall (A B : 'M[R]_n.+1),
  matrix_inf_norm (A + B) <= matrix_inf_norm A + matrix_inf_norm B.
Proof.
  intros. rewrite /matrix_inf_norm.
  apply /RleP. apply bigmax_le_0head.
  { rewrite size_map size_enum_ord //=. }
  2:{ intros. move /mapP in H. destruct H as [ix H1 H2]. rewrite H2.
      rewrite /row_sum. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rabs_pos. }
  intros. rewrite (@nth_map _ 0).
  2:{ rewrite size_map size_enum_ord in H. rewrite size_enum_ord. auto. }
  rewrite enum_inord.
  2:{ rewrite size_map size_enum_ord in H. auto. }
  rewrite /row_sum.
  apply Rle_trans with (\sum_(j < n.+1) Rabs (A (inord i) j) + \sum_(j < n.+1) Rabs (B (inord i) j))%Re.
  { assert (\sum_(j < n.+1) Rabs ((A + B)%Ri (inord i) j) = 
            \sum_(j < n.+1) Rabs (A (inord i) j + B (inord i) j)).
    { apply eq_big; auto. intros. rewrite !mxE. rewrite -RplusE //=. }
    rewrite {}H0. apply sum_abs_le. }
  apply Rplus_le_compat.
  + apply bigmax_ler_0head.
    - apply (@map_f _ _ (fun i0 => \sum_(j < n.+1) Rabs (A i0 j))). apply mem_enum.
    - intros. move /mapP in H0. destruct H0. rewrite H1. apply sum_of_pos. intros.
      apply /RleP. apply Rabs_pos.
  + apply bigmax_ler_0head.
    - apply (@map_f _ _ (fun i0 => \sum_(j < n.+1) Rabs (B i0 j))). apply mem_enum.
    - intros. move /mapP in H0. destruct H0. rewrite H1. apply sum_of_pos. intros.
      apply /RleP. apply Rabs_pos.
Qed.


Lemma matrix_norm_sum {n:nat} (f : nat -> 'M[R]_n.+1) (k:nat):
  matrix_inf_norm
   (\sum_(j < k.+1) f j) <= 
  \sum_(j < k.+1) (matrix_inf_norm (f j)).
Proof.
induction k.
+ rewrite !big_ord_recr //= !big_ord0 !add0r. by apply /RleP; nra.
+ rewrite big_ord_recr //=.
  assert (\sum_(j < k.+2) matrix_inf_norm (f j) = 
          \sum_(j < k.+1) matrix_inf_norm (f j) + matrix_inf_norm (f k.+1)).
  { by rewrite big_ord_recr //=. } rewrite H.
  apply /RleP. 
  apply Rle_trans with 
  (matrix_inf_norm (\sum_(i < k.+1) f i) + matrix_inf_norm (f k.+1))%Re.
  - apply /RleP. apply matrix_norm_add.
  - rewrite -RplusE. 
    apply Rplus_le_compat_r.
    by apply /RleP.
Qed.



Lemma matrix_inf_norm_1 {n:nat}:
  @matrix_inf_norm n.+1 1 = 1%Re.
Proof.
  rewrite /matrix_inf_norm. rewrite seq_equiv.
  assert (mkseq (fun i : nat => row_sum 1 (@inord n i)) n.+1 = 
          mkseq (fun i : nat => 1%Re) n.+1).
  { apply eq_map. unfold eqfun. intros.
    rewrite /row_sum. 
    rewrite (bigD1 (inord x)) //=.
    assert (\sum_(i < n.+1 | i != inord x) Rabs ((1%:M : 'M[R]_n.+1) (inord x) i) = 0%Re).
    { rewrite big_0_ex_abstract.
      + by [].
      + intros. rewrite !mxE.
        assert (inord x == i = false).
        { rewrite eq_sym. apply /eqP. by apply /eqP. } rewrite H0 //=.
        by rewrite Rabs_R0. 
        } rewrite H !mxE //=.
    rewrite addr0. 
    assert (@inord n x == @inord n x = true).
    { by apply /eqP. } rewrite H0 //=. by rewrite Rabs_R1.
  } rewrite {}H.  
  rewrite /mkseq. apply bigmax_const_seq. lra.
Qed.


Lemma matrix_inf_norm_pow {n:nat}:
  forall (A: 'M[R]_n.+1) (i: nat),
  (matrix_inf_norm (A ^+ i) <= (matrix_inf_norm A)^+i)%Re.
Proof.
intros.
induction i.
+ rewrite !expr0. rewrite matrix_inf_norm_1 . apply Rle_refl.
+ rewrite !exprS. 
  apply Rle_trans with 
  (matrix_inf_norm A * matrix_inf_norm (A ^+ i))%Re.
  - apply /RleP. apply matrix_norm_le .
  - rewrite -RmultE. apply Rmult_le_compat_l.
    * apply /RleP. apply matrix_norm_pd.
    * apply IHi.
Qed.









