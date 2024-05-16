From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

Set Bullet Behavior "Strict Subproofs". 


From Iterative Require Import   lemmas.


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


(** Infinity norm of a vector is the maximum of 
    absolute values of the entries of a vector 
**)
Definition vec_inf_norm {n:nat} (v : 'cV[R]_n) :=
 bigmaxr 0%Re [seq (Rabs (v i 0)) | i <- enum 'I_n].

(** Infinity norm of a matrix is the maximum of the columm sums **)
Definition matrix_inf_norm {n:nat} (A: 'M[R]_n) :=
  bigmaxr 0%Re [seq (row_sum A i) | i <- enum 'I_n].

Lemma vec_inf_norm_0_is_0 {n:nat}: 
  @vec_inf_norm n.+1 0 = 0%Re.
Proof.
rewrite /vec_inf_norm. apply bigmaxrP.
split.
+ apply /mapP. exists (@ord0 n).
  - by rewrite mem_enum.
  - by rewrite mxE Rabs_R0.
+ intros. rewrite nth_seq_0_is_0. apply /RleP. apply Rle_refl.
  by rewrite size_map size_enum_ord in H. 
Qed.

Ltac seq_rewrite := unfold mkseq; rewrite -val_enum_ord; rewrite -[in RHS]map_comp ;apply eq_map; unfold eqfun; intros.

Lemma triang_ineq {n:nat} : forall a b: 'cV[R]_n.+1,
vec_inf_norm(a + b) <= vec_inf_norm a + vec_inf_norm b.
Proof.
intros.
rewrite /vec_inf_norm. apply /RleP.
apply lemmas.bigmax_le.
+ by rewrite size_map size_enum_ord. 
+ intros. rewrite -RplusE. 
  apply Rle_trans with 
    ([seq Rabs (a i0 0) | i0 <- enum 'I_n.+1]`_i + 
     [seq Rabs (b i0 0) | i0 <- enum 'I_n.+1]`_i)%Re.
  - assert ([seq Rabs ((a + b)%Ri i0 0) | i0 <- enum 'I_n.+1] = 
               mkseq (fun i =>  Rabs ((a + b)%Ri (@inord n i) 0)) n.+1).
    { 
      seq_rewrite. rewrite !mxE //=. rewrite !mxE. by rewrite inord_val.
    } rewrite H0 nth_mkseq; last by rewrite size_map size_enum_ord in H.  
    assert ([seq Rabs (a i0 0) | i0 <- enum 'I_n.+1] = 
               mkseq (fun i =>  Rabs (a (@inord n i) 0)) n.+1).
    { 
      seq_rewrite. by rewrite //= inord_val //=.
    } rewrite H1 nth_mkseq ; last by rewrite size_map size_enum_ord in H.
    assert ([seq Rabs (b i0 0) | i0 <- enum 'I_n.+1] = 
               mkseq (fun i =>  Rabs (b (@inord n i) 0)) n.+1).
    { 
      seq_rewrite. by rewrite //= inord_val //=.
    } rewrite H2 nth_mkseq ; last by rewrite size_map size_enum_ord in H.
    rewrite !mxE //=. rewrite -RplusE. apply Rabs_triang.
  - apply Rplus_le_compat.
      all: apply /RleP.
      1: apply (@bigmaxr_ler _ 0%Re [seq Rabs (a i0 0) | i0 <- enum 'I_n.+1] i).
      2: apply (@bigmaxr_ler _ 0%Re [seq Rabs (b i0 0) | i0 <- enum 'I_n.+1] i).
      all: (rewrite size_map size_enum_ord; by rewrite size_map size_enum_ord in H).
Qed.



Lemma submult_prop {n:nat} (A: 'M[R]_n.+1) (v : 'cV[R]_n.+1):
  vec_inf_norm (A *m v) <=
  matrix_inf_norm A * vec_inf_norm v.
Proof.
rewrite /vec_inf_norm /matrix_inf_norm. rewrite mulrC.
rewrite -bigmaxr_mulr.
+ apply /RleP. apply lemmas.bigmax_le.
  - by rewrite size_map size_enum_ord.
  - intros.
    apply Rle_trans with
    [seq (bigmaxr 0
           [seq Rabs (v i1 0) | i1 <- enum 'I_n.+1] *
         row_sum A i0)%Ri
      | i0 <- enum 'I_n.+1]`_i.
    * assert ([seq Rabs ((A *m v) i0 0) | i0 <- enum 'I_n.+1] = 
              mkseq (fun i => Rabs ((A *m v) (@inord n i) 0)) n.+1).
      { 
        seq_rewrite. rewrite !mxE //=. rewrite !mxE. by rewrite //= inord_val //=.
      } rewrite H0 nth_mkseq ; last by rewrite size_map size_enum_ord in H.
      assert ([seq bigmaxr 0
                  [seq Rabs (v i1 0) | i1 <- enum 'I_n.+1] *  row_sum A i0
                    | i0 <- enum 'I_n.+1] = 
               mkseq (fun i =>  bigmaxr 0  
                        [seq Rabs (v i1 0) | i1 <- enum 'I_n.+1] *  row_sum A (@inord n i)) n.+1).
      { 
        seq_rewrite. by rewrite //= inord_val //=.
      } rewrite H1 nth_mkseq ; last by rewrite size_map size_enum_ord in H.
      rewrite -RmultE. rewrite !mxE.
      apply Rle_trans with 
        (\sum_j Rabs (A (inord i) j * v j 0)).
      ++ apply /RleP. apply Rabs_ineq.
      ++ assert (\sum_j Rabs (A (inord i) j * v j 0) = 
                  \sum_j (Rabs (A (inord i) j) * Rabs (v j 0))).
         { apply eq_big. by []. intros. by rewrite Rabs_mult. }
         rewrite H2. rewrite Rmult_comm. apply /RleP. rewrite RmultE. rewrite -bigmaxr_mulr.
         apply /RleP. 
         rewrite bigmaxr_mulr. rewrite -RmultE. rewrite /row_sum.
         rewrite big_distrl //=.
         apply /RleP. apply big_sum_ge_ex_abstract. intros.
         rewrite -!RmultE. apply Rmult_le_compat_l.
         -- apply Rabs_pos.
         -- apply Rle_trans with [seq Rabs (v i1 0) | i1 <- enum 'I_n.+1]`_i0.
            ** assert ([seq Rabs (v i1 0) | i1 <- enum 'I_n.+1] = 
                       mkseq (fun i => Rabs (v (@inord n i) 0)) n.+1).
               { 
                 seq_rewrite. by rewrite //= inord_val //=.
               } rewrite H4 nth_mkseq ; last by rewrite size_map size_enum_ord in H. 
               rewrite //= inord_val. nra.
            ** apply /RleP. apply (@bigmaxr_ler _ 0%Re [seq Rabs (v i1 0) | i1 <- enum 'I_n.+1] i0).
                rewrite size_map size_enum_ord.
                by rewrite size_map size_enum_ord in H.
         -- unfold row_sum. apply big_ge_0_ex_abstract. intros.
            apply /RleP. apply Rabs_pos.
         -- unfold row_sum. apply big_ge_0_ex_abstract. intros.
            apply /RleP. apply Rabs_pos.
    * apply /RleP. 
      apply (@bigmaxr_ler _ 0%Re [seq bigmaxr 0
                [seq Rabs (v i1 0) | i1 <- enum 'I_n.+1] * row_sum A i0
                  | i0 <- enum 'I_n.+1] i).
      rewrite size_map size_enum_ord.
      by rewrite size_map size_enum_ord in H.
+ apply bigmax_le_0.
  - by apply /RleP; apply Rle_refl.
  - intros. 
    assert ([seq Rabs (v i0 0) | i0 <- enum 'I_n.+1]= 
              mkseq (fun i => Rabs (v (@inord n i) 0)) n.+1).
    { 
      seq_rewrite. by rewrite //= inord_val //=.
    } rewrite H0 nth_mkseq ; last by rewrite size_map size_enum_ord in H.
    unfold row_sum. apply /RleP. apply Rabs_pos.
Qed.



Lemma matrix_norm_pd {n:nat} (A : 'M[R]_n.+1):
  0 <= matrix_inf_norm A.
Proof.
rewrite /matrix_inf_norm.
apply bigmax_le_0.
+ by apply /RleP; apply Rle_refl.
+ intros. rewrite seq_equiv.
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
  rewrite /row_sum. apply big_ge_0_ex_abstract.
  intros. apply /RleP. apply Rabs_pos.
Qed.




Lemma vec_norm_pd {n:nat} (v : 'cV[R]_n.+1):
  0 <= vec_inf_norm v.
Proof.
rewrite /vec_inf_norm.
apply bigmax_le_0.
+ by apply /RleP; apply Rle_refl.
+ intros. rewrite seq_equiv.
  rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
  apply /RleP. apply Rabs_pos.
Qed.


Lemma reverse_triang_ineq:
  forall n a b c, 
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
apply /RleP. apply lemmas.bigmax_le.
+ by rewrite size_map size_enum_ord.
+ intros. rewrite seq_equiv. rewrite nth_mkseq.
  - rewrite /row_sum. 
    apply Rle_trans with 
    (\sum_(j < n.+1) (\sum_(k < n.+1) (Rabs (A (inord i) k) * Rabs (B k j))%Re)).
    * apply /RleP. apply big_sum_ge_ex_abstract. intros.
      rewrite !mxE.
      apply Rle_trans with 
      (\sum_j (Rabs ((A (inord i) j) * B j i0))).
      ++ apply /RleP. apply Rabs_ineq.
      ++ assert (\sum_j Rabs (A (inord i) j * B j i0) = 
                  \sum_(k < n.+1) (Rabs (A (inord i) k) * Rabs (B k i0))%Re).
         { apply eq_big. by []. intros. by rewrite Rabs_mult. }
         rewrite H1. nra.
    * assert (\sum_(j < n.+1)
                \sum_(k < n.+1)
                   (Rabs (A (inord i) k) * Rabs (B k j))%Re = 
               \sum_(k < n.+1)
                  \sum_(j < n.+1)
                     (Rabs (A (inord i) k) * Rabs (B k j))%Re).
      { apply exchange_big. } rewrite H0. 
      rewrite mulrC. rewrite -bigmaxr_mulr.

      apply Rle_trans with 
      (nth 0 [seq (bigmaxr 0 [seq \sum_(j < n.+1) Rabs (B i1 j)
                      | i1 <- enum 'I_n.+1] *
                    (\sum_(j < n.+1) Rabs (A i0 j)))%Ri | i0 <- enum 'I_n.+1] i).
      ++ rewrite seq_equiv. rewrite nth_mkseq. 
         -- rewrite big_distrr //=. apply /RleP.
            apply big_sum_ge_ex_abstract. intros.
            rewrite -RmultE. rewrite Rmult_comm.
            rewrite -big_distrr //=. rewrite -RmultE.
            apply Rmult_le_compat_l.
            ** apply Rabs_pos.
            ** apply /RleP. 
               assert (\sum_(i1 < n.+1) Rabs (B i0 i1) = 
                        nth 0 [seq \sum_(j < n.+1) Rabs (B i1 j)
                               | i1 <- enum 'I_n.+1]  i0).
                { rewrite seq_equiv. rewrite nth_mkseq. by rewrite inord_val. apply ltn_ord. }
                rewrite H2. 
                apply (@bigmaxr_ler _ 0  [seq \sum_(j < n.+1) Rabs (B i1 j)
                                           | i1 <- enum 'I_n.+1] i0).
                rewrite size_map size_enum_ord. apply ltn_ord.
         -- by rewrite size_map size_enum_ord in H.
      ++ apply /RleP. 
         apply (@bigmaxr_ler _ 0%Re [seq bigmaxr 0
                       [seq \sum_(j < n.+1) Rabs (B i1 j)
                          | i1 <- enum 'I_n.+1] *
                     (\sum_(j < n.+1) Rabs (A i0 j))
                   | i0 <- enum 'I_n.+1] i).
         rewrite size_map size_enum_ord.
         by rewrite size_map size_enum_ord in H.
      ++ apply bigmax_le_0.
         -- apply /RleP. apply Rle_refl.
         -- intros. rewrite seq_equiv. rewrite nth_mkseq.
            ** apply big_ge_0_ex_abstract. intros.
               apply /RleP. apply Rabs_pos.
            ** by rewrite size_map size_enum_ord in H1.
  - by rewrite size_map size_enum_ord in H.
Qed.

Lemma matrix_norm_add {n:nat}:
  forall (A B : 'M[R]_n.+1),
  matrix_inf_norm (A + B) <= matrix_inf_norm A + matrix_inf_norm B.

Proof.
intros. rewrite /matrix_inf_norm.
apply /RleP. apply lemmas.bigmax_le.
+ by rewrite size_map size_enum_ord //=.
+ intros.
  rewrite seq_equiv. rewrite nth_mkseq.
  - rewrite /row_sum.
    apply Rle_trans with 
    (\sum_(j < n.+1) Rabs (A (inord i) j) + 
     \sum_(j < n.+1) Rabs (B (inord i) j))%Re.
    * assert (\sum_(j < n.+1) Rabs ((A + B)%Ri (inord i) j) = 
              \sum_(j < n.+1) Rabs (A (inord i) j + B (inord i) j)).
      { apply eq_big. by []. intros. rewrite !mxE. by rewrite -RplusE. }
      rewrite H0. apply sum_abs_le .
    * apply Rplus_le_compat.
      ++ assert (\sum_(j < n.+1) Rabs (A (inord i) j) = 
                  nth 0 [seq \sum_(j < n.+1) Rabs (A i0 j)
                            | i0 <- enum 'I_n.+1] i).
         { rewrite seq_equiv. rewrite nth_mkseq.
           + by [].
           + by rewrite size_map size_enum_ord in H.
         } rewrite H0. apply /RleP.
         apply (@bigmaxr_ler _ 0 [seq \sum_(j < n.+1) Rabs (A i0 j)
                                      | i0 <- enum 'I_n.+1] i). 
          rewrite size_map size_enum_ord in H.
         by rewrite size_map size_enum_ord.
         (* seq_rewrite' H H0 A j n i0 i.  *)
      ++ assert (\sum_(j < n.+1) Rabs (B (inord i) j) = 
                  nth 0 [seq \sum_(j < n.+1) Rabs (B i0 j)
                            | i0 <- enum 'I_n.+1] i).
         { rewrite seq_equiv. rewrite nth_mkseq.
           + by [].
           + by rewrite size_map size_enum_ord in H.
         } rewrite H0. apply /RleP.
         apply (@bigmaxr_ler _ 0 [seq \sum_(j < n.+1) Rabs (B i0 j)
                                      | i0 <- enum 'I_n.+1] i).
         rewrite size_map size_enum_ord in H.
         by rewrite size_map size_enum_ord.
         (* seq_rewrite' H H0 B j n i0 i. *)
  - by rewrite size_map size_enum_ord in H.
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
} rewrite H.
apply bigmaxrP.
split.
+ assert (1%Re = nth 0 (mkseq (fun=> 1) n.+1) 0).
  { by rewrite nth_mkseq. } rewrite H0. rewrite inE //=. 
  apply /orP. by left.
+ intros. rewrite nth_mkseq.
  - apply /RleP. apply Rle_refl.
  - assert (mkseq (fun i : nat => 1%Re) n.+1 = 
             [seq 1%Re | i <- enum 'I_n.+1]).
    { by rewrite seq_equiv. } rewrite H1 in H0.
    rewrite size_map size_enum_ord //= in H0.
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









