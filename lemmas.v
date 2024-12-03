(** This file contains random necessary lemmas for the project, 
including the definition of error_sum used in the conclusion of the 
main global accuracy theorem **)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

Set Bullet Behavior "Strict Subproofs". 

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

Lemma sum_1_eq:
  forall k, 
  \sum_(j < k.+1) 1 = k.+1%:R :> R.
Proof.
intros. induction k.
+ rewrite !big_ord_recr //= big_ord0 add0r //=.
+ rewrite big_ord_recr //=. rewrite IHk. rewrite -[in RHS]addn1.
  by rewrite natrD.
Qed.


Lemma big_0_ex_abstract I r (P: pred I) (E : I -> R):
  (forall i, P i -> E i = 0) ->
  \big[+%R/0]_(i <-r | P i) E i = 0.
Proof.
move => Eq. apply big_ind. 
+ by [].
+ intros. rewrite H H0 addr0 //=. 
+ by apply /Eq.
Qed.

Lemma nat_ge_0:
  forall (k:nat),
  (0 <= k.+1%:R)%Re.
Proof.
intros. induction k.
+ apply Rle_0_1.
+ rewrite -addn1. rewrite natrD. rewrite -RplusE.
  apply Rplus_le_le_0_compat.
  - apply IHk.
  - apply Rle_0_1.
Qed.



Lemma m_ge_n (m n :nat) :
  (m <= n)%N -> (m%:R <= n%:R)%Re.
Proof.
intros. induction n.
+ rewrite leqn0 in H. assert ( m = 0%N). { by apply /eqP. }
  rewrite H0. nra.
+ rewrite leq_eqVlt in H.
  assert ( (m == n.+1) \/ (m < n.+1)%N).
  { by apply /orP. } destruct H0.
  - assert ( m = n.+1). { by apply /eqP. }
    rewrite H1. nra.
  - assert ( (m <=n)%N). { by []. }
    specialize (IHn H1).
    rewrite -addn1 natrD. apply Rle_trans with n%:R.
    * apply IHn.
    * rewrite -RplusE. 
      assert (n%:R = (n%:R + 0)%Re). { nra. }
      rewrite H2. 
      assert ((n%:R + 0 + 1%:R)%Re = (n%:R + 1%:R)%Re).
      { nra. } rewrite H3. apply Rplus_le_compat. 
      nra. apply Rlt_le. apply Rlt_0_1. 
Qed.



Lemma real_cast (n:nat):
  n%:R = INR n.
Proof.
induction n.
+ by simpl.
+ rewrite -addn1. rewrite natrD. rewrite plus_INR.
  rewrite IHn. reflexivity.
Qed.




Definition row_sum {n:nat} (A: 'M[R]_n) (i: 'I_n) :=
  \big[+%R/0]_(j<n) Rabs (A i j).
  


Definition theta_x {n:nat} (x1 : 'cV[R]_n) (x2 : nat -> 'cV[R]_n) (m:nat) :=
  Lub_Rbar (fun x => 
    x = bigmaxr 0 [seq (Rabs (x2 m i 0) / Rabs (x1 i 0)) | i <- enum 'I_n]). 



Definition error_sum (n:nat) (S:R) :=
  if (n == 0%N) then 0%Re else
    \big[+%R/0]_(l < n) S^+l. 



Definition listR_to_vecR {n:nat} (l : list R) := \col_(i < n) 
  match (nat_of_ord i) with 
    | S n =>  List.nth (S n) l 0
    | _ => List.nth 0 l 0
  end.




Lemma x_minus_x_is_0 {n:nat}:
  forall x: 'cV[R]_n, x - x = 0.
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE //=. apply /eqP.
by rewrite subr_eq0.
Qed.

Lemma nth_seq_0_is_0 {n:nat} (i:nat):
  (i < n)%N -> 
  [seq Rabs ((GRing.zero : 'cV[R]_n) i0 0) | i0 <- enum 'I_n]`_i = 0%Re.
Proof.
intros.
assert ([seq Rabs ((GRing.zero : 'cV[R]_n) i0 0) | i0 <- enum 'I_n] = 
          mkseq (fun _ => 0) n).
{ unfold mkseq. rewrite -val_enum_ord.
  rewrite -[in RHS]map_comp.
  apply eq_map. unfold eqfun.
  intros. rewrite mxE Rabs_R0 //=.  
} rewrite H0. by rewrite nth_mkseq.
Qed.




Lemma bigmax_le (x0:R) lr (x:R):
 (0 < size lr)%N ->
 (forall i:nat, (i < size lr)%N -> ((nth x0 lr i) <= x)%Re) ->
 ((bigmaxr x0 lr) <= x)%Re.
Proof.
intros.
move /(nthP x0): (bigmaxr_mem x0 H).
move => [i i_size <-].
by apply H0.
Qed.



Lemma enum_list:
  enum 'I_3 = [:: ord0;  1; (@inord 2 2)].
Proof.
apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite /iota //=.
assert ((1 %% 3)%N = 1%N). { by []. } rewrite H //=.
by rewrite inordK.
Qed.





Lemma s_destruct (x0:R) s:
  s != [::] ->
  s = head x0 s :: behead s.
Proof.
induction s.
+ by [].
+ by intros. 
Qed.
  
Lemma bigmax_le_0 (x0:R) s:
  0 <= x0 ->
  (forall i, (i < size s)%N -> 0 <= nth x0 s i) ->
  0 <= bigmaxr x0 s.
Proof.
intros.
rewrite /bigmaxr.
induction s.
+ by rewrite big_nil //=. 
+ rewrite big_cons //=.
  assert (s = [::] \/ s != [::]).
  { destruct s.
    + by left.
    + by right.
  } destruct H1.
  - rewrite H1 //=. rewrite H1 //= in H0.
    rewrite big_nil. specialize (H0 0%N).
    assert ((0 < 1)%N). { by []. } specialize (H0 H2).
    simpl in H0. rewrite -RmaxE. rewrite Rmax_left.
    * by [].
    * nra.
  - assert (s = head x0 s :: behead s).
    { by apply s_destruct. }
    rewrite H2. rewrite bigrmax_dflt. rewrite -H2.
    rewrite le_maxr. apply /orP.
    specialize (H0 0%N). simpl in H0.
    left. by apply H0. 
Qed.


Lemma big_ge_0_ex_abstract I r (P: pred I) (E : I -> R):
  (forall i, P i -> (0 <= E i)) ->
  (0 <= \big[+%R/0]_(i <-r | P i) E i).
Proof.
move => leE. apply big_ind.
+ apply /RleP. apply Rle_refl.
+ intros. apply /RleP.
  rewrite -RplusE. apply Rplus_le_le_0_compat.  
  - by apply /RleP.
  - by apply /RleP.
+ apply leE.
Qed.


Lemma big_sum_ge_ex_abstract I r (P: pred I) (E1 E2: I -> R):
  (forall i, P i -> (E1 i <= E2 i)%Re) ->
  (\big[+%R/0]_(i <-r | P i) E1 i <= \big[+%R/0]_(i <-r | P i) E2 i).
Proof.
move => leE12. apply /RleP. apply big_ind2.
+ nra.
+ intros. rewrite -!RplusE. by apply Rplus_le_compat.
+ apply leE12.
Qed.

Lemma Rabs_ineq {n:nat} (f : 'I_n.+1 -> R):
  Rabs (\sum_j f j) <= \sum_j (Rabs (f j)).
Proof.
induction n.
+ simpl. rewrite !big_ord_recr //= !big_ord0 !add0r //=.
+ simpl. rewrite big_ord_recr //=.
  assert (\sum_(j < n.+2) Rabs (f j) = 
            \sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) + Rabs (f ord_max)).
  { by rewrite !big_ord_recr//=. } rewrite H. 
  apply /RleP. rewrite -!RplusE.
  apply Rle_trans with 
  (Rabs (\sum_(i < n.+1) f (widen_ord (leqnSn n.+1) i)) +
    Rabs (f ord_max))%Re.
  - apply Rabs_triang.
  - apply Rplus_le_compat_r. apply /RleP. by apply IHn.
Qed.
  




Lemma seq_equiv {n:nat} (f : 'I_n.+1 -> R) :
  [seq f i | i <- enum 'I_n.+1] = 
  mkseq (fun i => f (@inord n i)) n.+1.
Proof.
unfold mkseq. rewrite -val_enum_ord.
rewrite -[in RHS]map_comp.
apply eq_map. unfold eqfun. intros.
by rewrite //= inord_val //=.
Qed.




Lemma bigmax_le_implies (x0:R) lr (x:R):
 (0 < size lr)%N ->
  ((bigmaxr x0 lr) <= x)%Re -> 
 (forall i:nat, (i < size lr)%N -> ((nth x0 lr i) <= x)%Re).
Proof.
intros.
apply Rle_trans with (bigmaxr x0 lr).
+ apply /RleP. by apply (@bigmaxr_ler _ x0 lr i).
+ apply H0.
Qed.


Definition error_sum_ind:= 
  fun (error : R) (n : nat) =>
  match n with
  | 0%nat => 0
  | S n' => sum_f 0 n' (fun m : nat => error ^ m)
  end.

Lemma error_sum_equiv:
  forall (n:nat) (f: R),  
  error_sum n f = error_sum_ind f n.
Proof.
intros.
induction n.
+ rewrite /error_sum /error_sum_ind //=.
+ rewrite /error_sum /error_sum_ind in IHn.
  destruct n.
  - simpl in IHn. rewrite /error_sum /error_sum_ind //=.
    rewrite /sum_f big_ord_recr //= big_ord0 add0r //=.
  - simpl in IHn. rewrite /error_sum /error_sum_ind //=.
    rewrite big_ord_recr //=. rewrite /sum_f //=.
    rewrite /sum_f //= in IHn.
    assert ((n - 0)%coq_nat = n). { lia. } rewrite H in IHn.
    rewrite IHn. 
    assert ((n + 0)%coq_nat = n). { lia. } rewrite H0.
    by rewrite !RplusE.  
Qed.



Lemma vec_sum_simpl {n:nat}:
  forall (a b c : 'cV[R]_n),
  a - c = a - b + b - c.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -!RplusE -!RoppE.
rewrite !Rplus_assoc.
f_equal.
rewrite -Rplus_assoc Rplus_opp_l Rplus_0_l //.
Qed.


Ltac rewrite_scope :=
  try apply /RleP;
  try rewrite -!RplusE -!RmultE
. 


Lemma Rle_minus_l :
  forall a b c : R, (a - b <= c) -> (a <= c + b). 
Proof.
intros. rewrite -RplusE.
rewrite_scope.
rewrite -RminusE in H.
assert (a - b <= c)%Re.
rewrite_scope; auto.
nra.
Qed.

Lemma mulmx_distrr {n:nat}:
  forall (A :'M[R]_n) (f : nat -> 'cV[R]_n) (k:nat),
  \sum_(i < k.+1) (A *m (f i)) = A *m (\sum_(i < k.+1) (f i)).
Proof.
intros. induction k.
+ rewrite !big_ord_recr //= !big_ord0. by rewrite !add0r.
+ rewrite big_ord_recr //=.
  assert (\sum_(i < k.+2) f i = (\sum_(i < k.+1) f i) + f k.+1).
  { by rewrite !big_ord_recr //= !big_ord0. } rewrite H.
  rewrite mulmxDr. by rewrite IHk.
Qed.


Lemma two_not_zero:
  2%Re <> 0%Re.
Proof. nra. Qed.

Lemma f_pow_ge_0: 
  forall (i:nat) (f:R),
  0 <= f -> 0 <= f^+i.
Proof.
intros. induction i.
+ rewrite expr0. apply /RleP. apply Rle_0_1.
+ rewrite exprS. apply /RleP. rewrite -RmultE.
  by apply Rmult_le_pos; apply /RleP.
Qed.

Lemma error_sum_ge_0:
  forall (n:nat) (f:R),
  0 <= f ->
  0 <= error_sum n f.
Proof.
intros. rewrite /error_sum.
destruct (n == 0%N).
+ apply /RleP;apply Rle_refl.
+ apply big_ge_0_ex_abstract.
  intros. by apply f_pow_ge_0.
Qed.


Lemma pow_add: 
  forall (er : R (*_ringType*) ) (n:nat), 
  (er ^ (n + 1)%N) = (er * er ^ n).
Proof.
intros. 
induction n.
+ rewrite add0n //=. 
rewrite expr1z expr0z.
rewrite  -!RmultE.
rewrite Rmult_1_r.
auto. 
+
rewrite exprzD_nat.
rewrite expr1z.
repeat rewrite -RmultE. 
nra.
Qed.


Lemma error_sum_aux2 er n:
  er * error_sum_ind er n + 1  = error_sum_ind er (S n).
Proof. 
intros.
induction n. 
+ simpl. unfold sum_f. rewrite mulr0 add0r //=. 
+ unfold error_sum_ind. rewrite /error_sum_ind in IHn.
  destruct n.
  - rewrite /sum_f. simpl. rewrite /sum_f in IHn. simpl in IHn.
    rewrite mulr0 in IHn. rewrite add0r in IHn. rewrite -IHn. 
    rewrite mulr1. rewrite RplusE //=. 
    assert (er ^ 1%N = er). { by rewrite //=. } rewrite H.
    by rewrite addrC.
  - rewrite /sum_f. rewrite /sum_f in IHn. simpl.
    assert ( (n + 0)%coq_nat = n). { lia. } rewrite H.
    rewrite !RplusE. simpl in IHn. rewrite H in IHn.
    rewrite mulrDr.
    assert ((n - 0)%coq_nat = n). { lia. } rewrite H0 in IHn.
    rewrite -!addrA -(addrC 1) !addrA IHn RplusE //.
Qed.



Lemma mult_abs_le {n:nat}:
  forall (f g : 'I_n.+1 -> R),
  (\sum_(j < n.+1) Rabs (f j * g j) <=
    (\sum_(j < n.+1) Rabs (f j)) *
    \sum_(j < n.+1) Rabs (g j))%Re.
Proof.
intros. induction n.
+ rewrite !big_ord_recr //= !big_ord0 !add0r.
  rewrite Rabs_mult. nra.
+ rewrite big_ord_recr //=.
  assert (\sum_(j < n.+2) Rabs (f j) = 
          \sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) + Rabs (f ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H.
  assert (\sum_(j < n.+2) Rabs (g j) = 
          \sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j)) + Rabs (g ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H0.
  rewrite -!RplusE.
  assert (((\sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) +
            Rabs (f ord_max)) *
           (\sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j)) +
            Rabs (g ord_max)) )%Re = 
          (((\sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j))) *
            \sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j))) +
          ((Rabs (f ord_max) * Rabs (g ord_max)) +
            (Rabs (f ord_max) * (\sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j))) +
             Rabs (g ord_max) * (\sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j))))))%Re).
  { nra. } rewrite H1. apply Rplus_le_compat.
  - apply IHn.
  - assert (Rabs (f ord_max * g ord_max) = (Rabs (f ord_max * g ord_max) + 0)%Re).
    { nra. } rewrite H2. rewrite Rabs_mult. apply Rplus_le_compat_l.
    apply Rplus_le_le_0_compat.
    * apply Rmult_le_pos.
      ++ apply Rabs_pos.
      ++ apply /RleP. apply big_ge_0_ex_abstract. intros.
         apply /RleP. apply Rabs_pos.
    * apply Rmult_le_pos.
      ++ apply Rabs_pos.
      ++ apply /RleP. apply big_ge_0_ex_abstract. intros.
         apply /RleP. apply Rabs_pos.
Qed.



Lemma sum_abs_le {n:nat}:
  forall (f g : 'I_n.+1 -> R),
  (\sum_(j < n.+1) Rabs (f j + g j) <=
    \sum_(j < n.+1) Rabs (f j) +
    \sum_(j < n.+1) Rabs (g j))%Re.
Proof.
intros. induction n.
+ rewrite !big_ord_recr //= !big_ord0 !add0r. 
  apply Rabs_triang.
+ rewrite big_ord_recr //=. rewrite -RplusE.
  assert (\sum_(j < n.+2) Rabs (f j) = 
          \sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) + Rabs (f ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H.
  assert (\sum_(j < n.+2) Rabs (g j) = 
          \sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j)) + Rabs (g ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H0.
  rewrite -!RplusE.
  assert ((\sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) +
             Rabs (f ord_max) +
             (\sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j)) +
              Rabs (g ord_max)))%Re = 
           ((\sum_(j < n.+1) Rabs (f (widen_ord (leqnSn n.+1) j)) +
            \sum_(j < n.+1) Rabs (g (widen_ord (leqnSn n.+1) j))) +
            (Rabs (f ord_max) +  Rabs (g ord_max)))%Re).
  { nra. } rewrite H1.
  apply Rplus_le_compat.
  - apply IHn.
  - apply Rabs_triang.
Qed.
 

Lemma mulmx_distrl {n:nat}:
  forall (A :'cV[R]_n) (f : nat -> 'M[R]_n) (k:nat),
  \sum_(i < k.+1) ((f i) *m A) = (\sum_(i < k.+1) (f i)) *m A.
Proof.
intros. induction k.
+ rewrite !big_ord_recr //= !big_ord0. by rewrite !add0r.
+ rewrite big_ord_recr //=.
  assert (\sum_(i < k.+2) f i = (\sum_(i < k.+1) f i) + f k.+1).
  { by rewrite !big_ord_recr //= !big_ord0. } rewrite H.
  rewrite mulmxDl. by rewrite IHk.
Qed.


Lemma error_sum_le :
  forall k er er',  
  0 <= er ->   
  er <= er' -> 
  error_sum k er <= error_sum k er'.
Proof.
intros. 
induction k.
- simpl; auto.
- repeat rewrite error_sum_equiv.
repeat rewrite error_sum_equiv in IHk.
repeat rewrite <- error_sum_aux2.
apply ler_add; auto.
apply ler_pmul; auto.
rewrite <- error_sum_equiv.
apply error_sum_ge_0; auto.
Qed.

Lemma error_sum_1 :
  forall k,  
  (error_sum k 1 = INR k).
Proof.
intros. 
induction k.
- simpl; auto.
- repeat rewrite error_sum_equiv.
repeat rewrite error_sum_equiv in IHk.
repeat rewrite <- error_sum_aux2.
rewrite_scope.
rewrite Rmult_1_l.
rewrite IHk.
rewrite S_INR; auto.
Qed.


