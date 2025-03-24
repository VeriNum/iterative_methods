(** This file contains random necessary lemmas for the project, 
including the definition of error_sum used in the conclusion of the 
main global accuracy theorem **)

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

Set Bullet Behavior "Strict Subproofs". 

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
intros. generalize dependent m. induction n; intros.
+ rewrite leqn0 in H. assert (m = 0%N). { apply /eqP; auto. }
  rewrite H0. apply Rle_refl.
+ rewrite leq_eqVlt in H.
  assert ( (m == n.+1) \/ (m < n.+1)%N).
  { apply /orP; auto. }
  destruct H0.
  - assert (m = n.+1). { apply /eqP; auto. }
    rewrite H1. apply Rle_refl.
  - assert ((m <= n)%N). { auto. }
    pose proof (IHn m H1).
    rewrite -addn1 natrD -RplusE. 
    apply Rle_trans with n%:R; auto.
    replace n%:R with (n%:R + 0%Ri)%Re at 1.
    2:{ rewrite Rplus_0_r. auto. }
    apply Rplus_le_compat_l. apply Rle_0_1.
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


(* Definition theta_x {n : nat} (x1 : 'cV[R]_n) (x2 : nat -> 'cV[R]_n) (m : nat) :=
  Lub_Rbar (fun x =>
    x = \big[Order.Def.max/0]_(i<-enum 'I_n) (Rabs (x2 m i 0) / Rabs (x1 i 0))). *)

Definition theta_x {n : nat} (x1 : 'cV[R]_n) (x2 : nat -> 'cV[R]_n) (m : nat) :=
  Lub_Rbar (fun x => x = 
    let s := [seq (Rabs (x2 m i 0) / Rabs (x1 i 0)) | i <- enum 'I_n] in 
    \big[maxr / head 0%Re s]_(i <- s) i).


(* bigmaxr deprecated *)
(* Definition theta_x {n:nat} (x1 : 'cV[R]_n) (x2 : nat -> 'cV[R]_n) (m:nat) :=
  Lub_Rbar (fun x => 
    x = bigmaxr 0 [seq (Rabs (x2 m i 0) / Rabs (x1 i 0)) | i <- enum 'I_n]). *)
 



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
intros. 
rewrite !mxE //=. apply /eqP.
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

(* bigmax_le exists in mathcomp.analysis.order *)
Check bigmax_le.

(* bigmaxr deprecated *)


Lemma bigmax_mem_0head  (lr : seq R) :
  (0 < size lr)%N ->
  (forall x, x \in lr -> x >= 0) ->
  (\big[maxr/0%Re]_(i <- lr) i) \in lr.
Proof.
  induction lr as [|x lr']; intros.
  + inversion H.
  + rewrite big_cons. remember (\big[maxr/0%Re]_(j <- lr')  j) as maxlr'.
    assert (maxr x (\big[maxr/0%Re]_(j <- lr')  j) = maxr x maxlr').
    { rewrite Heqmaxlr'. auto. } rewrite H1.
    rewrite /maxr. destruct (x < maxlr') eqn:E.
    2:{ apply mem_head. }
    destruct (size lr') eqn : Esize.
    - destruct lr'. 2:{ inversion Esize. } 
      subst maxlr'. rewrite big_nil in E. 
      assert (0 <= x).
      { apply H0. apply mem_head. }
      move /RltP in E. move /RleP in H2. 
      apply Rlt_not_le in H2; auto.
    - assert (maxlr' \in lr').
      { apply IHlr'. auto. intros. apply H0. rewrite in_cons. apply /orP. auto. }
      rewrite in_cons. apply /orP. auto.
Qed.

Lemma bigmax_le_0head lr (x:R):
  (0 < size lr)%N ->
  (forall i:nat, (i < size lr)%N -> ((nth (0%Re) lr i) <= x)%Re) ->
  (forall x, x \in lr -> x >= 0) ->
  (\big[maxr/0%Re]_(i <- lr) i <= x)%Re.
Proof.
  intros.
  pose proof (@bigmax_mem_0head lr H H1).
  move /(nthP 0%Re): H2.
  move => [i i_size <-].
  by apply H0.
Qed.

Lemma maxr_l (x y : R) : x <= maxr x y.
Proof.
  rewrite /maxr. destruct (x < y) eqn:E; auto.
Qed.

Lemma maxr_r (x y : R) : y <= maxr x y.
Proof. 
  rewrite maxC. apply maxr_l.
Qed.

Lemma maxr_l_le (x y z : R) : x <= y -> x <= maxr y z.
Proof.
  intros. rewrite /maxr. destruct (y < z) eqn:E; auto.
  assert (y < z) by auto. 
  apply /RleP. move /RltP in H0. move /RleP in H.
  apply Rlt_le in H0. nra.
Qed.

Lemma maxr_r_le (x y z : R) : x <= z -> x <= maxr y z.
Proof.
  intros. rewrite maxC. apply maxr_l_le; auto.
Qed.

Lemma bigmax_ler_0head lr (x:R):
  x \in lr ->
  (forall x, x \in lr -> x >= 0) ->
  (x <= \big[maxr/0%Re]_(i <- lr) i)%Re.
Proof.
  intros. induction lr as [|y lr'].
  + inversion H.
  + rewrite in_cons in H. move /orP in H. destruct H.
    - move /eqP in H. rewrite H. rewrite big_cons. apply /RleP. apply maxr_l.
    - rewrite big_cons. apply /RleP. apply maxr_r_le. apply /RleP. apply IHlr'; auto.
      intros. apply H0. rewrite in_cons. apply /orP. auto.
Qed.

Lemma bigmax_mulr_0head lr (k : R) :
  let klr := [seq (k * x) | x <- lr] in
  (0 < size lr)%N ->
  (forall x, x \in lr -> x >= 0) ->
  (k >= 0) ->
  (k * (\big[maxr/0%Re]_(i <- lr) i) = \big[maxr/0%Re]_(i <- klr) i)%Re.
Proof.
  intros. induction lr as [|x lr']; [inversion H|].
  remember [seq k * x | x <- lr'] as klr'.
  assert (klr = (k * x) :: klr').
  { subst klr klr'. rewrite //=. } 
  rewrite H2. rewrite big_cons big_cons. rewrite //= in IHlr'.
  rewrite RmultE. rewrite maxr_pMr; auto.
  assert (k * \big[maxr/0%Re]_(j <- lr')  j =
    \big[maxr/0%Re]_(j <- klr')  j).
  { destruct (size lr') eqn:E.
    + apply size0nil in E. subst lr' klr'. rewrite !big_nil //=.
      rewrite -RmultE. nra.
    + apply IHlr'.
      { rewrite E //=. }
      intros. apply H0. rewrite in_cons. apply /orP. auto. } 
  rewrite H3. reflexivity.
Qed.   

(* Lemma bigmax_le_deprecated (x0:R) lr (x:R):
 (0 < size lr)%N ->
 (forall i:nat, (i < size lr)%N -> ((nth x0 lr i) <= x)%Re) ->
 ((bigmaxr x0 lr) <= x)%Re.
Proof.
intros.
move /(nthP x0): (bigmaxr_mem x0 H).
move => [i i_size <-].
by apply H0.
Qed. *)


Lemma enum_list:
  enum 'I_3 = [:: ord0;  1; (@inord 2 2)].
Proof.
  apply (inj_map val_inj). rewrite val_enum_ord.
  rewrite /iota. simpl.
  assert ((1 %% 3) = 1)%N. { auto. } rewrite H.
  rewrite inordK; auto.
Qed.





Lemma s_destruct (x0:R) s:
  s != [::] ->
  s = head x0 s :: behead s.
Proof.
induction s.
+ by [].
+ by intros. 
Qed.
  

Lemma bigmax_le_0 (x0 : R) s :
  0 <= x0 ->
  (forall i, (i < size s)%N -> 0 <= nth x0 s i) ->
  0 <= \big[Order.Def.max / head x0 s]_(i <- s) i.
  (* 0 <= \big[Order.Def.max / x0]_(i <- enum 'I_(size s)) (nth x0 s i). *)
Proof.
  intros. induction s as [|s0 s'].
  + rewrite //= big_nil. exact H.
  + rewrite //= big_cons //=.
    destruct s' as [| s1 s'].
    - rewrite big_nil. specialize (H0 0). simpl in H0.
      replace (maxr s0 s0) with s0.
      apply H0. auto. rewrite /maxr. replace (s0 < s0) with false; auto. 
    - rewrite le_max. apply /orP.
      pose proof (H0 0). rewrite //= in H1. left. by apply H1.
Qed.

Lemma bigmax_le_0_0head s :
  (forall i, (i < size s)%N -> 0 <= nth 0 s i) ->
  0 <= \big[maxr/0%Re]_(i <- s) i.
Proof.
  intros. induction s as [|s0 s'].
  + rewrite //= big_nil. apply /RleP. apply Rle_refl.
  + rewrite //= big_cons //=.
    destruct s' as [| s1 s'].
    - rewrite big_nil. apply maxr_r. 
    - rewrite le_max. apply /orP.
      right. apply IHs'. intros. 
      pose proof (H i.+1). apply H1. rewrite //=.
Qed.

(* bigmaxr deprecated *)
(* Lemma bigmax_le_0_deprecated (x0:R) s:
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
    rewrite le_max. apply /orP.
    specialize (H0 0%N). simpl in H0.
    left. by apply H0. 
Qed. *)



Lemma big_ge_0_ex_abstract I r (P: pred I) (E : I -> R):
  (forall i, P i -> (0 <= E i)) ->
  (0 <= \big[+%R/0]_(i <-r | P i) E i).
Proof.
  intros. apply big_ind; auto.
  intros. apply /RleP. apply Rplus_le_le_0_compat; apply /RleP; auto.
Qed.


Lemma big_sum_ge_ex_abstract I r (P: pred I) (E1 E2: I -> R):
  (forall i, P i -> (E1 i <= E2 i)%Re) ->
  (\big[+%R/0]_(i <-r | P i) E1 i <= \big[+%R/0]_(i <-r | P i) E2 i).
Proof.
  intros. apply /RleP. apply big_ind2; auto; try lra.
  intros. apply /RleP. apply lerD; by apply /RleP.
Qed. 

Lemma Rabs_ineq {n:nat} (f : 'I_n.+1 -> R):
  Rabs (\sum_j f j) <= \sum_j (Rabs (f j)).
Proof.
  induction n as [|n'].
  + rewrite //= !big_ord_recr //= !big_ord0 !add0r //=.
  + rewrite //= big_ord_recr //=.
    assert ((\sum_(j < n'.+2) Rabs (f j)) 
      = (\sum_(j < n'.+1) Rabs (f (widen_ord (leqnSn n'.+1) j)) + Rabs (f ord_max)))
      by rewrite //= !big_ord_recr //=.
    rewrite H. apply /RleP. 
    eapply Rle_trans. { apply Rabs_triang. }
    apply Rplus_le_compat_r. apply /RleP. apply IHn'.
Qed.

Lemma sum_mult_distrl {n : nat} (x : R) (f : 'I_n.+1 -> R) :
  \sum_(i < n.+1) (x * f i) = x * (\sum_(i < n.+1) f i).
Proof.
  induction n as [|n'].
  + rewrite !big_ord_recr //= !big_ord0 !add0r //=.
  + rewrite big_ord_recr //= IHn' [in RHS]big_ord_recr //=.
    rewrite -!RplusE -!RmultE. rewrite Rmult_plus_distr_l //=.
Qed.

Lemma sum_mult_distrr {n : nat} (x : R) (f : 'I_n.+1 -> R) :
  \sum_(i < n.+1) (f i * x) = (\sum_(i < n.+1) f i) * x. 
Proof.
  induction n as [|n'].
  + rewrite !big_ord_recr //= !big_ord0 !add0r //=.
  + rewrite big_ord_recr //= IHn' [in RHS]big_ord_recr //=.
    rewrite -!RplusE -!RmultE. rewrite Rmult_plus_distr_r //=.
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

Lemma seq_sum_mult_distrl {n : nat} (x : R) (f : 'I_n.+1 -> R) :
  [seq x * i | i <- [seq f i | i <- enum 'I_n.+1]] = [seq x * f i | i <- enum 'I_n.+1].
Proof.
  induction n as [|n']; rewrite -map_comp //=.
Qed. 

Lemma sum_all_terms_le {n : nat} (f1 f2 : 'I_n.+1 -> R) :
  (forall i, (f1 i <= f2 i)%Re) ->
  \sum_(i < n.+1) f1 i <= \sum_(i < n.+1) f2 i.
Proof.
  induction n as [|n']; intros.
  + rewrite !big_ord_recr //= !big_ord0 //= !add0r. apply /RleP. apply H.
  + rewrite big_ord_recr //=. 
    assert (\sum_(i < n'.+2)  f2 i = \sum_(i < n'.+1) f2 (widen_ord (leqnSn n'.+1) i) + f2 ord_max).
    { rewrite big_ord_recr //=. } rewrite {}H0.
    apply /RleP. apply Rplus_le_compat; auto.
    apply /RleP. apply IHn'; auto.
Qed.

(* Lemma bigmax_form_eq (x0 : R) lr :
  (0 < size lr)%N ->
  \big[Order.Def.max / head x0 lr]_(i <- lr) i = 
  \big[Order.Def.max / head x0 lr]_(i <- enum 'I_(size lr)) nth x0 lr i.
Proof.
  intros. induction lr as [|x lr'].
  + inversion H.
  + rewrite //=. destruct lr' as [|y lr'].
    - simpl. rewrite big_cons big_nil big_enum //=. admit.
    - simpl. rewrite big_cons. 
 *)

Lemma bigmax_seq_idx_eq (x0 : R) lr :
  \big[Order.Def.max/x0]_(i <- lr) i = \big[Order.Def.max/x0]_(i < (size lr)) nth x0 lr i.
Proof.
  induction lr as [|x lr'].
  + rewrite big_ord0 big_nil //.
  + rewrite //= big_cons big_ord_recl //= IHlr' //=.
Qed.


Lemma bigmax_le_implies (x0 : R) lr (x : R):
  (0 < size lr) %N ->
  (\big[Order.Def.max / x0]_(i <- lr) i <= x)%Re ->
  (forall i : nat, (i < size lr)%N -> ((nth x0 lr i) <= x)%Re).
Proof.
  intros. apply Rle_trans with (\big[Order.Def.max / x0]_(i <- lr) i); auto.
  apply /RleP. 
  remember (size lr) as n.
  destruct n as [| n'].
  + inversion H1.
  + pose proof ( @le_bigmax _ _ _ x0 (fun i => nth x0 lr (nat_of_ord i)) (@inord n' i)).
    rewrite //= in H2.
    rewrite bigmax_seq_idx_eq -Heqn.
    replace (nth x0 lr i) with (nth x0 lr (@inord n' i)). apply H2.
    rewrite inordK; auto.
Qed.


(* bigmaxr deprecated *)
(* Lemma bigmax_le_implies_deprecated (x0:R) lr (x:R):
 (0 < size lr)%N ->
  ((bigmaxr x0 lr) <= x)%Re -> 
 (forall i:nat, (i < size lr)%N -> ((nth x0 lr i) <= x)%Re).
Proof.
intros.
apply Rle_trans with (bigmaxr x0 lr).
+ apply /RleP. by apply (@bigmaxr_ler _ x0 lr i).
+ apply H0.
Qed. *)


(* Computes error ^ 0 + error ^ 1 + ... + error ^ (n-1) *)
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
  move => a b c /RleP H. rewrite -RminusE in H.
  rewrite_scope. rewrite -RplusE.
  nra.
Qed.

Lemma mulmx_distrr {n:nat}:
  forall (A :'M[R]_n) (f : nat -> 'cV[R]_n) (k:nat),
  \sum_(i < k.+1) (A *m (f i)) = A *m (\sum_(i < k.+1) (f i)).
Proof.
  intros. induction k.
  + rewrite !big_ord_recr //= !big_ord0 !add0r //=.
  + rewrite big_ord_recr //= IHk.
    assert ((\sum_(i < k.+2)  f i) = (\sum_(i < k.+1) f i + f k.+1)).
    { rewrite big_ord_recr //=. }
    rewrite H  mulmxDr //=.
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
  induction n as [|n'].
  + rewrite //= /sum_f //= mulr0 expr0z add0r //=.
  + unfold error_sum_ind in *.
    destruct n' as [|n''].
    - rewrite /sum_f //= expr0z mulr1 expr1z RplusE addrC //=.
    - rewrite /sum_f //= -!plus_n_O. 
      rewrite /sum_f //= -!plus_n_O Nat.sub_0_r in IHn'.
      rewrite !RplusE. rewrite !RplusE in IHn'.
      rewrite mulrDr -!addrA (addrC (er * er ^ n''.+1)) addrA IHn'.
      rewrite addrA -exprS //=.
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
  intros. induction n as [|n'].
  + rewrite !big_ord_recr //= !big_ord0 !add0r.
    apply Rabs_triang.
  + rewrite big_ord_recr //=. 
    eapply Rle_trans.
    { eapply (Rplus_le_compat_r). apply IHn'. }
    assert (\sum_(j < n'.+2)  Rabs (f j) = 
      \sum_(j < n'.+1)  Rabs ((fun j0 : 'I_n'.+1 => f (widen_ord (leqnSn n'.+1) j0)) j) + Rabs (f ord_max)). 
    { rewrite big_ord_recr //=. } 
    assert (\sum_(j < n'.+2)  Rabs (g j) = 
      \sum_(j < n'.+1)  Rabs ((fun j0 : 'I_n'.+1 => g (widen_ord (leqnSn n'.+1) j0)) j) + Rabs (g ord_max)).
    { rewrite big_ord_recr //=. }
    rewrite H H0. clear H H0.
    rewrite -!RplusE. 
    remember (\sum_(j < n'.+1)  Rabs (f (widen_ord (leqnSn n'.+1) j))) as S1.
    remember (\sum_(j < n'.+1)  Rabs (g (widen_ord (leqnSn n'.+1) j))) as S2.
    remember (f ord_max) as x1.
    remember (g ord_max) as x2.
    eapply Rle_trans.
    { eapply Rplus_le_compat_l. apply Rabs_triang. }
    lra.
Qed.
 

Lemma mulmx_distrl {n:nat}:
  forall (A :'cV[R]_n) (f : nat -> 'M[R]_n) (k:nat),
  \sum_(i < k.+1) ((f i) *m A) = (\sum_(i < k.+1) (f i)) *m A.
Proof.
  intros. induction k as [|k'].
  + rewrite !big_ord_recr //= !big_ord0. rewrite !add0r //=.
  + rewrite big_ord_recr //= IHk'.
    assert (\sum_(i < k'.+2)  f i = \sum_(i < k'.+1) f i + f k'.+1).
    { rewrite big_ord_recr //=. } 
    rewrite H mulmxDl //=.
Qed.

Lemma sum_of_pos {n : nat} (f : 'I_n.+1 -> R) :
  (forall i, (0 <= f i)) ->
  (0 <= \sum_(i < n.+1) f i).
Proof.
  intros. induction n as [|n'].
  + rewrite !big_ord_recr //= !big_ord0 !add0r //=.
  + rewrite big_ord_recr //=.  apply addr_ge0.
    - apply IHn'. intros. apply H.
    - apply H.
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
apply lerD; auto.
apply ler_pM; auto.
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

Lemma maxr_both_le (x y z : R) :
  x <= z -> y <= z -> (maxr x y) <= z.
Proof.
  intros. unfold maxr. destruct (x < y) eqn:E; auto.
Qed.

Lemma ltS_nat (x y : N) :
  (x < y)%N -> (x.+1 < y.+1)%N.
Proof.
  intros. rewrite //=.
Qed.

Lemma bigmaxrP_le (x0 : R) lr (x : R) :
  x0 <= x ->
  (forall i : nat, (i < size lr)%N -> nth x0 lr i <= x) ->
  \big[maxr / head x0 lr]_(i <- lr) i <= x.
Proof.
  intros. revert x H H0. induction lr as [|r0 lr']; intros.
  + rewrite //= big_nil //=.
  + rewrite //= big_cons. apply maxr_both_le.
    { apply (H0 0). rewrite //=. }
    destruct lr' as [|r1 lr'].
    { rewrite //= big_nil //=. apply (H0 0). by []. }
    simpl in *. assert (\big[maxr/r1]_(i <- (r1 :: lr')) i <= x).
    { apply IHlr'; auto. intros. specialize (H0 i.+1).
      apply H0. rewrite //=. }
    rewrite big_cons. rewrite big_cons in H1.
Abort.

Lemma zero_vec_entry {n : nat} :
  forall (i : 'I_n.+1), (0 : 'cV[R]_n.+1) i 0 = 0.
Proof.
  intros. rewrite /GRing.zero //= mxE //=.
Qed.

Lemma seq_const_nseq {A : Type} {B : Type} {n : nat} (a : A) (l : seq B) :
  size l = n.+1 ->
  [seq a | _ <- l] = nseq n.+1 a.
Proof.
  revert n. induction l as [|h t]; intros.
  + rewrite //=.
  + rewrite //= in H. inversion H.
    destruct t as [|h' t'].
    - rewrite //=.
    - pose proof (IHt (length t')).
      rewrite //=. rewrite //= in H0. f_equal. apply H0. auto.
Qed.

Lemma enum_inord {n : nat} (i : nat) :
  (i < n.+1)%N -> (enum 'I_n.+1)`_i = inord i.
Proof.
  intros.
  pose proof (@nth_ord_enum n.+1 GRing.zero (inord i)). 
  rewrite -H0 //=. 
  rewrite inordK; auto.
Qed.

Lemma bigmax_const_seq (m n : nat) (a : R) :
  (0 < a)%Re ->
  \big[maxr/0%Re]_(i <- [seq a | _ <- iota m n.+1]) i = a.
Proof.
  intros. revert m. induction n as [|n'].
  + rewrite //= big_cons big_nil.
    intros. rewrite /maxr. destruct (a < 0%Re) eqn:E.
    - move /RltP in E. nra.
    - reflexivity.
  + intros. rewrite //= !big_cons //=.
    rewrite //= in IHn'. specialize (IHn' m.+1).
    rewrite big_cons in IHn'. rewrite IHn'. 
    rewrite /maxr. destruct (a < a) eqn:E.
    { move /RltP in E. nra. } reflexivity.
Qed.


(* Lemma sum_abs {n : nat} (f : 'I_n.+1 -> R) :
  Rabs (\sum_i f i) <= \sum_i Rabs (f i).
Proof.
  revert n f. induction n as [|n']; intros.
  + rewrite !big_ord_recr //= !big_ord0 -RplusE.
    apply /RleP. apply Rle_trans with (Rabs 0 + Rabs (f ord_max)).
    { apply Rabs_triang. }
    rewrite -!RplusE. apply Rplus_le_compat_r. rewrite Rabs_R0. apply Rle_refl.
  + rewrite big_ord_recr //=. 
    assert (\sum_(i < n'.+2)  Rabs (f i) = \sum_(i < n'.+1)  Rabs (f (widen_ord (leqnSn n'.+1) i)) + Rabs (f ord_max)).
    { rewrite big_ord_recr //=. }
    rewrite {}H.
    apply /RleP. rewrite -!RplusE.
    eapply Rle_trans. { apply Rabs_triang. }

    apply Rplus_le_compat_r. 
    remember (fun i => (f (widen_ord (leqnSn n'.+1) i))) as g.
    specialize (IHn' g). *)

