From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg all_algebra seq matrix.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 

Require Import floatlib.


Section WITHNANS.
Context {NANS: Nans}. 

Definition sum ty `{STD: is_standard ty} (a b : ftype ty) : ftype ty := BPLUS a b.

Definition list_to_vec_float {ty}  `{STD: is_standard ty}{n:nat} 
(l : list (ftype ty)): 'cV[ftype ty]_n := 
\col_(i < n) (List.nth (nat_of_ord i) l (Zconst ty 0)).


(** Define matrix_addition **)
Definition addmx_float {ty}  `{STD: is_standard ty}{m n:nat} (A B: 'M[ftype ty]_(m,n))
  : 'M[ftype ty]_(m,n) :=
  \matrix_(i, j) (sum ty (A i j) (B i j)).


Fixpoint vec_to_list_float {ty} {n:nat} (m:nat) (v :'cV[ftype ty]_n.+1)
   : list (ftype ty) := 
   match m with 
   | O => []
   | S p => [v (@inord n p) ord0] ++ vec_to_list_float p v
   end.


Definition vec_to_list_float_1 {ty} {n:nat} (m:nat) (v :'cV[ftype ty]_n.+1) := 
  rev (vec_to_list_float m v). 

Lemma nth_vec_to_list_float {ty} {n:nat} i m (v :'cV[ftype ty]_n.+1) d:
  (i < m)%nat ->
  nth (m.-1 -i) (@vec_to_list_float _ n m v) d = v (@inord n i) ord0.
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
  - assert (nth (m.-1 - i) (vec_to_list_float m v)
                d = v (inord i) ord0).
    { by apply IHm. } 
    rewrite -H1. rewrite -[in RHS]predn_sub.
    rewrite -subn_gt0 in H0. rewrite -predn_sub in H1.
    by destruct (m - i)%nat.
Qed.




Definition dotprod_r {t: type} `{STD: is_standard t} (v1 v2: list (ftype t)) : ftype t :=
  fold_right (fun x12 s => BFMA (fst x12) (snd x12) s) 
                 (Zconst t 0) (List.combine v1 v2)  .

Lemma combine_rev {ty}:
forall (v1 v2: vector ty),
  length v1 = length v2 ->
  (combine (rev v1) (rev v2)) = rev (combine v1 v2).
Proof.
intros.
elim: v1 v2 H => [ |s v1 IHv1] v2 H.
+ simpl;auto.
+ destruct v2.
  - by simpl in H.
  - specialize (IHv1 v2).
    assert (length v1 = length v2).
    { simpl in H. lia. } specialize (IHv1 H0).
    simpl. rewrite -IHv1.
    assert (length (rev v1) = length (rev v2)).
    { by rewrite !rev_length. }
    clear IHv1 H H0.
    elim: (rev v1) (rev v2) H1  => [ |a1 v3 IHv3] v4 H.
    * destruct v4.
      ++ simpl;auto.
      ++ by simpl in H.
    * destruct v4.
      ++ by simpl in H.
      ++ simpl. rewrite IHv3; try by [].
         simpl in H. lia.
Qed.


Lemma dotprod_rev_equiv {ty} `{STD: is_standard ty} (v1 v2: vector ty):
  length v1 = length v2 ->
  dotprod (rev v1) (rev v2) = dotprod_r v1 v2.
Proof.
intros.         
unfold dotprod, dotprod_r.
assert (combine (rev v1) (rev v2) = rev (combine v1 v2)).
{ by rewrite combine_rev. } rewrite H0.
rewrite <-fold_left_rev_right.
rewrite rev_involutive. reflexivity.
Qed.

(** The issue is that b could appear more than once in the list. 
    So the current version of lemma is not correct 
***)
(*
Lemma fold_right_except_zero {A B} 
  (f: B -> A -> A) (a : A) (L: list B) (b :  B) :
  In b L ->
  (forall s d, In s L -> s <> b -> f s d = d) ->
  fold_right f a L = f b a.
Admitted.
*)

Definition mulmx_float {ty} `{STD: is_standard ty} {m n p : nat} 
  (A: 'M[ftype ty]_(m.+1,n.+1)) (B: 'M[ftype ty]_(n.+1,p.+1)) : 
  'M[ftype ty]_(m.+1,p.+1):=
  \matrix_(i, k)
    let l1 := vec_to_list_float n.+1 (\row_(j < n.+1) A i j)^T in
    let l2 := vec_to_list_float n.+1 (\col_(j < n.+1) B j k) in
    @dotprod_r ty _ l1 l2.

Definition opp_mat {ty} `{STD: is_standard ty} {m n: nat} (A : 'M[ftype ty]_(m.+1, n.+1)) 
  : 'M[ftype ty]_(m.+1, n.+1) :=
  \matrix_(i,j) (BOPP (A i j)). 


Definition sub_mat {ty} `{STD: is_standard ty} {m n: nat} (A B : 'M[ftype ty]_(m.+1, n.+1)) 
  : 'M[ftype ty]_(m.+1, n.+1) :=
  \matrix_(i,j) (BMINUS (A i j) (B i j)). 


Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).


Definition A1_inv_J {ty} `{STD: is_standard ty} {n:nat} (A: 'M[ftype ty]_n.+1) : 'cV[ftype ty]_n.+1 :=
  \col_i (BDIV (Zconst ty 1) (A i i)).

Definition A2_J {ty} `{STD: is_standard ty} {n:nat} (A: 'M[ftype ty]_n.+1): 
  'M[ftype ty]_n.+1 :=
  \matrix_(i,j) 
    if (i==j :> nat) then (Zconst ty 0) else A i j.


Definition diag_vector_mult {ty} `{STD: is_standard ty} {n:nat} (v1 v2: 'cV[ftype ty]_n.+1)
  : 'cV[ftype ty]_n.+1 :=
  \col_i (BMULT (nth (n.+1.-1 -i) (vec_to_list_float n.+1 v1) (Zconst ty 0))
            (nth (n.+1.-1 - i) (vec_to_list_float n.+1 v2) (Zconst ty 0))).

Definition jacobi_iter {ty} `{STD: is_standard ty} {n:nat} x0 b (A: 'M[ftype ty]_n.+1) : 
  'cV[ftype ty]_n.+1 :=
   let r := b -f ((A2_J A) *f x0) in
   diag_vector_mult (A1_inv_J A) r.


Definition X_m_jacobi {ty} `{STD: is_standard ty} {n:nat} m x0 b (A: 'M[ftype ty]_n.+1) :
  'cV[ftype ty]_n.+1 :=
   Nat.iter m  (fun x0 => jacobi_iter x0 b A) x0.


Definition matrix_inj' {t} (A: matrix t) m n  d d': 'M[ftype t]_(m,n):=
    \matrix_(i < m, j < n) 
     nth j (nth i A d) d'.

Definition matrix_inj {t} `{STD: is_standard t} (A: matrix t) m n  : 'M[ftype t]_(m,n):=
  matrix_inj' A m n [::] (Zconst t 0).

Definition vector_inj' {t} `{STD: is_standard t} (v: vector t) n d : 'cV[ftype t]_n :=
   \col_(i < n) nth i v d.

Definition vector_inj {t} `{STD: is_standard t} (v: vector t) n : 'cV[ftype t]_n :=
   vector_inj' v n (Zconst t 0).



Lemma length_veclist {ty} {n m:nat} (v: 'cV[ftype ty]_n.+1):
  length (@vec_to_list_float _ n m v) = m.
Proof.
induction m.
+ simpl. auto.
+ simpl. by rewrite IHm.
Qed.

Definition FT2R_mat {m n: nat} {ty} (A : 'M[ftype ty]_(m.+1, n.+1)) :
   'M[R]_(m.+1, n.+1):=
  \matrix_(i, j) FT2R (A i j).

End WITHNANS.
