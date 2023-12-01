Require Import vcfloat.FPStdLib.
Require Import List.
Import ListNotations.

Require Import common op_defs list_lemmas.

Section NAN.

(* vanilla dot-product *)
Definition dotprod {NAN: Nans} (t: type) (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BPLUS (BMULT (fst x12) (snd x12)) s) 
                (List.combine v1 v2) neg_zero.

Inductive dot_prod_rel {NAN: Nans} {t : type} : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| dot_prod_rel_nil  : dot_prod_rel  nil (neg_zero )
| dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    dot_prod_rel  l s ->
    dot_prod_rel  (xy::l) (BPLUS (BMULT (fst xy) (snd xy)) s).

Lemma fdot_prod_rel_fold_right {NAN: Nans} t :
forall (v1 v2: list (ftype t)), 
    dot_prod_rel (rev (List.combine v1 v2)) (dotprod t v1 v2).
Proof.
intros v1 v2. 
 unfold dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ simpl; auto. apply dot_prod_rel_nil. }
simpl. apply dot_prod_rel_cons. auto.
Qed.


(* FMA dot-product *)
Definition fma_dotprod {NAN: Nans} (t: type) (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2) (Zconst t 0).

Inductive fma_dot_prod_rel {NAN: Nans} {t : type} : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| fma_dot_prod_rel_nil  : fma_dot_prod_rel nil (Zconst t 0)
| fma_dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    fma_dot_prod_rel  l s ->
    fma_dot_prod_rel  (xy::l) (BFMA (fst xy) (snd xy) s).


Lemma fma_dot_prod_rel_fold_right {NAN: Nans} t :
forall (v1 v2: list (ftype t)), 
    fma_dot_prod_rel (rev (List.combine v1 v2)) (fma_dotprod t v1 v2).
Proof.
intros v1 v2. 
 unfold fma_dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ simpl; auto. apply fma_dot_prod_rel_nil. }
simpl. apply fma_dot_prod_rel_cons. auto.
Qed.


End NAN.

(* real model *)

Require Import Reals.
Open Scope R.

Inductive R_dot_prod_rel : 
            list (R * R) -> R -> Prop :=
| R_dot_prod_rel_nil  : R_dot_prod_rel  nil 0%R
| R_dot_prod_rel_cons : forall l xy s,
    R_dot_prod_rel  l s ->
    R_dot_prod_rel  (xy::l)  (fst xy * snd xy + s).

Definition sum_fold: list R -> R := fold_right Rplus 0%R.

Lemma sum_rev l:
sum_fold l = sum_fold (rev l).
Proof.
unfold sum_fold. 
rewrite fold_left_rev_right.
replace (fun x y : R => y + x) with Rplus
 by (do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra).
induction l; simpl; auto.
rewrite IHl.
rewrite <- fold_left_Rplus_0; f_equal; nra.
Qed.

Definition FR2 {t: type} (x12: ftype t * ftype t) := (FT2R (fst x12), FT2R (snd x12)).

Lemma FT2R_FR2 t : 
  (forall a a0 : ftype t, (FT2R a, FT2R a0) = FR2 (a, a0)) .
Proof. intros. unfold FR2; simpl; auto. Qed.

Lemma R_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map FR2 (List.combine v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (List.combine v1 v2))) (sum_fold prods).
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- !map_rev.
induction (map FR2 (rev (combine v1 v2))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. apply R_dot_prod_rel_cons; auto.
Qed.

Definition Rabsp p : R * R := (Rabs (fst p), Rabs (snd p)).

Lemma R_dot_prod_rel_fold_right_Rabs t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map Rabsp (map FR2 (List.combine v1 v2))) in
    R_dot_prod_rel (rev (map Rabsp (map FR2 (List.combine v1 v2)))) (sum_fold prods).
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- !map_rev.
induction (map Rabsp (map FR2 (rev (combine v1 v2)))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. apply R_dot_prod_rel_cons; auto.
Qed.


Lemma R_dot_prod_rel_single rs a:
R_dot_prod_rel [a] rs -> rs = (fst a * snd a).
Proof.
intros.
inversion H.
inversion H3; subst; nra.
Qed.

Lemma R_dot_prod_rel_single' a:
R_dot_prod_rel [a] (fst a * snd a).
Proof.
replace (fst a * snd a) with (fst a * snd a + 0) by nra.
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil.
Qed.

Lemma R_dot_prod_rel_Rabs_eq :
forall l s,
R_dot_prod_rel (map Rabsp l) s -> Rabs s = s.
Proof.
induction  l.
{ intros.
inversion H.
rewrite Rabs_R0.
nra. }
intros.
inversion H; subst; clear H.
unfold Rabsp. destruct a; simpl.
replace (Rabs(Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- IHl; try apply Rabs_pos; auto.
Qed.


Lemma dot_prod_sum_rel_R_Rabs :
forall l s1 s2,
R_dot_prod_rel l s1 -> R_dot_prod_rel (map Rabsp l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
{ intros.
inversion H.
inversion H0.
nra. }
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold Rabsp; destruct a; simpl.
eapply Rle_trans; [
apply Rabs_triang |].
replace (Rabs (Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0).
eapply Rplus_le_compat; try nra.
rewrite Rabs_mult; nra.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
apply Rabs_pos.
Qed.

Lemma dot_prod_combine_map_Rmult a u v r:
length u = length v ->
R_dot_prod_rel (combine u v) r -> 
R_dot_prod_rel (combine (map (Rmult a) u) v) (a * r). 
Proof. revert u r. induction v.
{ intros. rewrite !combine_nil in *.  
  inversion H0; subst; rewrite Rmult_0_r; apply R_dot_prod_rel_nil. }
destruct u.
  { intros; pose proof Nat.neq_0_succ (length v); try contradiction. }
  intros.   inversion H0. assert (Hlen: length u = length v) by (simpl in H; lia).
  specialize (IHv u s Hlen H4).
  simpl. replace (a * (r * a0 + s)) with 
    (a * r * a0 + a * s) by nra. apply R_dot_prod_rel_cons; auto.
Qed.


Lemma dotprod_rel_R_exists {NAN: Nans}:
  forall (t : type) (l : list (ftype t * ftype t)) (fp : ftype t)
  (Hfp : dot_prod_rel l fp),
  exists rp, R_dot_prod_rel (map FR2 l) rp.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply R_dot_prod_rel_nil. }
intros. inversion Hfp; subst. 
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (FT2R (fst a) * FT2R (snd a) + rs); simpl. 
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma dotprod_rel_R_exists_fma {NAN: Nans}:
  forall (t : type) (l : list (ftype t * ftype t)) (fp : ftype t)
  (Hfp : fma_dot_prod_rel l fp),
  exists rp, R_dot_prod_rel (map FR2 l) rp.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply R_dot_prod_rel_nil. }
intros. inversion Hfp; subst. 
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (FT2R (fst a) * FT2R (snd a) + rs); simpl. 
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma sum_rel_R_abs_exists_fma {NAN: Nans}:
  forall (t : type) (l : list (ftype t * ftype t)) (fp : ftype t)
  (Hfp : fma_dot_prod_rel l fp),
  exists rp, R_dot_prod_rel (map Rabsp (map FR2 l)) rp.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply R_dot_prod_rel_nil. }
intros. inversion Hfp; subst. 
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (Rabs (FT2R (fst a)) * Rabs (FT2R (snd a)) + rs); simpl. 
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma dotprodR_rel_bound'  :
  forall (t : type) (l : list (ftype t * ftype t)) (rp a: R)
  (Ha : 0 <= a)
  (Hrp : R_dot_prod_rel (map FR2 l) rp)
  (Hin : forall x, In x l -> Rabs (FT2R (fst x)) <= sqrt a /\ Rabs (FT2R (snd x)) <= sqrt a),
  Rabs rp <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrp; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrp; subst. 
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat | ].
  rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos.
  apply Hin; simpl; auto.
  apply Hin; simpl; auto.
  apply IHl; auto; [ apply Ha| intros; apply Hin; simpl; auto].
  rewrite sqrt_def; auto. apply Req_le;
  replace (length (a::l)) with ( S(length l)) by auto. 
  rewrite S_INR; nra.
Qed.

Lemma dotprodR_rel_bound''  :
  forall (t : type) (l : list (ftype t * ftype t)) (rs_abs a: R)
  (Ha : 0 <= a)
  (Hrp : R_dot_prod_rel (map Rabsp (map FR2 l)) rs_abs)
  (Hin : forall x, In x l -> Rabs (FT2R (fst x)) <= sqrt a /\ Rabs (FT2R (snd x)) <= sqrt a),
  rs_abs <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrp; subst; simpl; nra. }
  inversion Hrp; subst. 
  eapply Rle_trans; [ apply Rplus_le_compat | ].
  apply Rmult_le_compat; 
  [ destruct a; simpl; apply Rabs_pos | destruct a; simpl; apply Rabs_pos | | ].
  apply Hin; simpl; auto.
  apply Hin; simpl; auto.
  apply IHl; auto; [ apply Ha| intros; apply Hin; simpl; auto].
  rewrite sqrt_def; auto. apply Req_le;
  replace (length (a::l)) with ( S(length l)) by auto. 
  rewrite S_INR; nra.
Qed.

Close Scope R.

