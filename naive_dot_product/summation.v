From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


Section WITHNANS.
Context {NANS: Nans}. 

Definition sum {A: Type} (sum_op : A -> A -> A) (a b : A) : A := sum_op a b.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum sum_op a s).

Definition sum_rel_F := @sum_rel (ftype Tsingle) 0%F32 (BPLUS Tsingle).
Definition sum_rel_R := @sum_rel R 0%R Rplus.


Definition _a := 1%positive. (* current element *)
Definition _b := 2%positive. (* accumulator *)

Definition vmap_list ty (a b : ftype ty) := 
   [(_a, existT ftype _ a); (_b, existT ftype _ b)].

Definition vmap {ty} (a b : ftype ty) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap_list ty a b)) in exact z).


Definition bmap_list {ty} : list varinfo := 
  let ov := powerRZ 2 (femax ty) in 
  [ Build_varinfo Tsingle _a (-ov) ov;
    Build_varinfo Tsingle _b (-ov) ov ].

Definition bmap {ty} : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (@bmap_list ty ) ) in exact z).

Definition sum_expr {ty} (a b : ftype ty) := ltac :( let e' :=
  HO_reify_float_expr constr:([_a; _b]) (BPLUS ty) in exact e').


Require Import Interval.Tactic.

Lemma real_lt_1 :
forall a b c,
a <= b -> b < c -> a < c.
Proof. intros; apply Rle_lt_trans with b; auto. Qed.

Lemma bnd_lt_overflow n :
  (2 <= n )%nat ->
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let ov := powerRZ 2 (femax Tsingle) in 
  let bnd := (ov - (INR n - 1) * 2 * e * (1 + d) ^ (n - 2)) /
       ((INR n - 1) * d * (1 + d) ^ (n - 2) + 1)  in
bnd * (1 + d) + e < 0x1p128%xR.
Proof.
intros.
subst bnd.
rewrite <- Rcomplements.Rlt_minus_r.
replace (0x1p128%xR) with ov by (subst ov; simpl; nra).
match goal with |- context [?a / ?b * ?c] =>
replace (a/b  *c) with ((a  *c) / b)
end.
assert (Hn: 1 <= INR n - 1).
assert (Hn2: INR 2 <= INR n); try apply le_INR; auto.
eapply Rle_trans; [  | apply  Rplus_le_compat; [ apply Hn2| apply Rle_refl]]; try simpl; nra.
assert (Hd: 1 <= (1 + d) ^ (n - 2)).
assert (H1: 1 = (1 + d) ^ 0) by nra. 
eapply Rle_trans; [ rewrite H1  | apply Rle_refl]; apply Rle_pow; 
  subst d; simpl; try nra; try lia.
apply Rdiv_lt_left.
eapply Rlt_le_trans; [ idtac | apply  Rplus_le_compat; 
    [apply  Rmult_le_compat ; [| | apply Rmult_le_compat |]| apply Rle_refl]]; 
   try apply Hn; try apply Hd; try nra; try rewrite Rmult_1_l; try rewrite Rmult_0_l;
   try apply Rle_refl; try subst d; try simpl; nra.
set (A:= (INR n - 1) * (1 + d) ^ (n - 2)).
assert (HA: 1 <= A).
subst A.
eapply Rle_trans; [ idtac | apply  Rmult_le_compat];
   try apply Hn; try apply Hd; try nra.
replace ((INR n - 1) * d * (1 + d) ^ (n - 2)) with (A * d) by (subst A; nra).
replace ((INR n - 1) * 2 * e * (1 + d) ^ (n - 2)) with (A * 2 * e) by (subst A; nra).
replace ((ov - A * 2 * e) * (1 + d)) with (ov + (- 2 * A * e * d + ov * d - 2 * A * e )) by nra.
replace ((ov - e) * (A * d + 1)) with (ov + (- A * e * d + ov * A * d - e )) by nra.
apply Rplus_lt_compat_l.
apply Rplus_lt_compat.
apply Rplus_lt_le_compat.
assert (lem: forall a b c, 
  0 < c -> a < b -> a * c < b * c) by (intros;nra).
repeat apply lem; try subst d; try simpl; try nra;
  try subst e; try simpl; try nra;
  try subst A; try simpl;  
  try apply Hneg.
rewrite Rmult_assoc.
eapply Rle_trans; [ | apply Rmult_le_compat_l; [ subst ov; simpl; nra| 
  apply Rmult_le_compat_r; [ subst d; simpl; nra | apply HA ]]]; nra.
apply Ropp_lt_contravar.
rewrite Rmult_comm.
eapply Rle_lt_trans with (e * 1); try nra.
apply Rmult_lt_compat_l; try subst e; simpl; try nra.
nra.
Qed.


Lemma prove_rndoff' :
  forall (a b : ftype Tsingle) vmap n,
  (2 <= n )%nat ->
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let ov := powerRZ 2 (femax Tsingle) in 
  let bnd := (ov - (INR n - 1) * 2 * e * (1 + d) ^ (n - 2)) /
       ((INR n - 1) * d * (1 + d) ^ (n - 2) + 1)  in
  - (bnd * (INR n - 1) / INR n) <= FT2R b <= bnd * (INR n - 1) / INR n -> 
  - (bnd * / INR n) <= FT2R a <= bnd * / INR n -> 
  prove_roundoff_bound (@bmap Tsingle) (vmap a b) (@sum_expr Tsingle a b) 
     (Rabs ( FT2R a + FT2R b) * d + e).
Proof.
intros ? ?  ?  ? ? ? ? ? ? ?bnd1 ?bnd2.
prove_roundoff_bound.
- 
prove_rndval.
clear BOUND BOUND0.
(* prove_rndval SHOULD SUBST V_A  & V_B ABOVE THE LINE *)
assert (Ha : FT2R v_a = FT2R a) by admit.
assert (Hb : FT2R v_b = FT2R b) by admit.
rewrite Ha, Hb; clear Ha Hb.
simpl in e; simpl in d.
assert (Rabs (1 + u0) <= 1 + d) as Hu2. 
{ subst e; eapply Rle_trans;
 [apply Rabs_triang | eapply Rplus_le_compat;
                                      [ rewrite Rabs_R1; apply Rle_refl | apply H1 ]]. }
apply Rlt_Rminus.
rewrite Rmult_1_l. 
try apply Rabs_le in bnd1, bnd2.
eapply real_lt_1; [eapply Rabs_triang | 
    rewrite Rabs_mult; eapply real_lt_1; [ eapply Rplus_le_compat; 
          [eapply Rmult_le_compat; try apply Rabs_pos; 
                      [eapply Rle_trans; [apply Rabs_triang | eapply Rplus_le_compat; 
                                      [apply bnd2| apply bnd1]] 
                          | eapply Rle_trans; [ apply Hu2 | apply Rle_refl] ] | apply H0 ] | ]].
replace (bnd * / INR n + bnd * (INR n - 1) / INR n) with bnd.
apply Rle_lt_trans with (bnd * (1+d) + e). 
  apply Rplus_le_compat; [apply Rle_refl| subst e; simpl; nra].
apply bnd_lt_overflow; auto.
field.
apply not_0_INR; try lia.
-
prove_roundoff_bound2.
clear BOUND BOUND0.
(* prove_roundoff_bound2 SHOULD SUBST V_A  & V_B IN
  RHS *)
assert (Ha : v_a = a) by admit.
assert (Hb : v_b = b) by admit.
rewrite Ha, Hb; clear Ha Hb.
try apply Rabs_le in bnd1, bnd2.
match goal with |- context[Rabs ?a <= _] =>
field_simplify a
end.
assert (He0: Rabs e1 <= e).
{ eapply Rle_trans. apply E. subst e; simpl; nra. }
assert (Hd: Rabs d0 <= d).
{ eapply Rle_trans. apply E0. subst d; simpl; nra. }
replace (a * d0 + b * d0 + e1) with ((a + b) * d0 + e1) by nra.
eapply Rle_trans; [
apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat; [rewrite Rabs_mult; eapply Rle_trans;
  [apply Rmult_le_compat; 
      [ apply Rabs_pos | apply Rabs_pos |   apply Rle_refl | apply Hd ] | 
  apply Rle_refl ]  | apply He0 ] | ]  ].
nra.
Admitted.

End WITHNANS.

Lemma reflect_reify_sumF : 
  forall a b,
  fval (env_ (vmap a b)) (@sum_expr Tsingle a b) = sum Tsingle a b .
Proof. reflexivity. Qed.

Lemma reflect_reify_sumR : 
  forall a b,
  rval (env_ (vmap a b)) (@sum_expr Tsingle a b) = FT2R a + FT2R b .
Proof. reflexivity. Qed.


Lemma prove_rndoff:
  forall (a b : ftype Tsingle) (n : nat),
  let ty:= Tsingle in let nr := INR n in 
( 1 <= n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
boundsmap_denote (@bmap Tsingle n) (vmap a b)  ->
   Rabs (FT2R (sum Tsingle a b) - (FT2R a + FT2R b)) <= 
     ( Rabs ( FT2R a + FT2R b ) * u0 + u) .
Proof.
intros ? ? ? ? ? Hn ? ? HBMD.
pose proof prove_rndoff' a b  vmap  n Hn HBMD.
unfold roundoff_error_bound in H.
rewrite <- reflect_reify_sumR.
rewrite <- reflect_reify_sumF.
destruct H as (H1 & H2); eapply Rle_trans; [apply H2| subst u0 u; nra].
Qed.

Definition Flist_to_Rlist {ty} (L : list ( ftype ty)) :=
  map (fun a => (FT2R a)) L.


Definition Flist_to_Rlist_abs {ty} (L : list ( ftype ty)) :=
  map (fun a => Rabs (FT2R a)) L.

Lemma Rabs_list_rel {ty} (L : list ( ftype ty)):
  Rabs (sum_fixR (Flist_to_Rlist L)) <= sum_fixR (Flist_to_Rlist_abs L).
Proof.
induction L.
+ simpl. rewrite Rabs_R0. nra.
+ simpl.
  apply Rle_trans with 
  (Rabs (FT2R a) + Rabs (sum_fixR (Flist_to_Rlist L))).
  apply Rabs_triang.
  apply Rplus_le_compat; nra.
Qed.


Definition default_val : ftype Tsingle := 0%F32. 

Lemma sum_lt_overflow : 
  forall (L1 : list (ftype Tsingle)),
FT2R (hd default_val L1) <= (@strict_overflow_bnd Tsingle ) / INR (length L1) ->
FT2R  (sum_fixF Tsingle (tl L1)) <= (@strict_overflow_bnd Tsingle ) * INR (length L1 - 1) / INR (length L1) ->
FT2R (sum_fixF Tsingle L1) <= (@strict_overflow_bnd Tsingle ).
Proof.
destruct L1.
-simpl.
intros.
unfold strict_overflow_bnd.
simpl; nra.
-
intros.
simpl.
set (b:= (sum_fixF Tsingle L1)) in *.
pose proof prove_rndoff f b (length (f::L1)).
Admitted.



Lemma prove_rndoff_n_sum_aux :
  forall (L1 : list (ftype Tsingle)) ,
  let n:= length L1 in 
  (1 <= n )%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (forall a, In a L1 -> Rabs (FT2R a) <= (@strict_overflow_bnd Tsingle ) / INR (length L1))->
  Rabs (FT2R (sum_fixF Tsingle L1) - sum_fixR (Flist_to_Rlist L1)) <= 
      (sum_fixR (Flist_to_Rlist_abs L1)) * ((1 + u0)^n - 1) + 
      u * ((1 + u0)^n - 1) / u0.
Proof.
intros.
induction L1.
+ simpl. rewrite Rminus_0_r. rewrite Rabs_R0. 
  assert ((1 - 1) = 0). { nra. } rewrite H1. nra.
+ simpl in IHL1.
  remember (length L1) as m.
  assert (n = (m+1)%nat). { unfold n. simpl. rewrite Heqm. lia. }
  assert (L1 = [:: ] \/ L1 <> [::]).
  { destruct L1.
    + by left.
    + by right. 
  } destruct H2.
  - rewrite H2. simpl. rewrite !Rplus_0_r. 
    assert (length L1 = 0%nat).
    { rewrite H2 //=. } rewrite H3 //=. 
    pose proof (prove_rndoff a 0%F32 2%nat).
    simpl in H4. 
    assert ((1 <= 2)%nat). { lia. } specialize (H4 H5).
    assert (boundsmap_denote (@bmap Tsingle 2) (vmap a 0%F32)).
    { admit. } specialize (H4 H6).
    rewrite Rplus_0_r in H4.
    apply Rle_trans with 
    (Rabs (FT2R a) * (/ 2 * / IZR (Z.pow_pos 2 23)) +
     / 2 * / IZR (Z.pow_pos 2 149)).
    * apply H4.
    * apply Rplus_le_compat.
      ++ apply Rmult_le_compat_l.
         -- apply Rabs_pos.
         -- unfold u0. simpl. nra.
      ++ unfold u, u0. simpl. nra.
  - simpl.
    assert ((1 <= m)%nat).
    { rewrite Heqm. destruct L1.
      + by contradict H2.
      + simpl. lia.
    } specialize (IHL1 H3). 
    assert (forall a : ftype Tsingle,
              In a L1 ->
              Rabs (FT2R a) <= @strict_overflow_bnd Tsingle / INR m).
    { intros. specialize (H0 a0).
      assert (In a0 (a :: L1)).
      { simpl. by right. } apply H0 in H5.
      apply Rle_trans with 
      (@strict_overflow_bnd Tsingle / INR (length (a :: L1))).
      + apply H5.
      + apply Rmult_le_compat_l. 
        - apply overflow_pos.
        - simpl. destruct (length L1).
          * rewrite Heqm in H3. contradict H3. lia.
          * apply Rlt_le. apply Rinv_1_lt_contravar.
            ++ assert (1 = INR 1). { reflexivity. } rewrite H6.
               apply le_INR. lia.
            ++ rewrite Heqm. nra.
    } specialize (IHL1 H4).
    rewrite -Heqm. 
    apply Rle_trans with
       (Rabs(FT2R (sum Tsingle a (sum_fixF Tsingle L1)) -
                (FT2R a + FT2R (sum_fixF Tsingle L1))) + 
        Rabs ((FT2R a + FT2R (sum_fixF Tsingle L1)) -
               (FT2R a + sum_fixR (Flist_to_Rlist L1)))).
    -- assert ((FT2R (sum Tsingle a (sum_fixF Tsingle L1)) -
                    (FT2R a + sum_fixR (Flist_to_Rlist L1))) = 
                  (FT2R (sum Tsingle a (sum_fixF Tsingle L1)) - 
                    (FT2R a + FT2R (sum_fixF Tsingle L1))) + 
                  ((FT2R a + FT2R (sum_fixF Tsingle L1)) - 
                   (FT2R a + sum_fixR (Flist_to_Rlist L1)))).
       { nra. } rewrite H5. apply Rabs_triang.
    -- pose proof (prove_rndoff a (sum_fixF Tsingle L1) n).
       specialize (H5 H). simpl in H5.
       assert (boundsmap_denote (@bmap Tsingle n)
                      (vmap a (sum_fixF Tsingle L1))).
       { admit. } specialize (H5 H6).
       apply Rle_trans with 
       ( (Rabs (FT2R a + FT2R (sum_fixF Tsingle L1)) *
           (/ 2 * / IZR (Z.pow_pos 2 23)) +
           / 2 * / IZR (Z.pow_pos 2 149)) + 
         ( sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
             u * ((1 + u0) ^ m - 1) / u0)).
       ** apply Rplus_le_compat.
          ++ apply H5.
          ++ assert ((FT2R a + FT2R (sum_fixF Tsingle L1) -
                        (FT2R a + sum_fixR (Flist_to_Rlist L1))) = 
                      FT2R (sum_fixF Tsingle L1) - 
                      sum_fixR (Flist_to_Rlist L1)).
             { nra. } rewrite H7. apply IHL1.
       ** apply Rle_trans with 
          ((Rabs (FT2R a) + Rabs (FT2R (sum_fixF Tsingle L1))) *
            (/ 2 * / IZR (Z.pow_pos 2 23)) +
            / 2 * / IZR (Z.pow_pos 2 149) +
            (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
             u * ((1 + u0) ^ m - 1) / u0)).
          ++ repeat apply Rplus_le_compat. apply Rmult_le_compat_r.
             nra. apply Rabs_triang. nra. nra. nra.
          ++ assert (Rabs (FT2R (sum_fixF Tsingle L1)) - 
                     Rabs (sum_fixR (Flist_to_Rlist L1)) <= 
                     sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                      u * ((1 + u0) ^ m - 1) / u0).
             { apply Rle_trans with (Rabs
                             (FT2R (sum_fixF Tsingle L1) -
                              sum_fixR (Flist_to_Rlist L1))).
               apply Rabs_triang_inv. nra.
             } 
             assert (Rabs (FT2R (sum_fixF Tsingle L1)) <=
                          Rabs (sum_fixR (Flist_to_Rlist L1)) + 
                          sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                          u * ((1 + u0) ^ m - 1) / u0).
             { nra. } 
             assert (Rabs (FT2R (sum_fixF Tsingle L1)) <=
                     sum_fixR (Flist_to_Rlist_abs L1) + 
                     sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                      u * ((1 + u0) ^ m - 1) / u0).
             { apply Rle_trans with 
                (Rabs (sum_fixR (Flist_to_Rlist L1)) +
                   sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                   u * ((1 + u0) ^ m - 1) / u0).
               + nra.
               + repeat apply Rplus_le_compat_r. apply Rabs_list_rel.
             } 
             apply Rle_trans with 
             ((Rabs (FT2R a) + 
               (sum_fixR (Flist_to_Rlist_abs L1) +
                     sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                     u * ((1 + u0) ^ m - 1) / u0))*
                (/ 2 * / IZR (Z.pow_pos 2 23)) +
                / 2 * / IZR (Z.pow_pos 2 149) +
                (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                 u * ((1 + u0) ^ m - 1) / u0)).
              --- repeat apply Rplus_le_compat_r. apply Rmult_le_compat_r; nra.
              --- assert ((Rabs (FT2R a) +
                           (sum_fixR (Flist_to_Rlist_abs L1) +
                            sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                            u * ((1 + u0) ^ m - 1) / u0)) *
                          (/ 2 * / IZR (Z.pow_pos 2 23)) +
                          / 2 * / IZR (Z.pow_pos 2 149) +
                          (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) ^ m - 1) +
                           u * ((1 + u0) ^ m - 1) / u0) = 
                          (Rabs (FT2R a) * (/ 2 * / IZR (Z.pow_pos 2 23))) +
                          (sum_fixR (Flist_to_Rlist_abs L1) *
                            ((/ 2 * / IZR (Z.pow_pos 2 23)) + 
                              (/ 2 * / IZR (Z.pow_pos 2 23)) * ((1 + u0) ^ m - 1)+
                              ((1 + u0) ^ m - 1)) +
                           (((/ 2 * / IZR (Z.pow_pos 2 149)) +  u * ((1 + u0) ^ m - 1) / u0) +
                             (/ 2 * / IZR (Z.pow_pos 2 23)) * (u * ((1 + u0) ^ m - 1) / u0)))).
                  { nra. } rewrite H10. clear H10.
                  assert ((Rabs (FT2R a) + sum_fixR (Flist_to_Rlist_abs L1)) *
                            ((1 + u0) * (1 + u0) ^ m - 1) +
                            u * ((1 + u0) * (1 + u0) ^ m - 1) / u0 = 
                          (Rabs (FT2R a) * ((1 + u0) * (1 + u0) ^ m - 1)) +
                          (sum_fixR (Flist_to_Rlist_abs L1) * ((1 + u0) * (1 + u0) ^ m - 1) +
                           u * ((1 + u0) * (1 + u0) ^ m - 1) / u0)).
                  { nra. } rewrite H10. clear H10.
                  repeat apply Rplus_le_compat.
                  *** apply Rmult_le_compat_l.
                      apply Rabs_pos.
                      simpl in u, u0. rewrite -/u -/u0.  
                      apply u_bound. unfold u0. nra.
                  *** apply Rmult_le_compat_l.
                      ---- apply sum_abs_ge_0.
                      ---- simpl in u, u0. rewrite /u /u0.  nra. 
                  *** simpl in u, u0. rewrite /u /u0. nra.
Admitted. 


Lemma pow_rel:
  forall (x:R) (n:nat),
  (1 + x) ^ n - 1 <= INR n * x / (1 - x).
Admitted.


Lemma prove_rndoff_n_sum :
  forall (L1 : list (ftype Tsingle)) ,
  let n:= length L1 in 
  (1 <= n )%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  (forall a, In a L1 -> Rabs (FT2R a) <= (@strict_overflow_bnd Tsingle ) / INR (length L1))->
  Rabs (FT2R (sum_fixF Tsingle L1) - sum_fixR (Flist_to_Rlist L1)) <= 
      (INR n * u0 / (1 - u0)) * ((sum_fixR (Flist_to_Rlist_abs L1))) + 
      (INR n * u / (1 - u0)).
Proof.
intros.
apply Rle_trans with
((sum_fixR (Flist_to_Rlist_abs L1)) * ((1 + u0)^n - 1) + 
      u * ((1 + u0)^n - 1) / u0).
+ apply prove_rndoff_n_sum_aux. by rewrite -/n. apply H0.
+ apply Rplus_le_compat.
  - rewrite Rmult_comm. apply Rmult_le_compat_r.
    apply sum_abs_ge_0. apply pow_rel.
  - assert (u * ((1 + u0) ^ n - 1) / u0 = 
            ((1 + u0) ^ n - 1) * (u / u0)).
    { nra. } rewrite H1.
    assert (INR n * u / (1 - u0)  =
            (INR n * u0 / (1 - u0)) * (u / u0)).
    { rewrite /u /u0. simpl. nra. } rewrite H2.
    apply Rmult_le_compat_r.
    * rewrite /u /u0. simpl. nra.
    * apply pow_rel.
Qed.




Lemma x_pow: forall (x:R) (n:nat),
  0 <= x ->
  0 <= x^n.
Proof.
intros. 
induction n.
+ simpl. nra.
+ simpl. apply Rmult_le_pos; nra.
Qed.


Lemma x_pow_minus_1: forall (x:R) (n:nat),
  1 <= x ->
  0 <= x^n - 1.
Proof.
intros. 
induction n.
+ simpl. nra.
+ simpl.
  assert (x * x ^ n - 1 = x * (x^n - 1) + (x - 1)).
  { nra. } rewrite H0.
  apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos. nra. nra.
  - nra.
Qed.

Definition Flist_to_Rlist_pair {ty} (L : list ( (ftype ty) * (ftype ty))) :=
  map (fun a => (FT2R (fst a), FT2R (snd a))) L.

Definition Flist_to_Rlist_pair_abs {ty} (L : list ( (ftype ty) * (ftype ty))) :=
  map (fun a => (Rabs (FT2R (fst a)), Rabs (FT2R (snd a)))) L.



Lemma x_bound_S:
  forall (x:R) (m:nat),
  0 < x -> 
  x * x + 2 * x <= (1 + x) * (1 + x) ^ (m + 1) - 1.
Proof.
intros.
induction m.
+ simpl. nra.
+ apply Rle_trans with ((1 + x) * (1 + x) ^ (m + 1) - 1).
  - apply IHm.
  - apply Rplus_le_compat_r.
    assert ((1 + x) * (1 + x) ^ (m + 1) = 
             1* ((1 + x) * (1 + x) ^ (m + 1))).
    { nra. } rewrite H0.
    assert ((1 + x) * (1 + x) ^ (S m + 1) = 
             (1+x) * ((1 + x) * (1 + x) ^ (m + 1))).
    { simpl. nra. } rewrite H1. apply Rmult_le_compat_r.
    nra. nra.
Qed.

Lemma sum_abs_pair_rel:
  forall (L: list ((ftype Tsingle) * (ftype Tsingle))),
  0 <= sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L)).
Proof.
intros.
induction L.
+ simpl. nra.
+ simpl. 
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; apply Rabs_pos.
  apply IHL.
Qed.


Lemma sum_abs_pair_le:
forall (L: list ((ftype Tsingle) * (ftype Tsingle))),
Rabs (dot_prodR (Flist_to_Rlist_pair L)) <=
dot_prodR (Flist_to_Rlist_pair_abs L).
Proof.
intros.
induction L.
+ simpl. unfold dot_prodR. simpl.
  rewrite Rabs_R0. nra.
+ simpl. unfold dot_prodR. simpl. 
  apply Rle_trans with
  (Rabs (FT2R (fst a) * FT2R (snd a)) + 
   Rabs (dot_prodR (Flist_to_Rlist_pair L))).
  - apply Rabs_triang.
  - apply Rplus_le_compat. rewrite Rabs_mult. nra.
    apply IHL.
Qed.

Lemma forward_error_dot_aux:
  forall (L: list ((ftype Tsingle) * (ftype Tsingle))),
  let ty := Tsingle in 
  let n:= length L in 
  let nr := INR n in
  (1 <= n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  Rabs (FT2R (dot_prodF _ L) - dot_prodR (Flist_to_Rlist_pair L)) <=
  (dot_prodR (Flist_to_Rlist_pair_abs L)) * ((1 + u0)^(n+1) -1) + 
  nr * u * (1+u0)^n + u * ((1+u0)^n -1) / u0.
Proof.
intros.
induction L.
+ simpl. unfold dot_prodR. simpl.
  rewrite Rminus_0_r. 
  assert ((1 - 1) = 0). { nra. } rewrite H0.
  rewrite !Rmult_0_r. rewrite Rabs_R0. 
  assert (0 * ((1 + u0) * 1 - 1) + nr * u * 1 + 0 / u0 = 
          nr * u).
  { nra. } rewrite H1.
  apply Rmult_le_pos. 
  - unfold nr. apply pos_INR. 
  - unfold u. simpl. nra.
+ unfold dot_prodF, dot_prodR. simpl. 
  remember (length L) as m.
  assert (n = (m+1)%nat). { unfold n. simpl. rewrite Heqm. lia. }
  assert (L = [:: ] \/ L <> [::]).
    { destruct L.
      + by left.
      + by right. 
    } destruct H1.
    - rewrite H1. simpl.
      remember (fst a) as b1.
      remember (snd a) as b2. rewrite Rplus_0_r.
      assert ( length L = 0%nat).
      { rewrite H1. by simpl. } rewrite H2 in Heqm.
      rewrite Heqm //=.  simpl.
      pose proof (prove_rndoff (prod Tsingle b1 b2)
                  (Binary.B754_zero (fprec Tsingle) 128
                         false)).
      specialize (H3 2%nat). simpl in H3.
      assert ((1 <= 2)%nat). { lia. } 
      assert ( boundsmap_denote (@bmap ty 2%nat)
                  (vmap (prod Tsingle b1 b2) (Binary.B754_zero (fprec Tsingle) 128
                         false))).
      { admit. } specialize (H3 H4 H5).
      apply Rle_trans with 
      (Rabs
       (FT2R
          (sum Tsingle (prod Tsingle b1 b2) (Binary.B754_zero (fprec Tsingle) 128
                         false)) -
        (FT2R (prod Tsingle b1 b2) + 0)) + 
        Rabs ((FT2R (prod Tsingle b1 b2)) - FT2R b1 * FT2R b2)).
      ++ assert ((FT2R
                   (sum Tsingle (prod Tsingle b1 b2)
                      (Binary.B754_zero (fprec Tsingle) 128
                         false)) - FT2R b1 * FT2R b2) = 
                  (FT2R
                      (sum Tsingle (prod Tsingle b1 b2) (Binary.B754_zero (fprec Tsingle) 128
                         false)) -
                    (FT2R (prod Tsingle b1 b2) + 0)) + 
                    (((FT2R (prod Tsingle b1 b2)) - FT2R b1 * FT2R b2))).
         { simpl. nra. } rewrite H6. apply Rabs_triang.
      ++ apply Rle_trans with 
          (Rabs (FT2R (prod Tsingle b1 b2) + 0) *
           (/ 2 * / IZR (Z.pow_pos 2 23)) +
           / 2 * / IZR (Z.pow_pos 2 149) + 
           Rabs (FT2R (prod Tsingle b1 b2) - FT2R b1 * FT2R b2)).
          -- by apply Rplus_le_compat_r.
          -- pose proof (prove_rndoff_prod b1 b2).
             specialize (H6 2%nat).
             assert ((1 < 2)%nat). { lia. } specialize (H6 H7).
             simpl in H6.
             assert (boundsmap_denote (@bmap_prod ty  2) (vmap b1 b2)).
             { admit. } specialize (H6 H8). rewrite Rplus_0_r.
             apply Rle_trans with 
             (Rabs (FT2R (prod Tsingle b1 b2)) *
                (/ 2 * / IZR (Z.pow_pos 2 23)) +
                / 2 * / IZR (Z.pow_pos 2 149) + 
              ( Rabs (FT2R b1 * FT2R b2) *
                 (/ 2 * / IZR (Z.pow_pos 2 23)) +
                 / 2 * / IZR (Z.pow_pos 2 149))).
             ** by apply Rplus_le_compat_l.
             ** assert (Rabs (FT2R (prod Tsingle b1 b2)) - 
                        Rabs (FT2R b1 * FT2R b2) <= 
                        Rabs (FT2R b1 * FT2R b2) *
                         (/ 2 * / IZR (Z.pow_pos 2 23)) +
                         / 2 * / IZR (Z.pow_pos 2 149)).
                { apply Rle_trans with 
                  (Rabs (FT2R (prod Tsingle b1 b2) -
                            FT2R b1 * FT2R b2)).
                  apply Rabs_triang_inv. nra.
                } 
                assert (Rabs (FT2R (prod Tsingle b1 b2)) <= 
                        Rabs (FT2R b1 * FT2R b2) +
                        Rabs (FT2R b1 * FT2R b2) *
                         (/ 2 * / IZR (Z.pow_pos 2 23)) +
                         / 2 * / IZR (Z.pow_pos 2 149)).
                { nra. } 
                apply Rle_trans with 
                (( Rabs (FT2R b1 * FT2R b2) +
                  Rabs (FT2R b1 * FT2R b2) *
                  (/ 2 * / IZR (Z.pow_pos 2 23)) +
                  / 2 * / IZR (Z.pow_pos 2 149)) * (/ 2 * / IZR (Z.pow_pos 2 23)) + 
                  (/ 2 * / IZR (Z.pow_pos 2 149)) + 
                    (Rabs (FT2R b1 * FT2R b2) *
                       (/ 2 * / IZR (Z.pow_pos 2 23)) +
                       / 2 * / IZR (Z.pow_pos 2 149)) ).
                 +++ repeat apply Rplus_le_compat_r.
                     apply Rmult_le_compat_r. nra.
                     nra.
                 +++ rewrite -/u -/u0. 
                     assert ((Rabs (FT2R b1 * FT2R b2) +
                               Rabs (FT2R b1 * FT2R b2) * u0 + u) * u0 + u +
                              (Rabs (FT2R b1 * FT2R b2) * u0 + u) = 
                             Rabs (FT2R b1 * FT2R b2) * (2 * u0 + u0 * u0) + u* u0 + 2 *u).
                     { nra. } rewrite H11. rewrite Rabs_mult. rewrite Rplus_0_r.
                     assert (Rabs (FT2R b1) * Rabs (FT2R b2) *
                              ((1 + u0) * ((1 + u0) * 1) - 1) +
                              nr * u * ((1 + u0) * 1) +
                              u * ((1 + u0) * 1 - 1) / u0 = 
                             Rabs (FT2R b1) * Rabs (FT2R b2) *
                              ((1 + u0) * ((1 + u0) * 1) - 1) + 
                              nr * u * u0 + (nr * u + u * (u0 / u0))).
                     { nra. } rewrite H12. clear H12.
                     repeat apply Rplus_le_compat.
                     --- apply Rmult_le_compat_l.
                         *** apply Rmult_le_pos; apply Rabs_pos.
                         *** nra.
                     --- apply Rmult_le_compat_r.
                         *** unfold u0. simpl. nra.
                         *** assert (u = 1 * u). { nra. } rewrite H12.
                             assert (nr * (1 * u) = nr * u). { nra. } rewrite H13.
                             apply Rmult_le_compat_r.
                             unfold u; simpl; nra.
                             unfold nr. assert (1 = INR 1). { reflexivity. }
                             rewrite H14. by apply le_INR.
                     --- assert ( u0 / u0 = 1). 
                         { apply Rinv_r. unfold u0. simpl. nra. }
                         rewrite H12. 
                         assert (nr * u + u * 1 = (nr + 1) * u).
                         { nra. } rewrite H13. apply Rmult_le_compat_r.
                         unfold u; simpl; nra.
                         assert (1 <= nr -> 2 <= nr + 1). { nra. }
                         apply H14. clear H14.
                         unfold nr. assert (1 = INR 1). { reflexivity. }
                         rewrite H14. by apply le_INR.  
    - simpl in IHL.
      assert ((1 <= m)%nat).
      { rewrite Heqm. 
        destruct L.
        + by contradict H1.
        + simpl. lia.
      } specialize (IHL H2).
      apply Rle_trans with 
      (Rabs (FT2R
               (sum Tsingle (prod Tsingle (fst a) (snd a))
                  (sum_fixF Tsingle (prod_fixF Tsingle L))) -
             (FT2R (prod Tsingle (fst a) (snd a)) + 
               FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)))) +
       Rabs ((FT2R (prod Tsingle (fst a) (snd a)) + 
               FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) -
            (FT2R (fst a) * FT2R (snd a) +
             sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
       * assert ((FT2R
                   (sum Tsingle (prod Tsingle (fst a) (snd a))
                      (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                 (FT2R (fst a) * FT2R (snd a) +
                  sum_fixR (prod_fixR (Flist_to_Rlist_pair L)))) =
                 (FT2R
                 (sum Tsingle (prod Tsingle (fst a) (snd a))
                    (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                 (FT2R (prod Tsingle (fst a) (snd a)) + 
                   FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)))) + 
                  ((FT2R (prod Tsingle (fst a) (snd a)) + 
                   FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) -
                  (FT2R (fst a) * FT2R (snd a) +
                   sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
         { nra. } rewrite H3. clear H3.
         apply Rabs_triang.
       * pose proof (prove_rndoff_prod (prod Tsingle (fst a) (snd a))
                      (sum_fixF Tsingle (prod_fixF Tsingle L))).
         specialize (H3 (n+1)%nat).
         assert ((1 < n+1)%nat). { lia. } specialize (H3 H4).
         assert (boundsmap_denote (@bmap_prod ty (n + 1))
                  (vmap (prod Tsingle (fst a) (snd a))
                    (sum_fixF Tsingle (prod_fixF Tsingle L)))).
         { admit. } specialize (H3 H5).
         simpl in H3. rewrite -/u -/u0 in H3.
         pose proof (prove_rndoff (prod Tsingle (fst a) (snd a))
                        (sum_fixF Tsingle (prod_fixF Tsingle L))).
         specialize (H6 (m+1)%nat). simpl in H6.
         assert ((1 <= m + 1)%nat). { lia. } specialize (H6 H7).
         assert (boundsmap_denote (@bmap ty (m + 1))
                   (vmap (prod Tsingle (fst a) (snd a))
                      (sum_fixF Tsingle (prod_fixF Tsingle L)))).
         { admit. } specialize (H6 H8).
         rewrite -/u -/u0 in H6.
         apply Rle_trans with 
         ((Rabs
               (FT2R (prod Tsingle (fst a) (snd a)) +
                FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) *
             u0 + u) + Rabs
            (FT2R (prod Tsingle (fst a) (snd a)) +
             FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
             (FT2R (fst a) * FT2R (snd a) +
              sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
         ++ by apply Rplus_le_compat_r.
         ++ apply Rle_trans with
            ((Rabs
               (FT2R (prod Tsingle (fst a) (snd a)) +
                FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) *
             u0 + u) +
             (Rabs (FT2R (prod Tsingle (fst a) (snd a)) - (FT2R (fst a) * FT2R (snd a))) +
             Rabs (FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
                    sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
             -- apply Rplus_le_compat_l.
                assert ((FT2R (prod Tsingle (fst a) (snd a)) +
                           FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
                           (FT2R (fst a) * FT2R (snd a) +
                            sum_fixR (prod_fixR (Flist_to_Rlist_pair L)))) = 
                          (FT2R (prod Tsingle (fst a) (snd a)) - (FT2R (fst a) * FT2R (snd a))) +
                          (FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
                              sum_fixR (prod_fixR (Flist_to_Rlist_pair L)))).
                { nra. } rewrite H9. apply Rabs_triang.
             -- remember (fst a) as b1.
                remember (snd a) as b2.
                pose proof (prove_rndoff_prod b1 b2).
                specialize (H9 2%nat).
                assert ((1 < 2)%nat). { lia. }
                assert (boundsmap_denote (@bmap_prod ty 2) (vmap b1 b2)).
                { admit. } specialize (H9 H10 H11). simpl in H9.
                rewrite -/u -/u0 in H9.
                apply Rle_trans with 
                (Rabs
                  (FT2R (prod Tsingle b1 b2) +
                   FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) *
                u0 + u +
                (Rabs (FT2R b1 * FT2R b2) * u0 + u +
                 Rabs
                   (FT2R (sum_fixF Tsingle (prod_fixF Tsingle L)) -
                    sum_fixR (prod_fixR (Flist_to_Rlist_pair L))))).
                ** by apply Rplus_le_compat_l, Rplus_le_compat_r.
                ** apply Rle_trans with 
                   (Rabs
                      (FT2R (prod Tsingle b1 b2) +
                       FT2R (sum_fixF Tsingle (prod_fixF Tsingle L))) *
                    u0 + u +
                    (Rabs (FT2R b1 * FT2R b2) * u0 + u +
                     (dot_prodR (Flist_to_Rlist_pair_abs L) *
                        ((1 + u0) ^ (m + 1) - 1) +
                        INR m * u * (1 + u0) ^ m +
                        u * ((1 + u0) ^ m - 1) / u0))).
                   +++  by repeat apply Rplus_le_compat_l.
                   +++ assert (Rabs (FT2R (prod Tsingle b1 b2)) - 
                               Rabs (FT2R b1 * FT2R b2) <= 
                               Rabs (FT2R b1 * FT2R b2) * u0 + u).
                       { apply Rle_trans with (Rabs
                             (FT2R (prod Tsingle b1 b2) -
                              FT2R b1 * FT2R b2)). 
                         + apply Rabs_triang_inv.
                         + apply H9.
                       } 
                       assert (Rabs (FT2R (prod Tsingle b1 b2)) <=
                               Rabs (FT2R b1 * FT2R b2) *(1 + u0) + u). 
                       { nra. } 
                       assert (Rabs (FT2R (dot_prodF Tsingle L)) - 
                               Rabs (dot_prodR (Flist_to_Rlist_pair L)) <=
                               dot_prodR (Flist_to_Rlist_pair_abs L) *
                                ((1 + u0) ^ (m + 1) - 1) +
                                INR m * u * (1 + u0) ^ m +
                                u * ((1 + u0) ^ m - 1) / u0).
                       { apply Rle_trans with 
                         (Rabs
                            (FT2R (dot_prodF Tsingle L) -
                             dot_prodR (Flist_to_Rlist_pair L))).
                         + apply Rabs_triang_inv.
                         + nra.
                       }
                       assert (Rabs (FT2R (dot_prodF Tsingle L)) <=
                               dot_prodR (Flist_to_Rlist_pair_abs L) +
                               (dot_prodR (Flist_to_Rlist_pair_abs L) *
                                  ((1 + u0) ^ (m + 1) - 1) +
                                  INR m * u * (1 + u0) ^ m +
                                  u * ((1 + u0) ^ m - 1) / u0)).
                       { apply Rle_trans with
                         (Rabs (dot_prodR (Flist_to_Rlist_pair L)) + 
                           (dot_prodR (Flist_to_Rlist_pair_abs L) *
                              ((1 + u0) ^ (m + 1) - 1) +
                              INR m * u * (1 + u0) ^ m +
                              u * ((1 + u0) ^ m - 1) / u0)).
                         + nra.
                         + apply Rplus_le_compat_r.
                           apply sum_abs_pair_le.
                       } 
                       apply Rle_trans with 
                       ((((Rabs (FT2R b1 * FT2R b2) * (1 + u0) + u) +
                        (dot_prodR (Flist_to_Rlist_pair_abs L) +
                          (dot_prodR (Flist_to_Rlist_pair_abs L) *
                           ((1 + u0) ^ (m + 1) - 1) +
                           INR m * u * (1 + u0) ^ m +
                           u * ((1 + u0) ^ m - 1) / u0))) *u0 + u) +
                         (Rabs (FT2R b1 * FT2R b2) * u0 + u +
                           (dot_prodR (Flist_to_Rlist_pair_abs L) *
                            ((1 + u0) ^ (m + 1) - 1) +
                            INR m * u * (1 + u0) ^ m +
                            u * ((1 + u0) ^ m - 1) / u0))).
                       --- apply Rplus_le_compat_r.
                           apply Rle_trans with 
                           ((Rabs (FT2R (prod Tsingle b1 b2)) +
                            Rabs (FT2R (dot_prodF Tsingle L))) * u0 + u).
                           *** apply Rplus_le_compat_r.
                               apply Rmult_le_compat_r.
                               unfold u0; simpl;nra.
                               apply Rabs_triang.
                           *** apply Rplus_le_compat_r.
                               apply Rmult_le_compat_r.
                               unfold u0; simpl;nra.
                               apply Rplus_le_compat; nra.
                       --- rewrite !Rabs_mult.
                           assert ((Rabs (FT2R b1) * Rabs (FT2R b2) * (1 + u0) + u +
                                     (dot_prodR (Flist_to_Rlist_pair_abs L) +
                                      (dot_prodR (Flist_to_Rlist_pair_abs L) *
                                       ((1 + u0) ^ (m + 1) - 1) +
                                       INR m * u * (1 + u0) ^ m +
                                       u * ((1 + u0) ^ m - 1) / u0))) * u0 + u +
                                    (Rabs (FT2R b1) * Rabs (FT2R b2) * u0 + u +
                                     (dot_prodR (Flist_to_Rlist_pair_abs L) *
                                      ((1 + u0) ^ (m + 1) - 1) +
                                      INR m * u * (1 + u0) ^ m +
                                      u * ((1 + u0) ^ m - 1) / u0)) = 
                                    (Rabs (FT2R b1) * Rabs (FT2R b2) * (u0 * u0 + 2 * u0)) +
                                    ((dot_prodR (Flist_to_Rlist_pair_abs L)) *
                                    (u0 + u0 * ((1 + u0) ^ (m + 1) - 1) + ((1 + u0) ^ (m + 1) - 1)) +
                                    ((1 + u0) * (INR m * u * (1 + u0) ^ m +
                                                  u * ((1 + u0) ^ m - 1) / u0) +
                                     u0 * u + 2 * u))).
                          { nra. } rewrite H16. clear H16.
                          unfold dot_prodR.
                          assert ((Rabs (FT2R b1) * Rabs (FT2R b2) +
                                     sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L))) *
                                    ((1 + u0) * (1 + u0) ^ (m + 1) - 1) +
                                    nr * u * ((1 + u0) * (1 + u0) ^ m) +
                                    u * ((1 + u0) * (1 + u0) ^ m - 1) / u0 =
                                   (Rabs (FT2R b1) * Rabs (FT2R b2) * ((1 + u0) * (1 + u0) ^ (m + 1) - 1)) +
                                   ((sum_fixR (prod_fixR (Flist_to_Rlist_pair_abs L))) * ((1 + u0) * (1 + u0) ^ (m + 1) - 1) +
                                    (nr * u * ((1 + u0) * (1 + u0) ^ m) +
                                    u * ((1 + u0) * (1 + u0) ^ m - 1) / u0))).
                          { nra. } rewrite H16. clear H16.
                          apply Rplus_le_compat.
                          *** repeat apply Rmult_le_compat_l.
                              ++++ repeat apply Rmult_le_pos; apply Rabs_pos.
                              ++++ apply x_bound_S. unfold u0; simpl; nra.
                          *** apply Rplus_le_compat.
                              ++++ apply Rmult_le_compat_l.
                                   apply sum_abs_pair_rel. nra.
                              ++++ assert ((1 + u0) * (INR m * u * (1 + u0) ^ m +
                                              u * ((1 + u0) ^ m - 1) / u0) + u0 * u +  2 * u = 
                                            INR m * u* (1+u0) *(1+u0)^m + u * (1+u0) * ((1+u0)^m - 1) / u0 + (u0 * u + 2* u) ).
                                   { nra. } rewrite H16. clear H16. unfold nr. rewrite H0. rewrite plus_INR.
                                   simpl.
                                   assert ((INR m + 1) * u * ((1 + u0) * (1 + u0) ^ m) +
                                            u * ((1 + u0) * (1 + u0) ^ m - 1) / u0 = 
                                            INR m * u * (1 + u0) * (1 + u0) ^ m +
                                            (u * ((1 + u0) * (1 + u0) ^ m - 1) / u0 + 
                                            u * ((1 + u0) * (1 + u0) ^ m))).
                                   { nra. } rewrite H16. 
                                   assert (INR m * u * (1 + u0) * (1 + u0) ^ m +
                                            u * (1 + u0) * ((1 + u0) ^ m - 1) / u0 +
                                            (u0 * u + 2 * u) = 
                                           INR m * u * (1 + u0) * (1 + u0) ^ m +
                                            (u * (1 + u0) * ((1 + u0) ^ m - 1) / u0 +
                                            (u0 * u + 2 * u))). { nra. } rewrite H17.
                                   apply Rplus_le_compat_l.
                                   assert (u * (1 + u0) * ((1 + u0) ^ m - 1) / u0  = 
                                            u * ((1 + u0) * (1 + u0) ^ m - 1) / u0  - u * (u0 / u0)). 
                                   { nra. } rewrite H18.
                                   assert (u0 / u0 = 1). { apply Rinv_r. unfold u0. simpl. nra. }
                                   rewrite H19.
                                   assert (u * ((1 + u0) * (1 + u0) ^ m - 1) / u0 - u * 1 +
                                            (u0 * u + 2 * u) = 
                                           u * ((1 + u0) * (1 + u0) ^ m - 1) / u0 + 
                                           u * (u0 + 1)).
                                   { nra. } rewrite H20.
                                   apply Rplus_le_compat_l. apply Rmult_le_compat_l.
                                   unfold u; simpl; nra.
                                   assert (u0 <= (1 + u0) * (1 + u0) ^ m - 1 ->
                                            u0 + 1 <= (1 + u0) * (1 + u0) ^ m).
                                   { nra. } apply H21. apply u_bound. unfold u0; simpl; nra.
Admitted. 


(** Using Coq's combine function to combibe two lists to get a 
    list of pairs
**)
Lemma forward_error_dot_precise:
  forall (L1 L2: list (ftype Tsingle)),
  let L := combine L1 L2 in
  let ty := Tsingle in 
  let n:= length L in 
  let nr := INR n in
  (1 <= n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  Rabs (FT2R (dot_prodF _ L) - dot_prodR (Flist_to_Rlist_pair L)) <=
  (dot_prodR (Flist_to_Rlist_pair_abs L)) * ((1 + u0)^(n+1) -1) + 
  nr * u * (1+u0)^n + u * ((1+u0)^n -1) / u0.
Proof.
intros.
by apply forward_error_dot_aux.
Qed.



Lemma forward_error_dot:
  forall (L1 L2: list (ftype Tsingle)),
  let ty := Tsingle in 
  let n:= length L1 in 
  let nr := INR n in
  (1 <= n)%nat ->
  let u  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let u0 := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  Rabs (FT2R (dot_prodF _ L1 L2) - dot_prodR (Flist_to_Rlist L1) (Flist_to_Rlist L2)) <=
  (nr * u0 * (1 + u0) / (1 - u0) + u0) * dot_prodR (Flist_to_Rlist L1) (Flist_to_Rlist L2) +
  ((nr^2 + nr) / (1 - u0) + nr) * u.
Admitted.












End WITHNANS.