(** This file contains definitions of the VCFloat data structures **) 

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


Require Import real_model float_model lemmas.

Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.

(* we want to approximate the round-off error associated with a single update of 
   the solution vector *) 


Definition _x1 : ident  := 1%positive.  
Definition _x2 : ident  := 2%positive.  
Definition _x3 : ident  := 3%positive. 


Definition x1 (x y z: ftype Tsingle )
  : ftype Tsingle  :=  list_nth 0 (X_m 1 [x;y;z] [1;1;1] 1).
Definition x2 (x y z: ftype Tsingle )
  : ftype Tsingle  := list_nth 1 (X_m 1 [x;y;z] [1;1;1] 1).
Definition x3 (x y z: ftype Tsingle )
  : ftype Tsingle  := list_nth 2 (X_m 1 [x;y;z] [1;1;1] 1).


(* the functional model must be reified into the VCFloat abstract syntax trees*)
Definition x1' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x1; _x2; _x3]) x1 in exact e').
Definition x2' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x1; _x2; _x3]) x2 in exact e').
Definition x3' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x1; _x2; _x3]) x3 in exact e').

(* you can look at an example of one of these trees *)
Print x1'.

Definition state : Type := list (ftype Tsingle). 

Definition assoc_list (s : state) := 
   [(_x1, existT ftype _ (list_nth 0 s));(_x2, existT ftype _ (list_nth 1 s));
    (_x3, existT ftype _ (list_nth 2 s))]. 

Definition varmap (s: state) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (assoc_list s)) in exact z).


Definition bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _x1 (-100)  100 ;  
    Build_varinfo Tsingle _x2 (-100)  100 ;
    Build_varinfo Tsingle _x3 (-100)  100 ].


Definition bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list bmap_list) in exact z).

Import IntervalFlocq3.Tactic.

Open Scope R_scope.


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

Definition FT2R_list (l : list (ftype Tsingle)) : list R :=  map FT2R l.


(**  Reification and reflection. *)  
(* get back the floating point functional model by applying the "fval" function *)
Lemma reflect_reify_sF : forall s : state, 
    let e := env_ (varmap s) in 
    let b := [1%F32;1%F32;1%F32] in
     [fval e x1'; fval e x2' ; fval e x3'] = (X_m 1 s b 1%F32).
Proof. reflexivity. Qed.

Lemma FT2R_list_eq :
forall n l1 b, 
FT2R (List.nth n l1 b) = List.nth n (FT2R_list l1) (FT2R b).
Proof.
intros.
symmetry.
apply map_nth.
Qed.


(* get back the real functional model by applying the "rval" function *)
Lemma reflect_reify_sR : forall s : state, 
    let e := env_ (varmap s) in 
    let s1 := @listR_to_vecR 3%nat (FT2R_list s) in 
    let b  := @listR_to_vecR 3%nat [1;1;1] in
    listR_to_vecR [rval e x1'; rval e x2' ; rval e x3'] = (X_m_real 1 s1 b 1%Re).
Proof.
intros. 
subst e.
apply matrixP. unfold eqrel. intros. rewrite mxE.
rewrite /X_m_real. rewrite !mxE.
rewrite /s1 /b. 
unfold x1', x2', x3'.
unfold_rval.  simpl.
assert (x = 0 \/ x = 1 \/ x = inord 2).
{ assert (x \in enum 'I_3). 
  { by rewrite mem_map. }  
  assert (enum 'I_3 = [:: ord0;  1; (@inord 2 2)]).
  { apply enum_list. } rewrite H0 in H. rewrite inE in H.
  assert ((x == ord0) \/ (x \in [:: 1; inord 2])).
  { by apply /orP. } destruct H1.
  + left. by apply /eqP.
  + rewrite inE in H1.
    assert ((x == 1) \/ (x \in [:: inord 2])).
    { by apply /orP. } destruct H2.
    - right. left.  by apply /eqP.
    - rewrite inE in H2. right;right;by apply /eqP. 
}
destruct H.
+ rewrite H //=. rewrite !big_ord_recr //= !big_ord0 !add0r !mxE.
  assert (widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max) = 0).
  { by apply /eqP. } rewrite H0 //=.
  rewrite !big_ord_recr //= !big_ord0 !add0r !mxE H0//= !RplusE !RmultE .
  rewrite  !oppr0 !mul0r !addr0 !add0r !mulr1//=. 
  assert (((2 / 1)%Re - (2 / 1)%Re) = 0%Re).
  { rewrite -!RplusE -!RoppE. nra. } rewrite H1. rewrite !mulr0 !mul0r !add0r !addr0.
  assert ((2 / 1)%Re = 2%Re). { nra. } rewrite H2.
  assert ((-1 / 1)%Re = (-1)%Re). { nra. } rewrite H3.
  rewrite -!RdivE. rewrite -!RplusE -!RmultE -!RoppE. 
  assert ((- (1 / 2) * -1)%Re = (1/2)%Re). { nra. } rewrite H4. 
  rewrite /default_val //=.
  f_equal.
  f_equal.
  simpl; apply FT2R_list_eq.
  assert (2%Re <> 0%Re -> 2 != 0). { intros. by apply /eqP. } apply H4; nra.
+ destruct H.
  - rewrite H //=. rewrite !big_ord_recr //= !big_ord0 !add0r !mxE.
    assert (widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max) = 0).
    { by apply /eqP. } rewrite H0 //=.
    rewrite !big_ord_recr //= !big_ord0 !add0r !mxE H0//= !RplusE !RmultE .
    rewrite  !oppr0 !mul0r !addr0 !add0r !mulr1//=. 
    assert (((2 / 1)%Re - (2 / 1)%Re) = 0%Re).
    { rewrite -!RplusE -!RoppE. nra. } rewrite H1. rewrite !mulr0 !mul0r !addr0.
    assert ((2 / 1)%Re = 2%Re). { nra. } rewrite H2.
    assert ((-1 / 1)%Re = (-1)%Re). { nra. } rewrite H3.
    rewrite -!RdivE. rewrite -!RplusE -!RmultE -!RoppE. 
    assert ((- (1 / 2) * -1)%Re = (1/2)%Re). { nra. } rewrite H4. 
    rewrite /default_val //=. 
  f_equal.
  f_equal.
  f_equal.
  simpl; apply FT2R_list_eq.
  f_equal.
  simpl; apply FT2R_list_eq.
  assert (2%Re <> 0%Re -> 2 != 0). { intros. by apply /eqP. } apply H4; nra.
  - rewrite H //=.
    assert (nat_of_ord (@inord 2 2) = 2%N :> nat ). { by rewrite inordK. } rewrite H0.
    rewrite !big_ord_recr //= !big_ord0 !add0r !mxE.
    assert (widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max) = 0).
    { by apply /eqP. } rewrite H0 //=.
    rewrite !big_ord_recr //= !big_ord0 !add0r !mxE H0//= !RplusE !RmultE .
    rewrite  !oppr0 !mul0r !addr0 !add0r !mulr1//=. 
    assert (((2 / 1)%Re - (2 / 1)%Re) = 0%Re).
    { rewrite -!RplusE -!RoppE. nra. } rewrite H2 //=.
    rewrite !mulr0 !mul0r !addr0 !add0r.
    assert ((2 / 1)%Re = 2%Re). { nra. } rewrite H3.
    assert ((-1 / 1)%Re = (-1)%Re). { nra. } rewrite H4.
    rewrite -!RdivE. rewrite -!RplusE -!RmultE -!RoppE. 
    assert ((- (1 / 2) * -1)%Re = (1/2)%Re). { nra. } rewrite H5. 
    rewrite /default_val //=.
  f_equal.
  f_equal.
  simpl; apply FT2R_list_eq.
  assert (2%Re <> 0%Re -> 2 != 0). { intros. by apply /eqP. } apply H5; nra.
Qed.


Ltac unfold_all_fval :=  (* move this to vcfloat *)
 repeat
  match goal with
  | |- context [fval (env_ ?e) ?x] =>
     pattern (fval (env_ e) x);
     let M := fresh in match goal with |- ?MM _ => set (M := MM) end;
     unfold fval; try unfold x; unfold type_of_expr; unfold_fval;
    repeat match goal with |- context [env_ ?a ?b ?c] => 
       let u := constr:(env_ a b c) in 
       let u1 := eval hnf in u in
      change u with u1
     end;
    subst M; cbv beta
end.

End WITHNANS.

