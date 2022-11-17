From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import ssreflect ssralg all_algebra seq.


Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


Section WITHNANS.
Context {NANS: Nans}. 

Definition sum ty (a b : ftype ty) : ftype ty := BPLUS ty a b.


Fixpoint sum_fixF ty (L1: list (ftype ty)) : ftype ty :=
  match L1 with 
   | hd :: tl => match tl with
                 | [] => hd
                 | _ => sum ty hd (sum_fixF ty tl)
                 end
   | [] => (Zconst ty 0)
  end.



Fixpoint sum_fixR (L1: list R) : R :=
  match L1 with 
   | hd :: tl =>  Rplus hd (sum_fixR tl)
   | [] => 0%R
  end.  


Definition _a := 1%positive. (* represents current element from list *)
Definition _b := 2%positive. (* represents accumulator of sum *)

Definition vmap_list ty (a b : ftype ty) := 
   [(_a, existT ftype _ a); (_b, existT ftype _ b)].

Definition vmap {ty} (a b : ftype ty) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap_list ty a b)) in exact z).


Definition F_max:= powerRZ 2 (femax Tsingle).

Definition F' := F_max * (1-  / (Raux.bpow Zaux.radix2 (fprec Tsingle -1))).


(** a < F'/n * (1+d)^n  **)
(** b < (n-1)* F' / n  + 2 * e/d **)

Definition bmap_list {ty} (n : nat) : list varinfo := 
  let nr := INR n in
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax ty - fprec ty) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec ty + 1) in 
  [ Build_varinfo Tsingle _a 
      (- (F' / (nr * (1+d)^n)) ) (F' / (nr * (1+d)^n)) ;
    Build_varinfo Tsingle _b 
      (- (F' * (nr - 1) / nr + 2 * e/d))
      (F' * (nr - 1) / nr + 2 * e/d ) ].



Definition bmap {ty} (n: nat) : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (@bmap_list ty n) ) in exact z).

Definition sum_expr {ty} (a b : ftype ty) := ltac :( let e' :=
  HO_reify_float_expr constr:([_a; _b]) (sum ty) in exact e').


(*** Product***)
Definition prod ty (a b : ftype ty) : ftype ty := BMULT ty a b.


Definition bmap_list_prod {ty} (n: nat) : list varinfo := 
  let nr := INR n in 
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax ty - fprec ty) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec ty + 1) in 
  [ Build_varinfo Tsingle _a 
      (- sqrt(F' / (nr * (1+d)^n) - e ) ) 
        ( sqrt( F' / (nr * (1+d)^n) - e )) ;
    Build_varinfo Tsingle _b 
      (- sqrt(F' / (nr * (1+d)^n) - e  )) 
        ( sqrt( F' / (nr * (1+d)^n) - e ))  ].



Definition bmap_prod {ty} (n: nat) : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (@bmap_list_prod ty n) ) in exact z).

Definition prod_expr {ty} (a b : ftype ty) := ltac :( let e' :=
  HO_reify_float_expr constr:([_a; _b]) (prod ty) in exact e').


(** List of product of two lists **)

Fixpoint prod_fixF ty (L: list ((ftype ty) * (ftype ty))) : list (ftype ty) :=
  match L with 
  | h :: t => [prod _ (fst h) (snd h)] ++ prod_fixF _ t
  | _ => []
  end.


Fixpoint prod_fixR (L: list (R * R)) : list R :=
  match L with 
  | h :: t => [Rmult (fst h) (snd h)] ++ prod_fixR  t
  | _ => []
  end.

Definition dot_prodF ty (L: list ((ftype ty) * (ftype ty))) : ftype ty :=
  sum_fixF _ (prod_fixF _ L).


Definition dot_prodR (L : list (R * R)) : R :=
  sum_fixR (prod_fixR L).

End WITHNANS.
