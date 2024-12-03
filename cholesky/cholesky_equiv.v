Require Import VST.floyd.proofauto.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Import FPCore FPCompCert.
Require Import Cholesky.cholesky_model.
From libValidSDP Require cholesky_infnan.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div prime binomial ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
From mathcomp.algebra_tactics Require Import ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


From libValidSDP Require binary_infnan.


Definition Nans_eqv (A: binary_infnan.Nans)  (B: Nans) :=
    (forall (ty1 ty2 : type) (H1: is_standard ty1) (H2: is_standard ty2),
      A.(binary_infnan.conv_nan) = B.(FPCore.conv_nan) ty1 ty2)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.plus_nan) = B.(FPCore.plus_nan) ty)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.mult_nan) = B.(FPCore.mult_nan) ty)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.div_nan)  = B.(FPCore.div_nan) ty)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.abs_nan)  = B.(FPCore.abs_nan) ty)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.opp_nan)  = B.(FPCore.opp_nan) ty)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.sqrt_nan) = B.(FPCore.sqrt_nan) ty)
 /\ (forall ty (H: is_standard ty), A.(binary_infnan.fma_nan)  = B.(FPCore.fma_nan) ty).


Lemma Bminus_Bplus_Bopp:
 forall prec emax Hprec Hemax plus_nan opp_nan x y,
  Binary.Bplus prec emax Hprec Hemax plus_nan BinarySingleNaN.mode_NE x (Binary.Bopp prec emax opp_nan y) =
  Binary.Bminus prec emax Hprec Hemax plus_nan BinarySingleNaN.mode_NE x y.
Admitted.  (* Not strictly true, may raise a different NaN *)


Lemma stilde_infnan_subtract_loop:
 forall 
  (NanA : binary_infnan.Nans)
  (NanB : Nans)
  (NAB : Nans_eqv NanA NanB)
  (t : type) (STD : is_standard t)
  (PREC1 : (1 < fprecp t)%positive)
  (PREC2 : (@binary_infnan.prec (fprecp t)) <? femax t)
  (n : nat)
  (A R : 'M[float_infnan_spec.FIS (@binary_infnan.binary_infnan NanA (fprecp t) (femax t) PREC1 PREC2)]_n.+1)
  (i j : Z)
  (H1 : 0 <= j < Z.of_nat n.+1)
  (H3 : 0 <= i < Z.of_nat n.+1), 
 cholesky_infnan.stilde_infnan (A (inord (Z.to_nat i)) (inord (Z.to_nat j)))
  [ffun k : ordinal (@inord n (Z.to_nat i)) => R (inord k) (inord (Z.to_nat i))] 
  [ffun k : ordinal (@inord n (Z.to_nat i)) => R (inord k) (inord (Z.to_nat j))] = 
 float_of_ftype
  (subtract_loop (fun i0 j0 : Z => ftype_of_float (A (inord (Z.to_nat i0)) (inord (Z.to_nat j0))))
     (fun i0 j0 : Z => ftype_of_float (R (inord (Z.to_nat i0)) (inord (Z.to_nat j0)))) i j i).
Proof.
intros.
rewrite !fintype.inordK; [ | rewrite Rcomplements.SSR_leq; lia].
set i'' := Z.to_nat i.
rewrite -(Z2Nat.id i); [ | lia].
rewrite -/i''. clearbody i''. clear H3 i. rename i'' into i.
set (j'' := Z.to_nat j).
rewrite - (Z2Nat.id j); [ |lia].
rewrite -/j''. clearbody j''. clear H1 j. rename j'' into j.

rewrite /subtract_loop !Nat2Z.id.
set Aij := matrix.fun_of_matrix A (fintype.inord i) (fintype.inord j).
clearbody Aij.
rewrite List.map_map /BMULT /BMINUS /BINOP.
set Mult := Binary.Bmult _ _ _ _ _ _.
set Minus := Binary.Bminus _ _ _ _ _ _.
transitivity (fold_left Minus 
              (List.map (fun k => Mult (R (inord k) (inord i)) (R (inord k) (inord j))) 
                (iota 0 i))
              Aij).
2:{
clearbody Minus.
clearbody Mult.
rewrite -!fold_left_rev_right -!List.map_rev (*rev_involutive*) !fold_right_map.
induction (List.rev (iota 0 i)).
simpl. rewrite float_of_ftype_of_float //.
simpl. rewrite !float_of_ftype_of_float !Nat2Z.id. f_equal; auto.
}
set (i' := inord i). set (j' := inord j). clearbody i'. clearbody j'. 
simpl in Aij.
rename Aij into acc.
set fi := (@binary_infnan.binary_infnan _ _ _ _ _).
replace Mult with (@float_infnan_spec.fimult fi).
2:{
subst Mult.
simpl.
extensionality x y.
rewrite /binary_infnan.fimult /=. f_equal.
apply proof_irr.
apply NAB.
}
replace Minus with (@float_infnan_spec.fiminus fi).
2:{
subst Minus.
extensionality x y.
simpl.
etransitivity.
apply Bminus_Bplus_Bopp.
f_equal.
apply proof_irr.
apply NAB.
}
clear Mult Minus.
change [ffun k : ordinal i => R (inord k) i']
  with ([ffun k : ordinal i => R (inord (O+k)) i']).
change [ffun k : ordinal i => R (inord k) j']
  with ([ffun k : ordinal i => R (inord (O+k)) j']).
forget O as m.
clear.
(*set f := (_ oo _).*)
revert m acc; induction i; intros; auto.
simpl.
rewrite -{}IHi.
f_equal.
f_equal.
f_equal.
f_equal.
1,2: rewrite ffunE; simpl; rewrite addn0 //.
clear.
*
apply eq_dffun; intro k.
rewrite ffunE.
simpl.
f_equal.
f_equal.
unfold bump.
simpl.
lia.
*
apply eq_dffun; intro k.
rewrite ffunE.
simpl.
f_equal.
f_equal.
unfold bump.
simpl.
lia.
Qed.


Lemma ftype_of_float_inj: forall t (STD: is_standard t) x y,
  ftype_of_float x = ftype_of_float y -> x=y.
Proof.
intros.
rewrite - (float_of_ftype_of_float _ _ x) -(float_of_ftype_of_float _ _ y) H //.
Qed.

Lemma cholesky_eqv:
  forall NanA NanB (NAB: Nans_eqv NanA NanB) (t: type) {STD: is_standard t}
   (PREC1: (1 < fprecp t)%positive) PREC2
   n A R,
  @cholesky_infnan.cholesky_spec_infnan (@binary_infnan.binary_infnan NanA (fprecp t) (femax t) PREC1 PREC2) n A R
  <-> @cholesky_jik_spec NanB t STD (Z.of_nat n.+1) 
      (fun i j => ftype_of_float (matrix.fun_of_matrix A (fintype.inord (Z.to_nat i)) (fintype.inord (Z.to_nat j))))
      (fun i j => ftype_of_float (matrix.fun_of_matrix R (fintype.inord (Z.to_nat i)) (fintype.inord (Z.to_nat j)))).
Proof.
move => NanA NanB NAB t STD PREC1 PREC2 n A R.
split.
-
move => [H H0] i j H1.
split.
+
move => H2.
set i' := @fintype.inord n (Z.to_nat i).
set j' := @fintype.inord n (Z.to_nat j).
rewrite (H j' i') {H H0}.
2: rewrite !Rcomplements.SSR_leq /i' /j' !fintype.inordK; lia.
rewrite /BDIV /BINOP.
f_equal.
simpl.
rewrite /binary_infnan.fidiv float_of_ftype_of_float.
f_equal.
apply proof_irr.
apply NAB.
subst i' j'.
have H3: (0 <= i < Z.of_nat n.+1) by lia.
clear H2.
apply stilde_infnan_subtract_loop; auto.
+
intro Hj; subst j.
rewrite H0.
clear H H0.
rewrite /cholesky_infnan.ytildes_infnan /= /float_infnan_spec.fisqrt /binary_infnan.fisqrt /BSQRT /UNOP.
f_equal.
f_equal.
apply proof_irr.
apply NAB.
apply stilde_infnan_subtract_loop; auto.
-
move => H.
split.
+
move => j i Hij.
symmetry.
have Hin: (j<n.+1)%N by apply ltn_ord.
specialize (H (Z.of_nat i) (Z.of_nat j) ltac:(lia)).
destruct H as [H _].
specialize (H ltac:(lia)).
rewrite !Nat2Z.id !inord_val in H.
rewrite /BDIV /BINOP in H.
apply ftype_of_float_inj in H.
rewrite float_of_ftype_of_float in H.
rewrite {}H /cholesky_infnan.ytilded_infnan /float_infnan_spec.fidiv /= /binary_infnan.fidiv.
f_equal; try apply proof_irr.
apply NAB.
rewrite -stilde_infnan_subtract_loop; auto; try lia.
rewrite !Nat2Z.id !inord_val.
auto.
+
move => j.
symmetry.
have Hin: (j<n.+1)%N by apply ltn_ord.
specialize (H (Z.of_nat j) (Z.of_nat j) ltac:(lia)).
destruct H as [_ H].
specialize (H ltac:(lia)).
rewrite /BSQRT /UNOP in H.
apply ftype_of_float_inj in H.
rewrite !Nat2Z.id !inord_val in H.
rewrite {}H /cholesky_infnan.ytildes_infnan /float_infnan_spec.fisqrt /= /binary_infnan.fisqrt.
f_equal; try apply proof_irr.
apply NAB.
rewrite -stilde_infnan_subtract_loop; auto; try lia.
rewrite !Nat2Z.id !inord_val.
auto.
Qed.





















