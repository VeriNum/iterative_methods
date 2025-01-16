From libValidSDP Require Import float_infnan_spec float_spec.
From libValidSDP Require binary_infnan.
From LAProof Require Import dot_acc.
From vcfloat Require FPCore FPLib.
Require Import ZArith.

Set Bullet Behavior "Strict Subproofs".

Instance SDP_of_VCF_Nan (N: FPCore.Nans) : binary_infnan.Nans :=
   binary_infnan.Build_Nans 
        FPCore.conv_nan
        FPCore.plus_nan
        FPCore.mult_nan 
        FPCore.div_nan
        FPCore.abs_nan
        FPCore.opp_nan
        FPCore.sqrt_nan
        FPCore.fma_nan.

Definition FIS_of_VCF (NAN: FPCore.Nans) (ty: FPCore.type) : Float_infnan_spec
  :=  @binary_infnan.binary_infnan
        (SDP_of_VCF_Nan NAN) 
        (FPCore.fprecp ty) (FPCore.femax ty) (FPCore.fprec_gt_one ty)
        (proj2 (Z.ltb_lt _ _) (FPCore.fprec_lt_femax _)).

Import Reals.

Section FIS_algs.

Variable FI: Float_infnan_spec.

Definition dotprodF (v1 v2: list (FIS FI)): FIS FI :=
  List.fold_left (fun s x12 => fiplus (fimult (fst x12) (snd x12)) s) 
                (List.combine v1 v2) (FIS0 FI).

Definition dotprodR (v1 v2: list R): R :=
  List.fold_left (fun s x12 => Rplus (Rmult (fst x12) (snd x12)) s) 
                (List.combine v1 v2) R0.

Definition F2R (x: FIS FI) : R := FS_val (FIS2FS x).

Definition γ (n: nat) : R := ((1 + eps (fis FI))^n - 1).
Definition γ1 (n1 n2: nat) : R := INR n1 * eta (fis FI) * (1 + γ n2).

End FIS_algs.


Section FIS_instance.

Context {NAN: FPCore.Nans} {t: FPCore.type} {Std: FPCore.is_standard t}.

Definition FI: Float_infnan_spec := @FIS_of_VCF NAN t.

Lemma default_rel_eps:
  @common.default_rel t = @flocq_float.eps (FPCore.fprecp t).
Proof.
unfold common.default_rel, flocq_float.eps.
Search (Raux.bpow _ (_ + _) = _).
rewrite Raux.bpow_plus_1.
simpl.
rewrite <- Rmult_assoc.
rewrite Rinv_l by Lra.lra.
rewrite Rmult_1_l.
auto.
Qed.

Lemma default_abs_eta: @common.default_abs t = eta FI.
Proof.
unfold common.default_abs, FI, eta, fis, FIS_of_VCF, binary_infnan.binary_infnan.
unfold binary_infnan.fis.
unfold flocq_float.flocq_float.
unfold flocq_float.eta.
set (u := (3 - _ - _)%Z).
rewrite Float_lemmas.bpow_minus1. rewrite Rmult_comm.
reflexivity.
Qed.

Lemma g_γ: @common.g t= γ FI.
Proof.
intros.
unfold common.g, γ.
rewrite default_rel_eps; auto.
Qed.

Lemma g1_γ1: @common.g1 t = γ1 FI.
Proof.
intros.
unfold common.g1, γ1.
rewrite g_γ.
rewrite default_abs_eta.
auto.
Qed.

Lemma BPLUS_translate:
  forall (x y: FPCore.ftype t),
  FPCore.BPLUS x y = FPCore.ftype_of_float
       (@binary_infnan.fiplus (SDP_of_VCF_Nan NAN)
        (FPCore.fprecp t) (FPCore.femax t)
        (FPCore.fprec_gt_one t)
        (proj2 (Z.ltb_lt (FPCore.fprec t) (FPCore.femax t))
           (FPCore.fprec_lt_femax t))
         (FPCore.float_of_ftype x) (FPCore.float_of_ftype y)).
Proof.
intros.
unfold FPCore.BPLUS, FPCore.BINOP, binary_infnan.fiplus.
f_equal. f_equal. apply Classical_Prop.proof_irrelevance.
Qed.

Lemma BMULT_translate:
  forall (x y: FPCore.ftype t),
  FPCore.BMULT x y = FPCore.ftype_of_float
       (@binary_infnan.fimult (SDP_of_VCF_Nan NAN)
        (FPCore.fprecp t) (FPCore.femax t)
        (FPCore.fprec_gt_one t)
        (proj2 (Z.ltb_lt (FPCore.fprec t) (FPCore.femax t))
           (FPCore.fprec_lt_femax t))
         (FPCore.float_of_ftype x) (FPCore.float_of_ftype y)).
Proof.
intros.
unfold FPCore.BMULT, FPCore.BINOP, binary_infnan.fimult.
f_equal. f_equal. apply Classical_Prop.proof_irrelevance.
Qed.

Lemma dotprodR_translate:
  dotprodR = dotprod_model.dotprodR.
Proof.
apply FunctionalExtensionality.functional_extensionality; intro x.
apply FunctionalExtensionality.functional_extensionality; intro y.
unfold dotprodR, dotprod_model.dotprodR.
set (z := R0). change 0%R with z. clearbody z.
revert z y; induction x; destruct y; simpl; intros; auto.
rewrite IHx. f_equal. apply Rplus_comm.
Qed.


Lemma dotprod_mixed_error:
  forall (v1 v2: list (FIS FI))
    (Hlen: length v1 = length v2)
    (Hfin: is_true (finite (dotprodF FI v1 v2))),
  exists (u : list R) (η : R),
    length u = length v2 /\
    F2R FI (dotprodF FI v1 v2) = dotprodR u (List.map (F2R FI) v2) + η /\
    (forall n, (n < length v2)%nat -> exists delta,
      List.nth n u 0 = F2R FI (List.nth n v1 (fiopp (FIS0 FI))) * (1 + delta) /\ Rabs delta <= γ FI (length v2))  /\
    Rabs η <= γ1 FI (length v2) (length v2).
Proof.
intros.
destruct (dot_acc.dotprod_mixed_error 
        (List.map FPCore.ftype_of_float v1)
        (List.map FPCore.ftype_of_float v2))
 as [u [η [? [? [? ?]]]]].
-
rewrite !List.map_length; auto.
-
red in Hfin.
simpl in Hfin.
rewrite FPCore.is_finite_Binary.
rewrite <- Hfin.
f_equal.
unfold dotprodF, dotprod_model.dotprodF, dotprod_model.dotprod.
clear - Hlen.
unfold FPCore.Zconst.
change (IEEE754_extra.BofZ _ _ _ _ _) with (FIS0 FI).
set (c := FIS0 FI). clearbody c.
revert c v2 Hlen; induction v1; destruct v2; intros; inversion Hlen; clear Hlen; auto.
simpl.
apply FPCore.float_of_ftype_of_float.
simpl.
rewrite <- IHv1; auto; clear IHv1.
now rewrite BPLUS_translate, BMULT_translate, !FPCore.float_of_ftype_of_float.
-
exists u, η; [split; [ | split; [ | split]]].
+ rewrite H. rewrite List.map_length. reflexivity.
+ clear - Hlen H0.
Import FPCore.
rewrite <- Rounding.B2R_float_of_ftype in H0.
rewrite List.map_map in H0.
replace (@List.map (FIS FI) R (LA_SDP.F2R FI) v2)
 with (@List.map (Binary.binary_float (fprec t) (femax t)) R
           (fun x : Binary.binary_float (fprec t) (femax t) =>
            @FT2R t (@ftype_of_float t Std x)) v2)
 by (clear; induction v2; simpl; f_equal; auto;
             apply FPCore.FT2R_ftype_of_float).
rewrite <- dotprodR_translate in H0.
rewrite <- H0. clear H0.
unfold LA_SDP.F2R.
simpl. f_equal.
clear - Hlen.
unfold dotprod_model.dotprodF, dotprod_model.dotprod, dotprodF.
simpl.
set (z1 := binary_infnan.FI0).
change (Zconst t 0) with (ftype_of_float z1).
clearbody z1.
revert z1 v2 Hlen; induction v1; destruct v2; simpl; intros; try discriminate; auto.
symmetry; apply float_of_ftype_of_float.
injection Hlen; intro.
rewrite BPLUS_translate, BMULT_translate, !FPCore.float_of_ftype_of_float.
apply IHv1; auto.
+
intros.
destruct (H1 n) as [delta [? ?]].
rewrite List.map_length; auto.
exists delta; split.
rewrite H4.
f_equal.
unfold LA_SDP.F2R.
simpl.
rewrite List.map_nth.
rewrite FT2R_ftype_of_float.
f_equal.
rewrite List.map_length in H5.
unfold common.g in H5. unfold γ.
simpl.
rewrite <- default_rel_eps.
auto.
+
rewrite !List.map_length in H2.
rewrite g1_γ1 in H2; auto.
Qed.

End FIS_instance.

