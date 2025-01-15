From libValidSDP Require Import float_infnan_spec float_spec.
From libValidSDP Require binary_infnan.
From LAProof Require Import dot_acc.
From vcfloat Require FPCore FPLib.
Require Import ZArith.

Set Bullet Behavior "Strict Subproofs".


Local Lemma p_lt_e (p e: Z) (a: (1<p)%Z) (b: BinarySingleNaN.Prec_lt_emax p e) :
   Base.ZLT (Z.pos (Z.to_pos p)) e.
Proof.
Search (Z.pos (Z.to_pos _) = _).
rewrite Z2Pos.id; auto.
apply Base.ZLT_intro; auto.
destruct p; try discriminate; reflexivity.
Qed.


Local Lemma p_gt_0 (p: Z) (a: (1<p)%Z) : 
    Bool.Is_true (negb (Z.to_pos p =? 1)%positive).
Proof.
destruct p; try discriminate.
destruct p; try discriminate; hnf; auto.
Qed.

Instance SDP_of_VCF_Nan (N: FPCore.Nans) : binary_infnan.Nans.
destruct N.
apply binary_infnan.Build_Nans.
-
intros p1 e1 a1 b1 p2 e2 a2 b2 x.
destruct p1 as [| p1 | ]; try discriminate.
destruct p2 as [| p2 | ]; try discriminate.
set (t1 := FPCore.TYPE _ _ (p_lt_e _ _ a1 b1) (p_gt_0 _ a1)).
set (t2 := FPCore.TYPE _ _ (p_lt_e _ _ a2 b2) (p_gt_0 _ a2)).
apply (conv_nan (FPCore.fprec t1) (FPCore.femax t1)
       (FPCore.fprec t2) (FPCore.femax t2) (FPCore.fprec_gt_one t2)
     x).
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply plus_nan; eauto with typeclass_instances.
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply mult_nan; eauto with typeclass_instances.
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply div_nan; eauto with typeclass_instances.
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply abs_nan; eauto with typeclass_instances.
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply opp_nan; eauto with typeclass_instances.
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply sqrt_nan; eauto with typeclass_instances.
-
intros p e a b x.
destruct p as [| p | ]; try discriminate.
set (t := FPCore.TYPE _ _ (p_lt_e _ _ a b) (p_gt_0 _ a)).
eapply fma_nan; eauto with typeclass_instances.
Defined.

Definition FIS_of_VCF (NAN: FPCore.Nans) (ty: FPCore.type) `{Std: FPCore.is_standard ty} : Float_infnan_spec.
apply (@binary_infnan.binary_infnan (SDP_of_VCF_Nan NAN) (FPCore.fprecp ty) (FPCore.femax ty)) .
apply FPCore.fprec_gt_one.
apply Z.ltb_lt.
apply FPCore.fprec_lt_femax.
Defined.

Import Reals.

Section FIS_instance.

Context {NAN: FPCore.Nans} {t: FPCore.type} {Std: FPCore.is_standard t}.

Definition FI: Float_infnan_spec := @FIS_of_VCF NAN t Std.

Definition dotprodF (v1 v2: list (FIS FI)): FIS FI :=
  List.fold_left (fun s x12 => fiplus (fimult (fst x12) (snd x12)) s) 
                (List.combine v1 v2) (FIS0 FI).

Definition dotprodR (v1 v2: list R): R :=
  List.fold_left (fun s x12 => Rplus (Rmult (fst x12) (snd x12)) s) 
                (List.combine v1 v2) R0.

Definition F2R (x: FIS FI) : R := FS_val (FIS2FS x).

Definition γ (n: nat) : R := ((1 + eps (fis FI))^n - 1).
Definition γ1 (n1 n2: nat) : R := INR n1 * eta (fis FI) * (1 + γ n2).

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

Lemma g_γ: @common.g t= γ.
Proof.
intros.
unfold common.g, γ.
rewrite default_rel_eps; auto.
Qed.

Lemma g1_γ1: @common.g1 t = γ1.
Proof.
intros.
unfold common.g1, γ1.
rewrite g_γ.
rewrite default_abs_eta.
auto.
Qed.

Lemma dotprod_mixed_error:
  forall (v1 v2: list (FIS FI))
    (Hlen: length v1 = length v2)
    (Hfin: is_true (finite (dotprodF v1 v2))),
  exists (u : list R) (η : R),
    length u = length v2 /\
    F2R (dotprodF v1 v2) = dotprodR u (List.map F2R v2) + η /\
    (forall n, (n < length v2)%nat -> exists delta,
      List.nth n u 0 = F2R (List.nth n v1 (fiopp (FIS0 FI))) * (1 + delta) /\ Rabs delta <= γ (length v2))  /\
    Rabs η <= γ1 (length v2) (length v2).
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
f_equal.
f_equal.
unfold FPCore.BPLUS, FPCore.BINOP.
f_equal.
unfold FPCore.BMULT, FPCore.BINOP.
rewrite FPCore.float_of_ftype_of_float.
unfold binary_infnan.fiplus.
f_equal.
+
apply Classical_Prop.proof_irrelevance.
+
clear.
apply FunctionalExtensionality.functional_extensionality; intro x.
apply FunctionalExtensionality.functional_extensionality; intro y.
destruct NAN; simpl.
reflexivity.
+
unfold binary_infnan.fimult; simpl.
f_equal.
apply Classical_Prop.proof_irrelevance.
clear.
apply FunctionalExtensionality.functional_extensionality; intro x.
apply FunctionalExtensionality.functional_extensionality; intro y.
destruct NAN; simpl.
reflexivity.
apply FPCore.float_of_ftype_of_float.
apply FPCore.float_of_ftype_of_float.
+
apply FPCore.float_of_ftype_of_float.
-
exists u, η; [split; [ | split; [ | split]]].
+ rewrite H. rewrite List.map_length. reflexivity.
+ clear - Hlen H0.
Import FPCore.
rewrite <- Rounding.B2R_float_of_ftype in H0.
rewrite List.map_map in H0.
replace (@List.map (FIS FI) R FIS_instance.F2R v2)
 with (@List.map (Binary.binary_float (fprec t) (femax t)) R
           (fun x : Binary.binary_float (fprec t) (femax t) =>
            @FT2R t (@ftype_of_float t Std x)) v2).
2:{ clear. induction v2; simpl; f_equal; auto;
             apply FPCore.FT2R_ftype_of_float. }
replace dotprod_model.dotprodR with dotprodR in H0.
2:{ 
apply FunctionalExtensionality.functional_extensionality; intro x.
apply FunctionalExtensionality.functional_extensionality; intro y.
unfold dotprodR, dotprod_model.dotprodR.
set (z := R0). change 0%R with z. clearbody z.
revert z y; induction x; destruct y; simpl; intros; auto.
rewrite IHx. f_equal. apply Rplus_comm.
}
rewrite <- H0.
unfold FIS_instance.F2R.
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
unfold BPLUS at 2. unfold BINOP.
set (y1 := Binary.Bplus _ _ _ _ _ _ _ _).
set (y2 := binary_infnan.fiplus (binary_infnan.fimult a f) z1).
replace y1 with y2.
2:{ subst y1 y2; simpl. 
unfold binary_infnan.fiplus, binary_infnan.fimult; simpl.
unfold BMULT, BINOP.
rewrite !float_of_ftype_of_float.
f_equal; try apply proof_irr.
apply FunctionalExtensionality.functional_extensionality; intro x.
apply FunctionalExtensionality.functional_extensionality; intro y.
destruct NAN; simpl.
reflexivity.
f_equal.
apply proof_irr.
apply FunctionalExtensionality.functional_extensionality; intro x.
apply FunctionalExtensionality.functional_extensionality; intro y.
destruct NAN; simpl.
reflexivity.
}
clearbody y2.
apply IHv1; auto.
+
intros.
destruct (H1 n) as [delta [? ?]].
rewrite List.map_length; auto.
exists delta; split.
rewrite H4.
f_equal.
unfold FIS_instance.F2R.
simpl.
rewrite List.map_nth.
rewrite FT2R_ftype_of_float.
f_equal.
rewrite List.map_length in H5.
unfold common.g in H5. unfold γ.
simpl.
Set Nested Proofs Allowed.
rewrite <- default_rel_eps.
auto.
+
rewrite !List.map_length in H2.
rewrite g1_γ1 in H2; auto.
Qed.
