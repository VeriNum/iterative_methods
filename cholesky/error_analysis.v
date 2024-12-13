Require Import Reals Flocq.Core.Raux.

From libValidSDP Require Import misc.

Require Import Psatz.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
From mathcomp.ssreflect Require Import fintype finfun.
From mathcomp.algebra Require Import ssralg matrix.

Require Import mathcomp.analysis.Rstruct.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

From libValidSDP Require Import fsum_l2r fcmsum real_matrix cholesky.
From Cholesky Require Import cholesky_real.

Set Bullet Behavior "Strict Subproofs".


Section Cholesky.

Variable fs : Float_spec.
Hypothesis eta_neq_0 : eta fs <> 0.

Notation F := (FS fs).      (* the set-predicate of floating point numbers *)
Notation frnd := (frnd fs).  (* rounding function, R -> fs *)
Notation eps := (eps fs).  (* relative error bound *)
Notation eta := (eta fs).  (* absolute error bound, denormalized numbers *)


Variable n : nat.
Variable A : 'M[F]_n.+1.
Hypothesis SymA : MF2R A^T = MF2R A.
Hypothesis PD: positive_definite (MF2R A).
Variable Rt : 'M[F]_n.+1.
Let RteF := \matrix_(i, j) if (i <= j)%N then (Rt i j) else F0 fs.
Let Rte := MF2R RteF.

Hypothesis HAR : cholesky_success A Rt.

Definition γ (n: nat) := ((INR n * eps) / (1 - INR n * eps))%Re.

Definition ΔA : 'M[R]_n.+1 := (Rte^T *m Rte) - MF2R A.

From mathcomp.algebra_tactics Require Import ring lra.

Lemma add_one: forall n: nat, n+1 = n.+1.
Proof.
intro. lia.
Qed.


(*  CASE SPLIT ON i<j 
case: (orP (leqVgt j i)); [ rewrite leq_eqVlt => /orP [Hij | Hij] | ].
+
have Hij': i=j by apply ord_inj; lia. subst j.
admit.
+
admit.
+
*)

Lemma higham_equation_10_4: 
    forall i j : 'I_n.+1, 
       (nat_of_ord i < nat_of_ord j)%N ->
      Rabs ((A i j) - \sum_(k<i.+1) (Rt (inord k) i * Rt (inord k) j)%Re) <= 
                γ i * \sum_(k<i.+1) (Rabs (Rte (inord k) i) * Rabs (Rte (inord k) j)).
Proof.
move => i j Hij.
have HCR := cholesky_correct PD.
set Rr := cholesky (MF2R A) in HCR.
destruct HCR as [UT [DP CC]].
have CJIK: MF2R A i j = \sum_k Rr^T i k * Rr k j.
 by rewrite -CC !mxE.
move :HAR => [[H H0] H1]. clear HAR.
have Rii_neq_0: FS_val (Rt i i) <> R0
  by (clear - H1; move => Hii; move :(H1 i); Lra.lra).
 specialize (H _ _ Hij).
(*
  pose Hin: (i<=n.+1)%N := ltnW (ltn_ord i).
*)
(*
  have Hinordk: forall k: 'I_i, (@inord n k <= i)%N. {
     move => k.
   clear - Hij Hin.
   change (@nat_of_ord (@nat_of_ord n.+1 i) k) with (@nat_of_ord n.+1 (widen_ord Hin k)).
   rewrite inord_val. simpl. apply /leP.
   move :(ltn_ord j) => /ltP Hj. move :(ltn_ord k) => /ltP. lia.
  }
  have Hinord: forall k: 'I_i, widen_ord Hin k = inord k.
     move => k;
     symmetry; change (@nat_of_ord (@nat_of_ord n.+1 i) k) with (@nat_of_ord n.+1 (widen_ord Hin k));
     apply inord_val.
*)
  pose widen1 := widen_ord (ltn_ord i).
  pose widen0 := widen_ord (ltnW (ltn_ord i)).
  unify widen0 (widen_ik i).
  have Hinord0: forall k: 'I_i, inord k = widen0 k. {
     move => k.
     change (@nat_of_ord (@nat_of_ord n.+1 i) k) with (@nat_of_ord n.+1 (widen0 k)).
     apply inord_val.
  }
  have Hinord1: forall k: 'I_i.+1, inord k = widen1 k. {
     move => k. 
     change (@nat_of_ord (S (@nat_of_ord n.+1 i)) k) with (@nat_of_ord n.+1 (widen1 k)).
     apply inord_val.
  }
  rewrite (_: [ffun k: 'I_i => Rt (inord k) i] = [ffun k => Rt (widen0 k) i]) in H *.
    2: by apply eq_ffun => k; rewrite Hinord0.
  rewrite (_: [ffun k: 'I_i => Rt (inord k) j] = [ffun k => Rt (widen0 k) j]) in H *.
    2: by apply eq_ffun => k; rewrite Hinord0.
  have CUT1 : \sum_k Rr^T i k * Rr k j = \sum_k [ffun k => Rr (widen1 k) i * Rr (widen1 k) j] k. {
  transitivity (\sum_k [ffun k => Rr k i * Rr k j] (widen1 k)).
 2: apply eq_big; auto; move => k _; rewrite !ffunE //.
  change (\sum_k Rr^T i k * Rr k j) with (\sum_(k<n.+1 | true) Rr^T i k * Rr k j) .
  rewrite -big_ord_narrow.
  pose f k := fun_of_matrix Rr^T i (inord k) * fun_of_matrix Rr (inord k) j.
  transitivity (\sum_(k < n.+1 | predT (nat_of_ord k)) f (nat_of_ord k)).
     apply eq_bigr; move => z _; by rewrite /f inord_val.
  rewrite -(big_mkord (fun _ => true)) /predT {}/f.
  transitivity (\sum_(0 <= i0 < n.+1 | (i0 < i.+1)%N) [ffun k => Rr k i * Rr k j] (inord i0)).
    2: rewrite big_mkord; apply eq_bigr; move => z _; by rewrite inord_val.
  rewrite !(big_cat_nat _ _ _ (leq0n i.+1) (ltn_ord i)) /=.
  f_equal.
  - rewrite big_nat.
    apply eq_big.
    + move => k; lia.
    + move => k Hk. rewrite ffunE mxE //.
  - rewrite big_nat.
    change (i.+1) with (O+i.+1)%nat.
    rewrite !big_addn !big_mkord /=.
    set ni := subn _ _.
    rewrite (eq_bigl (fun _ => true)).
    2: move => k; clear; move :(ltn_ord k) => /ltP; move:(ltn_ord i) => /ltP; lia.
    symmetry; rewrite (eq_bigl (fun _ => false)).
    2: move => k; clear; move :(ltn_ord k) => /ltP; move:(ltn_ord i) => /ltP; lia.
    rewrite big_pred0_eq.
    transitivity (\sum_(i0<ni) R0).
    2:{ apply eq_big. move => k; auto. move => k _.
      clear - Hij UT.
      move :UT => /is_trig_mxP UT. rewrite UT. rewrite mul0r //.
      rewrite inordK. lia.
      subst ni.
      apply /ltP. move :(ltn_ord k) => /ltP Hk. lia.
     }
     symmetry.
     apply big_rec => [//|k x _ ->]; rewrite GRing.addr0 //.
   }

  have H2_1 := @lemma_2_1 fs eta_neq_0 i
      [ffun k : 'I_i => RteF (widen0 k) i] [ffun k : 'I_i => RteF (widen0 k) j] 
      (A i j) (Rt i i) Rii_neq_0.
  rewrite mxE in CJIK.
  set Aij := A i j in H2_1 H CJIK *.
  rewrite {}CUT1 in CJIK.
  rewrite (_: \sum_k
              ((FS_val ([ffun k : 'I_i => (RteF (widen0 k) i)] k) *
               FS_val ([ffun k : 'I_i => (RteF (widen0 k) j)] k)))%Re = 
          \sum_(k: 'I_i) (Rt (widen0 k) i * Rt (widen0 k) j)%Re)  in H2_1 H.
  2:{ apply eq_big; auto; move => k _; rewrite !ffunE !mxE (_: (k<=j)%N=true).
      2: apply /leP; move :Hij => /ltP; move :(ltn_ord k) => /ltP; lia.
      rewrite (ltnW (ltn_ord _):  (k<=i)%N=true) //.
  }
(*  rewrite CJIK in H2_1.*)
  rewrite (_: [ffun k : 'I_i => RteF (widen0 k) i] =
              [ffun k : 'I_i => Rt (widen0 k) i]) in H2_1.
   2: by apply eq_ffun; move =>k; rewrite /RteF mxE /= (ltnW (ltn_ord _)).
  rewrite (_: [ffun k : 'I_i => RteF (widen0 k) j] =
              [ffun k : 'I_i => Rt (widen0 k) j]) in H2_1.
  2:{ apply eq_ffun; move =>k; rewrite /RteF mxE /= (_: (k<=j)%N=true) //.
      apply /leP. move :Hij => /ltP. move :(ltn_ord k) => /ltP; lia.
   }
  rewrite big_ord_recr in CJIK.
  simpl Rminus in CJIK.
  rewrite ffunE in CJIK.
  replace (widen1 ord_max) with i in CJIK. simpl in CJIK.
    2: clear; destruct i; compute; f_equal; apply proof_irr.
(*  rewrite H in H2_1.*)
  rewrite /ytilded in H2_1 H.
  set st := stilde _ _ _ in H2_1 H *.
  rewrite -{}H in H2_1.
  rewrite Rabs_minus_sym in H2_1. rewrite -Rminus_plus_distr in H2_1.
  rewrite (_: (\sum_(k < i) (FS_val (Rt (widen0 k) i) * Rt (widen0 k) j) + Rt i i * Rt i j)%Re
            = (\sum_(k<i.+1) (FS_val (Rt (widen1 k) i) * Rt (widen1 k) j))%Re) in H2_1.
  2:{ rewrite big_ord_recr.
      replace (widen1 ord_max) with i.
      2: clear; destruct i; compute; f_equal; apply proof_irr.
      simpl.
      apply Rplus_eq_compat_r.
      apply eq_big; auto; move => k _.
      f_equal; f_equal; f_equal;
       rewrite /widen1 /widen0 /widen_ord; f_equal; apply proof_irr.
  }
  rewrite (_: \sum_(k < i.+1) (Rt (inord k) i * Rt (inord k) j)%Re = 
                \sum_(k < i.+1) (Rt (widen1 k) i * Rt (widen1 k) j)%Re).
   2: by apply eq_big; auto; move => k _; rewrite Hinord1.
  eapply Rle_trans. apply Rlt_le. apply H2_1.
  clear H2_1 st CJIK.
  pattern (\sum_(k < i.+1) Rabs (Rte (inord k) i) * Rabs (Rte (inord k) j)).
  set (foo := (fun _ => _)).
  rewrite big_ord_recr;  simpl. subst foo; cbv beta.

Admitted.

End Cholesky.

