Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model spec_sparse spec_jacobi.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := JacobiASI ++ SparseASI ++ MathASI.

Lemma Zlength_jacobi_iter: 
  forall {t} A1 (A2: matrix t) b x, 
   Zlength A1 = matrix_rows A2 ->
   Zlength b = matrix_rows A2 ->
   Zlength x = matrix_rows A2 ->
   Zlength (jacobi_iter A1 A2 b x) = matrix_rows A2.
Proof.
   intros. 
   unfold jacobi_iter, diagmatrix_vector_mult,
        vector_sub, map2.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      unfold jacob_list_fun_model.matrix_vector_mult.
      rewrite Zlength_map. unfold matrix_rows in *. lia.
Qed.

Lemma norm2_snoc:
  forall {t} (al: vector t) (x: ftype t),
   norm2 (al ++ [x]) = BFMA x x (norm2 al).
 Proof.
  intros. unfold norm2, dotprod.
 rewrite combine_app by auto.
 rewrite fold_left_app. reflexivity.
 Qed.

Lemma BMULT_congr:
 forall {t} (x x' y y': ftype t), float_eqv x x' -> float_eqv y y' -> 
   float_eqv (BMULT t x y) (BMULT t x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor.
destruct H2,H1; subst. repeat proof_irr.
apply float_eqv_refl.
Qed.

Lemma BMINUS_congr:
 forall {t} (x x' y y': ftype t), float_eqv x x' -> float_eqv y y' -> 
   float_eqv (BMINUS t x y) (BMINUS t x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor;
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto;
 destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto.
Qed.

Lemma Znth_jacobi_iter {t}:
  forall i A1 A2 (b x: vector t) (y: ftype t),
  Zlength A1 = matrix_rows A2 -> 
  Zlength b = matrix_rows A2 -> 
  Zlength x = matrix_rows A2 -> 
  0 <= i < matrix_rows A2 ->
  float_eqv y (dotprod (Znth i A2) x) ->
  float_eqv (Znth i (jacobi_iter A1 A2 b x))
     (BMULT t (Znth i A1)
         (BMINUS t (Znth i b) y)).
Proof.
intros. unfold matrix_rows in *.
 unfold jacobi_iter, diagmatrix_vector_mult, vector_sub, map2,
   jacob_list_fun_model.matrix_vector_mult.
change jacob_list_fun_model.dotprod with (@dotprod t).
  rewrite Znth_map.
2:rewrite Zlength_combine, Zlength_map,
     Zlength_combine, Zlength_map; lia.
rewrite Znth_combine.
2:rewrite Zlength_map, Zlength_combine, Zlength_map; lia.
rewrite Znth_map.
2:rewrite Zlength_combine, Zlength_map; lia.
rewrite Znth_combine.
2:rewrite Zlength_map; lia.
rewrite Znth_map by lia.
unfold uncurry.
apply BMULT_congr; auto.
apply BMINUS_congr; auto.
symmetry.
auto.
Qed.

Lemma floatlist_eqv_rev:  forall {t} (x x': vector t),
 floatlist_eqv x x' -> floatlist_eqv (rev x) (rev x').
Proof.
induction 1.
constructor.
simpl.
apply Forall2_app; auto.
Qed.

Lemma strict_floatlist_eqv_rev:  forall {t} (x x': vector t),
 strict_floatlist_eqv x x' -> strict_floatlist_eqv (rev x) (rev x').
Proof.
induction 1.
constructor.
simpl.
apply Forall2_app; auto.
Qed.

Lemma dotprod_congr {t} (x x' y y' : vector t):
 strict_floatlist_eqv x x' ->
 strict_floatlist_eqv y y' ->
 length x = length y ->
 float_eqv (dotprod x y) (dotprod x' y').
Proof.
 intros.
 unfold dotprod.
 pose proof (Forall2_length H).
 pose proof (Forall2_length H0).
 rewrite <- !fold_left_rev_right.
 apply strict_floatlist_eqv_rev in H, H0.
 rewrite !rev_combine by lia.
 clear - H H0.
 set (a := rev x) in *; clearbody a. set (a' := rev x') in *; clearbody a'.
 set (b := rev y) in *; clearbody b. set (b' := rev y') in *; clearbody b'.
 revert b b' H0; induction H; simpl; intros; auto.
 inv H1. auto. simpl. apply BFMA_mor; auto.
Qed.


Lemma norm2_congr: 
  forall {t} (x x': vector t), strict_floatlist_eqv x x' -> 
           float_eqv (norm2 x) (norm2 x').
Proof.
intros.
apply dotprod_congr; auto.
Qed.

Lemma Znth_vector_sub:
 forall {t} i (x y: vector t) , Zlength x = Zlength y ->
   0 <= i < Zlength x ->
   Znth i (vector_sub x y) = BMINUS t (Znth i x) (Znth i y).
Proof.
intros.
unfold vector_sub, map2.
rewrite Znth_map by (rewrite Zlength_combine; lia).
rewrite Znth_combine by lia.
reflexivity.
Qed.

Lemma BFMA_xx_mor:
 forall {t} (x x' s s': ftype t), 
  float_eqv x x' -> 
  float_eqv s s' ->
  float_eqv (BFMA x x s) (BFMA x' x' s').
Proof.
intros.
red.
unfold BFMA.
destruct x,x'; inv H; simpl; auto;
 destruct s,s'; inv H0; simpl; auto;
repeat proof_irr; 
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto;
 destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto.
Qed.

Lemma vector_sub_congr: forall {t} (x x' y y': vector t),
  floatlist_eqv x x' -> floatlist_eqv y y' ->
  floatlist_eqv (vector_sub x y) (vector_sub x' y').
Proof.
induction x; destruct x'; intros; inv H.
constructor.
specialize (IHx x').
inv H0. constructor.
specialize (IHx _ _ H6 H1).
constructor; auto.
apply BMINUS_congr; auto.
Qed.

Lemma norm2_loose_congr: 
 forall {t} (x x': vector t),  floatlist_eqv x x' -> float_eqv (norm2 x) (norm2 x').
Proof.
intros.
unfold norm2.
unfold dotprod.
rewrite <- !fold_left_rev_right.
pose proof (Forall2_length H).
rewrite !rev_combine by auto.
clear H0.
apply floatlist_eqv_rev in H.
set (a := rev x) in *. clearbody a.
set (b := rev x') in *. clearbody b.
induction H.
constructor.
simpl.
apply BFMA_xx_mor; auto.
Qed.

Lemma strict_float_eqv_i1:
  forall {t} (x y: ftype t), 
    finite x -> float_eqv x y ->
    strict_float_eqv x y.
Proof.
 intros.
 red in H.
 destruct x; inv H;
 destruct y; inv H0. constructor. constructor; auto.
Qed.

Lemma body_jacobi2_oneiter: semax_body Vprog Gprog f_jacobi2_oneiter jacobi2_oneiter_spec.
Proof.
start_function.
forward_call.
forward.
pose (r := jacobi_iter A1 A2 b x).
set (N := matrix_rows A2) in *.
assert (0 <= N < Int.max_unsigned) by (unfold matrix_rows in N; rep_lia).
clear H0 H1; rename H6 into H0.
assert_PROP (Zlength A1 = N /\ Zlength b = N /\ Zlength x = N).
  entailer!. rewrite Zlength_map in *. auto. 
forward_for_simple_bound N
  (EX i:Z, EX y: vector Tdouble, EX s: ftype Tdouble,
   PROP (floatlist_eqv y (sublist 0 i r);
             float_eqv s (norm2 (sublist 0 i (vector_sub x r))))
   LOCAL (temp _s (Vfloat s);
       temp _N (Vint (Int.repr (matrix_rows A2))); 
       temp _A1inv A1p; temp _A2 A2p; temp _b bp; 
       temp _x xp; temp _y yp)
   SEP (crs_rep sh1 A2 A2p;
   data_at sh1 (tarray tdouble N) (map Vfloat A1) A1p;
   data_at sh1 (tarray tdouble N) (map Vfloat b) bp;
   data_at sh1 (tarray tdouble N) (map Vfloat x) xp;
   data_at sh2 (tarray tdouble N) (map Vfloat y ++ Zrepeat Vundef (N-i)) yp))%assert.
- Exists (@nil (ftype Tdouble)) (Zconst Tdouble 0). entailer!.
   rewrite sublist_nil. constructor. simpl app.
   apply derives_refl.
- forward_call (sh1,sh1,sh2, A2p, A2, xp, x, i).
   replace (Zlength x) with N by (clear - H1; lia).  cancel.
   replace (Zlength x) with N by (clear - H1; lia).  auto.
   replace (Zlength x) with N by (clear - H1; lia).
   Intros y'.
   forward. 
   progress change float with (ftype Tdouble) in *.
   rewrite Znth_map by lia.
   forward.
       entailer!. rewrite Znth_map by lia. hnf; auto.
   rewrite Znth_map by lia.
   forward.
   forward.
       entailer!. rewrite Znth_map by lia. hnf; auto.
   rewrite Znth_map by lia.
   forward.
   forward_call.
   forward.
   autorewrite with float_elim in *.
   pose proof (Zlength_jacobi_iter A1 A2 b x ltac:(lia) ltac:(lia) ltac:(lia)).
   fold r in H10.
  change (Binary.Bfma _ _ _ _ _ _ ?x ?y ?z) with (BFMA x y z).
   Exists (y ++ [Znth i A1 * (Znth i b - y')]%F64).
   EExists.
   entailer!.
 + 
  set (N := matrix_rows A2) in *.
  assert (Zlength (vector_sub x r) = N). {
     unfold vector_sub, map2. rewrite Zlength_map, Zlength_combine. lia.
  } 
  rewrite !(sublist_split 0 i (i+1)) by lia.
  rewrite !sublist_len_1 by lia.
  split.
  * apply Forall2_app; auto.
     constructor; [ | constructor].
     symmetry; eapply Znth_jacobi_iter; eauto; lia.
  *
    rewrite norm2_snoc.
    clear - H8 H9 H5 H2 H3 H4 H H1 H6 H10 .
    destruct H1 as [? [? ?]].
    rewrite Znth_vector_sub by lia.
    apply BFMA_xx_mor; auto.
    apply BMINUS_congr; auto.
    subst r.
   erewrite Znth_jacobi_iter; eauto.
 +
   apply derives_refl'; f_equal.
   clear - H10 H6 H1 H0 H21.  list_solve.
-
 Intros y s. forward. Exists y s.
 rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
 unfold crs_rep. Intros.
 entailer!.
 pose proof (Zlength_jacobi_iter A1 A2 b x ltac:(lia) ltac:(lia) ltac:(lia)).
 fold r in H22|-*. 
  set (N := matrix_rows A2) in *.
  assert (Zlength (vector_sub x r) = N). {
     unfold vector_sub, map2. rewrite Zlength_map, Zlength_combine. lia.
  } 
 rewrite sublist_same in H6,H7 by lia.
 split; auto.
 rewrite H7.
 clearbody r. clearbody N.
 destruct H1 as [_ [_ ?]].
 clear - H22 H6 H5 H1.
 apply norm2_loose_congr.
 apply vector_sub_congr; auto.
 clear - H5. induction H5; constructor; auto.
 clear - H6. induction H6; constructor; auto.
 symmetry; auto.
Qed.

