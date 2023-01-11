Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Lemma Zlength_jacobi_iter: 
  forall {t} A1 (A2: matrix t) b x, 
   Zlength A1 = matrix_rows A2 ->
   Zlength b = matrix_rows A2 ->
   Zlength x = matrix_rows A2 ->
   Zlength (jacobi_iter A1 A2 b x) = matrix_rows A2.
Proof.
   intros. 
   unfold jacobi_iter, diagmatrix_vector_mult,
        vector_sub, map2, invert_diagmatrix.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      rewrite !Zlength_map.
      rewrite Zlength_combine.
      unfold matrix_vector_mult.
      rewrite Zlength_map. unfold matrix_rows in *. lia.
Qed.

Lemma Znth_jacobi_iter {t}:
  forall i A1 A2 (b x: vector t) (y: ftype t),
  Zlength A1 = matrix_rows A2 -> 
  Zlength b = matrix_rows A2 -> 
  Zlength x = matrix_rows A2 -> 
  0 <= i < matrix_rows A2 ->
  feq y (dotprod (Znth i A2) x) ->
  feq (Znth i (jacobi_iter A1 A2 b x))
     (BMULT t (BDIV t (Zconst t 1) (Znth i A1))
         (BMINUS t (Znth i b) y)).
Proof.
intros. unfold matrix_rows in *.
 unfold jacobi_iter, diagmatrix_vector_mult, vector_sub, map2,
   matrix_vector_mult, invert_diagmatrix.
  rewrite Znth_map.
2:rewrite Zlength_combine, !Zlength_map,
     Zlength_combine, Zlength_map; lia.
rewrite Znth_combine.
2:rewrite !Zlength_map, Zlength_combine, Zlength_map; lia.
rewrite Znth_map by lia.
rewrite Znth_map
 by (rewrite Zlength_combine, Zlength_map; lia).
rewrite Znth_combine by (rewrite Zlength_map; lia).
rewrite Znth_map by lia.
unfold uncurry.
apply BMULT_congr; auto.
apply BMINUS_congr; auto.
symmetry.
auto.
Qed.

Lemma matrix_cols_remove_diag:
  forall {t} (m: matrix t), matrix_cols m (matrix_rows m) ->
    matrix_cols (remove_diag m) (matrix_rows m).
Proof.
 unfold remove_diag. intros.
 rewrite <- Zmatrix_rows_nat.
 rewrite <- Zmatrix_cols_nat.
 apply matrix_by_index_cols.
Qed.

Lemma finite_remove_diag:
 forall {t} (m: matrix t),
   matrix_cols m (matrix_rows m) ->
   Forall (Forall finite) m ->
   Forall (Forall finite) (remove_diag m).
Proof.
intros.
 apply matrix_by_index_prop.
 constructor.
 intros.
 if_tac. constructor.
 eapply matrix_index_prop; eauto.
 rewrite <- Zmatrix_rows_nat in H.
 rewrite <- Zmatrix_cols_nat in H.
 auto.
Qed.

Lemma matrix_rows_remove_diag: forall {t} (m: matrix t), 
     matrix_rows (remove_diag m) = matrix_rows m.
Proof.
intros.
rewrite <- !Zmatrix_rows_nat.
f_equal.
apply matrix_by_index_rows.
Qed.

#[export] Hint Rewrite @Zmatrix_rows_nat : sublist rep_lia.

Add Parametric Morphism {t}: (@diagmatrix_vector_mult _ t)
  with signature Forall2 feq ==> Forall2 feq ==> Forall2 feq 
 as diagmatrix_vector_mult_mor.
Proof.
intros.
unfold diagmatrix_vector_mult.
apply Forall2_map.
revert x0 y0 H0; induction H; simpl; intros; auto.
destruct x0,y0; inv H1; simpl; intros; auto.
constructor; auto.
unfold uncurry.
apply BMULT_congr; auto.
Qed.

Add Parametric Morphism {t}:  (@jacobi_iter _ t)
 with signature Forall2 strict_feq ==> Forall2 (Forall2 feq) 
       ==> Forall2 feq ==> Forall2 feq ==> Forall2 feq
  as jacobi_iter_mor.
Proof.
unfold jacobi_iter; intros.
apply diagmatrix_vector_mult_mor.
unfold invert_diagmatrix.
apply Forall2_map.
clear - H.
eapply Forall2_impl; try apply H; intros.
apply BDIV_mor; auto.
apply vector_sub_mor; auto.
apply matrix_vector_mult_mor; auto.
Qed.

Add Parametric Morphism {t}:  (@jacobi_residual _ t)
 with signature Forall2 strict_feq ==> Forall2 (Forall2 feq) 
       ==> Forall2 feq ==> Forall2 feq ==> Forall2 feq
  as jacobi_residual_mor.
Proof.
unfold jacobi_residual; intros.
apply diagmatrix_vector_mult_mor; auto.
eapply Forall2_impl. apply subrelation_strict_feq. auto.
apply vector_sub_mor; auto.
apply jacobi_iter_mor; auto.
Qed.

Lemma finite_dist2_e2: 
  forall {t} (x y: vector t), 
  Zlength x = Zlength y ->
  finite (dist2 x y) -> 
  Forall finite y.
Proof.
  intros.
   unfold dist2.
   apply finite_norm2_e in H0.
   rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
   revert y H H0; induction x; destruct y; simpl; intros; 
     inv H; inv H0; constructor; auto.
   clear - H3.
   rewrite finite_is_finite in H3.
   destruct a, f; inv H3; try constructor; auto.
   destruct s,s0; inv H0.
Qed.

Lemma Zlength_diag_of_matrix: 
    forall {t} (A: matrix t), Zlength (diag_of_matrix A) = matrix_rows A.
Proof.
intros.
unfold diag_of_matrix.
rewrite Zlength_map.
unfold matrix_rows, matrix_rows_nat.
rewrite !Zlength_correct, seq_length.
auto.
Qed.

Definition stop {t} (s acc: ftype t) := 
   andb (Binary.is_finite (fprec t) (femax t) s) (BCMP _ Gt true s acc).

Add Parametric Morphism {t: type} : (@dist2 t)
  with signature Forall2 feq ==> Forall2 feq ==> feq
  as dist2_mor.
Proof.
intros.
unfold dist2.
rewrite H, H0. auto.
Qed.

Add Parametric Morphism {t} : (@stop t)
  with signature feq ==> strict_feq ==> eq
  as stop_mor.
Proof.
 intros.
destruct x,y; inv H; simpl; auto.
destruct x0,y0; inv H0; simpl; auto.
destruct H2; subst; auto.
proof_irr.
destruct x0,y0; inv H0;  auto.
destruct H1; subst; auto.
Qed.

Ltac iter_stop_S :=
   change (@iter_stop ?t _  ?norm2 ?res ?f (S ?n) ?acc ?x) with
        (if stop (norm2 (res x)) acc
           then iter_stop norm2 res f n acc (f x) else (norm2 (res x), (f x))).

Lemma iter_stop_congr {t}:
 forall (norm2: vector t -> ftype t) residual f acc (FINacc: finite acc) n (z z': vector t),
   Proper (Forall2 feq ==> feq) norm2 ->
   Proper (Forall2 feq ==> Forall2 feq) residual ->
   Proper (Forall2 feq ==> Forall2 feq) f ->
 Forall2 feq z z' ->
 Forall2 feq (snd (iter_stop norm2 residual f n acc z))
    (snd (iter_stop norm2 residual f n acc z')).
Proof.
induction n; simpl; intros.
apply H1;auto.
assert (feq (norm2 (residual z)) (norm2 (residual z'))).
apply H; apply H0; auto.
replace  (Binary.is_finite (fprec t) (femax t) (norm2 (residual z')))
  with (Binary.is_finite (fprec t) (femax t) (norm2 (residual z)))
  by (rewrite H3; auto).
destruct (Binary.is_finite _ _ _) eqn:?H.
simpl.
apply finite_is_finite in H4.
replace (BCMP t Gt true (norm2 (residual z')) acc) 
     with (BCMP t Gt true (norm2 (residual z)) acc)
  by (apply BCMP_mor; auto; apply strict_feq_i1; auto).
destruct (BCMP _ _ _ _ _).
apply IHn; auto.
simpl; auto.
simpl.
apply H1; auto.
Qed.

Fixpoint iter_stop_n {t} {A} (norm2: A -> ftype t) (residual: A -> A) (f : A -> A) (n: nat) (acc: ftype t) (x: A) :=
   match n with
 | O => Some x
 | S n' => match iter_stop_n norm2 residual f n' acc x
                  with Some y => 
                         let s := norm2 (residual y) in
                          if (Binary.is_finite _ _ s && BCMP t Gt true s acc )%bool
                          then Some (f y)
                          else None
                 | None => None
               end
  end.

Fixpoint iter_stop_n_alt {t} {A} (norm2: A -> ftype t) (residual: A -> A) (f : A -> A) (n: nat) (acc: ftype t) (x: A) :=
   match n with
 | O => Some x
 | S n' => let s := norm2 (residual x) in
                if (Binary.is_finite _ _ s && BCMP t Gt true s acc )%bool
                then iter_stop_n_alt norm2 residual f n' acc (f x)
                else None
  end.

Lemma iter_stop_n_eq_alt: @iter_stop_n = @iter_stop_n_alt.
Proof.
extensionality t A.
extensionality norm2 residual f.
extensionality n acc x.
revert x; induction n; intros; simpl; auto.
rewrite IHn; clear IHn.
revert x; induction n; intros;simpl.
auto.
destruct (andb _ _) eqn:?H; auto.
Qed.

Lemma iter_stop_n_lem1:
  forall t A norm2 (residual: A -> A) (f: A->A) (acc: ftype t) k n x y, 
   iter_stop_n norm2 residual f n acc x = Some y ->
   (Binary.is_finite _ _ (norm2 (residual y)) && BCMP t Gt true (norm2 (residual y)) acc)%bool = false ->
   iter_stop norm2 residual f (n+k) acc x = (norm2 (residual y), f y).
Proof.
rewrite iter_stop_n_eq_alt.
induction n; simpl; intros; auto.
inv H; auto.
destruct k; auto. simpl. rewrite H0. auto.
destruct (andb _ _) eqn:J in H; try discriminate.
rewrite J.
apply IHn; auto.
Qed.  

Lemma iter_stop_n_lem2: 
  forall t A norm2 residual (f: A->A) (acc: ftype t) n x y, 
   iter_stop_n norm2 residual f n acc x = Some y ->
   (Binary.is_finite _ _ (norm2 (residual y)) && BCMP t Gt true (norm2 (residual y)) acc)%bool = true ->
   iter_stop norm2 residual f n acc x = (norm2 (residual y), f y).
Proof.
rewrite iter_stop_n_eq_alt.
induction n; simpl; intros; auto.
inv H; auto.
destruct (andb _ _) eqn:J in H; try discriminate.
rewrite J.
apply IHn; auto.
Qed.  

Lemma iter_stop_n_Zlength:
 forall {t} residual f N n acc x v
    (LENf: forall x, Zlength x = N -> Zlength (f x) = Zlength x)
    (CONGR_f: forall x x' : list (ftype t),
          Zlength x = N ->
          Forall2 strict_feq x x' -> Forall2 feq (f x) (f x'))
    (FINRES: forall x, Zlength x = N -> Forall finite (residual x) -> Forall finite (f x)),
    Zlength x = N -> Forall finite x ->
    iter_stop_n norm2 residual f n acc x = Some v ->
    Zlength v = N.
Proof.
intros.
rewrite iter_stop_n_eq_alt in H1.
revert x H H0 H1; induction n; simpl; intros.
inv H1; auto.
destruct (andb _ _) eqn:?H in H1; try discriminate.
rewrite andb_true_iff in H2. destruct H2.
apply finite_is_finite in H2.
apply finite_norm2_e in H2.
apply IHn in H1; auto.
rewrite LENf; auto.
Qed.

Lemma finres_jacobi {t}: forall A1 A2 b (x: vector t),
   Zlength A1 = Zlength x ->
   Zlength (jacobi_iter A1 A2 b x) = Zlength x ->
   Forall finite (jacobi_residual A1 A2 b x) ->
   Forall finite (jacobi_iter A1 A2 b x).
Proof.
intros.
unfold jacobi_residual in *.
set (y := jacobi_iter _ _ _ _) in *. clearbody y.
unfold diagmatrix_vector_mult, vector_sub in H1.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H, H0.
revert A1 y H H0 H1; induction x; destruct A1,y; intros; inv H; inv H0; inv H1; 
  constructor; auto.
-
clear - H4.
assert (finite (BMINUS t f0 a))
  by (destruct f, (BMINUS t f0 a); try contradiction H4; simpl; auto).
clear H4.
destruct f0,a; try destruct s; try destruct s0; try contradiction H; simpl; auto.
-
apply (IHx _ _ H3 H2 H5).
Qed.

Lemma Zlength_jacobi_residual: 
  forall {t} A1 (A2: matrix t) b x, 
   Zlength A1 = matrix_rows A2 ->
   Zlength b = matrix_rows A2 ->
   Zlength x = matrix_rows A2 ->
   Zlength (jacobi_residual A1 A2 b x) = matrix_rows A2.
Proof.
   intros. 
   unfold jacobi_residual, diagmatrix_vector_mult,
        vector_sub, map2.
      rewrite Zlength_map.
      rewrite Zlength_combine.
      rewrite !Zlength_map.
      rewrite Zlength_combine.
      rewrite Zlength_jacobi_iter by auto. lia.
Qed.

Lemma diag_of_matrix_prop:
  forall {t} (P: ftype t -> Prop) (A: matrix t), 
      matrix_cols A (matrix_rows A) ->
      Forall (Forall P) A -> Forall P (diag_of_matrix A).
Proof.
intros.
unfold diag_of_matrix.
apply Forall_map, Forall_seq.
intros. red.
assert (0 <= matrix_rows A).
unfold matrix_rows in *. rep_lia.
rewrite <- Z2Nat.id in H by lia.
apply Zmatrix_cols_nat in H.
eapply matrix_index_prop. eauto. auto. lia.
rewrite <- Zmatrix_rows_nat. lia.
Qed.



