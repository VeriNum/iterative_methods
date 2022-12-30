Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Ltac entbangbang :=
 intros;
 try lazymatch goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try lazymatch goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 lazymatch goal with
 | |- local _ && ?P |-- _ => clean_up_stackframe; go_lower;
          rewrite ?TT_andp, ?andp_TT; try apply TT_right
 | |- ?P |-- _ =>
    lazymatch type of P with
    | ?T => tryif unify T (environ->mpred)
                 then fail "entailer! found an (environ->mpred) entailment that is missing its 'local' left-hand-side part (that is, Delta)"
                 else tryif unify T mpred
                    then (clear_Delta; pull_out_props)
                    else fail "Unexpected type of entailment, neither mpred nor environ->mpred"
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ |-- _ "
 end;
 repeat lazymatch goal with
        | |- context [force_val (sem_binary_operation' ?op ?t1 ?t2 ?v1 ?v2)] =>
          progress 
              simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
                (force_val (sem_binary_operation' op t1 t2 v1 v2))
        end;
 simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
        sem_cast;
 (*saturate_local; *)
 ent_iter;
 repeat change (mapsto_memory_block.spacer _ _ _ _) with emp;
 first [ contradiction
        | simple apply prop_right; my_auto
        | lazymatch goal with |- ?Q |-- !! _ && ?Q' => constr_eq  Q Q';
                      simple apply prop_and_same_derives'; my_auto
          end
        | simple apply andp_right;
            [apply prop_right; my_auto 
            | cancel; rewrite <- ?sepcon_assoc; autorewrite with norm ]
        | normalize; cancel; rewrite <- ?sepcon_assoc
        ].

Tactic Notation "entailer" "!!" := entbangbang.

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
     (BMULT t (Znth i A1)
         (BMINUS t (Znth i b) y)).
Proof.
intros. unfold matrix_rows in *.
 unfold jacobi_iter, diagmatrix_vector_mult, vector_sub, map2,
   matrix_vector_mult.
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


Lemma matrix_by_index_prop:
 forall {t} (f: nat -> nat -> ftype t) (P: ftype t -> Prop) rows cols,
  P (Zconst t 0) ->
  (forall i j, (i < rows)%nat -> (j < cols)%nat -> P (f i j)) ->
  Forall (Forall P) (matrix_by_index rows cols f).
Proof.
intros.
unfold matrix_by_index.
apply Forall_nth; intros.
rewrite map_length, seq_length in H1.
rewrite nth_map_seq by auto.
apply Forall_nth; intros.
rewrite map_length, seq_length in H2.
rewrite nth_map_seq by auto.
apply H0; auto.
Qed.

Lemma Zmatrix_cols_nat: 
 forall {t} (m: matrix t) cols,
  matrix_cols_nat m cols  <-> matrix_cols m (Z.of_nat cols).
Proof.
induction m; simpl; intros; split; intro; inv H; constructor; auto.
apply Zlength_correct.
clear - H3.
induction H3; constructor; auto. rewrite <- H; apply Zlength_correct.
rewrite Zlength_correct in H2. lia.
clear - H3.
induction H3; constructor; auto. rewrite Zlength_correct in H; lia.
Qed.

Lemma Zlength_seq: forall lo n, Zlength (seq lo n) = Z.of_nat n.
Proof.
intros. rewrite Zlength_correct. f_equal. apply seq_length.
Qed.
#[export] Hint Rewrite Zlength_seq : sublist rep_lia.

Lemma Zmatrix_rows_nat: forall {t} (m: matrix t), Z.of_nat (matrix_rows_nat m) = matrix_rows m.
Proof.
unfold matrix_rows.
induction m; simpl; auto. list_solve.
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

Add Parametric Morphism {t: type}: (@norm2 t)
  with signature Forall2 feq ==> feq
 as norm2_mor.
Proof.
exact norm2_congr.
Qed.

Add Parametric Morphism {t: type}: (@vector_sub t)
  with signature Forall2 feq ==> Forall2 feq ==> Forall2 feq
  as vector_sub_mor.
Proof.
intros; eapply vector_sub_congr; eauto.
Qed.

Add Parametric Morphism {T: Type} (rel: relation T): (@Zlength T)
  with signature Forall2 rel ==> eq
  as Zlength_mor.
Proof.
induction 1; auto.
rewrite !Zlength_cons; f_equal; auto.
Qed.

Add Parametric Morphism {t: type}: (@finite t)
  with signature feq ==> iff
  as finite_rel.
Proof.
destruct x,y; split; intros; inv H0; inv H; constructor; auto.
Qed.

Lemma jacobi_iter_congr: 
 forall {t} A1 A2 (b: vector t) x x',
  Forall2 strict_feq x x' ->
  Forall finite A1 ->
  Forall (Forall finite) A2 ->
  Forall finite b ->  
   Zlength b = matrix_rows A2 ->
   Zlength A1 = matrix_rows A2 ->
   matrix_cols A2 (Zlength x) ->
   Forall2 feq (jacobi_iter A1 A2 b x) (jacobi_iter A1 A2 b x') .
Proof.
intros.
unfold jacobi_iter.
unfold diagmatrix_vector_mult.
unfold map2.
apply Forall2_map.
rewrite <- Zmatrix_rows_nat in *.
rewrite Zlength_correct in *.
apply Zmatrix_cols_nat in H5.
apply Nat2Z.inj in H3,H4.
unfold matrix_rows_nat in *.
revert A1 A2 H0 H1 H3 H4 H5; induction H2; 
   destruct A1 as [|A1r A1]; destruct A2 as [|A2r A2]; intros;
  try inv H0; try inv H1; try inv H3; try inv H4; constructor; auto;
   inv H5; inv H6.
-
unfold uncurry.
 apply BMULT_congr; auto.
 apply BMINUS_congr; auto.
 apply dotprod_congr; auto.
-
 apply IHForall; auto.
Qed.

Lemma strict_floatlist_eqv_i1: 
   forall {t} (a b: list (ftype t)),
    Forall finite a -> Forall2 feq a b -> Forall2 strict_feq a b.
Proof.
induction 2; inv H;constructor.
apply strict_feq_i1; auto.
apply IHForall2; auto.
Qed.

Lemma finite_is_finite: forall {t} (x: ftype t),
   finite x <-> Binary.is_finite _ _ x = true.
Proof.
split; intros;
destruct x; inv H; try reflexivity.
constructor; auto.
Qed.

Lemma feq_strict_feq:
 forall {t} (x y: ftype t),
   finite x -> feq x y -> strict_feq x y.
Proof.
 intros.
 destruct x; inv H; destruct y; inv H0; constructor; auto.
Qed.

Lemma strict_feq_finite1:
  forall {t} (x y: ftype t),
    strict_feq x y -> finite x.
Proof.
intros.
destruct x,y; inv H; constructor; auto.
Qed.

Lemma finite_dotprod_e: forall {t} (x y: vector t),
  Zlength x = Zlength y ->
  finite (dotprod x y) -> Forall finite x /\ Forall finite y.
Proof.
intros.
rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
unfold dotprod in H0.
rewrite <- fold_left_rev_right in H0.
rewrite rev_combine in H0 by auto.
rewrite <- (rev_length x), <- (rev_length y) in H.
assert (Forall finite (rev x) /\ Forall finite (rev y)).
2:rewrite <- (rev_involutive x), <- (rev_involutive y);
   destruct H1; split; apply Forall_rev; auto.
forget (rev x) as a; forget (rev y) as b.
revert b H H0; induction a; destruct b; intros; inv H.
split; constructor.
specialize (IHa _ H2).
simpl in H0.
set (u := fold_right _ _ _) in *. clearbody u.
assert (finite a /\ finite f /\ finite u); [ | split; constructor; tauto].
clear - H0.
apply finite_is_finite in H0.
destruct a,f,u; inv H0; try solve [split3; constructor; auto].
destruct s,s0,s1; inv H1.
destruct s,s0,s1; inv H1.
destruct s,s0,s1; inv H1.
Qed.


Lemma finite_norm2_e: forall {t} (x: vector t),
  finite (norm2 x) -> Forall finite x.
Proof.
intros.
apply finite_dotprod_e in H; auto.
destruct H; auto.
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

Add Parametric Morphism {t: type} : (Binary.is_finite (fprec t) (femax t))
  with signature feq ==> eq
  as is_finite_mor.
Proof.
intros.
destruct x, y; inv H; reflexivity.
Qed.

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
   change (@iter_stop ?t _  ?dist2 ?f (S ?n) ?acc ?x) with
        (if stop (dist2 x (f x)) acc
           then iter_stop dist2 f n acc (f x) else (dist2 x (f x), (f x))).

Lemma strict_floatlist_eqv_unstrict:
   forall {t} (x y: vector t), Forall2 strict_feq x y -> Forall2 feq x y.
Proof.
induction 1; constructor; auto.
apply subrelation_strict_feq; auto.
Qed.

Add Parametric Morphism {t}: (BCMP t) 
 with signature eq ==> eq ==> strict_feq ==> strict_feq ==> eq
 as BCMP_mor.
Proof.
intros.
destruct x,y1; inv H; destruct x0,y2; inv H0; simpl.
destruct y,s,s0,s1,s2;simpl; auto.
destruct H1; subst.
proof_irr.
destruct y0,s,s0,s2; simpl; auto.
destruct H2; subst.
proof_irr.
destruct y0,s,s0,s1; simpl; auto.
destruct H1,H2; subst.
repeat proof_irr.
destruct y0,s0,s1; simpl; auto.
Qed.

Lemma iter_stop_congr {t}:
 forall f acc (FINacc: finite acc) n (z z': vector t),
 (forall x, Zlength x = Zlength z -> Zlength (f x) = Zlength x) ->
 (forall x x': vector t, Zlength x = Zlength z -> Forall2 strict_feq x x' -> Forall2 feq (f x) (f x')) ->
 Forall2 strict_feq z z' ->
 Forall2 feq (snd (iter_stop dist2 f n acc z))
    (snd (iter_stop dist2 f n acc z')).
Proof.
induction n; simpl; intros.
apply H0;auto.
assert (feq (dist2 z (f z))  (dist2 z' (f z'))).
apply dist2_mor; auto.
apply strict_floatlist_eqv_unstrict; auto.
replace  (Binary.is_finite (fprec t) (femax t) (dist2 z' (f z')))
  with (Binary.is_finite (fprec t) (femax t) (dist2 z (f z)))
  by (rewrite H2; auto).
destruct (Binary.is_finite _ _ _) eqn:?H.
simpl.
apply finite_is_finite in H3.
replace (BCMP t Gt true (dist2 z' (f z')) acc) with (BCMP t Gt true (dist2 z (f z)) acc)
  by (apply BCMP_mor; auto; apply strict_feq_i1; auto).
destruct (BCMP _ _ _ _ _).
apply IHn.
intros; auto. rewrite H in H4; auto. 
intros; apply H0; auto. rewrite H in H4; auto.
apply strict_floatlist_eqv_i1; auto.
apply finite_dist2_e2 in H3; auto.
symmetry; apply H; auto.
simpl snd. apply H0; auto.
simpl.
apply H0; auto.
Qed.

Fixpoint iter_stop_n {t} {A} (dist2: A -> A -> ftype t) (f : A -> A) (n: nat) (acc: ftype t) (x: A) :=
   match n with
 | O => Some x
 | S n' => match iter_stop_n dist2 f n' acc x
                  with Some y => 
                         let s := dist2 y (f y) in
                          if (Binary.is_finite _ _ s && BCMP t Gt true s acc )%bool
                          then Some (f y)
                          else None
                 | None => None
               end
  end.

Fixpoint iter_stop_n_alt {t} {A} (dist2: A -> A -> ftype t) (f : A -> A) (n: nat) (acc: ftype t) (x: A) :=
   match n with
 | O => Some x
 | S n' => let s := dist2 x (f x) in
                if (Binary.is_finite _ _ s && BCMP t Gt true s acc )%bool
                then iter_stop_n_alt dist2 f n' acc (f x)
                else None
  end.

Lemma iter_stop_n_eq_alt: @iter_stop_n = @iter_stop_n_alt.
Proof.
extensionality t A.
extensionality dist2 f.
extensionality n acc x.
revert x; induction n; intros; simpl; auto.
rewrite IHn; clear IHn.
revert x; induction n; intros;simpl.
auto.
destruct (andb _ _) eqn:?H; auto.
Qed.

Lemma iter_stop_n_lem1:
  forall t A dist2 (f: A->A) (acc: ftype t) k n x y, 
   iter_stop_n dist2 f n acc x = Some y ->
   (Binary.is_finite _ _ (dist2 y (f y)) && BCMP t Gt true (dist2 y (f y)) acc)%bool = false ->
   iter_stop dist2 f (n+k) acc x = (dist2 y (f y), f y).
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
  forall t A dist2 (f: A->A) (acc: ftype t) n x y, 
   iter_stop_n dist2 f n acc x = Some y ->
   (Binary.is_finite _ _ (dist2 y (f y)) && BCMP t Gt true (dist2 y (f y)) acc)%bool = true ->
   iter_stop dist2 f n acc x = (dist2 y (f y), f y).
Proof.
rewrite iter_stop_n_eq_alt.
induction n; simpl; intros; auto.
inv H; auto.
destruct (andb _ _) eqn:J in H; try discriminate.
rewrite J.
apply IHn; auto.
Qed.  

Lemma iter_stop_n_Zlength:
 forall {t} f N n acc x v
    (LENf: forall x, Zlength x = N -> Zlength (f x) = Zlength x)
    (CONGR_f: forall x x' : list (ftype t),
          Zlength x = N ->
          Forall2 strict_feq x x' -> Forall2 feq (f x) (f x')),
    Zlength x = N -> Forall finite x ->
    iter_stop_n dist2 f n acc x = Some v ->
    Zlength v = N.
Proof.
intros.
rewrite iter_stop_n_eq_alt in H1.
revert x H H0 H1; induction n; simpl; intros.
inv H1; auto.
destruct (andb _ _) eqn:?H in H1; try discriminate.
rewrite andb_true_iff in H2. destruct H2.
apply finite_is_finite in H2.
apply finite_dist2_e2 in H2.
apply IHn in H1; auto.
rewrite LENf; auto.
rewrite LENf; auto.
Qed.

