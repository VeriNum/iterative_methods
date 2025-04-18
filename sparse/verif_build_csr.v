Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import build_csr sparse_model spec_sparse spec_build_csr distinct.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := Build_CSR_ASI ++ SparseASI ++ MathASI.

Lemma coo_wellformed_e {t} [coo: coo_matrix t]:
  coo_matrix_wellformed coo ->
  forall i, 
  0 <= i < Zlength (coo_entries coo) ->
  0 <= fst (fst (Znth i (coo_entries coo))) < coo_rows coo /\
  0 <= snd (fst (Znth i (coo_entries coo))) < coo_cols coo.
Proof.
intros.
destruct H as [_ H].
eapply Forall_forall in H.
apply H.
apply Znth_In; auto.
Qed.

Lemma fold_coo_rep:
  forall sh (coo: coo_matrix Tdouble) p (maxn: Z) (rp cp vp : val), 
  !! (0 <= Zlength (coo_entries coo) <= maxn /\ maxn <= Int.max_signed 
     /\ 0 <= coo_rows coo < Int.max_signed 
     /\ 0 <= coo_cols coo < Int.max_signed /\ coo_matrix_wellformed coo) &&
  data_at sh t_coo (rp, (cp, (vp, (Vint (Int.repr (Zlength (coo_entries coo))), (Vint (Int.repr maxn), 
                     (Vint (Int.repr (coo_rows coo)), 
                     (Vint (Int.repr (coo_cols coo))))))))) p *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (fst (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) rp *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (snd (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) cp *
  data_at sh (tarray tdouble maxn)
    (map (fun e => Vfloat (snd e)) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) vp
 |-- coo_rep sh coo p.
Proof. intros. unfold coo_rep. Exists maxn rp cp vp. entailer!!. Qed.

Lemma fold_csr_rep': forall sh (csr: csr_matrix Tdouble) (v: val) (ci: val) (rp: val) (p: val),
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp
  |-- csr_rep' sh csr v ci rp p.
Proof. intros. unfold csr_rep'. cancel. Qed.


Lemma coo_to_matrix_equiv:
  forall {t} (m: matrix t) (coo coo': coo_matrix t),
    coo_matrix_equiv coo coo' -> coo_to_matrix coo m -> coo_to_matrix coo' m.
Proof.
intros.
destruct H0 as [? [? ?]].
destruct H as [? [? ?]].
split3; try congruence.
intros.
rewrite <- H in H5. rewrite <- H3 in H6.
specialize (H2 i H5 j H6).
econstructor 4; try apply H2.
apply Permutation_map.
apply Permutation_filter.
auto.
Qed.

Lemma coo_matrix_equiv_refl:
  forall {t} (a : coo_matrix t), coo_matrix_equiv a a.
Proof.
intros.
split3; auto.
Qed.

Lemma coo_matrix_equiv_symm:
  forall {t} (a b : coo_matrix t), coo_matrix_equiv a b -> coo_matrix_equiv b a.
Proof.
intros.
destruct H as [? [? ?]].
split3; auto.
apply Permutation_sym; auto.
Qed.

Lemma coo_matrix_equiv_trans:
  forall {t} (a b c : coo_matrix t), coo_matrix_equiv a b -> coo_matrix_equiv b c -> coo_matrix_equiv a c.
Proof.
intros.
destruct H as [? [? ?]], H0 as [? [? ?]].
split3; try congruence.
eapply Permutation_trans; eassumption.
Qed.

Definition coo_upto (i: Z) {t} (coo: coo_matrix t) :=
  Build_coo_matrix _ (coo_rows coo) (coo_cols coo) (sublist 0 i (coo_entries coo)).

Definition cde_upto (i: Z) {t} (coo: coo_matrix t) : Z :=
   count_distinct (sublist 0 i (coo_entries coo)).

Definition CSR_entry_exists {t} (csr: csr_matrix t) (i j: Z) : Prop :=
  In j (sublist (Znth i (csr_row_ptr csr)) (Znth (i+1) (csr_row_ptr csr)) (csr_col_ind csr)).


Inductive csr_matrix_wellformed {t} (csr: csr_matrix t) : Prop :=
 build_csr_matrix_wellformed:
 forall (CSR_wf_rows: 0 <= csr_rows csr)
        (CSR_wf_cols: 0 <= csr_cols csr)
        (CSR_wf_vals: Zlength (csr_vals csr) = Zlength (csr_col_ind csr))
        (CSR_wf_vals': Zlength (csr_vals csr) = Znth (csr_rows csr) (csr_row_ptr csr))
        (CSR_wf_sorted: list_solver.sorted Z.le (0 :: csr_row_ptr csr ++ [Int.max_unsigned]))
        (CSR_wf_rowsorted: forall r, 0 <= r < csr_rows csr -> 
              sorted Z.lt 
                (-1 :: sublist (Znth r (csr_row_ptr csr)) (Znth (r+1) (csr_row_ptr csr)) (csr_col_ind csr) ++ [csr_cols csr])),
    csr_matrix_wellformed csr.

Definition exists_in_csr {t} (csr: csr_matrix t) (ij: Z*Z) : Prop :=
   exists k, 
     Znth (fst ij) (csr_row_ptr csr) <= k < Znth (fst ij + 1) (csr_row_ptr csr) /\
     Znth k (csr_col_ind csr) = snd ij.



Definition entries_correspond {t} (coo: coo_matrix t) (csr: csr_matrix t) :=
forall h, 
0 <= h < Zlength (coo_entries coo) ->
let '(r,c) := fst (Znth h (coo_entries coo)) in
let k := cde_upto (h+1) coo - 1 in
Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) /\
Znth k (csr_col_ind csr) = c.

Definition no_extra_zeros {t} (coo: coo_matrix t) (csr: csr_matrix t) := 
  forall r k, 0 <= r < coo_rows coo ->
     Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) ->
     let c := Znth k (csr_col_ind csr) in
        In (r,c) (map fst (coo_entries coo)).

Definition values_correspond {t} (coo: coo_matrix t) (csr: csr_matrix t) :=
  forall h, 
   0 <= h < Zlength (coo_entries coo) ->
    let k := cde_upto (h+1) coo - 1 in
    let rc := fst (Znth h (coo_entries coo)) in
    let batch := filter (coord_eqb rc oo fst) (coo_entries coo) in
        sum_any (map snd batch) (Znth k (csr_vals csr)).

Inductive coo_csr {t} (coo: coo_matrix t) (csr: csr_matrix t) : Prop :=
 build_coo_csr:
 forall
    (coo_csr_rows: coo_rows coo = csr_rows csr)
    (coo_csr_cols: coo_cols coo = csr_cols csr)
    (coo_csr_vals: Zlength (csr_vals csr) = count_distinct (coo_entries coo))
    (coo_csr_entries: entries_correspond coo csr)
    (coo_csr_zeros: no_extra_zeros coo csr)
    (coo_csr_values: values_correspond coo csr),
    coo_csr coo csr.

Inductive partial_CSR (h: Z) (r: Z) (coo: coo_matrix Tdouble)
      (rowptr: list val) (colind: list val) (val: list val) : Prop :=
build_partial_CSR:
   forall 
    (partial_CSR_coo: coo_matrix_wellformed coo)
    (partial_CSR_coo_sorted: sorted coord_le (coo_entries coo))
    (partial_CSR_i: 0 <= h <= Zlength (coo_entries coo))
    (partial_CSR_r: 0 <= r <= coo_rows coo + 1)
    (partial_CSR_r': Forall (fun e => fst (fst e) < r) (coo_entries (coo_upto h coo)))
    (partial_CSR_r'': Forall (fun e => fst (fst e) >= r-1) (sublist h (Zlength (coo_entries coo)) (coo_entries coo)))
    (csr: csr_matrix Tdouble)
    (partial_CSR_wf: csr_matrix_wellformed csr)
    (partial_CSR_coo_csr: coo_csr (coo_upto h coo) csr)
    (partial_CSR_val: sublist 0 (Zlength (csr_vals csr)) val = map Vfloat (csr_vals csr))
    (partial_CSR_colind: sublist 0 (Zlength (csr_col_ind csr)) colind = map (Vint oo Int.repr) (csr_col_ind csr))
    (partial_CSR_rowptr: sublist 0 r rowptr = map (Vint oo Int.repr) (sublist 0 r (csr_row_ptr csr)))
    (partial_CSR_val': Zlength val = count_distinct (coo_entries coo))
    (partial_CSR_colind': Zlength colind = count_distinct (coo_entries coo))
    (partial_CSR_rowptr': Zlength rowptr = coo_rows coo + 1)
    (partial_CSR_dbound: count_distinct (coo_entries coo) <= Int.max_unsigned),
    partial_CSR h r coo rowptr colind val.

Lemma partial_CSR_rowptr': forall {t} r (coo: coo_matrix t) (csr: csr_matrix t),
   coo_matrix_wellformed coo ->
   csr_matrix_wellformed csr ->
   coo_csr coo csr ->
   0 <= r <= coo_rows coo + 1 ->
   Forall (fun e => fst (fst e) < r) (coo_entries coo) ->
   sublist r (coo_rows coo + 1) (csr_row_ptr csr) = Zrepeat (Zlength (csr_vals csr)) (coo_rows coo + 1 - r).
Proof.
 intros.
 inversion_clear H1.
 apply Znth_eq_ext;
 unfold csr_rows in *.
 list_solve.
 intros.
 rewrite Znth_sublist by list_solve.
 rewrite Znth_Zrepeat by list_solve.
 autorewrite with sublist in H1.
 inversion_clear H0.
 assert (Znth (i+r) (csr_row_ptr csr) <= Zlength (csr_vals csr)). {
    rewrite CSR_wf_vals'.
    specialize (CSR_wf_sorted (i+r+1) (csr_rows csr + 1)).
    unfold csr_rows in *. specialize (CSR_wf_sorted ltac:(list_solve)).
    list_solve.
 }
 assert (0 <= Znth (i+r) (csr_row_ptr csr)). {
    specialize (CSR_wf_sorted 0 (i+r+1)).
    unfold csr_rows in *. specialize (CSR_wf_sorted ltac:(list_solve)).
    list_solve.
 }
 destruct (zlt (Znth (i+r) (csr_row_ptr csr)) (Zlength (csr_vals csr))); [ | lia].
 exfalso. clear H0.
 clear CSR_wf_rowsorted.
 assert (exists i', i + r <= i' < coo_rows coo /\ Znth i' (csr_row_ptr csr) < Znth (i'+1) (csr_row_ptr csr)). {
  rewrite CSR_wf_vals' in l. rewrite coo_csr_rows in H1|-*.
  clear -H1 CSR_wf_sorted l H2. destruct H2 as [H2 _].
  unfold csr_rows in *.
  forget (csr_row_ptr csr) as al.
  assert (0 <= i+r < Zlength al) by lia; clear H1 H2.
  forget (i+r) as r'. clear r i. rename r' into r.
  pose (bl := sublist r (Zlength al) al).
  assert (Znth 0 bl < Znth (Zlength bl - 1) bl) by (subst bl; list_solve).
  assert (exists i, 0 <= i < Zlength bl-1 /\ Znth i bl < Znth (i+1) bl). 
  2:{ destruct H1 as [i [? ?]]. exists (i+r); split. subst bl; list_solve. subst bl; list_solve. }
  assert (list_solver.sorted Z.le bl). {
    clear - CSR_wf_sorted H.
    intros x y [? ?].
    subst bl.
    rewrite !Znth_sublist by list_solve.
    specialize (CSR_wf_sorted (x+r+1) (y+r+1)).
    autorewrite with sublist in CSR_wf_sorted.
    autorewrite with sublist in H1.
    rewrite !Znth_pos_cons in CSR_wf_sorted by list_solve.
    rewrite !Znth_app1 in CSR_wf_sorted by list_solve.
    rewrite !Z.add_simpl_r in CSR_wf_sorted.
    apply CSR_wf_sorted; lia.
  }
  assert (0 < Zlength bl) by (subst bl; list_solve).
  clearbody bl. clear - H1 H0 H2.
  destruct bl; [list_solve|].
  autorewrite with sublist in *. clear H2.
  unfold Z.succ in H0. rewrite Z.add_simpl_r in H0.
  revert z H0 H1; induction bl; simpl; intros.
  list_solve.
  autorewrite with sublist in *.
  rewrite Znth_pos_cons in H0 by list_solve.
  unfold Z.succ in H0. rewrite Z.add_simpl_r in H0.
  destruct (zlt z a).
  exists 0; list_solve.
  assert (a=z). { specialize (H1 0 1). list_solve. }
  subst a.
  destruct (IHbl z) as [i [? ?]].
  list_solve. intros x y ?; specialize (H1 (x+1) (y+1)).
  destruct H.
  rewrite !(Znth_pos_cons (_ + 1)) in H1 by list_solve.
  rewrite !Z.add_simpl_r in H1.
  apply H1. list_solve.
  exists (i+1). list_solve.
 }
  destruct H0 as [i' [? ?]].
  unfold csr_rows in *.
  pose proof coo_csr_zeros i' (Znth i' (csr_row_ptr csr)) ltac:(lia).
  specialize (H6 ltac:(lia)).
  rewrite Forall_forall in H3.
  apply In_Znth in H6. destruct H6 as [b [??]].
  specialize (H3 (Znth b (coo_entries coo))).
  rewrite Znth_map in H7 by list_solve.
  rewrite H7 in H3. simpl in H3.
  spec H3. apply Znth_In. list_solve. lia.
Qed.

Definition matrix_upd {t} (i j: Z) (m: matrix t) (x: ftype t) : matrix t :=
  upd_Znth i m (upd_Znth j (Znth i m) x).

Lemma BPO_eqv_iff: forall {t} a b, @BPO.eqv _ _ (@CoordBPO t) a b <-> fst a = fst b.
 intros ? [[??]?] [[??]?]. unfold BPO.eqv, coord_le; simpl; split; intro.
 f_equal; lia. inv H; lia.
Qed.

Lemma partial_CSR_duplicate:
    forall h r coo (f: ftype Tdouble) ROWPTR COLIND VAL,
    0 < h < Zlength (coo_entries coo) ->
    fst (Znth (h-1) (coo_entries coo)) = fst (Znth h (coo_entries coo)) ->
    r = fst (fst (Znth (h-1) (coo_entries coo))) ->
    Znth (cde_upto h coo - 1) VAL = Vfloat f ->
    partial_CSR h (r+1) coo ROWPTR COLIND VAL ->
    partial_CSR (h+1) (r+1) coo ROWPTR COLIND 
      (upd_Znth (cde_upto h coo - 1) VAL
         (Vfloat (Float.add f (snd (Znth h (coo_entries coo)))))).
Proof.
intros * H Hdup **. 
assert (Hcde: 0 < cde_upto h coo). {
  apply count_distinct_bound'. autorewrite with sublist; lia.
}
inversion H2; clear H2.
destruct (coo_wellformed_e partial_CSR_coo h) as [Hr Hc]; [ lia |].
destruct (Znth h (coo_entries coo)) as  [[r' c] x] eqn:Hentry.
assert (r'=r) by (rewrite Hdup in H0; simpl in H0; auto).
subst r'. simpl in Hdup, Hr, Hc. 
clear H0. simpl.
assert (coo_matrix_wellformed (coo_upto h coo)). {
  clear - partial_CSR_coo H.
  inversion_clear partial_CSR_coo; constructor; auto.
  unfold coo_upto; simpl.
  apply Forall_sublist; auto.
}
assert (HR := partial_CSR_rowptr' (r+1) (coo_upto h coo) csr H0 partial_CSR_wf partial_CSR_coo_csr ltac:(simpl; lia) ltac:(auto)).
clear H0.
inversion_clear partial_CSR_coo_csr.
simpl in coo_csr_rows, coo_csr_cols.
set (d := cde_upto h coo) in *.
change (count_distinct (coo_entries (coo_upto h coo))) with d in *.
set (x' := Float.add f x).
pose (val' := upd_Znth (d - 1) (csr_vals csr) x').
pose (csr' := Build_csr_matrix _ (csr_cols csr) val' 
                (csr_col_ind csr) (csr_row_ptr csr)).
clear partial_CSR_r.
inversion_clear partial_CSR_wf.
apply (build_partial_CSR (h+1) (r+1) coo _ _ _ ltac:(assumption) ltac:(assumption) ltac:(lia)) with 
      (csr:=csr'); auto; try lia.
- simpl.  rewrite (sublist_split 0 h) by rep_lia. apply Forall_app; split; auto.
  rewrite sublist_one by lia. constructor; auto. rewrite Hentry; simpl. lia.
- clear - H partial_CSR_r''. list_solve.
-
 constructor; auto; simpl; change (csr_rows csr') with (csr_rows csr); try lia.
 + simpl. unfold val'. list_solve.
 + unfold val'. list_solve.
- 
   assert (H3: cde_upto (h+1) (coo_upto (h+1) coo) = cde_upto h (coo_upto h coo)). {
     unfold cde_upto, coo_upto. simpl. autorewrite with sublist.
     symmetry; apply count_distinct_noincr. lia.
     unfold BPO.lt, coord_le. rewrite Hdup, Hentry. simpl. lia.
   }
  constructor; auto.
 + transitivity d; [ simpl; unfold val'; list_solve | ].
   apply count_distinct_noincr; auto.
   unfold BPO.lt, coord_le; rewrite Hentry, Hdup; simpl; lia.
 + intros g ?.
   simpl.
   destruct (zeq g h).
  * subst g. autorewrite with sublist.
   pose proof (coo_csr_entries (h-1) ltac:(simpl; list_solve)). simpl in H2.
   autorewrite with sublist in H2.
   rewrite Hentry. rewrite Hdup in H2. simpl.
   rewrite H3; clear H3. auto.
  * simpl in H0. autorewrite with sublist in H0.
    rewrite Znth_sublist by lia. 
    rewrite Z.add_0_r.
    pose proof (coo_csr_entries g).  simpl in H2.
    autorewrite with sublist in H2.
    unfold cde_upto, coo_upto in H2|-*. simpl in H2|-*.
    autorewrite with sublist in H2. autorewrite with sublist.
    destruct (fst (Znth g (coo_entries coo))) as [r' c'].
    apply H2; lia.
 + intros r' k ? ?.
   specialize (coo_csr_zeros r' k H0 H2).
   simpl in coo_csr_zeros|-*.
   rewrite (sublist_split 0 h) by list_solve.
   rewrite map_app, in_app. auto.
 + change float with (ftype Tdouble) in *.
   assert (Hf: Znth (d-1) (csr_vals csr) = f). {
         assert (Hf': Znth (d-1) (sublist 0 (Zlength (csr_vals csr)) VAL) = Vfloat f) by list_solve.
         rewrite partial_CSR_val in Hf'. 
         rewrite Znth_map in Hf' by list_solve.
         inv Hf'; auto. 
       }
   subst val'.
   intros g ?. simpl in H0. autorewrite with sublist in H0.
   simpl coo_entries. autorewrite with sublist.
   replace (cde_upto (g + 1) (coo_upto (h + 1) coo) - 1)
    with (cde_upto (g+1) coo - 1) 
     by  (unfold cde_upto; simpl; autorewrite with sublist; auto).
   rewrite (sublist_split 0 h) by lia. rewrite (sublist_one h) by lia.
   rewrite Hentry.
   intro k. destruct (fst (Znth g (coo_entries coo))) as [r' c'] eqn:?H.
   intro. subst rc.
   rewrite filter_app. simpl filter.
   destruct (coord_eqb (r',c') (r,c)) eqn:?H.
   * unfold coord_eqb in H4; simpl in H4.
    assert (r'=r /\ c'=c) by lia. destruct H5; subst r' c'. clear H4.    
    destruct (zeq g h).
    -- subst g.
       specialize (coo_csr_values (h-1)).
       spec coo_csr_values. unfold coo_upto; simpl; list_solve.
       rewrite Z.sub_simpl_r in coo_csr_values.
       rewrite <- H3 in coo_csr_values.
       replace (cde_upto (h + 1) (coo_upto (h + 1) coo) - 1) with k in coo_csr_values
         by (unfold k, cde_upto; simpl; autorewrite with sublist; auto).
       simpl coo_entries in coo_csr_values.
       autorewrite with sublist in coo_csr_values.
       rewrite Hdup in coo_csr_values.
       simpl in coo_csr_values|-*.
       set (batch := filter (coord_eqb (r,c) oo fst) (sublist 0 h (coo_entries coo))) in *.
       assert (k=d-1). { subst k d. f_equal.
         unfold cde_upto in H3|-*; simpl in H3|-*. autorewrite with sublist in H3; auto.
       }
       clearbody k; subst k. unfold x'. 
       change (Float.add f x) with (BPLUS f x).
       rewrite upd_Znth_same by lia. rewrite map_app. simpl map.
       rewrite Hf in coo_csr_values.
       apply Sum_Any_split; auto. constructor.
    -- 
       specialize (coo_csr_values g).
       spec coo_csr_values. unfold coo_upto; simpl; list_solve.
       replace (cde_upto (g + 1) (coo_upto h coo) - 1) with k in coo_csr_values.
       2:{ unfold cde_upto; simpl; autorewrite with sublist; auto. }
       replace (Znth g (coo_entries (coo_upto h coo))) with
                (Znth g (coo_entries coo)) in coo_csr_values
           by (unfold coo_upto; simpl; list_solve).
       rewrite H2 in coo_csr_values. unfold coo_upto in coo_csr_values; simpl coo_entries in coo_csr_values.
       set (batch := filter _ _) in coo_csr_values|-*.
       simpl. rewrite map_app. simpl map.
       clear csr'. subst x'.
       assert (k = d-1). { subst k d. f_equal.
         unfold cde_upto.
         destruct (zeq g (h-1)). subst g. f_equal; f_equal; lia.
         assert (0<=g<h-1) by lia.
         rewrite <- Hdup in H2.
         clear - H2 H4 partial_CSR_coo_sorted H. destruct H as [_ H].
         forget (coo_entries coo) as al.
         rewrite <- BPO_eqv_iff in H2.
         apply count_distinct_range_same; auto. lia.
        }
       rewrite H4.
       rewrite upd_Znth_same by lia.
       change (Float.add f x) with (BPLUS f x).
       rewrite H4,Hf in coo_csr_values.
       apply Sum_Any_split; auto. constructor.
   * rewrite app_nil_r.
     simpl csr_vals.
     assert (g<>h). { intro; subst g. rewrite Hentry in H2. simpl in H2.
                     unfold coord_eqb in H4. simpl in H4. inv H2; lia.
     }
     assert (k <> d-1). { subst k. assert (cde_upto (g+1) coo <> d); [ | lia].
        unfold d.
        assert (fst (Znth g (coo_entries coo)) <> fst (Znth (h-1) (coo_entries coo))).
          unfold coord_eqb in H4. simpl in H4. rewrite H2, Hdup. simpl.  intro Hx; inv Hx; lia.
        unfold cde_upto.
        destruct (zeq g (h-1)); [contradict H6; subst; auto | ].
        assert (0<=g<h-1) by lia. clear - H6 H7 H partial_CSR_coo_sorted.
        contradict H6.
        rewrite <- BPO_eqv_iff.
        apply count_distinct_range_same in H6; auto. lia. 
      }
     rewrite upd_Znth_diff; try lia.
     specialize (coo_csr_values g).
     replace (cde_upto (g + 1) (coo_upto h coo) - 1) with k in coo_csr_values.
     2:{ unfold cde_upto; simpl; autorewrite with sublist; auto. }
     simpl Znth in coo_csr_values. autorewrite with sublist in coo_csr_values.
     rewrite H2 in coo_csr_values. apply coo_csr_values.
     unfold coo_upto; simpl; list_solve.
     subst k. unfold cde_upto.
     pose proof (count_distinct_bound (sublist 0 (g + 1) (coo_entries coo))).
     autorewrite with sublist in H7.
     pose proof (count_distinct_bound' (sublist 0 (g + 1) (coo_entries coo)) ltac:(list_solve)).
     split; try lia.
     rewrite coo_csr_vals.
     unfold d, cde_upto.
     pose proof count_distinct_mono (sublist 0 h (coo_entries coo)) (g+1) ltac:(list_solve).
     autorewrite with sublist in H9. lia.
 -
  simpl. unfold val'. autorewrite with sublist.
  clear csr' coo_csr_entries. rewrite coo_csr_vals.
  rewrite coo_csr_vals in *.
  assert (d <= Zlength VAL). {
      rewrite partial_CSR_val'. unfold d, cde_upto; simpl.
      apply count_distinct_mono. lia.
  }
  rewrite sublist_upd_Znth_lr by lia.
  rewrite partial_CSR_val.
  rewrite <-upd_Znth_map. f_equal. lia.
 -
  simpl. unfold val'.  list_solve.
Qed.

Lemma coo_upto_wellformed: forall {t} i (coo: coo_matrix t),
  0 <= i <= Zlength (coo_entries coo) ->
  coo_matrix_wellformed coo -> coo_matrix_wellformed (coo_upto i coo).
Proof.
intros.
inversion_clear H0; constructor; simpl; auto.
apply Forall_sublist; auto.
Qed.

Lemma partial_CSR_newcol:
   forall i r c x coo ROWPTR COLIND VAL,
    coo_matrix_wellformed coo ->
   0 < i < Zlength (coo_entries coo) ->
   Znth i (coo_entries coo) = (r, c, x) ->
   r = fst (fst (Znth (i-1) (coo_entries coo))) ->
   c <> snd (fst (Znth (i-1) (coo_entries coo))) ->
   partial_CSR i (r+1) coo ROWPTR COLIND VAL ->
   partial_CSR (i + 1) (r+1) coo ROWPTR
  (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) COLIND
     (Vint (Int.repr c)))
  (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) VAL
     (Vfloat x)).
Proof.
intros * ? ? Hrcx ? ? ?.
inversion_clear H3.
assert (H3: 0 <= r < coo_rows coo). {
   clear - partial_CSR_coo partial_CSR_i Hrcx H0.
   inversion_clear partial_CSR_coo. rewrite Forall_forall in H1.
   destruct (H1 (Znth i (coo_entries coo))). apply Znth_In. lia.
   rewrite Hrcx in *; simpl in *; lia.
}
clear partial_CSR_r.
assert (Hlastrows := partial_CSR_rowptr' (r+1) (coo_upto i coo) csr
   (coo_upto_wellformed i coo ltac:(lia) partial_CSR_coo)
       partial_CSR_wf partial_CSR_coo_csr
      ltac:(change (coo_rows _) with (coo_rows coo); lia)
      partial_CSR_r'). change (coo_rows _) with (coo_rows coo) in Hlastrows.
      replace (coo_rows coo + 1 - (r + 1)) with (coo_rows coo - r) in Hlastrows by lia.
pose (new_row_ptr := sublist 0 (r+1) (csr_row_ptr csr) ++ Zrepeat (cde_upto (i+1) coo) (Zlength (csr_row_ptr csr) - (r+1))).
pose (csr' := Build_csr_matrix _ (csr_cols csr) 
       (sublist 0 (cde_upto i coo) (csr_vals csr) ++ [snd (Znth i (coo_entries coo))])
       (sublist 0 (cde_upto i coo) (csr_col_ind csr) ++ [c])
       new_row_ptr).
assert (H4: count_distinct (sublist 0 i (coo_entries coo)) + 1 = 
        count_distinct (sublist 0 (i+1) (coo_entries coo))). {
    apply count_distinct_incr; [ | lia].
    pose proof (sorted_e _ partial_CSR_coo_sorted  (i-1) i) ltac:(lia) ltac:(lia).
      red. rewrite Hrcx in H4|-*. split; auto. intro.
      clear - H4 H5 H1 H2. destruct (Znth (i - 1) (coo_entries coo)) as [[??]?]. simpl in *; subst.
      red in H5, H4; simpl in *. lia.
     }
assert (Hrows: csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
assert (Hrows': csr_rows csr' = csr_rows csr). {
    inversion_clear partial_CSR_coo_csr.
    unfold csr_rows; simpl. unfold new_row_ptr, cde_upto.
    rewrite <- H4.
    simpl in coo_csr_rows.
    unfold csr_rows in *. list_solve.
  }
assert (Hcde: cde_upto i coo = Zlength (csr_vals csr)). {
    unfold cde_upto.
    pose proof (count_distinct_sublist (coo_entries coo) i) ltac:(lia).
    pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
    autorewrite with sublist in H6.
    inversion_clear partial_CSR_wf.
    inversion_clear partial_CSR_coo_csr. rewrite coo_csr_vals.
    unfold coo_upto. simpl. lia.
}
apply build_partial_CSR with (csr:=csr'); auto; try lia.
- unfold coo_upto. simpl. rewrite (sublist_split 0 i) by lia. apply Forall_app; split; auto.
  rewrite sublist_one by lia. rewrite Hrcx. constructor; auto. simpl. lia.
- unfold coo_upto. simpl. rewrite (sublist_split i (i+1)) in partial_CSR_r'' by lia.
  apply Forall_app in partial_CSR_r''. apply partial_CSR_r''.
- inversion_clear partial_CSR_wf.
  inversion_clear partial_CSR_coo_csr.
  simpl in coo_csr_rows, coo_csr_vals, coo_csr_cols.
  assert (Zlength new_row_ptr = Zlength (csr_row_ptr csr))
       by (unfold csr_rows in *; simpl in Hrows'; lia).    
  constructor; simpl; auto; try lia.
  + unfold cde_upto. list_solve.
  + unfold cde_upto, csr', new_row_ptr, csr_rows; simpl. list_solve.
  + intros a b [??].
    pose proof CSR_wf_sorted a b ltac:(list_solve).
    unfold new_row_ptr.
    rewrite app_ass.
    repeat change (?A :: ?B ++ ?C) with ((A::B)++C).
    destruct (zle a (r+1)), (zle b (r+1)).    
    -- autorewrite with sublist.
       destruct (zeq 0 a), (zeq 0 b); try subst a; try subst b;
        autorewrite with sublist in H8|-*; try lia; list_solve.
    -- destruct (zeq 0 a).
         subst a; simpl; repeat rewrite Znth_0_cons in *; repeat rewrite Znth_pos_cons in * by list_solve.
         rewrite Znth_app2 by list_solve.
         destruct (zlt b (Zlength (csr_row_ptr csr)+1)); [ | list_solve].
         autorewrite with sublist in H8|-*.
         apply count_distinct_bound.
         simpl. repeat rewrite Znth_pos_cons in * by list_solve.
         rewrite (Znth_app2 _ _ _ _ (b-1)) by list_solve. 
         destruct (zlt b (Zlength (csr_row_ptr csr)+1)); [ | list_solve].
         autorewrite with sublist.
         rewrite !Znth_app1 in H8 by list_solve.
         pose proof CSR_wf_sorted a (Zlength (csr_row_ptr csr)) ltac:(list_solve).
         rewrite !Znth_pos_cons, ?Z.add_simpl_r, ?Znth_app1 in H9 by list_solve.
         clear - CSR_wf_vals' Hrows H9 coo_csr_vals H4. unfold cde_upto, csr_rows in *.
         lia.
    -- lia.
    -- simpl. repeat rewrite Znth_pos_cons in H8|-* by list_solve.
       rewrite !(Znth_app2 _ _ _ (_++_)) by list_solve. autorewrite with sublist.
       destruct (zlt a (Zlength (csr_row_ptr csr)+1)), (zlt b (Zlength (csr_row_ptr csr)+1));
        autorewrite with sublist; try lia.
      ++ 
        unfold csr_rows, cde_upto in *.
        assert (b = Zlength (csr_row_ptr csr) + 1) by list_solve. clear g1 H7; subst b.
        autorewrite with sublist.
        transitivity (count_distinct (coo_entries coo)); auto.
        apply count_distinct_mono; lia.
      ++ assert (a = Zlength (csr_row_ptr csr) + 1) by list_solve.
         assert (b = Zlength (csr_row_ptr csr) + 1) by list_solve.
         rewrite H9, H10; clear; list_solve.
  + intros r' Hr'; pose proof CSR_wf_rowsorted r' ltac:(lia).
    apply sorted_i; [hnf; lia | ]; intros a b Ha Hb.
    pose proof (sorted_e _ H6 a b Ha).
    subst new_row_ptr.
    rewrite Hrows' in Hr'.
    clear coo_csr_values coo_csr_zeros coo_csr_entries CSR_wf_rowsorted
         csr' Hrows' partial_CSR_rowptr partial_CSR_colind partial_CSR_val
         partial_CSR_val' partial_CSR_colind' partial_CSR_rowptr'0.
     pose proof CSR_wf_sorted 0 (r'+1)
            ltac:(autorewrite with sublist; simpl; lia).
     rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r, Znth_app1 in H8 by list_solve.
     pose proof CSR_wf_sorted (r'+1) (r'+1+1)
            ltac:(autorewrite with sublist; simpl; lia).
     rewrite !Znth_pos_cons, !Z.add_simpl_r, !Znth_app1 in H9 by list_solve.
     pose proof CSR_wf_sorted (r'+1+1) (Zlength (csr_row_ptr csr))
            ltac:(autorewrite with sublist; simpl; lia).
     rewrite !Znth_pos_cons, !Z.add_simpl_r, !Znth_app1 in H10 by list_solve.
    destruct (zlt r' r); [ | destruct (zeq r' r)].
   * rewrite Znth_app1 by list_solve.
     rewrite !Znth_app1 in Hb|-* by list_solve.
     autorewrite with sublist in H7,Hb|-*.
     rewrite Zlength_sublist in H7
       by (try lia; rewrite <- CSR_wf_vals, CSR_wf_vals'; unfold csr_rows; lia).
     rewrite sublist_app1 in Hb 
      by (try lia; autorewrite with sublist; unfold cde_upto, csr_rows in *; lia).
     rewrite sublist_sublist, Zlength_sublist in Hb
      by (try lia; autorewrite with sublist; unfold cde_upto, csr_rows in *; lia).
     spec H7. lia.
     rewrite sublist_app1, sublist_sublist, !Z.add_0_r
      by (try lia; autorewrite with sublist; unfold cde_upto, csr_rows in *; lia).
     auto.
   * clear g. subst r'.
     autorewrite with sublist in Hb,H7|-*.
     fold (cde_upto i coo) in *. fold (cde_upto (i+1) coo) in *.
     rewrite <- H4 in *. clear H5.
     rewrite <- Hrows in H10.
     rewrite sublist_app' by list_solve.
     rewrite !sublist_sublist by list_solve.
     rewrite Zlength_sublist by list_solve.
     rewrite (sublist_one 0), Znth_0_cons by list_solve.
     autorewrite with sublist.
     rewrite app_ass. simpl.
     change (?A :: ?B ++ ?C) with ((A::B)++C).
     change (?A :: ?B ++ ?C) with ((A::B)++C) in H7.  
     assert (Znth (r+1) (csr_row_ptr csr) = cde_upto i coo). {
         transitivity (Znth 0 (sublist (r+1) (coo_rows coo + 1) (csr_row_ptr csr))).
         list_solve. rewrite Hlastrows. list_solve.
       }   
     destruct (zlt b (cde_upto i coo +1 - Znth r (csr_row_ptr csr))).
    -- rewrite !Znth_app1 in H7 |-* by list_solve.
       autorewrite with sublist in H7.
       rewrite H5 in *. apply H7. lia.
    -- rewrite (Znth_app2 _ _ _ _ b) by list_solve. autorewrite with sublist.
       destruct (zlt a (cde_upto i coo +1 - Znth r (csr_row_ptr csr))).
       rewrite Znth_app1 in H7|-* by list_solve.
       rewrite H5 in *. autorewrite with sublist in H7.
       autorewrite with sublist in Hb.
       set (d := cde_upto i coo) in *. set (m := Znth r (csr_row_ptr csr)) in *.
       destruct (zeq b (Z.succ (d-m))).
       ++ rewrite <- e, Z.sub_diag, Znth_0_cons.
          admit. (* entirely plausible *)
       ++ rewrite (Znth_pos_cons (b - _)) by lia.
          replace (b - Z.succ(d-m)-1) with 0 by lia. rewrite Znth_0_cons.
          pose proof (sorted_e _ H6 a (1+(d-m)) ltac:(lia) ltac:(list_solve)).
          change (?A :: ?B ++ ?C) with ((A::B)++C) in H11.
          rewrite Znth_app1 in H11 by list_solve.
           rewrite Znth_app2 in H11 by list_solve.
           autorewrite with sublist in H11.
           replace (1 + (d-m) - Z.succ(d-m)) with 0 in H11 by lia.
           rewrite Znth_0_cons in H11. auto.
      ++ rewrite Znth_app2 by list_solve. autorewrite with sublist.
         set (u := Z.succ _). assert (a-u=0 /\ b-u=1) by list_solve.
         destruct H11. rewrite H11, H12.
         change (c < csr_cols csr).
         clear dependent a. clear dependent b.
         rewrite <- coo_csr_cols.
         clear - Hrcx H0 H. inversion_clear H.
         rewrite Forall_forall in H2. specialize (H2 (Znth i (coo_entries coo))).
         destruct H2. apply Znth_In; lia. rewrite Hrcx in H2. simpl in H2. lia.
   * assert (r'>r) by lia. clear g n.
     rewrite Znth_app2 by list_solve. autorewrite with sublist.
     autorewrite with sublist in Hb.
     assert (a=0/\b=1) by lia. destruct H12. rewrite H12, H13.
     change (-1 < csr_cols csr). lia.
- inversion_clear partial_CSR_coo_csr. 
  constructor; auto.
  + rewrite Hrows'. simpl. auto.
  + simpl. rewrite <- H4.
    rewrite Zlength_app. f_equal.
    unfold cde_upto in coo_csr_vals|-*. simpl in coo_csr_vals.
    pose proof (count_distinct_sublist (coo_entries coo) i) ltac:(lia).
    pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
    list_solve.
  + admit. (* blah, blah, blah  *)
  + admit. (* blah, blah, blah  *)
  + admit. (* blah, blah, blah  *)
-  simpl.
   inversion_clear partial_CSR_coo_csr.
   autorewrite with sublist.
   rewrite coo_csr_vals in partial_CSR_val. simpl in partial_CSR_val.
   fold (cde_upto i coo) in *. set (d := cde_upto i coo) in *. 
   assert (d < Zlength VAL). {
     rewrite partial_CSR_val'.
     admit. (* easy *)
   }
   rewrite (sublist_split 0 d) by list_solve.
   rewrite (sublist_one d) by list_solve.
   rewrite sublist_upd_Znth_l by list_solve.
   rewrite partial_CSR_val.
   rewrite map_app.
   rewrite sublist_same by list_solve. f_equal.
   rewrite upd_Znth_same by list_solve. rewrite Hrcx; simpl; auto.
- admit.
- admit.
- admit.
- admit.

Admitted.

Lemma partial_CSR_0: forall (coo: coo_matrix Tdouble),
  coo_matrix_wellformed coo ->
    sorted coord_le (coo_entries coo) ->
 let k := count_distinct (coo_entries coo)
 in k <= Int.max_unsigned ->
   partial_CSR 0 0 coo (Zrepeat Vundef (coo_rows coo + 1))
  (Zrepeat Vundef k) (Zrepeat Vundef k).
Proof.
intros. rename H1 into Hk.
pose proof count_distinct_bound (coo_entries coo).
apply build_partial_CSR with (csr := {| csr_cols := coo_cols coo; csr_vals := nil; csr_col_ind :=  nil;
               csr_row_ptr := Zrepeat 0 (coo_rows coo + 1) |}); auto; try rep_lia.
-
inversion_clear H; lia.
- inversion_clear H.
  autorewrite with sublist.
  eapply Forall_impl; try apply H3.
  intros. simpl in H. lia.
-
inversion_clear H.
destruct H2.
constructor; unfold csr_rows; simpl; try list_solve.
+ intros i j [??]. list_simplify; rep_lia.
+ intros. rewrite sublist_nil'. simpl. constructor; try lia. constructor. list_solve.
-
constructor; simpl; try list_solve.
+
inversion_clear H. 
unfold csr_rows; simpl. list_solve.
+
 intros  h ?. exfalso. simpl in H2. list_solve.
+
 intros  h ? ?; simpl in *. autorewrite with sublist. lia.
+ intros h ?; simpl in *. autorewrite with sublist in H2. lia.
- list_solve.
- list_solve.
- inversion_clear H. list_solve.
Qed.

Lemma partial_CSR_skiprow:
    forall i r coo ROWPTR COLIND VAL,
    coo_matrix_wellformed coo ->
    0 <= i < Zlength (coo_entries coo) ->
    r <= fst (fst (Znth i (coo_entries coo))) ->
    partial_CSR i r coo ROWPTR COLIND VAL ->
    partial_CSR i (r+1) coo 
  (upd_Znth r ROWPTR
     (Vint
        (Int.repr (count_distinct (sublist 0 i (coo_entries coo))))))
  COLIND VAL.
Admitted.

Lemma partial_CSR_newrow: 
    forall i ri ci xi coo ROWPTR COLIND VAL,
    coo_matrix_wellformed coo ->
    0 <= i < Zlength (coo_entries coo) ->
    Znth i (coo_entries coo) = (ri,ci,xi) ->
    partial_CSR i (ri+1) coo ROWPTR COLIND VAL ->
    partial_CSR (i + 1) (ri+1) coo ROWPTR
     (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) COLIND
        (Vint (Int.repr ci)))
     (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) VAL
        (Vfloat xi)).
Admitted.

Lemma partial_CSR_lastrows:
   forall r coo ROWPTR COLIND VAL,
    coo_matrix_wellformed coo ->
   partial_CSR (Zlength (coo_entries coo)) r coo ROWPTR COLIND VAL ->
   partial_CSR (Zlength (coo_entries coo)) (r+1) coo 
     (upd_Znth r ROWPTR (Vint (Int.repr (count_distinct (coo_entries coo))))) COLIND VAL.
Admitted.

Fixpoint build_csr_row {t} (cols: Z) (vals: list (ftype t)) (col_ind: list Z) : list (ftype t) :=
 match vals, col_ind  with
 | v::vals', c::col_ind' => Zrepeat (Zconst t 0) c ++ v :: 
                            build_csr_row (cols-c-1) vals' (map (fun j => j-c-1) col_ind')

 | _, _ => Zrepeat (Zconst t 0) cols
 end.

Lemma sorted_cons_e2: forall {A} (lt: relation A) a al, sorted lt (a::al) -> sorted lt al.
Proof. intros. destruct al; inv H; auto; constructor. Qed.

Lemma build_csr_row_correct:
  forall {t} cols (vals: list (ftype t)) col_ind,
     0 <= cols ->
     Zlength vals = Zlength col_ind ->
(*     Forall (fun j => 0 <= j < cols) col_ind ->*)
     sorted Z.lt (-1 :: col_ind ++ [cols]) ->
    csr_row_rep cols vals col_ind (build_csr_row cols vals col_ind).
Proof.
intros.
pose proof I.
revert col_ind cols H H0 H1; induction vals; destruct col_ind; intros; try list_solve.
-
unfold build_csr_row.
rewrite <- (Z2Nat.id cols) by auto.
clear H H1 H2.
induction (Z.to_nat cols). constructor.
replace (Z.of_nat (S n)) with (1+Z.of_nat n) by lia.
rewrite <- Zrepeat_app by lia.
simpl.
constructor.
replace (1 + Z.of_nat n - 1) with (Z.of_nat n) by lia.
simpl. auto.
-
assert (0<=z) by (inv H1; lia).
rewrite <- (Z2Nat.id z) in H0,H1|-* by lia.
forget (Z.to_nat z) as n.
clear z H3 H2.
autorewrite with sublist in H0.
simpl.
revert cols col_ind H0 H1 H; induction n; intros.
 + simpl Z.of_nat in *.
  rewrite !Z.sub_0_r.
  constructor.
  replace (map (fun j : Z => j - 0 - 1) col_ind) with (map Z.pred col_ind).
  2:{ clear. induction col_ind; auto. simpl. f_equal. lia. apply IHcol_ind; auto. }
  apply IHvals; auto; try list_solve.
  *
   pose proof sorted_e _ H1 1 (Zlength col_ind + 2) ltac:(list_solve) ltac:(list_solve). autorewrite with sublist in H2.
   rewrite (Znth_pos_cons 1), Z.sub_diag in H2 by lia. simpl in H2.  rewrite Znth_0_cons in H2.
   repeat change (?A :: ?B ++ ?C) with ((A::B)++C) in H2. rewrite Znth_app2 in H2 by list_solve.
   clear - H2. list_solve.
  * simpl in H1. inv H1. inv H6. list_solve.
    replace (map Z.pred col_ind ++ [cols-1]) with (map Z.pred (y::l))
      by (rewrite H2; apply map_app). clear - H3 H5. simpl. constructor. lia.
    clear H3. change (sorted Z.lt (map Z.pred (y::l))). forget (y::l) as al.
    induction H5; constructor; auto. lia.
 + rewrite inj_S.
   replace (Z.succ (Z.of_nat n)) with (1 + Z.of_nat n) by lia.
   rewrite <- Zrepeat_app by lia.
   change (Zrepeat (Zconst t 0) 1) with [Zconst t 0].
   simpl.
   apply csr_row_rep_zero.
   specialize (IHn (cols-1) (map Z.pred col_ind)).
   simpl map. replace (Z.pred (1+Z.of_nat n)) with (Z.of_nat n) by lia.
   replace (cols - (1+Z.of_nat n) -1 ) with (cols - 1 - Z.of_nat n - 1) by lia.
   replace (map (fun j : Z => j - (1 + Z.of_nat n) - 1) col_ind)
     with (map (fun j : Z => j - Z.of_nat n - 1) (map Z.pred col_ind)). 2: {
     clear. induction col_ind; simpl; auto. f_equal. lia. auto. 
   } 
   apply IHn; try list_solve.
   * clear - H1. rewrite inj_S in H1. simpl in *. inv H1. constructor. lia.
     replace (Z.of_nat n :: map Z.pred col_ind ++ [cols - 1])
          with (map Z.pred (Z.succ (Z.of_nat n) :: col_ind ++ [cols]))
       by (simpl; f_equal; [lia | apply map_app]).
     forget (Z.succ (Z.of_nat n) :: col_ind ++ [cols]) as al.
     induction H4; constructor; auto; lia.
   * clear - H1. rewrite inj_S in H1. inv H1.
     pose proof (sorted_e _ H4 0 (Zlength col_ind + 1) ltac:(list_solve) ltac:(list_solve)).
     rewrite Znth_0_cons in H. clear H4. list_solve.
Qed.

Fixpoint build_csr_rows {t} (csr: csr_matrix t) (k: Z) (row_ptr: list Z) : list (list (ftype t)) :=
 match row_ptr with
 | [] => nil
 | k'::row_ptr' => build_csr_row (csr_cols csr) (sublist k k' (csr_vals csr)) 
                  (sublist k k' (csr_col_ind csr)) ::
                  build_csr_rows csr k' row_ptr'
 end.

Definition build_csr_matrix {t} (csr: csr_matrix t) : matrix t :=
 match csr_row_ptr csr with
 | k::row_ptr' => build_csr_rows csr k row_ptr'
 | [] => []
 end.

Lemma build_csr_matrix_correct:
  forall {t} (csr: csr_matrix t),
  csr_matrix_wellformed csr ->
  csr_rep_aux (build_csr_matrix csr) csr.
Proof.
 intros.
 inversion_clear H.
 unfold build_csr_matrix.
 unfold csr_rep_aux.
 unfold csr_rows in *.
 destruct (csr_row_ptr csr) as [| k rowptr]. list_solve.
 assert (Zlength rowptr = Zlength (build_csr_rows csr k rowptr)). {
   clear.
   revert k; induction rowptr; simpl; intros. auto.
   autorewrite with sublist. f_equal. auto.
 }
 split3; [ | | split3].
 - list_solve.
 - rewrite <- H. rewrite CSR_wf_vals'. f_equal. list_solve.
 - rewrite <- H. list_solve.
 - auto.
 - rewrite <- H.
   intros r ?.
   rewrite !(Znth_pos_cons (r+1)), Z.add_simpl_r by lia.
   pose proof @build_csr_row_correct t (csr_cols csr)
    (sublist (Znth r (k :: rowptr)) (Znth r rowptr) (csr_vals csr))
    (sublist (Znth r (k :: rowptr)) (Znth r  rowptr) (csr_col_ind csr))
     ltac:(lia).
   autorewrite with sublist in CSR_wf_vals'. unfold Z.succ  in CSR_wf_vals'.
   assert (0 <= Znth r (k :: rowptr) <= Znth r rowptr /\
           Znth r rowptr <= Zlength (csr_col_ind csr)). {
    clear - CSR_wf_sorted H0 CSR_wf_vals CSR_wf_vals'.
    repeat split.
    + specialize (CSR_wf_sorted 0 (r+1)). autorewrite with sublist in *.
      rewrite Znth_pos_cons, Z.add_simpl_r in CSR_wf_sorted by lia.
      rewrite Znth_app1 in CSR_wf_sorted by list_solve. apply CSR_wf_sorted; list_solve.
    + specialize (CSR_wf_sorted (r+1) (r+1+1)). simpl in CSR_wf_sorted.
      rewrite !(Znth_pos_cons (r+1+1)), Z.add_simpl_r in CSR_wf_sorted by lia.
      rewrite !(Znth_pos_cons (r+1)), Z.add_simpl_r in CSR_wf_sorted by lia.
      repeat change (?A :: ?B ++ ?C) with ((A::B)++C) in CSR_wf_sorted.
      rewrite !Znth_app1 in CSR_wf_sorted by list_solve. apply CSR_wf_sorted; list_solve.
    + specialize (CSR_wf_sorted (r+1+1) (Zlength rowptr+1)). simpl in CSR_wf_sorted.
      rewrite (Znth_pos_cons (r+1+1)), Z.add_simpl_r in CSR_wf_sorted by lia.
      rewrite (Znth_pos_cons (r+1)), Z.add_simpl_r in CSR_wf_sorted by lia.
      rewrite (Znth_pos_cons (Zlength rowptr+1)), Z.add_simpl_r in CSR_wf_sorted by lia.
      repeat change (?A :: ?B ++ ?C) with ((A::B)++C) in CSR_wf_sorted.
      rewrite !Znth_app1 in CSR_wf_sorted by list_solve. 
      spec CSR_wf_sorted. list_solve. rewrite <- CSR_wf_vals, CSR_wf_vals'.  
      autorewrite with sublist. auto.
   }
   destruct H2.
   spec H1; [list_solve | ].
   spec H1. { clear H1. 
      assert (H1 := CSR_wf_rowsorted r ltac:(list_solve)); simpl in H1.
      rewrite !(Znth_pos_cons (r+1)), Z.add_simpl_r in H1 by lia. auto.
   }
   assert (Znth r (build_csr_rows csr k rowptr) =
       build_csr_row (csr_cols csr)
       (sublist (Znth r (k :: rowptr)) (Znth r rowptr) (csr_vals csr))
       (sublist (Znth r (k :: rowptr)) (Znth r rowptr) (csr_col_ind csr))); [clear H1 | rewrite H4; auto].
   clear - H0.
   revert k r H0; induction rowptr; simpl; intros; [list_solve | ].
   destruct (zeq r 0).
      + list_solve. 
      + rewrite !(Znth_pos_cons r) by lia.
        apply (IHrowptr a (r-1) ltac:(list_solve)).
Qed.

Lemma csr_row_rep_colsnonneg: 
   forall {t} cols (vals: list (ftype t)) col_ind v, 
       csr_row_rep cols vals col_ind v ->
       Zlength vals = Zlength col_ind ->
       Forall (Z.le 0) (col_ind ++ [cols]).
Proof.
intros.
apply Forall_app; split.
-
induction H. constructor. spec IHcsr_row_rep. list_solve.
 clear - IHcsr_row_rep. induction col_ind. constructor.
  inv IHcsr_row_rep. constructor. lia. auto.
  constructor.  lia. spec IHcsr_row_rep. list_solve.
 clear - IHcsr_row_rep. induction col_ind. constructor.
  inv IHcsr_row_rep. constructor. lia. auto.
-
repeat constructor.
induction H; try lia.
spec IHcsr_row_rep. list_solve. lia.
spec IHcsr_row_rep. list_solve. lia.
Qed.


Lemma matrix_index_Z: forall {t} (m: matrix t) cols i j,
  matrix_cols m cols ->
  0 <= i < matrix_rows m ->
  0 <= j < cols ->
  matrix_index m (Z.to_nat i) (Z.to_nat j) = Znth j (Znth i m).
Proof.
  unfold matrix_index, matrix_rows. intros.
  rewrite (nth_Znth i) by list_solve.
  red in H; rewrite Forall_forall in H.
  rewrite nth_Znth by (rewrite H; auto; apply Znth_In; lia).
  auto.
Qed.

Lemma coo_to_matrix_build_csr_matrix: 
  forall {t} 
  (coo : coo_matrix t)
  (csr : csr_matrix t)
  (partial_CSR_coo : coo_matrix_wellformed coo)
  (partial_CSR_wf : csr_matrix_wellformed csr)
  (partial_CSR_coo_csr : coo_csr coo csr),
  csr_rep_aux (build_csr_matrix csr) csr ->
  coo_to_matrix coo (build_csr_matrix csr).
Proof.
intros.
inversion_clear partial_CSR_coo.
inversion_clear partial_CSR_wf.
inversion_clear partial_CSR_coo_csr.
red in H; decompose [and] H; clear H.
assert (Hcols: matrix_cols (build_csr_matrix csr) (coo_cols coo)). {
  red. unfold build_csr_matrix in *.
  rewrite coo_csr_cols.
  clear dependent coo.
  unfold csr_rows in *.
  destruct csr as [cols vals colind rowptr].
  simpl csr_vals in *. simpl csr_row_ptr in *. simpl csr_col_ind in *. simpl csr_cols in *.
  destruct rowptr as [ | k rowptr];  [ list_solve | ].
  subst csr_rows. clear H5.
  pose (u := k::rowptr). change (build_csr_rows
     {|
       csr_cols := cols;
       csr_vals := vals;
       csr_col_ind := colind;
       csr_row_ptr := k :: rowptr
     |}) with (build_csr_rows
     {|
       csr_cols := cols;
       csr_vals := vals;
       csr_col_ind := colind;
       csr_row_ptr := u
     |}) in *.
  clearbody u. 
  set (csr := {|
            csr_cols := cols;
            csr_vals := vals;
            csr_col_ind := colind;
            csr_row_ptr := u
          |}) in *.
  clear H3 H4.
  revert k CSR_wf_rows CSR_wf_vals' CSR_wf_sorted CSR_wf_rowsorted H2 H7.
  induction rowptr; intros; constructor.
 + specialize (H7 0 ltac:(list_solve)). autorewrite with sublist in H7.
   unfold build_csr_rows in H7; fold (@build_csr_rows t) in H7.
   rewrite !(Znth_pos_cons 1), !Z.sub_diag, !Znth_0_cons in H7 by lia.
   set (row := build_csr_row _ _ _) in H7|-*. clearbody row.
   assert (0 <= k <= a /\ a <= Zlength vals). {
     clear - CSR_wf_sorted CSR_wf_vals CSR_wf_vals'.
     repeat split.
     - apply (CSR_wf_sorted 0 1); list_solve.
     - apply (CSR_wf_sorted 1 2); list_solve.
     - pose proof CSR_wf_sorted 2 (Zlength (k::a::rowptr)).
       spec H; [simpl; list_solve|].
       simpl in H; autorewrite with sublist in H. rewrite CSR_wf_vals'.
       do 2 rewrite Znth_pos_cons in H by list_solve. simpl in H.
       rewrite Znth_0_cons in H.
       do 2 rewrite Znth_pos_cons in H by list_solve.
       autorewrite with sublist. unfold Z.succ in *.
       rewrite Znth_pos_cons by list_solve.
       rewrite !Z.add_simpl_r in *.
       change (?A :: ?B ++ ?C) with ((A::B)++C)  in H.
       rewrite Znth_app1 in H by list_solve. auto.
    }
    pose proof CSR_wf_rowsorted 0 ltac:(list_solve).
    autorewrite with sublist in H0.
    rewrite Znth_pos_cons, Z.sub_diag, Znth_0_cons in H0 by lia.
    assert (Zlength (sublist k a vals) = a-k) by list_solve.
    assert (Zlength (sublist k a colind) = a-k) by list_solve.
    rewrite <- H3 in H1.
    forget (sublist k a vals) as vals'.
    forget (sublist k a colind) as colind'.
    clear - H1 H0 H7.
    induction H7.
    * list_solve.
   * 
    pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    assert (Zlength v = cols - 1); [ | list_solve].
    apply IHcsr_row_rep.
    --
    clear - H H0.
    change [cols-1] with (map Z.pred [cols]) in *. rewrite <- map_app in *.  
    apply sorted_cons_e2 in H0.
    induction (col_ind++[cols]); simpl in *; constructor; try lia.
    inv H. lia. change (sorted Z.lt (map Z.pred (a::l))).
    clear - H0. induction H0; constructor; auto. lia.
    -- list_solve.
   * pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    assert (Zlength v = cols - 1); [ | list_solve].
    apply IHcsr_row_rep.
    --
    clear - H H0. simpl in H0.
    change [cols-1] with (map Z.pred [cols]) in *. rewrite <- map_app in *.  
    apply sorted_cons_e2 in H0.
    change (-1) with (Z.pred 0). 
    change (sorted Z.lt (map Z.pred (0::col_ind ++ [cols]))). clear H.
    induction H0; constructor; auto. lia.
    -- list_solve.
 + fold (@build_csr_rows t).
    apply IHrowptr; auto; try lia.
   * list_solve.
   * list_solve. 
   * clear - CSR_wf_sorted.
     intros i j [? ?].
     destruct (zeq i 0), (zeq j 0); subst; autorewrite with sublist.
     -- lia.
     -- specialize (CSR_wf_sorted 0 (j+1) ltac:(list_solve)). list_solve.
     -- lia.
     -- specialize (CSR_wf_sorted (i+1) (j+1) ltac:(list_solve)); list_solve.
   * intros. specialize (CSR_wf_rowsorted (r+1) ltac:(list_solve)).
     clear - CSR_wf_rowsorted H.
     rewrite !(Znth_pos_cons (_ + _)), !Z.add_simpl_r in CSR_wf_rowsorted by list_solve.     
     rewrite !(Znth_pos_cons (_ + _)), Z.add_simpl_r in CSR_wf_rowsorted by list_solve.
     rewrite !(Znth_pos_cons (_ + _)), Z.add_simpl_r  by list_solve.
     auto.
   * clear - H2. autorewrite with sublist in *.
     unfold build_csr_rows in H2; fold (@build_csr_rows t) in H2. list_solve.
   * intros. unfold build_csr_rows in H7; fold (@build_csr_rows t) in H7.
     specialize (H7 (j+1) ltac:(list_solve)).
     repeat rewrite !(Znth_pos_cons (_ + _)), !Z.add_simpl_r in H7 by list_solve.
     rewrite !(Znth_pos_cons (_ + _)), !Z.add_simpl_r by list_solve.
     auto.
}
split3; auto.
- unfold matrix_rows, csr_rows in *; lia.
- intros.
  assert (csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
  specialize (H7 i ltac:(lia)).
  erewrite matrix_index_Z; try eassumption;
 [ | unfold matrix_rows; list_solve].
(*  forget (Znth i (build_csr_matrix csr)) as rowvals.*)
  red in coo_csr_values.
  red in coo_csr_zeros, coo_csr_entries.
  assert (Hi := CSR_wf_sorted 0 (i+1) ltac:(list_solve)).
    autorewrite with sublist in Hi.
    rewrite Znth_pos_cons, Z.add_simpl_r, Znth_app1 in Hi by list_solve.
  assert (Hi' := CSR_wf_sorted (i+1) (i+1+1) ltac:(list_solve)).
    autorewrite with sublist in Hi.
    rewrite !Znth_pos_cons, !Z.add_simpl_r in Hi' by list_solve.
    rewrite !Znth_app1 in Hi' by list_solve.
  assert (Hi1 := CSR_wf_sorted (i+1+1) (Zlength (csr_row_ptr csr)) ltac:(list_solve)).
    rewrite (Znth_pos_cons (i+1+1)), Z.add_simpl_r in Hi1 by list_solve.
    rewrite (Znth_pos_cons (Zlength (csr_row_ptr csr))) in Hi1 by list_solve.
    rewrite !Znth_app1 in Hi1 by list_solve.
    rewrite <- H8 in Hi1.
  destruct (filter _ _) eqn:Hfilter.
 +
  simpl.
  specialize (coo_csr_zeros i).
  assert (Znth j (Znth i (build_csr_matrix csr)) = Zconst t 0); [ |rewrite H9; constructor].
  assert (~In (i,j) (map fst (coo_entries coo))). {
    intro. apply list_in_map_inv in H9. destruct H9 as [x [? ?]].
    assert (In x (filter (coord_eqb (i, j) oo fst) (coo_entries coo))). {
      destruct x. simpl in H9; subst p. rewrite filter_In. split; auto. simpl.
      unfold coord_eqb; simpl; lia.
    }
  rewrite Hfilter in H11. apply H11.
  }
  clear Hfilter.
  assert (~In j (sublist (Znth i (csr_row_ptr csr))
                         (Znth (i + 1) (csr_row_ptr csr)) (csr_col_ind csr))). {
    contradict H9.  apply In_Znth in H9. destruct H9 as [k [? ?]].
    autorewrite with sublist in H9, H10.
    specialize (coo_csr_zeros (k + Znth i (csr_row_ptr csr)) ltac:(list_solve) ltac:(list_solve)).
    subst j. auto. 
  }
  clear H9.
  forget (Znth i (csr_row_ptr csr)) as lo.
  forget (Znth (i+1) (csr_row_ptr csr)) as hi.
  assert (Zlength (sublist lo hi (csr_vals csr)) = Zlength (sublist lo hi (csr_col_ind csr))) by list_solve.
  red in Hcols; rewrite Forall_forall in Hcols. specialize (Hcols (Znth i (build_csr_matrix csr))).
  rewrite <- Hcols in H6 by (apply Znth_In; lia).
  forget (Znth i (build_csr_matrix csr)) as rowvals.
  forget (sublist lo hi (csr_vals csr)) as vals.
  forget (sublist lo hi (csr_col_ind csr)) as colind.
  clear - H10 H9 H7 H6.
  revert j H6 H10; induction H7; intros.
  * list_solve.
  * destruct (zeq j 0). subst. reflexivity.
    rewrite Znth_pos_cons by lia.
    apply IHcsr_row_rep. list_solve. list_solve.
    contradict H10. apply list_in_map_inv in H10.
    destruct H10 as [x [? ?]]. assert (j=x) by lia. subst. auto.
  * assert (j<>0 /\ ~ In j col_ind). split; contradict H10; simpl; auto.
    destruct H.
    rewrite Znth_pos_cons by lia.
    apply IHcsr_row_rep. list_solve. list_solve.
    contradict H0.
   apply list_in_map_inv in H0.
    destruct H0 as [y [? ?]]. assert (j=y) by lia. subst. auto.
 + 
  assert (In p (coo_entries coo) /\ (coord_eqb (i,j) oo fst) p = true). {
    apply filter_In. rewrite Hfilter. left; auto.
  }
 rewrite <- Hfilter. clear l Hfilter.
 destruct H9.
 apply In_Znth in H9. destruct H9 as [h [? ?]].
 subst p.
 specialize (coo_csr_values h H9).
 destruct (Znth h (coo_entries coo)) as [[i' j'] x] eqn:?Hh.
 unfold coord_eqb in H10. simpl in H10.
 assert (i'=i /\ j'=j) by lia. clear H10; destruct H11; subst i' j'.
 simpl in coo_csr_values.
 replace   (Znth j (Znth i (build_csr_matrix csr)))
   with (Znth (cde_upto (h + 1) coo - 1) (csr_vals csr)); auto.
 specialize (coo_csr_entries h H9).
 rewrite Hh in coo_csr_entries.
 simpl in coo_csr_entries.
 destruct coo_csr_entries.
 subst j.
 forget (cde_upto (h + 1) coo - 1) as k.
 rewrite coo_csr_rows in H.
 rewrite coo_csr_cols in H6, Hcols.
 clear h Hh H9 H5. clear dependent coo.
 forget (build_csr_matrix csr) as m.
 forget (Znth i (csr_row_ptr csr)) as lo.
 forget (Znth (i+1) (csr_row_ptr csr)) as hi.
 assert (Zlength (sublist lo hi (csr_vals csr)) = Zlength (sublist lo hi (csr_col_ind csr))) by list_solve.
 forget (Znth i m) as rowvals.
 assert (0 <= Znth (k-lo) (sublist lo hi (csr_col_ind csr)) < csr_cols csr)
   by (autorewrite with sublist; auto); clear H6.
 transitivity (Znth (k-lo) (sublist lo hi (csr_vals csr))); [
   | transitivity (Znth (Znth (k-lo) (sublist lo hi (csr_col_ind csr))) rowvals)];
   [ list_solve | | list_solve].
 assert (0 <= k-lo < Zlength (sublist lo hi (csr_vals csr))) by list_solve.
 forget (k-lo) as k'. clear dependent k.
 forget (sublist lo hi (csr_vals csr)) as vals.
 forget (sublist lo hi (csr_col_ind csr)) as colind.
 clear lo hi Hi Hi' Hi1. clear i H.
 clear m Hcols H2 H4 H3 H8.
(* ? *)
 clear - H7 H1 H5 H0.
 revert k' H1 H5; induction H7; intros.
  * list_solve.
  * pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    apply Forall_app in H. destruct H.
    rewrite Forall_forall in H. specialize (H (Z.pred (Znth k' col_ind))).
    spec H. apply in_map. apply Znth_In. lia.
    rewrite Znth_pos_cons by lia. rewrite IHcsr_row_rep by list_solve.
    f_equal. rewrite Znth_map by lia. lia.
  * destruct (zeq k' 0). subst. autorewrite with sublist. auto.
    rewrite !(Znth_pos_cons k') by lia.
    rewrite Znth_pos_cons in H1 by lia.
    assert (Znth (k'-1) col_ind > 0).
    pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    apply Forall_app in H. destruct H.
    rewrite Forall_forall in H. specialize (H (Z.pred (Znth (k'-1) col_ind))).
    spec H. apply in_map. apply Znth_In. list_solve. lia.
    rewrite Znth_pos_cons by lia. rewrite IHcsr_row_rep by list_solve.
    f_equal. list_solve.
Qed.

Lemma partial_CSR_properties:
  forall coo ROWPTR COLIND VAL,
    coo_matrix_wellformed coo ->
    partial_CSR (Zlength (coo_entries coo)) (coo_rows coo + 1) coo ROWPTR COLIND VAL ->
    exists (m: matrix Tdouble) (csr: csr_matrix Tdouble),
            csr_rep_aux m csr /\ coo_to_matrix coo m
            /\ coo_rows coo = matrix_rows m 
            /\ coo_cols coo = csr_cols csr 
            /\ map Vfloat (csr_vals csr) = VAL
            /\ Zlength (csr_col_ind csr) = count_distinct (coo_entries coo)
            /\ map Vint (map Int.repr (csr_col_ind csr)) = COLIND
            /\ map Vint (map Int.repr (csr_row_ptr csr)) = ROWPTR
            /\ Zlength (csr_vals csr) = count_distinct (coo_entries coo).
Proof.
intros.
inversion_clear H0.
pose proof build_csr_matrix_correct csr partial_CSR_wf.
set (m := build_csr_matrix csr) in *.
exists m, csr.
replace (coo_upto (Zlength (coo_entries coo)) coo) with coo in *. 2:{
  unfold coo_upto. autorewrite with sublist. clear. destruct coo; auto.
}
repeat simple apply conj; auto.
- apply coo_to_matrix_build_csr_matrix; auto.
- red in H0. decompose[and] H0; clear H0. unfold matrix_rows.
  inversion_clear partial_CSR_coo_csr. rewrite coo_csr_rows.
  unfold csr_rows; rewrite H1. lia.
-   inversion_clear partial_CSR_coo_csr; auto.
- rewrite <- partial_CSR_val.  
  inversion_clear partial_CSR_coo_csr. rewrite coo_csr_vals.
  rewrite sublist_same; auto.
- 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf. 
  lia.
- rewrite list_map_compose. fold (Vint oo Int.repr). rewrite <- partial_CSR_colind.
  apply sublist_same; auto. rewrite partial_CSR_colind'. 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf. lia.
- 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf.
  unfold csr_rows in *.
  rewrite list_map_compose. fold (Vint oo Int.repr).
  autorewrite with sublist in partial_CSR_rowptr. list_solve.
- 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf.
  unfold csr_rows in *.
  list_solve.
Qed.


Lemma partial_CSR_VAL_defined:
  forall i r coo ROWPTR COLIND VAL h,
    coo_matrix_wellformed coo ->
    0 <= i < Zlength (coo_entries coo) ->
    0 < h <= count_distinct (sublist 0 i (coo_entries coo)) -> 
    partial_CSR i r coo ROWPTR COLIND VAL ->
    is_float (Znth (h-1) VAL).
Proof.
intros.
inversion_clear H2.
inversion_clear partial_CSR_wf.
inversion_clear partial_CSR_coo_csr.
unfold csr_rows in *.
assert (0 <= h - 1 < Zlength (csr_vals csr))
 by (rewrite coo_csr_vals; simpl coo_entries; lia).
replace (Znth (h-1) VAL)
  with (Znth (h-1) (sublist 0 (Zlength (csr_vals csr)) VAL)) by list_solve.
rewrite partial_CSR_val. rewrite Znth_map by auto.
red. auto.
Qed.

Lemma body_coo_to_csr_matrix: semax_body Vprog Gprog f_coo_to_csr_matrix coo_to_csr_matrix_spec.
Proof.
start_function.
unfold coo_rep.
Intros maxn rp cp vp.
assert_PROP (sizeof tdouble * Zlength(coo_entries coo) <= Ptrofs.max_unsigned) as Hbound. {
  entailer. apply prop_right. clear - H0 H12.
  autorewrite with sublist in H12.
  destruct H12 as [? [_ [? _]]]. destruct vp; try contradiction.
  simpl in H1|-*. rewrite Z.max_r in H1 by rep_lia. rep_lia.
}
forward.
set (n := Zlength (coo_entries coo)).
forward_call (sh,coo,p,0,n).
  unfold coo_rep; Exists maxn rp cp vp; entailer!!.
Intros coo'.
clear rp cp vp.
eapply coo_matrix_wellformed_equiv in H; try apply H4.
generalize H4; intros [? [? ?]].
apply Permutation_Zlength in H8.
subst n.
rewrite H8 in H0 |-*.
set (n := Zlength (coo_entries coo')).
autorewrite with sublist in H5.
rewrite H6 in H2. rewrite H7 in H3.
clear H6 H7 H8.
clear maxn H0 H1.
forward_call.
set (k := count_distinct _).
forward.
assert_PROP (n <= maxn <= Int.max_signed) as Hn by entailer!.
clear H1; rename Hn into H1.  
forward.
forward.
forward.
forward_call (Tstruct _csr_matrix noattr, gv).
Intros q. 
assert (Hbound' := count_distinct_bound (coo_entries coo')).
fold k in Hbound'.
forward_call (tarray tdouble k, gv).
 entailer!!.
  simpl. do 3 f_equal. rep_lia.
  simpl. rep_lia.
Intros val_p.
forward_call (tarray tuint k, gv).
  entailer!!.
  simpl. do 3 f_equal. rep_lia. simpl; rep_lia.
Intros colind_p.
forward_call (tarray tuint (coo_rows coo+1), gv).
  entailer!!; simpl; rewrite (proj1 H4). do 3 f_equal. rep_lia.
  simpl. rewrite (proj1 H4). rep_lia. 
rewrite (proj1 H4).
Intros rowptr_p.
forward.
forward.
forward.
freeze FR1 := (spec_malloc.mem_mgr _) 
  (spec_malloc.malloc_token _ _ rowptr_p)
  (spec_malloc.malloc_token _ _ colind_p)
  (spec_malloc.malloc_token _ _ val_p)
  (spec_malloc.malloc_token _ _ q). 
forward_for_simple_bound n 
 (EX i:Z, EX l:Z, EX r:Z, EX c:Z, 
  EX ROWPTR: list val, EX COLIND: list val, EX VAL: list val,
  PROP(0<=l<=k; l<=i<=n; 0 <= r <= coo_rows coo'; 0 <= c <= coo_cols coo';
       partial_CSR i r coo' ROWPTR COLIND VAL;
       l = count_distinct (sublist 0 i (coo_entries coo'));
       l=0 -> r=0;
       i<>0 -> r=(fst (fst (Znth (i-1) (coo_entries coo')))+1)%Z /\ c = snd (fst (Znth (i-1) (coo_entries coo')))) 
 LOCAL (temp _l (Vint (Int.repr l));
       temp _r (Vint (Int.repr r)); temp _c (Vint (Int.repr c));
       temp _row_ptr rowptr_p; temp _col_ind colind_p; temp _val val_p;
       temp _q q;
       temp _pval vp; temp _pcol_ind cp; temp _prow_ind rp;
       temp _rows (Vint (Int.repr (coo_rows coo')));
       temp _n (Vint (Int.repr n));
       temp _p p)
  SEP(FRZL FR1;
      data_at Ews (tarray tuint (coo_rows coo' + 1)) ROWPTR rowptr_p;
      data_at Ews (tarray tuint k) COLIND colind_p; 
      data_at Ews (tarray tdouble k) VAL val_p;
      data_at_ Ews (Tstruct _csr_matrix noattr) q;
      data_at sh t_coo
        (rp, (cp, (vp,
          (Vint (Int.repr (Zlength (coo_entries coo'))),
           (Vint (Int.repr maxn),
            (Vint (Int.repr (coo_rows coo')), Vint (Int.repr (coo_cols coo')))))))) p;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (fst (fst e))))
           (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         rp;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (snd (fst e))))
        (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         cp;
       data_at sh (tarray tdouble maxn)
         (map (fun e : Z * Z * float => Vfloat (snd e)) (coo_entries coo') ++
          Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) vp))%assert.
-
 Exists 0 0 0
     (Zrepeat Vundef (coo_rows coo' + 1)) (Zrepeat Vundef k) (Zrepeat Vundef k).
 entailer!!.  
  apply partial_CSR_0; auto.
  pose proof count_distinct_bound (coo_entries coo'). rep_lia.  
- forward.
   entailer!!. list_solve.
  rewrite Znth_app1 by Zlength_solve; rewrite Znth_map by rep_lia.
  forward.
   entailer!!. list_solve.
  rewrite Znth_app1 by Zlength_solve; rewrite Znth_map by rep_lia.
  forward.
   entailer!!.
   list_simplify. rewrite Znth_map.
   2: change (Zlength _) with n; lia. hnf; auto.
  rewrite Znth_app1 by Zlength_solve.
  rewrite Znth_map by (change (Zlength _) with n; rep_lia).
  destruct (Znth i (coo_entries coo')) as [[ri ci] xi] eqn:Hi.
  simpl snd; simpl fst.
  generalize H; intros [_ H99]. rewrite -> Forall_forall in H99.
  specialize (H99 (ri,ci,xi)). destruct H99 as [Hri Hci]. rewrite <- Hi; apply Znth_In; rep_lia.
  simpl in Hri, Hci.
    assert (Hk: 0 < k) by (apply count_distinct_bound'; lia).
  forward_if; [forward_if | ].
  + (* ri+1 = r, ci = c *)
    rewrite add_repr in H15. apply repr_inj_unsigned in H15; try rep_lia.
    subst r ci.
    assert (is_float (Znth (l-1) VAL))
      by (eapply partial_CSR_VAL_defined; try eassumption; lia).
    assert (Hl: 0<>l) by (intro; subst; lia).   
    clear H13.   
    forward.
    forward.
    destruct (Znth (l-1) VAL) eqn:VALl; try contradiction. clear H15.
    pose (VAL' := upd_Znth (l-1) VAL (Vfloat (Float.add f (snd (Znth i (coo_entries coo')))))).
    Exists l (ri+1) c ROWPTR COLIND VAL'.
    entailer!!.
    assert (i<>0). { intro; subst. rewrite sublist_nil in *. compute in Hl. auto. }
    specialize (H14 H12). destruct H14.
    rewrite Z.add_simpl_r. rewrite Hi. simpl. split3; auto.
    2:{ clear - H13 H14 Hi H12 H6. rewrite <- !(Z.add_comm 1) in H13. 
        apply Z.add_reg_l in H13. subst.
        forget (coo_entries coo') as al.
        assert (0<i<n) by lia. clear H6 H12.
        assert (fst (Znth (i-1) al) = fst (Znth i al))
            by (rewrite Hi, <- surjective_pairing; auto).
        clear Hi; rename H0 into Hi. 
       apply count_distinct_noincr; auto.
       rewrite <- BPO_eqv_iff in Hi. unfold BPO.lt, BPO.eqv in *. tauto.
        }
     eapply partial_CSR_duplicate; try eassumption; try lia.
     destruct (Znth (i-1) (coo_entries coo')) as [[??]?].
     rewrite Hi. simpl in *; subst. f_equal. lia.
  + (* ri+1 = r, ci <> c *)
    rewrite add_repr in H15. apply repr_inj_unsigned in H15; try rep_lia.
    subst r.
    assert (Hl: 0<>l) by (intro; subst; lia).   
    assert (Hi': i<>0). { intro; subst. rewrite sublist_nil in *. compute in Hl. auto. }
    assert (Hl': l<k). {
      clear - H12 H6 Hi H14 H16 Hk H5.
      destruct (zlt 0 i).
      * clear Hk. 
        spec H14; [rep_lia |]. destruct H14 as [_ H14]; subst.
        forget (coo_entries coo') as bl. subst k.
        destruct (Znth (i-1) bl) as [[r' c'] x'] eqn:H'. simpl in *.
        assert (fst (Znth i bl) <> fst (Znth (i-1) bl)). rewrite Hi,H'. simpl. congruence.
        clear ci c' H16 H' Hi ri r' xi x'.
        subst n.
        assert (0 <= i-1 < Zlength bl-1) by lia. clear H6 l0.
        apply count_distinct_incr'; auto.
        pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
       rewrite <- BPO_eqv_iff in H. unfold BPO.lt, BPO.eqv in *. tauto.        
      * assert (i=0) by lia. subst. autorewrite with sublist.
        unfold count_distinct. simpl. auto.
    }
    forward.
    forward.
    forward.
    forward.
    Exists (l+1) (ri+1) ci ROWPTR
     (upd_Znth l COLIND (Vint (Int.repr ci))) 
     (upd_Znth l VAL (Vfloat (snd (Znth i (coo_entries coo'))))).
    entailer!!.
    specialize (H14 Hi'). destruct H14 as [H14a H14b].
    split3; [ | | split].
    * eapply partial_CSR_newcol; try eassumption; try lia. rewrite Hi. auto.
    * apply count_distinct_incr; try lia.
      pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
      assert (~BPO.eqv (Znth (i-1) (coo_entries coo')) (Znth i (coo_entries coo'))). {
        rewrite BPO_eqv_iff. rewrite Hi. simpl.
      intro; subst. apply H16. rewrite H14. auto.
      }
      clear - H12 H14. unfold BPO.lt, BPO.eqv in *; tauto.
    * rewrite Z.add_simpl_r, Hi; auto.
    * rewrite Z.add_simpl_r, Hi; auto. 
  + (* r+1 <> r *)
    deadvars!.
    rewrite add_repr in H15. assert (ri+1<>r) by (contradict H15; f_equal; auto).
    clear H15. rename H16 into H15. 
  forward_while (EX r: Z, EX ROWPTR: list val,
   PROP ( 0 <= r <= ri+1; partial_CSR i r coo' ROWPTR COLIND VAL )
   LOCAL (temp _x (Vfloat (snd (Znth i (coo_entries coo'))));
   temp _ci (Vint (Int.repr ci)); temp _ri (Vint (Int.repr ri));
   temp _i (Vint (Int.repr i)); temp _l (Vint (Int.repr l));
   temp _r (Vint (Int.repr r));
   temp _row_ptr rowptr_p; temp _col_ind colind_p; 
   temp _val val_p; temp _q q; temp _pval vp; temp _pcol_ind cp;
   temp _prow_ind rp; temp _rows (Vint (Int.repr (coo_rows coo')));
   temp _n (Vint (Int.repr n)); temp _p p)
   SEP (FRZL FR1;
   data_at Ews (tarray tuint (coo_rows coo' + 1)) ROWPTR rowptr_p;
   data_at Ews (tarray tuint k) COLIND colind_p;
   data_at Ews (tarray tdouble k) VAL val_p;
   data_at_ Ews (Tstruct _csr_matrix noattr) q;
   data_at sh t_coo
     (rp,
      (cp,
       (vp,
        (Vint (Int.repr (Zlength (coo_entries coo'))),
         (Vint (Int.repr maxn),
          (Vint (Int.repr (coo_rows coo')),
           Vint (Int.repr (coo_cols coo')))))))) p;
   data_at sh (tarray tuint maxn)
     (map
        (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (fst (fst e))))
        (coo_entries coo') ++
      Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) rp;
   data_at sh (tarray tuint maxn)
     (map
        (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (snd (fst e))))
        (coo_entries coo') ++
      Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) cp;
   data_at sh (tarray tdouble maxn)
     (map (fun e : Z * Z * float => Vfloat (snd e)) (coo_entries coo') ++
      Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) vp))%assert.
  * Exists r ROWPTR. entailer!!.
    destruct (zeq i 0).
    -- subst. rewrite sublist_nil in *. rewrite H13 by reflexivity. lia.
    -- destruct (H14 n0). rewrite H12.
       destruct H as [H' H]; rewrite Forall_forall in H. 
       destruct (H (Znth (i-1) (coo_entries coo'))).
       apply Znth_In; lia.
       replace ri with (fst (fst (Znth i (coo_entries coo')))) by (rewrite Hi; auto).
       clear - n0 H6 H H5.
    split.
    destruct (H (Znth (i-1) (coo_entries coo'))); try lia.
    apply Znth_In; lia.
    pose proof sorted_e1 _ H5 (i-1) ltac:(lia).
    rewrite Z.sub_add in H0.
    destruct H0; lia. 
  * entailer!!.
  * clear ROWPTR H11. rename ROWPTR0 into ROWPTR.
    clear dependent r. rename r0 into r.
    forward.
    forward.
    forward.
    Exists (r+1, upd_Znth r ROWPTR (Vint (Int.repr l))).
    entailer!!. split; auto. lia.
   apply partial_CSR_skiprow; auto. rewrite Hi; simpl; lia.

  *
   assert (r0 = ri+1) by lia. subst r0.
   clear HRE H16.
   forward.
   assert (H87: 0 <= count_distinct (sublist 0 i (coo_entries coo')) < k). {
     subst k.
     split; try lia.
     destruct (zeq i 0). list_solve.
     destruct (H14 n0).
     apply count_distinct_incr'.
     pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
     assert (~BPO.eqv (Znth (i-1) (coo_entries coo')) (Znth i (coo_entries coo'))). {
        rewrite BPO_eqv_iff. rewrite Hi. simpl. intro. rewrite H20 in *. simpl in *. lia.
     } 
     clear - H19 H20. unfold BPO.lt, BPO.eqv in *. tauto.
     lia.
   }
   forward.
   forward.
   forward.
   Exists (l+1) (ri+1) ci ROWPTR0 (upd_Znth l COLIND (Vint (Int.repr ci)))
          (upd_Znth l VAL (Vfloat (snd (Znth i (coo_entries coo'))))).
   entailer!!.
   rewrite Z.add_simpl_r, Hi. simpl.
   split3; [ | | split]; auto; try lia.
   clear r H15 H14 H9 H11 H13.
   2:{ destruct (zeq i 0).
        - subst. autorewrite with sublist. rewrite sublist_one by lia. reflexivity. 
        - destruct (H14 n0). apply count_distinct_incr ; [ | lia].
          pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
          assert (~BPO.eqv (Znth (i - 1) (coo_entries coo'))
                        (Znth i (coo_entries coo'))). {
           rewrite Hi. rewrite BPO_eqv_iff. 
          destruct (Znth (i-1) (coo_entries coo')); subst. simpl.  intro; subst; simpl in *; lia. 
          }
          clear - H18 H19; unfold BPO.eqv, BPO.lt in *; tauto.
    }
   apply partial_CSR_newrow; auto.
 - Intros l r c ROWPTR0 COLIND VAL.
   deadvars!.
   autorewrite with sublist in H11.
   forward.
   rename r into r1.
forward_while
 (EX r:Z,
  EX ROWPTR: list val,
  PROP(k<=n; 0 <= r <= coo_rows coo'+1;
       partial_CSR n r coo' ROWPTR COLIND VAL)
  LOCAL (temp _l (Vint (Int.repr k));
       temp _r (Vint (Int.repr r)); temp _cols (Vint (Int.repr (coo_cols coo')));
       temp _row_ptr rowptr_p; temp _col_ind colind_p; temp _val val_p;
       temp _q q;
       temp _rows (Vint (Int.repr (coo_rows coo'))))
  SEP(FRZL FR1;
      data_at Ews (tarray tuint (coo_rows coo' + 1)) ROWPTR rowptr_p;
      data_at Ews (tarray tuint k) COLIND colind_p; 
      data_at Ews (tarray tdouble k) VAL val_p;
      data_at_ Ews (Tstruct _csr_matrix noattr) q;
      data_at sh t_coo
        (rp, (cp, (vp,
          (Vint (Int.repr (Zlength (coo_entries coo'))),
           (Vint (Int.repr maxn),
            (Vint (Int.repr (coo_rows coo')), Vint (Int.repr (coo_cols coo')))))))) p;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (fst (fst e))))
           (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         rp;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (snd (fst e))))
        (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         cp;
       data_at sh (tarray tdouble maxn)
         (map (fun e : Z * Z * float => Vfloat (snd e)) (coo_entries coo') ++
          Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) vp))%assert.
 + Exists r1 ROWPTR0. entailer!!.
 + entailer!!.
 + clear r1 c H13 H9 H8 H10 H12.
   forward.
   forward.
   forward.
   Exists (r+1, (upd_Znth r ROWPTR (Vint (Int.repr k)))).
   entailer!!.
   split. lia.
   apply partial_CSR_lastrows; auto.
 +
   clear r1 c H13 H8 H9 H10 H12.
   forward.
   forward.
   forward.
   forward.
   forward.
Ltac entailer_for_return ::= idtac.
   assert (l=k) by lia. subst l.
   clear H7 H6 H0 H14.
   fold n in Hbound'. 
   assert (r = coo_rows coo' + 1) by lia.
   subst r. clear HRE H15 ROWPTR0 H8.
   forward.
   entailer!!.
   destruct (partial_CSR_properties _ _ _ _ H H16)
    as [m [csr [H6a [H6b [H6c [H6d [H6e [H6f [H6g [H6h H6i]]]]]]]]]].
   fold k in H6f, H6i .
   Exists coo' m q.
   assert (Hcoo: coo_to_matrix coo m). {
     eapply coo_to_matrix_equiv; try eassumption.
     apply coo_matrix_equiv_symm; auto.
   }
   thaw FR1.
   entailer!!.
   sep_apply fold_coo_rep; auto.
   fold n. split3; try lia. split3; try lia; auto.
   rewrite H6c, H6d.
   assert_PROP (matrix_rows m = csr_rows csr) as Hrows'. {
    entailer. apply prop_right. destruct csr.
    unfold sparse_model.csr_rows, sparse_model.csr_row_ptr in *. simpl. list_solve.
   }
   rewrite Hrows'.
   fold t_csr.
   rewrite <- H6f.
   sep_apply fold_csr_rep'.
   unfold csr_token, csr_rep.
   Exists csr H6a.
   Exists val_p colind_p rowptr_p csr.
   rewrite prop_true_andp by auto.
   unfold csr_token'.
   Exists val_p colind_p rowptr_p.
   cancel.
   apply -> wand_sepcon_adjoint.
   rewrite H6f, H6i. cancel.
Qed.