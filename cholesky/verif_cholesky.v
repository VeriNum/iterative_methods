Require Import VST.floyd.proofauto.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
From Cholesky Require Import cholesky cholesky_model spec_cholesky.
Import FPCore FPCompCert.



Set Bullet Behavior "Strict Subproofs".

Open Scope logic.



Lemma update_i_lt_j:
  forall {t: type} {STD: is_standard t} n i j (A R: Z -> Z -> ftype t),
   0 <= i < j -> j < n ->
   cholesky_jik_upto n i j A R ->
   let rij := BDIV (subtract_loop A R i j i) (R i i) in
    cholesky_jik_upto n (i + 1) j A (updij R i j rij).
Proof.
intros.
intros i' j'.
subst rij.
split; intros.
-
specialize (H1 i' j').
destruct H1 as [H1 _]. specialize (H1 H2).
split; intros.
+
specialize (H1 H3). clear H3.
destruct H1 as [? _]. specialize (H1 H4). 
unfold updij.
destruct (zeq j j'); try lia.
if_tac; try lia.
* rewrite if_false by lia.
  subst i. rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H3.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
* rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  if_tac; auto. if_tac; try lia. auto.
+ specialize (H1 H3).
  destruct H1 as [_ H1].
  unfold updij. subst i'.
  if_tac; try lia.
  * rewrite if_false by lia.
  specialize (H1 (eq_refl _)).
  rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  *
  rewrite H1 by lia. f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H5.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
  if_tac; try lia; auto. if_tac; auto; try lia.
-
  red in H1|-*.
  subst j'.
  intro.
  split; intros; [ | lia].
 + unfold updij. destruct (zeq j j); try lia. clear e.
   destruct (zeq j i'); try lia.
   replace (if zeq i i' then R i' i' else R i' i') with (R i' i') by (if_tac; auto).
   if_tac.
  * subst i'. clear n0 H3 H0 H4.
    f_equal.
  match goal with |- _ = _ _ ?ff _ _ _ => set (f:=ff) end.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H0.
  subst f. simpl. if_tac; try lia; auto.
  * assert (i'<i) by lia. clear H5 H3 n0.
   specialize (H1 i' j). destruct H1 as [_ H1].
   destruct H1 as [H1 _]; try lia. rewrite H1 by auto.
   f_equal.
  unfold subtract_loop.
  f_equal. rewrite !map_map.
  apply map_ext_in.
  intros. apply iota_range in H3.
  f_equal.
  if_tac; try lia; auto.
  rewrite if_false by lia. auto.
Qed.

Lemma subtract_another:
  forall
   {t: type} {STD: is_standard t} i j k (A R: Z -> Z -> ftype t),
    0 <= i <= j -> 0 <= k < j ->
    subtract_loop A R i j (k+1) = 
     BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
unfold subtract_loop at 1.
replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
rewrite iota_plus1.
simpl.
rewrite !map_app.
simpl map.
rewrite fold_left_app.
simpl.
f_equal.
rewrite Z2Nat.id by lia.
f_equal.
Qed.

Lemma body_cholesky : 
  semax_body Vprog Gprog f_cholesky cholesky_spec.
Proof.
unfold cholesky_spec.
rewrite N_eq.
start_function.
rewrite <- N_eq.
forward_for_simple_bound n 
  (EX j:Z, EX R: Z->Z->ftype Tdouble,
      PROP(cholesky_jik_upto n 0 j A R)
      LOCAL(temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrix (lists_of_fun N (done_to_n (Vfloat oo float_of_ftype) n A)) a;
          data_at sh matrix (lists_of_fun N (done_to_ij (Vfloat oo float_of_ftype)  n j j R)) r))%assert.
-
Exists (fun _ _ : Z => Zconst _ 0).
set (Aval := lists_of_fun _ _).
set (Rval := lists_of_fun _ _).
entailer!!.
intros i j; split; intros; hnf; intros; split; intros; lia.
 sep_apply data_at__data_at.
 apply derives_refl'; f_equal.
 subst Rval.
 unfold matrix.
 unfold default_val. simpl.
 replace (done_to_ij _ _ _ _ _) with (fun _ _ :Z => Vundef)
  by (extensionality i j; unfold done_to_ij; repeat (if_tac; try lia); auto). 
 unfold lists_of_fun.
 forget O as i. rewrite <- repeat_Zrepeat.
 revert i; induction (Z.to_nat N); simpl; intros; f_equal; auto.
 unfold list_of_fun.
 clear i IHn0.
 forget O as i. rewrite <- repeat_Zrepeat.
 revert i; induction (Z.to_nat N); simpl; intros; f_equal; auto.
-
rename i into j.
forward_for_simple_bound j 
  (EX i:Z, EX R: Z->Z->ftype Tdouble,
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrix (lists_of_fun N (done_to_n (Vfloat oo float_of_ftype) n A)) a;
          data_at sh matrix (lists_of_fun N (done_to_ij (Vfloat oo float_of_ftype) n i (j+1) R)) r))%assert.
 + Exists R.
   assert (done_to_ij (Vfloat oo float_of_ftype) n 0 (j+1) R = done_to_ij (Vfloat oo float_of_ftype) n j j R). {
    extensionality i' j'.
    unfold done_to_ij.
    repeat (if_tac; try lia); auto.
   }
   rewrite H1; clear H1.
   entailer!!.
 + clear R.  rename R0 into R.
   unfold matrix.
   rewrite N_eq; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
    rewrite <- N_eq in *. 
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
   change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000)).
   forward_for_simple_bound i
     (EX k:Z, 
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _s (Vfloat (subtract_loop A R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrix (lists_of_fun N (done_to_n (Vfloat oo float_of_ftype) n A)) a;
          data_at sh matrix (lists_of_fun N (done_to_ij (Vfloat oo float_of_ftype) n i (j+1) R)) r))%assert.
  * entailer!!.  unfold done_to_n; rewrite Znth_lists_done by rep_lia; auto.
  * rename i0 into k.
    unfold matrix.
    rewrite N_eq in *; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
    rewrite <- N_eq in *; fold matrix.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    unfold matrix.
    rewrite N_eq in *; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
    rewrite <- N_eq in *; fold matrix.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
     forward.
     entailer!!.
     unfold done_to_ij, lists_of_fun.
     symmetry.
     rewrite Znth_map by (rewrite Zlength_iota; rep_lia).
     rewrite !Znth_i_list_of_fun by rep_lia.
     rewrite Znth_i_iota by rep_lia.
     repeat (if_tac; try rep_lia; [ ] ).
     simpl.
     f_equal.
     unfold subtract_loop.
     change (Float.sub ?x ?y) with (BMINUS x y).
     replace (seq.iota 0 (Z.to_nat (k + 1))) with (seq.iota 0 (Z.to_nat k) ++ [Z.to_nat k]).
     rewrite !map_app, fold_left_app.
     reflexivity.
     replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
     simpl.
      rewrite iota_plus1. f_equal.
    * 
     unfold matrix.
     rewrite N_eq in *; forward; 
     change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
     rewrite <- N_eq in *; fold matrix.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
     unfold matrix.
     rewrite N_eq in *.
     rewrite Znth_lists_done by lia.
     set (jj := lists_of_fun _ (done_to_ij _ _ _ _ _)).
     freeze FR1 := (data_at rsh _ _ _).
     forward.
     thaw FR1.
     set (rij := Float.div _ _).
     subst jj.
     Exists (updij R i j rij).
     rewrite <- N_eq.
     rewrite upd_Znth_lists_of_fun by rep_lia.
     entailer!!.
     change Float.div with BDIV in rij.
     apply update_i_lt_j; auto. lia.
  + clear R. Intros R.
    freeze FR2 := (data_at sh _ _ _).
    unfold matrix.
    rewrite N_eq in *.
    forward.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    rewrite <- N_eq in *; fold matrix.
    thaw FR2.
    freeze FR3 := (data_at rsh _ _ _).
    deadvars!.
   forward_for_simple_bound j
     (EX k:Z, 
      PROP()
      LOCAL(temp _s (Vfloat (subtract_loop A R j j k) );
            temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(FRZL FR3;
          data_at sh matrix (lists_of_fun N (done_to_ij (Vfloat oo float_of_ftype) n j (j+1) R)) r))%assert.
  * entailer!!.
    unfold done_to_n.
    rewrite Znth_lists_done by lia. reflexivity.
  * 
    unfold matrix.
    rewrite N_eq in *.
    forward.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    rewrite <- N_eq in *; fold matrix.
    rewrite Znth_lists_done by lia.
    forward.     
    entailer!!.
    f_equal.
    change Float.sub with BMINUS. change Float.mul with BMULT.
    apply @subtract_another; lia.
  * forward_call.
    unfold matrix.
    rewrite N_eq in *.
    forward.
    rewrite <- N_eq in *; fold matrix.
    rewrite upd_Znth_lists_of_fun by rep_lia.
    set (R' := updij _ _ _ _).
    Exists R'.
    thaw FR3.
    entailer!!.
    change (Binary.Bsqrt _ _ _ _ _ _ ?x) with (BSQRT _ _  x) in R'.
    intros i' j'.
    destruct (zlt j' (j+1));
      [ | split; intros; [ lia | split; intros; lia]].
    assert (Hsub: forall i j', 0 <= i <= j' -> i'<=j'<=j -> 
             subtract_loop A R' i j' i' = subtract_loop A R i j' i'). {
      clear j' l; intros i j' Hi Hj'.
      set (x := BSQRT _ _ _) in R'. clearbody x.
      subst R'. destruct H0.
      clear - H0 Hi Hj'.
      unfold subtract_loop.
      rewrite !map_map.
      pose (f z := BMULT z z ).
      set (g1 := BMULT). set (g2 := BMINUS).
      set (a := A i j'). clearbody a. clearbody g1. clearbody g2.
      set (n:=j) at 1 2 3 4.
      set (u := O).  assert (Z.of_nat (u+ Z.to_nat i')<=n) by lia. clearbody u. clearbody n.
      revert a u H; induction (Z.to_nat i'); intros; auto.
      simpl. rewrite IHn0 by lia. f_equal. f_equal. f_equal. unfold updij.
      rewrite if_false by lia. auto. unfold updij. rewrite if_false by lia. auto.
    }
    destruct (zlt j' j); split; intros; try lia.
    ++ clear H2 l.
      destruct (H1 i' j') as [? _].
      specialize (H2 l0).
      set (x := BSQRT _ _ _) in R'. clearbody x. clear - Hsub H2 l0 H0.
      intro.  specialize (H2 H). destruct H2.
      split; intros.
      ** rewrite Hsub by lia.
      unfold R', updij. rewrite !if_false by lia. auto. 
      ** rewrite Hsub by lia. 
      unfold R', updij. rewrite !if_false by lia. auto. 
    ++ assert (j'=j) by lia. subst j'. clear l g H2.
       red in H1.
       split; intros.
      **
       destruct (H1 i' j) as [_ ?]. specialize (H4 (eq_refl _) ltac:(lia)).
       red in H4. destruct H4 as [? _]; try lia.
       rewrite Hsub by lia.
       unfold R'. unfold updij. rewrite !if_false by lia.
       apply H4; auto. 
      ** subst i'. rewrite Hsub by lia. unfold R', updij.
         rewrite !if_true by auto. auto.
 - Intros R. Exists R.
   rewrite <- N_eq in *.
   entailer!!.
   intros i j.
   specialize (H0 i j).   
   destruct (zlt j n);[ | split; intros; lia].
   destruct H0.
   apply H0; auto.
Qed.



Lemma body_choleskyf : 
  semax_body Vprog Gprog f_choleskyf choleskyf_spec.
Proof.
unfold choleskyf_spec.
rewrite N_eq.
start_function.
rewrite <- N_eq.
forward_for_simple_bound n 
  (EX j:Z, EX R: Z->Z->ftype Tsingle,
      PROP(cholesky_jik_upto n 0 j A R)
      LOCAL(temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrixf (lists_of_fun N (done_to_n (Vsingle oo @float_of_ftype Tsingle _) n A)) a;
          data_at sh matrixf (lists_of_fun N (done_to_ij (Vsingle oo @float_of_ftype Tsingle _)  n j j R)) r))%assert.
-
Exists (fun _ _ : Z => Zconst Tsingle 0).
set (Aval := lists_of_fun _ _).
set (Rval := lists_of_fun _ _).
entailer!!.
intros i j; split; intros; hnf; intros; split; intros; lia.
 sep_apply data_at__data_at.
 apply derives_refl'; f_equal.
 subst Rval.
 unfold matrixf.
 unfold default_val. simpl.
 replace (done_to_ij _ _ _ _ _) with (fun _ _ :Z => Vundef)
  by (extensionality i j; unfold done_to_ij; repeat (if_tac; try lia); auto). 
 unfold lists_of_fun.
 forget O as i. rewrite <- repeat_Zrepeat.
 revert i; induction (Z.to_nat N); simpl; intros; f_equal; auto.
 unfold list_of_fun.
 clear i IHn0.
 forget O as i. rewrite <- repeat_Zrepeat.
 revert i; induction (Z.to_nat N); simpl; intros; f_equal; auto.
-
rename i into j.
forward_for_simple_bound j 
  (EX i:Z, EX R: Z->Z->ftype Tsingle,
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrixf (lists_of_fun N (done_to_n (Vsingle oo @float_of_ftype Tsingle _) n A)) a;
          data_at sh matrixf (lists_of_fun N (done_to_ij (Vsingle oo @float_of_ftype Tsingle _) n i (j+1) R)) r))%assert.
 + Exists R.
   assert (done_to_ij (Vsingle oo @float_of_ftype Tsingle _) n 0 (j+1) R = done_to_ij (Vsingle oo @float_of_ftype Tsingle _) n j j R). {
    extensionality i' j'.
    unfold done_to_ij.
    repeat (if_tac; try lia); auto.
   }
   rewrite H1; clear H1.
   entailer!!.
 + clear R.  rename R0 into R.
   unfold matrixf.
   rewrite N_eq; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tfloat 1000));
    rewrite <- N_eq in *. 
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
   change (Vundef :: _ :: _) with (default_val (tarray tfloat 1000)).
   forward_for_simple_bound i
     (EX k:Z, 
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _s (Vsingle (subtract_loop A R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrixf (lists_of_fun N (done_to_n (Vsingle oo @float_of_ftype Tsingle _) n A)) a;
          data_at sh matrixf (lists_of_fun N (done_to_ij (Vsingle oo @float_of_ftype Tsingle _) n i (j+1) R)) r))%assert.
  * entailer!!.  unfold done_to_n; rewrite Znth_lists_done by rep_lia; auto.
  * rename i0 into k.
    unfold matrixf.
    rewrite N_eq in *; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tfloat 1000));
    rewrite <- N_eq in *; fold matrixf.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    unfold matrixf.
    rewrite N_eq in *; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tfloat 1000));
    rewrite <- N_eq in *; fold matrixf.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
     forward.
     entailer!!.
     unfold done_to_ij, lists_of_fun.
     symmetry.
     rewrite Znth_map by (rewrite Zlength_iota; rep_lia).
     rewrite !Znth_i_list_of_fun by rep_lia.
     rewrite Znth_i_iota by rep_lia.
     repeat (if_tac; try rep_lia; [ ] ).
     simpl.
     f_equal.
     unfold subtract_loop.
     change (Float.sub ?x ?y) with (BMINUS x y).
     replace (seq.iota 0 (Z.to_nat (k + 1))) with (seq.iota 0 (Z.to_nat k) ++ [Z.to_nat k]).
     rewrite !map_app, fold_left_app.
     reflexivity.
     replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
     simpl.
      rewrite iota_plus1. f_equal.
    * 
     unfold matrixf.
     rewrite N_eq in *; forward; 
     change (Vundef :: _ :: _) with (default_val (tarray tfloat 1000));
     rewrite <- N_eq in *; fold matrixf.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
     unfold matrixf.
     rewrite N_eq in *.
     rewrite Znth_lists_done by lia.
     set (jj := lists_of_fun _ (done_to_ij _ _ _ _ _)).
     freeze FR1 := (data_at rsh _ _ _).
     forward.
     thaw FR1.
     set (rij := Float32.div _ _).
     subst jj.
     Exists (updij R i j rij).
     rewrite <- N_eq.
     rewrite upd_Znth_lists_of_fun by rep_lia.
     entailer!!.
     change Float32.div with (BDIV (ty:=Tsingle)) in rij.
     apply update_i_lt_j; auto. lia.
  + clear R. Intros R.
    freeze FR2 := (data_at sh _ _ _).
    unfold matrixf.
    rewrite N_eq in *.
    forward.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    rewrite <- N_eq in *; fold matrixf.
    thaw FR2.
    freeze FR3 := (data_at rsh _ _ _).
    deadvars!.
   forward_for_simple_bound j
     (EX k:Z, 
      PROP()
      LOCAL(temp _s (Vsingle (subtract_loop A R j j k) );
            temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(FRZL FR3;
          data_at sh matrixf (lists_of_fun N (done_to_ij (Vsingle oo @float_of_ftype Tsingle _) n j (j+1) R)) r))%assert.
  * entailer!!.
    unfold done_to_n.
    rewrite Znth_lists_done by lia. reflexivity.
  * 
    unfold matrixf.
    rewrite N_eq in *.
    forward.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    rewrite <- N_eq in *; fold matrixf.
    rewrite Znth_lists_done by lia.
    forward.     
    entailer!!.
    f_equal.
    change Float32.sub with (BMINUS (ty:=Tsingle)). change Float32.mul with (BMULT (ty:=Tsingle)).
    apply @subtract_another; lia.
  * forward_call.
    unfold matrixf.
    rewrite N_eq in *.
    forward.
    rewrite <- N_eq in *; fold matrixf.
    rewrite upd_Znth_lists_of_fun by rep_lia.
    set (R' := updij _ _ _ _).
    Exists R'.
    thaw FR3.
    entailer!!.
    change (Binary.Bsqrt _ _ _ _ _ _ ?x) with (BSQRT _ _  x) in R'.
    intros i' j'.
    destruct (zlt j' (j+1));
      [ | split; intros; [ lia | split; intros; lia]].
    assert (Hsub: forall i j', 0 <= i <= j' -> i'<=j'<=j -> 
             subtract_loop A R' i j' i' = subtract_loop A R i j' i'). {
      clear j' l; intros i j' Hi Hj'.
      set (x := BSQRT _ _ _) in R'. clearbody x.
      subst R'. destruct H0.
      clear - H0 Hi Hj'.
      unfold subtract_loop.
      rewrite !map_map.
      pose (f z := BMULT (ty:=Tsingle) z z ).
      set (g1 := BMULT (ty:=Tsingle)). set (g2 := BMINUS (ty:=Tsingle)).
      set (a := A i j'). clearbody a. clearbody g1. clearbody g2.
      set (n:=j) at 1 2 3 4.
      set (u := O).  assert (Z.of_nat (u+ Z.to_nat i')<=n) by lia. clearbody u. clearbody n.
      revert a u H; induction (Z.to_nat i'); intros; auto.
      simpl. rewrite IHn0 by lia. f_equal. f_equal. f_equal. unfold updij.
      rewrite if_false by lia. auto. unfold updij. rewrite if_false by lia. auto.
    }
    destruct (zlt j' j); split; intros; try lia.
    ++ clear H2 l.
      destruct (H1 i' j') as [? _].
      specialize (H2 l0).
      set (x := BSQRT _ _ _) in R'. clearbody x. clear - Hsub H2 l0 H0.
      intro.  specialize (H2 H). destruct H2.
      split; intros.
      ** rewrite Hsub by lia.
      unfold R', updij. rewrite !if_false by lia. auto. 
      ** rewrite Hsub by lia. 
      unfold R', updij. rewrite !if_false by lia. auto. 
    ++ assert (j'=j) by lia. subst j'. clear l g H2.
       red in H1.
       split; intros.
      **
       destruct (H1 i' j) as [_ ?]. specialize (H4 (eq_refl _) ltac:(lia)).
       red in H4. destruct H4 as [? _]; try lia.
       rewrite Hsub by lia.
       unfold R'. unfold updij. rewrite !if_false by lia.
       apply H4; auto. 
      ** subst i'. rewrite Hsub by lia. unfold R', updij.
         rewrite !if_true by auto. auto.
 - Intros R. Exists R.
   rewrite <- N_eq in *.
   entailer!!.
   intros i j.
   specialize (H0 i j).   
   destruct (zlt j n);[ | split; intros; lia].
   destruct H0.
   apply H0; auto.
Qed.







