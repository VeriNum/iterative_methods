From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div prime binomial ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
From mathcomp.algebra_tactics Require Import ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import GroupScope.
Import GRing.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Local Notation "A ^T" := (trmx A) : ring_scope.

Lemma pred_castmx_mn: forall 
  [F: Type] (P: forall [m n], 'M[F]_(m,n) -> Prop),
  forall {m m' n n'} (eqm: m=m') (eqn: n=n') (A: 'M[F]_(m,n)),
   P (castmx (eqm,eqn) A) = P A.
Proof. intros. subst m' n'. by rewrite castmx_id. Qed.

Lemma pred_castmx: forall 
  [F: Type] (P: forall [n], 'M[F]_n -> Prop),
  forall {n n'} (eqn: n=n') (A: 'M[F]_n),
   P (castmx (eqn,eqn) A) = P A.
Proof. intros. subst n'. by rewrite castmx_id. Qed.

Section SemiRing.

Variable F: semiRingType.

Lemma mulmx_castmx:
 forall m m' n n' p p' (eqm: m=m') (eqn: n=n') (eqp: p=p') (A: 'M[F]_(_,_))  B,
    castmx (eqm,eqn) A *m castmx (eqn,eqp) B = castmx (eqm,eqp) (A *m B).
Proof.
 intros.  subst. rewrite !castmx_id //.
Qed.

Definition symmetric {n} (A: 'M[F]_n) := A^T=A.

Lemma symmetric_ulsubmx:
 forall {n} (A: 'M_(n+1)),
  symmetric A -> symmetric (ulsubmx A).
Proof.
move => n A H. rewrite /symmetric trmx_ulsub H //.
Qed.

Definition upper_triangular {n} (A: 'M[F]_n) : Prop := is_trig_mx A^T.

Definition diagonal_nonzero {n} (A: 'M[F]_n) :=
  forall i, A i i != 0.

End SemiRing.

Section Solve_LT.

Variable F : fieldType.


Lemma trig_unitmx_diagonal_nonzero: forall {n} (A: 'M[F]_n),
  is_trig_mx A -> (A \in unitmx <-> forall i, A i i != 0).
Proof.
 move => n A H0. 
 rewrite unitmxE.
 rewrite (det_trig H0).
 transitivity (forall i: 'I_n, is_true true -> A i i != 0).
 - rewrite (rwP (prodf_neq0 _ _)) unitfE //.
 - split; intros; auto.
Qed.

Lemma upper_unitmx_diagonal_nonzero: forall {n} (A: 'M[F]_n),
  upper_triangular A -> (A \in unitmx <-> forall i, A i i != 0).
Proof.
move => n A H.
rewrite -unitmx_tr trig_unitmx_diagonal_nonzero //.
split; move => H0 i; move :(H0 i); by rewrite mxE.
Qed.

Ltac must_show P := lazymatch goal with |- ?Q => unify P Q end.

(*  let L be a nonsingular lower triangular matrix,
    let c be a column matrix,
    then solve_LT L c finds a column matrix x such that L x = c. *)
Fixpoint solve_LT {n} :  'M[F]_n.+1 -> 'M[F]_(n.+1,1) -> 'M[F]_(n.+1,1) :=
 match n with
 | 0 => fun L c => const_mx ((L 0 0)^-1 *  c 0 0 )
 | n'.+1 => fun L c =>
        let L' : 'M_(1 + n'.+1) := L in
        let c' : 'M_(1+n'.+1,1) := c in
        let x' := solve_LT (drsubmx L') (dsubmx c' - dlsubmx L' *m ((L 0 0)^-1 *: usubmx c')) in
         col_mx ( (L 0 0)^-1 *: usubmx c') x'
 end.

Lemma solve_LT_correct:
  forall n (L: 'M[F]_n.+1) (c: 'M[F]_(n.+1,1)),
    is_trig_mx L ->
    L \in unitmx ->  (*    diagonal_nonzero L ->*)
    L *m solve_LT L c = c.
Proof.
move => n L c H H0. rewrite (trig_unitmx_diagonal_nonzero H) in H0.
move :n L c H H0.
induction n.
- intros; simpl.
rewrite {1}(mx11_scalar L) mul_scalar_mx scalemx_const mulrA divrr ?unitfE //= mul1r.
apply matrixP => i j; rewrite !ord1 !mxE //=.
-
rewrite /solve_LT -/solve_LT -['M[F]_n.+2]/'M[F]_(1+n.+1) 
           -['cV[F]_n.+2]/'cV[F]_(1+n.+1) => L c H H0.
set c' := dsubmx c - dlsubmx L *m ((L 0 0)^-1 *: usubmx c).
must_show (L *m col_mx ((L 0 0)^-1 *: usubmx c) (solve_LT (drsubmx L) c') = c).
rewrite -{1}(submxK L) (mul_block_col (ulsubmx L)) (ursubmx_trig (A:=L)) //
         mul0mx addr0 -!scalemxAr.
must_show (col_mx ((L 0 0)^-1 *: (ulsubmx L *m usubmx c))
                  ((L 0 0)^-1 *: (dlsubmx L *m usubmx c) + drsubmx L *m solve_LT (drsubmx L) c') 
           = c).
rewrite {}IHn ; [ | by apply drsubmx_trig | by move => i; rewrite !mxE ].
must_show (col_mx ((L 0 0)^-1 *: (ulsubmx L *m usubmx c))
                  ((L 0 0)^-1 *: (dlsubmx L *m usubmx c) + c') = c).
subst c'.
rewrite -scalemxAr addrA (addrC _ (dsubmx c)) addrK scalemxAl (_: ulsubmx L = const_mx (L 0 0)).
2: apply matrixP => i j; by rewrite !ord1 !mxE !lshift0.
must_show (col_mx ((L 0 0)^-1 *: const_mx (L 0 0) *m usubmx c) (dsubmx c) = c).
rewrite scalemx_const mulrC divrr ?unitfE //= (_: const_mx _ = 1).
2: apply matrixP => i j; by rewrite !ord1 !mxE.
must_show (col_mx (1 *m usubmx c) (dsubmx c) = c).
by rewrite mulmxE mul1r vsubmxK.
Qed.

End Solve_LT.

From mathcomp Require Import ssrnum reals interval classical_sets topology normedtype boolp.
Import Num.Theory Num.Def numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.

Section PosDef.
(* Properties of positive definite matrices *)

Variable F : realType.

Definition posdef' {n} (A: 'M_n) :=
   forall x : 'cV_n, x != 0 -> (x^T *m A *m x) 0 0 > 0 :>F.

Definition positive_definite {n} (A: 'M_n) :=
  symmetric A /\ posdef' A.

Lemma positive_definite_ulsubmx:
 forall {n} (A: 'M_(n+1)),
  positive_definite A -> positive_definite (ulsubmx A).
Proof.
 move => n A [SYM H].
 split.
 by apply symmetric_ulsubmx.
 move => x H0.
 have H2: col_mx x 0%:M != 0. {
   move :H0; apply contra_neq => H0.
   rewrite -col_mx0 in H0.
   apply eq_col_mx in H0.
   apply H0.
 }
 move :(H _ H2).
 rewrite -{1}(submxK A) /block_mx (tr_col_mx x) (mul_row_col x^T)
     tr_scalar_mx mul_scalar_mx scale0r addr0 -mulmxA (mul_row_col (ulsubmx A))
     scalar_mxC mul_scalar_mx scale0r addr0 mulmxA //.
Qed.

Lemma posdef'_det_not_zero: forall {n} (A: 'M[F]_n), posdef' A -> \det A != 0.
Proof.
  move => n A. rewrite /posdef'. apply: contraPneq.
  move /eqP /det0P => [v Hn0 Hm0] Hposdef.
  have HTn0: v^T != 0 by move: Hn0; apply: contraTneq; move /eqP; rewrite trmx_eq0; move ->.
  move /(_ v^T HTn0): Hposdef. by rewrite trmxK Hm0 mul0mx mxE ltxx.
Qed.

Lemma posdef'_interval_det_not_zero: forall {n} (A: 'M[F]_n),
    posdef' A -> forall (t: F), 0 <= t <= 1 -> \det (t%:M + (1 - t) *: A) != 0.
Proof.
  move => n A Hpos t /andP [Hle0 Hle1]. apply: posdef'_det_not_zero.
  rewrite /posdef' => x Hx.
  rewrite mulmxDr mulmxDl mul_mx_scalar -mulmxA -!scalemxAl -scalemxAr mulmxA
         mxE [x in 0 < x + _]mxE [x in 0 < _ + x]mxE.
  have Hpos1: 0 < (x^T *m A *m x) 0 0 by move: Hpos; rewrite /posdef' => /(_ x Hx) //.
  have Hpos2: 0 < (x^T *m x) 0 0. {
    elim /col_ind: {Hpos1 Hpos Hle0 Hle1 t A} x Hx => [x | m r x Hi].
    - by rewrite !flatmx0 mulmx0 mxE => /eqP.
    - rewrite tr_col_mx mul_row_col. case: (r == 0) /eqP => [-> | Hn _].
      + rewrite mulmx0 add0r. case: (x == 0) /eqP => [-> | /eqP Hn _];
        first by rewrite col_mx0 => /eqP. exact: Hi Hn.
      + have Hlt0r: 0 < (r^T *m r) 0 0. {
          rewrite (@mx11_scalar _ r) tr_scalar_mx -scalar_mxM mxE /= mulr1n -GRing.expr2.
          have: 0 <= r 0 0 ^+ 2 by apply: sqr_ge0.
          rewrite le0r => /orP [ | //]. rewrite sqrf_eq0.
          move: Hn. rewrite {1}(@mx11_scalar _ r) => Hn Heq.
          move: Heq Hn => /eqP -> /eqP. by rewrite -scalemx1 scale0r => /eqP. }
        case: (x == 0) /eqP => [-> | /eqP Hneq]; first by rewrite mulmx0 addr0.
        rewrite mxE. apply: ltr_pDl => //. exact: Hi. }
  move: Hle0. rewrite le0r.
  move /orP => [/eqP -> | Heq]; first by rewrite mul0r add0r subr0 mul1r.
  apply: ltr_pwDl; first exact: mulr_gt0.
  apply: mulr_ge0; last exact: ltW.
  by rewrite subr_ge0.
Qed.

Lemma addr_continuous {K : numFieldType} {V : pseudoMetricNormedZmodType K} (x: V) :
  continuous ( +%R x).
Proof. by move=> t; apply: (cvg_comp2 (cvg_cst _) cvg_id (@add_continuous _ _ (_, _))). Qed.

Lemma interval_continuous: forall {n} (A: 'M[F]_n.+1),
    continuous ((fun t  => t%:M + (1 - t) *: A) :> F -> 'M[F]_n.+1).
Proof.
  move=> n A.
  under eq_fun do
      rewrite -scalemx1 scalerBl scale1r addrC -addrA [- _ + _] addrC -scalerBr.
  rewrite /continuous_at. move => x. apply: continuous_comp. apply: scalel_continuous.
  by apply: addr_continuous.
Qed.

Lemma fun_mul_continuous {K : numFieldType} {T: topologicalType} (f g: T -> K):
  continuous f -> continuous g -> continuous (fun M : T => f M * g M).
Proof.
  move => cf cg. rewrite /continuous_at => x. apply: continuousM.
  by apply cf. by apply cg.
Qed.

Lemma prod_continuous {K : numFieldType} {m: nat} {T: topologicalType} (f: T -> 'I_m.+1 -> K):
  (forall i, continuous (f ^~ i)) -> continuous (fun A : T => \prod_i (f A) i).
Proof.
  move: f. elim: m => [|m IHm] => f cf.
  - have -> : (fun A => \prod_i f A i) = (fun A => f A ord0).
    by under eq_fun do rewrite big_ord1. apply: cf.
  - have -> : (fun A => \prod_i f A i)=(fun A => f A ord0 * \prod_(i < m.+1) f A (lift ord0 i)).
    { by under eq_fun do rewrite big_ord_recl. }
    apply fun_mul_continuous. by apply: cf. by apply: IHm => i.
Qed.

Lemma sum_continuous {T: topologicalType} {I: eqType} {K : numFieldType}
  {V : normedModType K} (f: T -> I -> V) (r: seq I):
  (forall i, continuous (f ^~ i)) -> continuous (fun A : T => \sum_(i <- r) f A i).
Proof.
  move => cf. elim: r => [|h rest IHn].
  - have -> : (fun A : T => \sum_(i <- [::]) f A i) = (fun A : T => 0).
    { by under eq_fun do rewrite big_nil. } apply: cst_continuous.
  - have -> : (fun A : T => \sum_(i <- (h :: rest)) f A i) =
               (fun A : T => f A h + \sum_(i <- rest) f A i).
    { by under eq_fun do rewrite big_cons. }
    rewrite /continuous_at => x. apply: continuousD. by apply cf. by apply IHn.
Qed.

Lemma determinant_continuous: forall {n}, continuous (determinant :> 'M[F]_n.+1 -> F).
Proof.
  rewrite /determinant => n.
  remember (fun (A : 'M_n.+1) (s : 'S_n.+1) => (-1) ^+ s * \prod_i A i (s i) :> F) as f.
  have -> : (fun A : 'M_n.+1 => \sum_(s: 'S_n.+1) (-1) ^+ s * \prod_i A i (s i)) =
             (fun A : 'M_n.+1 => \sum_s f A s) by rewrite Heqf.
  apply: sum_continuous => /= => s. rewrite Heqf.
  apply: fun_mul_continuous => /=.
  - by apply: cst_continuous.
  - apply: prod_continuous => /= => i. by apply: coord_continuous.
Qed.

Lemma interval_det_continuous: forall {n} (A: 'M[F]_n.+1),
    continuous ((fun t  => \det (t%:M + (1 - t) *: A)) :> F -> F).
Proof.
  move => n A. rewrite /continuous_at. move=> x.
  apply: continuous_comp. apply: interval_continuous.
  by apply: determinant_continuous.
Qed.

(* Dan Shved (https://math.stackexchange.com/users/47560/dan-shved),
   Does a positive definite matrix have positive determinant?, URL
   (version: 2020-11-22): https://math.stackexchange.com/q/894397 *)
Lemma det_positive_definite: forall {n} (A: 'M[F]_(n.+1)),
  positive_definite A -> 0 < \det A .
Proof.
  move => n A [Hs Hp].
  remember ((fun t  => \det (t%:M + (1 - t) *: A)) :> F -> F) as f.
  have Hfc: {within `[0, 1], continuous f}
    by rewrite Heqf; apply: continuous_subspaceT; apply: interval_det_continuous.
  have Hn: ~ (exists2 c : F, c \in `[0, 1]%R & f c = 0). {
    move => [c Hin Hc]. move: Hin. rewrite itv_boundlr /<=%O /= => Hin.
    move: Hc. rewrite Heqf. apply/eqP. by apply : (posdef'_interval_det_not_zero Hp) Hin. }
  have: ~ (minr (f 0) (f 1) <= 0 <= maxr (f 0) (f 1))
    by move: Hn; apply: contra_not (IVT ler01 Hfc).
  move/negP /nandP. rewrite -!Order.TotalTheory.ltNge. move {Hn}.
  have -> : f 0 = \det A by rewrite Heqf subr0 scale1r -scalemx1 scale0r add0r.
  have -> : f 1 = 1 by rewrite Heqf subrr scale0r addr0 det1. move=> [Hlt | Hlt]; move: Hlt.
  - rewrite minElt. case: ifPn => [// |]. rewrite -Order.TotalTheory.leNgt.
    move/[swap] => _. apply: lt_le_trans ltr01.
  - rewrite maxElt. case: ifPn => [_ |].
    + rewrite Order.TotalTheory.ltNge. move /negP => Hc. exfalso. apply: Hc. by apply: ler01.
    + rewrite -Order.TotalTheory.leNgt. move/[swap] => _. apply: lt_le_trans ltr01.
Qed.

End PosDef.

Section MiscMatrixFacts.

Variable F : realType.

Lemma block_decompose {n1 n2} {A: 'M[F]_n1} {B: 'M[F]_(n1, n2)}
  {C: 'M[F]_(n2, n1)} {D: 'M[F]_n2}:
  A \in unitmx ->
  block_mx A B C D = (block_mx 1%:M 0 (C *m invmx A) 1%:M) *m
                     (block_mx A 0 0 (D - C *m invmx A *m B)) *m
                     (block_mx 1%:M (invmx A *m B) 0 1%:M).
Proof.
  move => Ai. rewrite !mulmx_block !mulmx0 !mul0mx !mulmx1 !mul1mx !addr0 add0r (mulmxA A).
  by rewrite (mulmxV Ai) -(mulmxA C) (mulVmx Ai) !mulmx1 mul1mx mulmxA addrCA subrr addr0.
Qed.

Lemma det_block_mx {n1 n2} (A: 'M[F]_(n1+n2)):
  ulsubmx A \in unitmx ->
  \det A = \det (ulsubmx A) * \det (drsubmx A - dlsubmx A *m invmx (ulsubmx A) *m ursubmx A).
Proof.
  move => Ai. rewrite -{1}(submxK A) (block_decompose Ai) !det_mulmx !det_lblock det_ublock.
  by rewrite !det1 !mulr1 mul1r.
Qed.

Lemma map_mx11: forall {V T} (f: GRing.Nmodule.sort V -> GRing.Nmodule.sort T) (a: GRing.Nmodule.sort V),
    @map_mx _ _ f 1 1 (@scalar_mx _ 1 a) = @scalar_mx _ 1 (f a).
Proof.
move => V T f a.
apply matrixP => i j.
by rewrite !ord1 !mxE eqxx /=  !mulr1n.
Qed.

End MiscMatrixFacts.

Section Cholesky.
Variable F : realType.

Lemma add_two {n}: n.+2 = n.+1+1.
Proof. rewrite addrC //. Qed.

(* This algorithm is from Theorem 10.1 of Higham, Accuracy and Stability of Numerical Methods *)
Fixpoint cholesky {n} : 'M[F]_n.+1 -> 'M[F]_n.+1 :=
  match n with
  | 0 => fun A => map_mx Num.sqrt A
  | n'.+1 => fun A =>
         let A' : 'M_(n'.+1+1):= castmx (add_two,add_two) A in
         let A1 := ulsubmx A' in
         let c := ursubmx A' in
         let α := drsubmx A' in
         let R1 := cholesky A1 in
         let r := solve_LT R1^T c in
         let β := map_mx Num.sqrt (α - ((r^T *m r))) in
         castmx (esym add_two, esym add_two) (block_mx R1 r 0 β)
  end.

Definition diagonal_positive {n} (A: 'M[F]_n) :=
  forall i, A i i > 0 :>F.

(*  Theorem 10.1 of Higham, Accuracy and Stability of Numerical Methods *)
Theorem cholesky_correct:
  forall n (A: 'M_n.+1),
    positive_definite A ->
    let R := cholesky A in
      upper_triangular R /\ diagonal_positive R /\ R^T * R = A.
Proof.
elim => [|n IHn] A.
-
 simpl.
 move => [H H0].
 repeat split.
 + apply mx11_is_trig.
 + move => i. rewrite ord1 !mxE.
   move :(H0 1 ltac:(apply oner_neq0)).
   rewrite trmx1 mul1mx mulmx1 sqrtr_gt0 //.
 + rewrite (mx11_scalar A) !map_mx11 tr_scalar_mx -mulmxE -scalar_mxM -expr2 sqr_sqrtr //.
   move : (H0 1 (oner_neq0 _)).
   rewrite !mulmxE trmx1 mulr1 mul1r.
   apply ltW.
-
rewrite -(castmxK add_two add_two A).
set A' : 'M_(n.+1 + 1) := castmx _ A.
rewrite pred_castmx.
move :A' => {}A PA.
rewrite /cholesky -/cholesky
 pred_castmx trmx_cast tr_block_mx -mulmxE mulmx_castmx castmxKV /=.
set A1 := ulsubmx A.
case: (IHn A1) => [ | UPPER [DP H1]] {IHn};
  first by apply positive_definite_ulsubmx.
move :(cholesky _) => R in UPPER DP H1 *.
set α := drsubmx A.
set c := ursubmx A.
have Runit : R \in unitmx. {
  rewrite upper_unitmx_diagonal_nonzero // => i.
  apply /negP => /eqP EQ. move :(DP i). rewrite EQ => GT.
  eapply lt_nsym; eassumption.
}
have H2 := @solve_LT_correct _ _ (R^T) c UPPER ltac:(rewrite unitmx_tr //).
move :(solve_LT _ _) => r in H2 *.
set β2 := α - r^T *m r.
set β := map_mx Num.sqrt β2.
have EQA: A = block_mx A1 c c^T α
    by rewrite -(submxK A) trmx_ursub (proj1 PA).
assert (POSβ: 0 < β2 0 0). {
 have Adet: 0 < \det A1
  by apply det_positive_definite, positive_definite_ulsubmx, PA.
 have A1unit: A1 \in unitmx
  by rewrite unitmxE unitfE; apply lt0r_neq0, Adet.
 move :(det_positive_definite PA).
 rewrite (det_block_mx (A:=A)) // -/A1 -/c -/α EQA block_mxKdl -H2 trmx_mul trmxK
        mulmxA -!(mulmxA r^T) -{2}H1.
 rewrite -H1 in A1unit.
 move :(mulmxK A1unit (invmx R^T)).
 rewrite !(mulmxA (invmx _)) mulVmx ?unitmx_tr // mul1mx.
 move => GG. rewrite {}GG mulVmx ?unitmx_tr // mul1mx det_mx11 mxE /β2.
 rewrite mxE pmulr_rgt0 //.
}
repeat split.
+ rewrite /upper_triangular tr_block_mx is_trig_block_mx // trmx0
       eqxx UPPER mx11_is_trig //.
+ move => i. rewrite castmxE /= esymK.
  case: (split_ordP (cast_ord add_two i)) => i0 e.
  * rewrite e block_mxEul //.
  * rewrite e block_mxEdr ord1 mxE sqrtr_gt0 //.
+
f_equal.
rewrite mulmx_block !mulmx0 !addr0 !mulmxE !H1 !trmx0 !mul0mx !addr0
    -{2}(trmxK R) -trmx_mul H2 EQA.
f_equal.
rewrite (mx11_scalar β) tr_scalar_mx -mulmxE -scalar_mxM /β mxE
  -expr2 sqr_sqrtr;
 last by apply ltW.
rewrite -mx11_scalar /β2 (addrC α) addrA addrN add0r //.
Qed.

Lemma vecnorm2_ge0: forall {n} (x: 'cV[F]_n), 0 <= (x^T *m x) 0 0.
Proof.
elim => [ | n IHn].
- move => x. rewrite flatmx0 trmx0 mulmx0 mxE //.
-
rewrite (_: n.+1 = n + 1); last by lia.
move => x.
rewrite -(vsubmxK x) tr_col_mx mul_row_col mxE.
apply addr_ge0.
apply IHn.
rewrite (mx11_scalar (dsubmx x)).
move :(dsubmx x 0 0) => a.
rewrite tr_scalar_mx mul_scalar_mx !mxE eqxx /= mulr1n -expr2.
apply sqr_ge0.
Qed.

Lemma vecnorm0: forall {n : nat} (x : 'cV[F]_n),
         (x^T *m x) 0 0 = 0 -> x=0.
Proof.
elim => [ | n IHn].
- move => x. rewrite flatmx0 trmx0 mulmx0 mxE //.
-
rewrite (_: n.+1 = n + 1); last by lia.
move => x.
rewrite -(vsubmxK x) tr_col_mx mul_row_col.
move :(usubmx x) => a.
move :(dsubmx x) => b.
move => H.
have Na := vecnorm2_ge0 a.
have Nb := vecnorm2_ge0 b.
have Ha: a=0. apply IHn. rewrite mxE in H.
  set a' := (a^T *m a) 0 0 in H Na *.
  set b' := (b^T *m b) 0 0 in H Nb *.
  clearbody a'. clearbody b'. clear - H Nb Na. lra.
subst a. rewrite trmx0 mulmx0 add0r in H.
have Hb: b=0.
rewrite (mx11_scalar b) tr_scalar_mx -scalar_mxM in H.
rewrite mxE eqxx /= mulr1n -expr2 in H.
move :H => /eqP H. 
rewrite sqrf_eq0 in H. move :H => /eqP H.
apply matrixP. move => i j. rewrite !ord1 H mxE //.
rewrite  Hb.
apply col_mx0.
Qed.

Lemma cholesky_upper_triangular:
  forall (n: nat) (A: 'M_n.+1),
    upper_triangular (cholesky A).
Proof.
elim => [ | n IHn] A.
- apply mx11_is_trig.
- rewrite -(castmxK add_two add_two A).
set A' : 'M_(n.+1 + 1) := castmx _ A.
clearbody A'; clear A; move :A' => A.
rewrite /cholesky -/cholesky pred_castmx.
set A1 := ulsubmx _.
move :(IHn A1). rewrite /upper_triangular {IHn} => IH.
rewrite tr_block_mx is_trig_block_mx // trmx0 eqxx IH /=.
apply mx11_is_trig.
Qed.

(* This useful theorem is not mentioned in Higham's book *)
Theorem cholesky_positive_definite:
  forall (n: nat) (A: 'M_n.+1),
    symmetric A ->  diagonal_positive (cholesky A) -> positive_definite A.
Proof.
intros.
split. done.
set R := cholesky A in H0 *.
suffices HH: R^T * R = A /\ posdef' A. apply HH.
revert n A H R H0.
(* Now the right induction hypothesis is set up *)
elim => [|n IHn].
-
 simpl.
 move => A SYMM DPOS.
 split.
 + rewrite (mx11_scalar A) !map_mx11 tr_scalar_mx -mulmxE -scalar_mxM -expr2 sqr_sqrtr //.
   move : (DPOS 0). rewrite !mxE sqrtr_gt0.
   apply ltW.
 + move => i Hi. rewrite (mx11_scalar i) tr_scalar_mx (mx11_scalar A).
   rewrite -!scalar_mxM. rewrite mxE eqxx /= mulr1n mulrC mulrA.
  move :(sqr_ge0 (i 0 0)). rewrite expr2 => Hii. 
  apply mulr_gt0; auto.
  have Hi': i 0 0 != 0
    by refine (contra_neq _ Hi) => Hi'; rewrite (mx11_scalar i) (mx11_scalar 0) Hi' mxE.
  rewrite (mx11_scalar i) in Hi.
  rewrite lt0r Hii Bool.andb_true_r mulf_neq0 //.
  move :(DPOS 0). rewrite mxE sqrtr_gt0 //.
-
move => A.
rewrite -(castmxK add_two add_two A).
set A' : 'M_(n.+1 + 1) := castmx _ A.
rewrite pred_castmx.
clearbody A'; clear A.
move :A' => A PA.
rewrite /cholesky -/cholesky
    !pred_castmx trmx_cast -mulmxE mulmx_castmx castmxKV /=.
set A1 := ulsubmx A.
set α := drsubmx A.
set c := ursubmx A.
move => DP.
case: (IHn A1);
 [by apply symmetric_ulsubmx
 | by move => i; move :(DP (lshift 1 i)); rewrite block_mxEul
 | ].
clear IHn.
move :(cholesky_upper_triangular A1) => UT1.
move :(cholesky _) => R1 in UT1 DP *.
move => H1 PD.
set r := solve_LT R1^T c in DP *.
have DPR: diagonal_positive R1.
  by move => i; move :(DP (lshift 1 i)); rewrite block_mxEul.
have R1unit: R1 \in unitmx. {
     rewrite unitmxE unitfE -det_tr (det_trig UT1).
     apply /prodf_neq0 => i _. rewrite mxE. 
     by apply lt0r_neq0. 
  }
have H2: R1^T *m r = c.
     by apply solve_LT_correct; auto; rewrite unitmx_tr.
move :r => r in DP H2 *.
set β2 : 'M_1 := α - r^T *m r in DP *.
set β := map_mx Num.sqrt β2 in DP *.
have EQA: A = block_mx A1 c c^T α
    by rewrite -(submxK A) trmx_ursub PA.
set R := block_mx R1 r 0 β in DP *.
have POSβ: 0 < β2 0 0. {
 have A1det: 0 < \det A1.
   apply det_positive_definite. split; last done. by apply symmetric_ulsubmx.
 have A1unit: A1 \in unitmx
  by rewrite unitmxE unitfE; apply lt0r_neq0, A1det.
 move :(DP (rshift n.+1 0)).
 rewrite /R block_mxEdr /β mxE sqrtr_gt0 //.
 }
have H3: R^T *m R = A. {
 rewrite /R tr_block_mx mulmx_block
     !mulmx0 !addr0 !mulmxE !H1 !trmx0 !mul0mx !addr0 H2 EQA.
 f_equal.
 rewrite -H2 trmx_mul trmxK //.
 rewrite (mx11_scalar β) tr_scalar_mx -mulmxE -scalar_mxM /β mxE -expr2 sqr_sqrtr. 
 rewrite -mx11_scalar /β2 (addrC α) addrA addrN add0r //.
 by apply ltW.
}
 split; first by rewrite H3.
 move => x Hx.
 rewrite -H3 mulmxA -mulmxA -trmx_mul.
 suffices HRx: R *m x != 0. {
   move :(R *m x) => a in HRx *.
   clear - HRx.
   rewrite lt0r. apply /andP. split.
   +  move :HRx; apply contra_neq => H. by apply vecnorm0.
   +  apply vecnorm2_ge0.
 }
 have UT: upper_triangular R. {
    rewrite /upper_triangular /R tr_block_mx is_trig_block_mx // trmx0 eqxx
            -/(upper_triangular R1) UT1 /=.
    apply mx11_is_trig.
 }
 have Runit: R \in unitmx.  {
     rewrite unitmxE unitfE -det_tr (det_trig UT).
     apply /prodf_neq0 => i _. rewrite mxE. 
     by apply lt0r_neq0. 
  }
  move: Hx. apply: contra_neq => Hx.
  by rewrite -(@mulKmx _ _ _ _ Runit x) Hx mulmx0.
Qed.

End Cholesky.

Unset Implicit Arguments.

Section Cholesky_jik.

Variable F : realType.

Axiom proof_irr: forall (P: Prop) (H1 H2: P), H1=H2.

Lemma ordinal_eq: forall {n m1 m2} P1 P2, m1=m2 -> @Ordinal n m1 P1 = @Ordinal n m2 P2.
Proof.
intros; subst. f_equal. apply proof_irr.
Qed.

Definition widen_ik [n: nat] (i: 'I_n) (k: 'I_i) : 'I_n := 
   widen_ord (ltnW (ltn_ord i)) k.

Definition widen_ik_subproof [n i: nat] (k: 'I_i) (H: (i<n.+1)%N) : (k < n.+1)%N := 
  widen_ord_proof k (ltnW (ltn_ord (Ordinal H))).

Lemma widen_ik_sub: 
  forall (n i: nat) (H: (i < n.+1)%N) (k: 'I_i),
   widen_ik (Sub i H) k = Sub (nat_of_ord k) (widen_ik_subproof k H).
Proof. reflexivity. Qed.

Lemma solve_LT_eq: forall [n] (L: 'M[F]_n.+1) (c: 'cV[F]_n.+1),
   let r := solve_LT L c in
     forall i: 'I_n.+1,
        r i 0 = (c i 0 - \sum_(k<i) (fun k' => L i k' * r k' 0) (widen_ik i k))/L i i.
Proof.
elim  => [ | n IH] L c r i.
- rewrite /r ord1 big_ord0 /= mxE mulrC subr0 //.
- simpl in r.
  set L': 'M_(1+n.+1) := L.
  set c': 'cV_(1+n.+1) := c.
  set c1 := dsubmx c' - dlsubmx L' *m ((L 0 0)^-1 *: usubmx c').
  specialize (IH (drsubmx L') c1).
  revert r.
  set r' := solve_LT (drsubmx L') c1 in IH *.
  move => r.
  cbv zeta in IH.
  clearbody r'.
  subst r.
  change 'I_(1+n.+1) in i.
  case: (split_ordP i) => i' Hi'; subst i. rewrite ord1; clear i'.
 + set x := _ *: _. simpl in x.
   rewrite -(vsubmxK c') !(col_mxEu _ _ (0:'I_1)).
   rewrite -(submxK L') (block_mxEul _ _ _ _ (0:'I_1) (0:'I_1)).
   change (_ *: _) with x in c1. simpl in c1.
   simpl. rewrite big_ord0 subr0 /x mxE mulrC /c' !mxE lshift0 //.
 + set x := _ *: _. simpl in x.
   rewrite -(vsubmxK c') (col_mxEd x) (col_mxEd (usubmx c')).
   rewrite -{2}(submxK L'). rewrite  (block_mxEdr (ulsubmx L')).
   rewrite (IH i') /c1 -/x. clear IH c1.
   f_equal.
   rewrite mxE -addrA.
   f_equal.
   rewrite big_split_ord /= big_ord1 mxE mxE.
   have ->: widen_ik (rshift 1 i') (lshift i' 0) = lshift n.+1 0.
     apply ordinal_eq; reflexivity.
   rewrite (col_mxEu x) big_ord1.
   have ->:  L' (rshift 1 i') (lshift n.+1 0) = dlsubmx L' i' 0.
      by rewrite -(submxK L') block_mxEdl block_mxKdl.
   move :(_ * _) => u.
   set a := bigop _ _ _. set b := bigop _ _ _.
   rewrite (_: a=b); first by field.
   apply eq_big; auto.
   move => i _.
   have ->: widen_ik (rshift 1 i') (rshift 1 i) = rshift 1 (widen_ik i' i)
       by apply ordinal_eq; reflexivity.
   f_equal.
   * rewrite -{2}(submxK L') (block_mxEdr (ulsubmx L')) //.
   *  rewrite (col_mxEd x) //.
Qed.

Definition sumR := List.fold_right GRing.add  (0:F).


Definition Mij {n} (A: 'M[F]_n.+1) (i j : nat) : F :=
 if insub i is Some i' then if insub j is Some j' then A i' j' else 0 else 0.

Definition Vi {n} (x: 'cV[F]_n.+1) (i: nat) : F :=
  if insub i is Some i' then x i' 0 else 0.
 

Lemma sum_nat_sumR: forall n (f: nat -> F),
  \sum_(0<= i < n) f i = sumR [seq f i | i <- index_iota 0 n].
Proof.
 intros i f.
  set lo := 0%nat.
  unfold index_iota.
  set n := (i-lo)%N. clearbody n.
  move :n lo.
  elim => [ | n Hn] lo. 
 + 
   have ->: iota lo 0 = index_iota lo 0. unfold index_iota. f_equal; lia.
   rewrite big_geq; auto.
 + transitivity (\sum_(k <- index_iota lo (lo+n).+1) f k).
   f_equal. unfold index_iota; f_equal; lia.
   rewrite big_nat_recl; last lia.
   simpl. rewrite -Hn. f_equal.
   have ->: iota lo.+1 n = index_iota lo.+1 ((n+lo).+1). unfold index_iota; f_equal; lia.
   rewrite big_add1.
   f_equal. f_equal. lia.
Qed.

Lemma iota_0_index_iota: forall i, iota 0 i = index_iota 0 i.
Proof.
move => i. rewrite /index_iota; f_equal; lia.
Qed.

Lemma solve_LT_eq': forall n (L: 'M[F]_n.+1) (c: 'cV[F]_n.+1),
   let r := solve_LT L c in
     forall i: nat,
        (i < n.+1)%N ->
        Vi r i = (Vi c i - sumR (map (fun k => Mij L i k * Vi r k) (iota 0 i))) / Mij L i i.
Proof.
move => n L c r i H.
have H0 := solve_LT_eq L c (Sub i H).
rewrite iota_0_index_iota.
rewrite -/r in H0. 
rewrite /Vi /Mij.
rewrite insubT.
rewrite {}H0.
f_equal. f_equal. f_equal.
transitivity (\sum_(0 <= k < i) Mij L i k * Vi r k).
-
  rewrite big_mkord.
  apply eq_bigr.
  move => k _.
  pose Hk := widen_ik_subproof k H.
  rewrite widen_ik_sub /Mij /Vi !insubT //.
- rewrite /Mij /Vi insubT sum_nat_sumR //.
Qed.

Definition cholesky_jik_spec {n} (A R: 'M[F]_(n.+1)) : Prop :=
  R = \matrix_(i,j) 
        if (i<j)%N then (A i j - \sum_(k<i) (R (widen_ik i k) i * R (widen_ik i k) j)) / R i i
        else if i==j then Num.sqrt(A j j - \sum_(k<i) (R (widen_ik i k) j ^+ 2))
        else 0.

Ltac if_lia b :=
 match goal with |- context[if ?A then _ else _] => 
    have ->: A=b by lia
 end.

Lemma cast_ord_inj': forall [n m: nat] (eq: n=m) x y, (cast_ord eq x == cast_ord eq y) = (x==y).
Proof.
intros.
have H := @cast_ord_inj _ _ eq x y.
apply /eqP.
destruct (@eqP _ x y).
f_equal; auto.
contradict n0; auto.
Qed.


Lemma cholesky_jik_unique: forall [n] (A: 'M[F]_n.+1) R1 R2,
  cholesky_jik_spec A R1 ->
  cholesky_jik_spec A R2 ->
  R1=R2.
Proof.
move => n A R1 R2 H1 H2.
apply matrixP.
red.
Admitted.
(*
assert (forall 

apply matrixP => i j.
assert (H: forall i' j': 'I_n.+1, (j' < j)%N || (j'==j)%N && (i' < i)%N -> R1 i' j' = R2 i' j').
2:{

 => j.
rewrite -(inord_val j).
elim (nat_of_ord j) => [ | j']; clear j.
+
move => i.
rewrite -(inord_val i).
elim (nat_of_ord i) => [ | i']; clear i.
*
rewrite H1 H2 !mxE ltnn eq_refl.
do 3 f_equal.
apply eq_big => i // _.
exfalso.
rewrite inordK in i.
destruct i.
move :i => /ltP; lia.
apply /ltP; lia.
*
move => H.

revert i
apply /ltP in i.
lia.
Search 'I_0.
destruct i.
Search (nat_of_ord (inord _) = _).
rewrite inord_val in i.
destruct i.
lia.
simpl in i.
rewrite ord0.
 auto. //.
intro.
 reflexivity.
apply eq_big_op.
Search (bigop.body _ _ _ = bigop.body _ _ _).
Search (\sum_ _ _ = \sum_ _ _).
rewrite /widen_ik.
f_equal.
f_eual.
Search (nat_of_ord (inord _) = _).
rewrite inordK.
rewrite big_ord0.
simpl.
rewrite 
 inordK.
Search (nat_of_ord (inord _)).
Search ((_ < _)%N = false).
 => [ | j''].
Search nat_of_ord.

*)


Lemma cholesky_jik_spec_eqv: forall n (A: 'M[F]_n.+1),  cholesky_jik_spec A (cholesky A).
Proof.
elim => [ | n IH] A.
-
apply matrixP.
move => i j.
rewrite !ord1 !mxE.
if_lia false.
simpl.
rewrite big_ord0 subr0 //.
-
red.
rewrite -(castmxK add_two add_two A).
move :(castmx (add_two,add_two) A).
clear A.
move => A.
rewrite /cholesky castmxKV.
change (_ n (ulsubmx A)) with (cholesky (ulsubmx A)).
set A1 := ulsubmx A.
specialize (IH A1).
set R1 := cholesky A1 in IH *.
set c := ursubmx A.
have Hr:= solve_LT_eq R1^T c.
set r := solve_LT _ _ in Hr *.
clearbody r.
cbv zeta in Hr.
set α := drsubmx A.
rewrite IH.
set R := castmx _ (block_mx _ _ _ _).
apply matrixP.
move => i j.
rewrite !mxE.
rewrite -(cast_ordK add_two i) -(cast_ordK add_two j).
case: (split_ordP (cast_ord add_two i)) => i0 Hi; rewrite Hi; clear i Hi;
case: (split_ordP (cast_ord add_two j)) => j0 Hj; rewrite Hj; clear j Hj;
rewrite !castmxE !cast_ordK ?block_mxEul ?block_mxEdl ?block_mxEur ?block_mxEdr !mxE; simpl.
+
rewrite cast_ord_inj'.
rewrite eq_refl.
case: (i0 < j0)%N /ltP => Hij.
*
if_lia false.
f_equal.
f_equal.
f_equal.
--
apply eq_bigr. move => i _.
f_equal.
++
rewrite {}/R /widen_ik.
have Hi0n: (i0 <= n.+1)%N by clear - Hij;  destruct i0; simpl in *; lia.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) i) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) Hi0n i))
 by apply ordinal_eq; reflexivity.
rewrite !castmxE !cast_ordK block_mxEul.
red in IH. rewrite -IH.
f_equal. apply ordinal_eq; reflexivity.
++
rewrite {}/R /widen_ik.
have Hi0n: (i0 <= n.+1)%N by clear - Hij;  destruct i0; simpl in *; lia.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) i) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) Hi0n i)).
 compute. f_equal. apply proof_irr.
rewrite !castmxE !cast_ordK block_mxEul.
red in IH. rewrite -IH.
f_equal. apply ordinal_eq; reflexivity.
--
f_equal.
rewrite IH mxE.
if_lia false.
rewrite eq_refl.
f_equal.
rewrite /A1.
f_equal.
rewrite ulsubmxEsub mxE //.
f_equal.
rewrite -IH //.
*
case: (i0 == j0) /eqP => Hij'.
--
subst j0. clear Hij.
rewrite eq_refl.
f_equal.
f_equal.
f_equal.
apply eq_bigr. move => k _.
rewrite {}/R /widen_ik.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) k) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) (ltnW (ltn_ord i0)) k))
 by apply ordinal_eq; reflexivity. 
rewrite !castmxE !cast_ordK block_mxEul.
rewrite -IH //.
--
have ->:(lshift 1 i0 == lshift 1 j0)=false.
apply gtn_eqF. simpl.
have Hij'': nat_of_ord i0 <> nat_of_ord j0 
 by clear - Hij'; destruct i0,j0; contradict Hij'; simpl in *; subst; f_equal; auto.
lia. auto.
+
rewrite ord1 {}Hr. clear j0.
if_lia false.
rewrite addn0 ltn_ord eq_refl !mxE.
f_equal.
*
f_equal.
f_equal.
apply eq_bigr. move => k _.
rewrite {}/R /widen_ik mxE.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) k) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) (ltnW (ltn_ord i0)) k))
 by apply ordinal_eq; reflexivity.
rewrite !castmxE !cast_ordK block_mxEul block_mxEur.
f_equal.
rewrite -IH //.
*
f_equal.
clear R c r α.
have ->: A (lshift 1 i0) (lshift 1 i0) = A1 i0 i0.
  rewrite /A1 ulsubmxEsub mxE //.
clearbody A1. clear A.
rewrite {1}IH mxE.
if_lia false. rewrite eq_refl. done.
+
have ->: (n.+1+i0<j0)%N=false.
clear - i0 j0; destruct i0,j0; simpl in *; lia.
case: (cast_ord (esym add_two) (rshift n.+1 i0) ==
  cast_ord (esym add_two) (lshift 1 j0)) /eqP => Hij; auto.
apply cast_ord_inj in Hij.
have HH := eq_rlshift i0 j0. rewrite Hij in HH. rewrite eq_refl in HH. done.
+
rewrite !ord1. clear i0 j0.
if_lia false.
rewrite eq_refl.
f_equal.
f_equal.
f_equal.
transitivity (\sum_(k<n.+1) R (cast_ord (esym add_two) (lshift 1 k))
 (cast_ord (esym add_two) (rshift n.+1 0)) ^+ 2).
*
apply eq_bigr.
move => i _.
rewrite !mxE !castmxE esymK !cast_ordKV block_mxEur expr2 //.
*
clearbody R. clear.
rewrite (big_ord_widen_leq (n.+1+@nat_of_ord 1 0)); last lia.
apply eq_big.
--
move => i. destruct i; simpl in *. lia.
--
simpl.
move => i Hi.
f_equal.
f_equal.
rewrite /widen_ik.
destruct i; simpl in*.
rewrite /widen_ord /cast_ord // /inord /insubd /odflt/oapp /insub.
destruct idP; last by lia.
apply ordinal_eq; reflexivity.
Qed.

Lemma cholesky_jik_correct:
  forall [n] (A R: 'M[F]_n.+1),  
   positive_definite A ->
   cholesky_jik_spec A R ->
   forall i j, A i j = \sum_k (R^T i k * R k j).
Proof.
move => n A R PD Cjik.
have H := cholesky_jik_spec_eqv _ A.
have H1 := cholesky_jik_unique A R (cholesky A) Cjik H.
Search cholesky.
move :(cholesky_correct PD) => [H2 [H3 H4]].
rewrite -H1 in H4.
clear - H4.
move => i j.
rewrite -{}H4.
rewrite !mxE //.
Qed.


End Cholesky_jik. 

