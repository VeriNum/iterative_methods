Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Axiom clean_LOCAL_right_spec_bangbang: forall gvar_ident
   (Delta: tycontext) (T1: Maps.PTree.t val) (T2: Maps.PTree.t (Ctypes.type * val)) (GV: option globals) P Q R S S'
  (LEGAL: fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true),
  local2ptree Q = (T1, T2, nil, GV) ->
  clean_LOCAL_right Delta T1 T2 GV S S' ->
  (local (tc_environ Delta) && PROPx P (LOCALx nil (SEPx R)) |-- liftx S') ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- S.

Inductive bangbang : Prop := bangbang_i.

Ltac choose_clean_LOCAL_right_spec L :=
 lazymatch goal with 
 | H: bangbang |- _ => eapply (@clean_LOCAL_right_spec_bangbang L)
 | |- _ => eapply (@clean_LOCAL_right_spec L)
 end.

Ltac eapply_clean_LOCAL_right_spec_rec gv L ::=
  match goal with
  | |- context [gv ?i] =>
      match L with
      | context [i] => fail 1
      | _ => eapply_clean_LOCAL_right_spec_rec gv (@cons ident i L)
      end
  | _ := gv ?i |- _ =>
      match L with
      | context [i] => fail 1
      | _ => eapply_clean_LOCAL_right_spec_rec gv (@cons ident i L)
      end
  | _ => match goal with
         | |- _ |-- |==> _ => eapply (@clean_LOCAL_right_bupd_spec L)
         | _ => choose_clean_LOCAL_right_spec L
         end
  end.

Ltac eapply_clean_LOCAL_right_spec ::=
   match goal with
   | |- context [gvars ?gv] => 
          eapply_clean_LOCAL_right_spec_rec gv (@nil ident)
   | _ => match goal with
         | |- _ |-- |==> _ => eapply (clean_LOCAL_right_bupd_spec nil)
         | _ => choose_clean_LOCAL_right_spec nil
         end
  end.

Ltac entbang ::=
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
   lazymatch goal with 
   | H: bangbang |- _ => idtac
   | |- _ => saturate_local
   end;
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

Ltac entbangbang :=
 let B := fresh "BangBang" in assert (BangBang :=bangbang_i);
 entbang;
 clear B.

Tactic Notation "entailer" "!!" := entbangbang.
