From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Lists.List.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import ZArith.Znat.
From Coq Require Import Logic.ProofIrrelevance.

Require Coq.Structures.OrdersFacts.
Require Import Unicode.Utf8.
Require Import Coq.Program.Wf.
Require Import Lia.
(*Add LoadPath "/Users/ruiterr/work/fluid/ChangeSetProofs" as ChangeSets.*)
Require Import NatHelper.
Require Import free_group.
Require Import multiset.
Require Import additional_group_lemmas.
Require Import helper_lemmas.
Require Import single_operation_algebra.
From Coq Require Import List. Import ListNotations.

Require Import BinPos BinInt BinNat Pnat Nnat.

Scheme Equality for list.

Module Type OperationSimplificationDef (AlgebraSig : SingleOperationAlgebraSig).

  Import AlgebraSig.
  
  Inductive simplificationOperationResult :=
    | Keep
    | Swap (B: Operation) (A: Operation)
    | Remove.

  Parameter simplifyOperations : Operation -> Operation -> simplificationOperationResult.
  Axiom simplifyOperationsInvolutive : ∀ A B A' B', (simplifyOperations A B) = (Swap B' A') → (simplifyOperations B' A') = Keep.
  Axiom simplifyOperationsSwapStable : ∀ A B C A' A'' B' C', 
          (simplifyOperations B C) = Keep →
          (simplifyOperations A B) = Swap B' A' →
          (simplifyOperations A' C) = Swap C' A'' →
          (simplifyOperations B' C') = Keep.

  Axiom simplifyOperationsSwapStable2 : ∀ A B C X A' X', 
             (simplifyOperations A B = Keep) →
             (simplifyOperations B C = Keep) →
             (simplifyOperations X A = Swap A' X') →
             (simplifyOperations A' C) = Keep.


  Axiom simplifyOperationsSwapCompatibleWithRebase : ∀ A B A' B' C, (simplifyOperations A B) = (Swap A' B') → 
                                                                 ((Some C) ↷ ((Some A) ↷ (Some B)) = (Some C) ↷ ((Some A') ↷ (Some B')))%OO.
  Axiom simplifyOperationsRemoveCompatibleWithRebase : ∀ A B C, (simplifyOperations A B) = Remove → 
                                                             ((Some C) ↷ ((Some A) ↷ (Some B)) = (Some C))%OO.
  (*Axiom simplifyOperationResultReduced : ∀ A B A' B', (simplifyOperations A B) = Swap B' A' → A' ≠ (invert B').*)
  Axiom simplifyOperationResultReduced : ∀ A B, (simplifyOperations A B) = Keep → A ≠ (invert B).
  Axiom simplifyOperationOppositesRemoved : ∀ A, (simplifyOperations (invert A) A) = Remove.

End OperationSimplificationDef.


Module SimplificationLemmas (simplificationDef: OperationSimplificationDef) (AlgebraSig: SingleOperationAlgebraSig).
  Module simplification := simplificationDef AlgebraSig.
  Module Algebra := SingleOperationAlgebra AlgebraSig.
  Import AlgebraSig.
  Import Algebra.
  Import simplification.

  Import Algebra.GroupLemmas.
  Import OperationGroup.


  (* Simplification algorithm, basically based on insertion sort *)

  Fixpoint insertOpInSimplifiedOpList (a: Operation) (ops : opList) : opList := 
    match ops with
      | [] => [a]
      | b::tail =>
        let simplifyResult := (simplifyOperations a b) in
          match simplifyResult with 
            | Keep => a::ops                                            (* Return input unmodified *)
            | Swap b' a' => (b':: (insertOpInSimplifiedOpList a' tail)) (* Swap the two entries at the head *)
            | Remove => tail                                            (* Remove both entries at the head *)
          end 
    end.

  Fixpoint simplifyOpList (ops : opList) : opList := 
    match (ops) with
      | [] => ops
      | a::tail =>
        let tailOps := (simplifyOpList tail) in 
        (insertOpInSimplifiedOpList a tailOps)
    end.


  (* Definition of a simplified list: all entries have to return keep with respect to the previous entry *)
  Inductive opList_simplified: opList → Prop := 
    | empty_oplist_simplified: opList_simplified ([] : opList)
    | single_operation_simplified: ∀a, opList_simplified ([a])
    | operation_with_keep_can_be_added_to_simplfied: ∀a b T, (simplifyOperations a b) = Keep → opList_simplified (b::T) → opList_simplified (a::b::T).

  Lemma insertOpInSimplifiedOpList_simplified: ∀a A, (opList_simplified A) → (opList_simplified (insertOpInSimplifiedOpList a A)).
  intro a. intro A. revert a.
  induction A.
  - intros.
    unfold insertOpInSimplifiedOpList.
    apply single_operation_simplified.
  - intros.
    unfold insertOpInSimplifiedOpList.
    remember (a::A) as A'.
    destruct H eqn:H_original.
    + discriminate.
    + inversion HeqA'.
      destruct (simplifyOperations a0 a) eqn:H_simplifyOperations.
      * apply operation_with_keep_can_be_added_to_simplfied; auto.
        apply single_operation_simplified.
      * apply simplifyOperationsInvolutive in H_simplifyOperations.
        apply operation_with_keep_can_be_added_to_simplfied; auto.
        apply single_operation_simplified.
      * apply empty_oplist_simplified.
    + destruct (simplifyOperations a0 a) eqn:H_simplifyOperations.
      * apply operation_with_keep_can_be_added_to_simplfied; auto.
        inversion HeqA'.
        now rewrite <-H1 in *.
      * set (X:=insertOpInSimplifiedOpList A0 A).
        specialize IHA with (a:=A0).
        fold X in IHA.
        unfold insertOpInSimplifiedOpList in X.
        fold X.
        assert (X=X) as H_X; auto.
        unfold X in H_X at 2.
        inversion HeqA'.
        rewrite <-H2 in H_X.
        destruct (simplifyOperations A0 b) eqn:H_SimplifyOperations2.
        ++ rewrite H_X in *.
           apply operation_with_keep_can_be_added_to_simplfied; auto.
           apply simplifyOperationsInvolutive in H_simplifyOperations; auto.
           apply IHA.
           now rewrite <-H2.
        ++ rewrite <-H1 in *.
           rewrite H_X in *.
           apply operation_with_keep_can_be_added_to_simplfied; auto.
           apply simplifyOperationsSwapStable with (A:=a0) (B:=a1) (C:=b) (A':=A0) (A'':=A1) (B':=B) (C':=B0); auto.
           apply IHA.
           rewrite <-H2; auto.
        ++ rewrite H_X.
           clear H_original.
           remember (b::T) as A'.
           destruct o eqn:H_O.
           -- discriminate.
           -- inversion HeqA'0.
              apply single_operation_simplified.
           -- inversion HeqA'0.
              apply operation_with_keep_can_be_added_to_simplfied; auto.
              clear H_O.
              rewrite H3 in *.
              rewrite H1 in *.
              apply simplifyOperationsSwapStable2 with (X:=a0) (A:=a) (B:=b) (X':=A0); auto.
     * inversion HeqA'.
       assumption.
  Qed.

  Lemma simplifyOpList_simplified: ∀A, (opList_simplified (simplifyOpList A)).
  intros.
  unfold simplifyOpList.
  induction A.
  - apply empty_oplist_simplified.
  - apply insertOpInSimplifiedOpList_simplified.
    apply IHA.
  Qed.


  Lemma simplifyOpList_fixes_simplified: ∀A, (opList_simplified A) → (simplifyOpList A) = A.
  intros.
  unfold simplifyOpList.
  induction A.
  - easy.
  - remember (a::A) as A_orig.
    destruct H eqn:H_simplified.
    + discriminate.
    + rewrite IHA.
      * unfold insertOpInSimplifiedOpList.
        inversion HeqA_orig.
        easy.
      * inversion HeqA_orig.
        apply empty_oplist_simplified.
    + rewrite IHA.
      * unfold insertOpInSimplifiedOpList.
        destruct A eqn:H_A; try discriminate.
        clear H_simplified.
        inversion HeqA_orig.
        rewrite H1 in *.
        rewrite H2 in *.
        now rewrite e.
      * now inversion HeqA_orig.
  Qed.

  Lemma simplifyOpList_idempotent: ∀A, (simplifyOpList (simplifyOpList A)) = (simplifyOpList A).
  intros.
  apply simplifyOpList_fixes_simplified.
  apply simplifyOpList_simplified.
  Qed.

  Lemma simplified_implies_reduced: ∀A, (opList_simplified A) → (reduced A).
  intros.
  induction A.
  - apply empty_str_reduced.
  - remember (a::A) as A'.
    destruct H.
    + discriminate.
    + apply single_letter_reduced.
    + apply join_reduced.
      * inversion HeqA'.
        rewrite <-H3 in IHA.
        now apply IHA.
      * apply simplifyOperationResultReduced in H.
        auto.
  Qed.

  Lemma simplifyOpList_reduced: ∀A, reduced (simplifyOpList A).
  intros.
  apply simplified_implies_reduced.
  apply simplifyOpList_simplified.
  Qed.

  Definition simplifyChangeSet (CS : ChangeSet) := 
    match CS with
      | CSet redOpList => CSet {|
          operations:= simplifyOpList (operations redOpList);
          operations_reduced:= simplifyOpList_reduced (operations redOpList)
        |}
      | InvalidCSet => InvalidCSet
    end.

  Notation "《 x 》" := (simplifyChangeSet x) (at level 40, no associativity, format "'《' x '》'").

  (* Define an equivalence relation for the simplify operation *)
  (*Inductive opLists_equivalent : opList -> opList -> Prop :=
  | insert_opposite_pair: forall (S T:group_str) (a:alphabet),
    group_str_equiv (S ++ T) (S ++ opposite a :: a :: T)
  | group_str_equiv_refl: forall S:group_str, group_str_equiv S S
  | group_str_equiv_sym: forall S T:group_str,
    group_str_equiv S T -> group_str_equiv T S
  | group_str_equiv_trans: forall S T U:group_str,
    group_str_equiv S T -> group_str_equiv T U ->
    group_str_equiv S U.*)

  Lemma simplify_will_remove_opposites: ∀a A, (opList_simplified (a::A)) → simplifyOpList ((opposite a)::a::A) = simplifyOpList A.
  intros.
  unfold simplifyOpList at 1.
  fold simplifyOpList.
  remember (simplifyOpList A) as X.
  destruct A.
  - rewrite HeqX.
    cbv.
    now rewrite simplifyOperationOppositesRemoved.
  - unfold insertOpInSimplifiedOpList at 1 2.
    remember (a :: o :: A) as A'.
    destruct H.
    + discriminate.
    + discriminate.
    + inversion HeqA'.
      rewrite H2 in *.
      rewrite H3 in *.
      rewrite H4 in *.
      rewrite simplifyOpList_fixes_simplified with (A:=o::A) in HeqX; auto.
      rewrite HeqX.
      rewrite H.
      now rewrite simplifyOperationOppositesRemoved.
  Qed.

  Lemma simplifyOpList_swaps_with_concat: ∀A B, simplifyOpList (A ++ B) =
                                                simplifyOpList (simplifyOpList A ++ simplifyOpList B).
  Admitted.

  Lemma str_equiv_implies_same_reduction: ∀A B, A ~~ B → (simplifyOpList A) = (simplifyOpList B).
  intros.
  induction H.
  - rewrite simplifyOpList_swaps_with_concat with (B:=opposite a :: a :: T).
    specialize simplify_will_remove_opposites with (a:=a) (A:=T) as H_noOpposites.
    autounfold in *.
    rewrite H_noOpposites.
    apply simplifyOpList_swaps_with_concat.
  - auto.
  - now rewrite IHgroup_str_equiv.
  - rewrite IHgroup_str_equiv1.
    now rewrite IHgroup_str_equiv2.
  Qed.

  Lemma simplifyOpList_reduces: ∀A, (simplifyOpList (reduction A)) = (simplifyOpList A).
  intros.
  apply str_equiv_implies_same_reduction.
  apply reduction_equiv.
  Qed.

  Lemma simplify_swaps_with_squash: ∀A B, 《A ○ B》 = 《《A》 ○ 《B》》.
  intros.
  unfold simplifyChangeSet.
  apply ProofIrrelevanceForChangeSets.
  destruct A.
  all: destruct B.
  all: autoChangeSetSimplification.
  simpl.
  enough ((simplifyOpList (squashOpList (operations ops) (operations ops0))) = 
          (simplifyOpList (squashOpList (simplifyOpList (operations ops)) (simplifyOpList (operations ops0))))).
  + rewrite H.
    apply list_op_beq_refl.
  + unfold squashOpList.
    unfold reduced_string_product.
    do 2 rewrite simplifyOpList_reduces.
    destruct ops.
    destruct ops0.
    unfold operations.
    apply simplifyOpList_swaps_with_concat.
  Qed.


