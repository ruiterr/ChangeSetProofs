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


  (*Lemma simplified_implies_tail_simplified: ∀a T, (opList_simplified (a::T)) → (opList_simplified T).
  intros.
  unfold opList_simplified in H.
  unfold simplifyOpList in H.
  destruct T.
  - now cbv.
  - set (T':= (simplifyOpList T)).
    unfold simplifyOpList in T'.
    fold T' in H.
    assert (∀x X Y, (insertOpInSimplifiedOpList x X) = (x :: Y) → X = Y). {
      intros.
      unfold insertOpInSimplifiedOpList in H0.
      destruct X eqn:H_X.
      - inversion H0.
        auto.
      - destruct (simplifyOperations x o0) eqn:H_simplifyOperations.
        + inversion H0.
          auto.
        + inversion H0.*)
          

  (*unfold opList_simplified in H.
  unfold simplifyOpList in H.*)
  (*remember (length T) as lenT.
  assert_nat ((length T) ≤ lenT) as H_ltLenT.
  clear HeqlenT.
  revert H_ltLenT.
  revert H.
  revert a.
  revert T.
  induction lenT.
  - intros.
    assert_nat(Datatypes.length T = 0) as HeqlenT.
    apply length_zero_iff_nil in HeqlenT.
    rewrite HeqlenT in *.
    now cbv.
  - intros.
    destruct T.
    + now cbv.
    + unfold opList_simplified in H.
      unfold simplifyOpList in H.
      set (T':= (simplifyOpList T)).
      unfold simplifyOpList in T'.
      
      fold T' in H.
      specialize IHlenT with (T := T') (a:=o).
      unfold insertOpInSimplifiedOpList at 1 in H.
      destruct ((insertOpInSimplifiedOpList o T')) eqn:H_ops.
      * discriminate H.
      * destruct (simplifyOperations a o0) eqn:H_simplifyOps.
        -- inversion H.
           rewrite H1 in *. clear H1.
           unfold insertOpInSimplifiedOpList in H_ops.
           destruct T' eqn:H_T'.
           ++ inversion H_ops.
              rewrite H2 in H3.
              discriminate.
           ++ destruct (simplifyOperations o o2) eqn:H_simplify2.
              ** 
        --

      fold T' in IHlenT.
    rewrite IHT in H.
  (*unfold opList_simplified.
  unfold simplifyOpList.
  remember (a::T) as L.
  revert HeqL.
  remember (length L) as lenL.
  revert HeqlenL.
  induction lenL.
  - intros.
    symmetry in HeqlenL.
    apply length_zero_iff_nil in HeqlenL.
    rewrite HeqlenL in *.
    discriminate.
  - intros.*)
    
  Admitted.*)

  (*Lemma simplified_implies_head_eq_keep: ∀a b T, (opList_simplified (a::b::T)) → (simplifyOperations a b) = Keep ∧ (opList_simplified T).
    intros.
    remember (length T) as lenT.
    assert_nat ((length T) ≤ lenT) as H_ltLenT.
    clear HeqlenT.
    revert H_ltLenT.
    revert H.
    revert a.
    revert T.
    induction lenT.
    - intros.
      assert_nat(Datatypes.length T = 0) as HeqlenT.
      apply length_zero_iff_nil in HeqlenT.
      rewrite HeqlenT in *.
      split.
      + unfold opList_simplified in H.
        unfold simplifyOpList in H.
        unfold insertOpInSimplifiedOpList in H.
        destruct (simplifyOperations a b).
        * easy.
        * give_up.
        * discriminate.
      + now cbv.
    - intros.

  Admitted.*)

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

  (*Lemma swapped_simplify_is_reduced: ∀(A B A' B': Operation) (tail tail2: opList), (simplifyOperations A B) = Swap B' A' → (reduced (tail)) → (tail = B::tail2) → (reduced (B'::A'::tail2)).
  intros.
  apply simplifyOperationResultReduced in H.
  Admitted.

  Lemma concat_reduced_if_list_reduced: ∀A tail l, (A::tail) = l → (reduced l) → reduced (A::tail).
  intros.
  rewrite H.
  auto.
  Qed.
  Print concat_reduced_if_list_reduced.*)

  (*Fixpoint simplifyOpList (ops : list Operation) (ops_reduced: (reduced ops)) : reducedOpList := 
    match (ops) with
      | [] => fun x => {| operations := ops; operations_reduced := ops_reduced |}
      | A::tail => fun x => (
        let simplifiedTail := (simplifyOpList tail (tailIsReduced2 ops tail A x ops_reduced)) in 
        let tailOps := simplifiedTail.(operations) in
        (match tailOps with
          | [] => (fun y => {|
              operations := [A];
              operations_reduced := (single_letter_reduced A)
            |})
          | B::tail2 => (fun y =>
            let simplifyResult := (simplifyOperations A B) in
              match simplifyResult with 
                | Keep => (* Return input unmodified *)
                  (fun z => {| 
                    operations := ops; 
                    operations_reduced := ops_reduced 
                  |})
                | Swap B' A' => (* Return input unmodified *)
                  (fun z => {| 
                    operations := B':: A' :: tail2; 
                    operations_reduced := (swapped_simplify_is_reduced A B A' B' tailOps tail2 z (operations_reduced simplifiedTail) y)
                  |}) 
                | Remove => (* Remove both entries at the head *)
                  (fun z => {| 
                    operations := tail2; 
                    operations_reduced := (tailIsReduced2 tailOps tail2 B (symmetry y) (operations_reduced simplifiedTail)) 
                  |}) 
              end (eq_refl simplifyResult)
            )
        end (eq_refl tailOps)))
    end eq_refl.*)

  Definition simplifyChangeSet (CS : ChangeSet) := 
    match CS with
      | CSet redOpList => CSet {|
          operations:= simplifyOpList (operations redOpList);
          operations_reduced:= simplifyOpList_reduced (operations redOpList)
        |}
      | InvalidCSet => InvalidCSet
    end.
