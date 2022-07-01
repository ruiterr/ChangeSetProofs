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
Require Import insert_remove_operation_definition.
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
  Axiom simplifyOperationRemovedImpliesOpposite: ∀A B, simplifyOperations A B = Remove → A = (invert B).
  Axiom opposites_swap_to_opposites: ∀a b a' b', simplifyOperations a b = Swap b' a' → simplifyOperations (invert a) b' = Swap b (invert a').
  Axiom opposites_swap_to_opposites2: ∀a b a' b', simplifyOperations a b = Swap b' a' → simplifyOperations a' (invert b) = Swap (invert b') a.

End OperationSimplificationDef.

Module InsertRemoveOperationDefinition <: OperationSimplificationDef InsertRemoveOperationDefinition.
  Import InsertRemoveOperationDefinition.
  Import InsertRemoveChangeSetAlgebra.

  Inductive simplificationOperationResult :=
    | Keep
    | Swap (B: Operation) (A: Operation)
    | Remove.

  Definition updateOpPosition (A:Operation) (increment: Z) : Operation := 
    (createOperation (getOperationType A) (getOpI A) (if (increment >? 0)%Z then (getOpP A) + 1 else (getOpP A) - 1 ) (getOpE A) (getOpC A) (getOpS A)).

  Definition simplifyOperations (A:Operation) (B:Operation) := 
    if Op_eqb (InsertRemoveOperationDefinition.invert A) B then
      Remove
    else
      if (getOpP A) <=? (getOpP B) then
        Keep
      else
        match (getOperationType B) with
          | InsertOperation =>
            Swap B (updateOpPosition A (1))
          | RemoveOperation =>
            Swap B (updateOpPosition A (-1))
        end.

  Inductive sameSimplification: Operation → Operation → Operation → Operation → Prop := 
    | sameSimplificationKeep: ∀a b A B, simplifyOperations a b = Keep → simplifyOperations A B = Keep → sameSimplification a b A B
    | sameSimplificationSwap (b' a' B' A': Operation): ∀a b a' b' A B A' B', simplifyOperations a b = Swap b' a' → simplifyOperations A B = Swap B' A' → sameSimplification a b A B
    | sameSimplificationRemove: ∀a b A B, simplifyOperations a b = Remove → simplifyOperations A B = Remove → sameSimplification a b A B.


  Lemma simplifyOperations_swap_preserved_under_swap_to_right: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification a c a c'.
  intros.
  assert (c = c'). {
    unfold simplifyOperations in H.
    destruct (Op_eqb (b⁻¹)%O); try discriminate.
    destruct (getOpP b <=? getOpP c); try discriminate.
    destruct (getOperationType c).
    all: now inversion H.
  }
  rewrite <-H0.
  destruct (simplifyOperations a c) eqn:H_simplifyOperations2.
  - apply sameSimplificationKeep; auto.
  - apply sameSimplificationSwap with (a':=A) (b':=B) (A':=A) (B':=B); auto.
  - apply sameSimplificationRemove; auto.
  Qed.
  