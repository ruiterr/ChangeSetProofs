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
            | Keep => ops                                               (* Return input unmodified *)
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

  Definition opList_simplified (ops : opList) := (simplifyOpList ops) = ops.

  Lemma simplifyOpList_idempotent: ∀A, (simplifyOpList (simplifyOpList A)) = (simplifyOpList A).
  Admitted.

  Lemma simplifyOpList_simplified: ∀A, (opList_simplified (simplifyOpList A)).
  intros.
  unfold opList_simplified.
  now rewrite simplifyOpList_idempotent.
  Qed.

  Lemma simplified_implies_head_keep_and_tail_simplified: ∀A,
  Lemma simplified_implies_reduced: ∀A, (opList_simplified A) → (reduced A).
  Admitted.

  Lemma swapped_simplify_is_reduced: ∀(A B A' B': Operation) (tail tail2: opList), (simplifyOperations A B) = Swap B' A' → (reduced (tail)) → (tail = B::tail2) → (reduced (B'::A'::tail2)).
  intros.
  apply simplifyOperationResultReduced in H.
  Admitted.

  Lemma concat_reduced_if_list_reduced: ∀A tail l, (A::tail) = l → (reduced l) → reduced (A::tail).
  intros.
  rewrite H.
  auto.
  Qed.
  Print concat_reduced_if_list_reduced.

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
      | CSet redOpList => CSet (simplifyOpList (operations redOpList) (operations_reduced redOpList))
      | InvalidCSet => InvalidCSet
    end.
