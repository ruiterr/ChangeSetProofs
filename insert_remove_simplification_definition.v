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

  Lemma updatePositionPlus: ∀ a, (getOpP (updateOpPosition a 1) = (getOpP a) + 1).
  intros.
  destruct a.
  all: now cbn.
  Qed.

  Lemma updatePositionMinus: ∀ a, (getOpP (updateOpPosition a (-1)) = (getOpP a) - 1).
  intros.
  destruct a.
  all: now cbn.
  Qed.

  Lemma updatePositionCancel: ∀ a, (getOpP a) > 0 → (updateOpPosition (updateOpPosition a (-1)) 1) = (updateOpPosition (updateOpPosition a 1) (-1)).
  intros.
  unfold getOpP in H.
  destruct a.
  all: (
    cbn; simpl; auto;
    assert_nat(p = p - 1 + 1) as H_p;
    assert_nat(p = p + 1 - 1) as H_p';
    rewrite <-H_p;
    rewrite <-H_p';
    easy
   ).
  Qed.

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


  Lemma simplifyOperations_right_argument_preserved_in_swap: ∀a b a' b', simplifyOperations a b = Swap b' a' → b = b'.
  intros.
  unfold simplifyOperations in H.
  destruct (Op_eqb (a⁻¹)%O b); try discriminate.
  destruct (getOpP a <=? getOpP b); try discriminate.
  destruct (getOperationType b).
  all: now inversion H.
  Qed.

  Lemma simplifyOperations_swap_preserved_under_swap_to_right: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification c a c' a.
  intros.
  apply simplifyOperations_right_argument_preserved_in_swap in H as H0.
  rewrite <-H0.
  destruct (simplifyOperations c a) eqn:H_simplifyOperations2.
  - apply sameSimplificationKeep; auto.
  - apply sameSimplificationSwap with (a':=A) (b':=B) (A':=A) (B':=B); auto.
  - apply sameSimplificationRemove; auto.
  Qed.

  Lemma simplifyOperations_swap_preserved_under_swap_to_left: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification a c a c'.
  intros.
  apply simplifyOperations_right_argument_preserved_in_swap in H as H0.
  rewrite <-H0.
  destruct (simplifyOperations a c) eqn:H_simplifyOperations2.
  - apply sameSimplificationKeep; auto.
  - apply sameSimplificationSwap with (a':=A) (b':=B) (A':=A) (B':=B); auto.
  - apply sameSimplificationRemove; auto.
  Qed.
  
  Lemma simplifyOperations_double_swap: ∀a b c a' b' c'' b'', simplifyOperations a b = Swap b' a' → simplifyOperations b c = Swap c'' b'' → ∃b''', simplifyOperations a' c = Swap c b'''.
  intros.
  unfold simplifyOperations in *.
  destruct (Op_eqb (a⁻¹)%O b) eqn:H_invab; try discriminate.
  destruct (Op_eqb (b⁻¹)%O c) eqn:H_invbc; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_paGtpb; try discriminate.
  destruct (getOpP b <=? getOpP c) eqn:H_pbGtpc; try discriminate.
  assert (Op_eqb (a'⁻¹)%O c = false). { give_up. }
  rewrite H1.
  destruct (getOperationType b).
  - inversion H.
    rewrite_nat.
    specialize updatePositionPlus with (a:=a) as H2.
    assert_nat (getOpP (updateOpPosition a 1) <=? getOpP c = false).
    rewrite H5.

    destruct (getOperationType c).
    + inversion H0.
      exists ((updateOpPosition (updateOpPosition a 1) 1)).
      easy.
    + inversion H0.
      exists (updateOpPosition (updateOpPosition a 1) (-1)).
      easy.
  - inversion H.
    specialize updatePositionMinus with (a:=a) as H2.

    assert_nat (getOpP (updateOpPosition a (-1)) <=? getOpP c = false).
    rewrite H5.

    destruct (getOperationType c).
    + inversion H0.
      exists ((updateOpPosition (updateOpPosition a (-1)) 1)).
      easy.
    + inversion H0.
      exists (updateOpPosition (updateOpPosition a (-1)) (-1)).
      easy.
  Admitted.
  
  Lemma simplifyOperations_swap_over_inverses: ∀a b c b_a a_b c_a a_c c_b b_c c_a_b a_b_c, simplifyOperations a b = Swap b_a a_b → simplifyOperations a c = Swap c_a a_c → simplifyOperations b c = Swap c_b b_c → 
                                                              simplifyOperations a_b c = Swap c_a_b a_b_c → simplifyOperations a_c b_c = Swap b_c a_b_c.
  intros.
  apply simplifyOperations_right_argument_preserved_in_swap in H as H'. rewrite <-H' in *. clear H'.
  apply simplifyOperations_right_argument_preserved_in_swap in H0 as H'. rewrite <-H' in *. clear H'.
  apply simplifyOperations_right_argument_preserved_in_swap in H1 as H'. rewrite <-H' in *. clear H'.
  apply simplifyOperations_right_argument_preserved_in_swap in H2 as H'. rewrite <-H' in *. clear H'.

  unfold simplifyOperations in *.
  destruct (Op_eqb (a⁻¹)%O b) eqn:H_invab; try discriminate.
  destruct (Op_eqb (b⁻¹)%O c) eqn:H_invbc; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_paGtpb; try discriminate.
  destruct (getOpP b <=? getOpP c) eqn:H_pbGtpc; try discriminate.
  assert (Op_eqb (a_c⁻¹)%O b_c = false). { give_up. }
  rewrite H3 in *.
  assert (Op_eqb (a_b⁻¹)%O c = false). { give_up. }
  rewrite H4 in *.
  assert (Op_eqb (a⁻¹)%O c = false). { give_up. }
  rewrite H5 in *.
  destruct (getOpP a <=? getOpP c) eqn:H_paGtpc; try discriminate.
  destruct (getOpP a_b <=? getOpP c) eqn:H_pabGtpc; try discriminate.
  destruct c.
  all: inversion H0.
  all: specialize updatePositionPlus with (a:=a) as H8.
  all: specialize updatePositionMinus with (a:=a) as H8'.
  all: destruct b eqn:H_b.
  all: rewrite <-H_b in *.
  all: (
    inversion H1;
    unfold getOperationType in *;
    specialize updatePositionPlus with (a:=b) as H10;
    specialize updatePositionMinus with (a:=b) as H11;
    try assert_nat (getOpP (updateOpPosition a 1) <=? getOpP (updateOpPosition b 1) = false) as H_finalComparison;
    try assert_nat (getOpP (updateOpPosition a (-1)) <=? getOpP (updateOpPosition b (-1)) = false) as H_finalComparison2;
    try rewrite H_finalComparison;
    try rewrite H_finalComparison2;
    rewrite H_b at 1;
    rewrite H_b in H at 1;
    cbn;
    inversion H2;
    inversion H;
    try assert_nat ((getOpP a) > 0);
    try rewrite updatePositionCancel; auto;
    easy
  ).
  Admitted.
  destruct (getOpP a <=? getOpP b); try discriminate.
