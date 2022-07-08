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
Require Import changeset_simplification_lemmas.
Require Import insert_remove_operation_definition.
From Coq Require Import List. Import ListNotations.

Require Import BinPos BinInt BinNat Pnat Nnat.

Scheme Equality for list.

Module InsertRemoveOperationSimplificationDefinition <: OperationSimplificationDef InsertRemoveOperationDefinition.
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

  Lemma rebase_opposites: ∀a c, ((Some a)⁻¹ ↷ (Some c) = ((Some a) ↷ (Some c))⁻¹)%OO.
  Admitted.
  
  Lemma ops_unmodified_by_larger_op_in_rebase: ∀a b, getOpP b > getOpP a → (Some a ↷ Some b)%OO = Some a.
  intros.
  unfold rebaseOperation.
  destruct b.
  all: destruct (negb (getOpP a =? p) && ((getOpI a =? i) || ms_contains i (getOpS a) && (c =? 0)%Z)); try easy.
  all:( unfold getOpP in H at 1;
    assert_nat (p <? getOpP a = false);
    rewrite H0;
    assert_nat (getOpP a <? p = true);
    now rewrite H1
  ).
  Qed.

  Lemma inverse_has_same_P: ∀a, getOpP a = getOpP (a⁻¹)%O.
  intros.
  destruct a.
  all: now cbv.
  Qed.

  Lemma rebaseWithAInverse1: ∀ a b a', simplifyOperations a b = Swap b a' → (Some b ↷ Some (a⁻¹)%O)%OO = Some b.
  intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H.
  
  destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
  destruct (getOperationType b) eqn:opTypeB.
  all: (
      assert_nat (getOpP a > getOpP b) as H_pAGtpB;

      rewrite inverse_has_same_P with (a:=a) in H_pAGtpB;
      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB;
      auto
  ).
  Qed.

  Lemma rebaseSwapWithA: ∀ a b a', simplifyOperations a b = Swap b a' → (Some b ↷ Some a)%OO = Some b.
  intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H.
  
  destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
  destruct (getOperationType b) eqn:opTypeB.
  all: (
      assert_nat (getOpP a > getOpP b) as H_pAGtpB;

      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB;
      auto
  ).
  Qed.

  Lemma rebaseWithA'Inverse1: ∀ a b a', simplifyOperations a b = Swap b a' → (Some a' ↷ Some (b⁻¹)%O)%OO = Some a'.
  intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H.
  
  assert (getOpP a' >= getOpP b). {
    destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
    destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
    destruct (getOperationType b) eqn:opTypeB.
    - inversion H.
      unfold getOpP.
      unfold updateOpPosition.
      unfold createOperation.
  
      destruct (getOperationType a) eqn:opTypeA.
      all: (
        rewrite_nat_all ( (1 >? 0)%Z = true);
        destruct b; try discriminate;
        destruct a; try discriminate;
        unfold getOpP in *;
        rewrite_nat;
        lia
      ).
    - inversion H.
      unfold getOpP.
      unfold updateOpPosition.
      unfold createOperation.
  
      destruct (getOperationType a) eqn:opTypeA.
      all: (
        rewrite_nat_all ( (-1 >? 0)%Z = false);
        destruct b; try discriminate;
        destruct a; try discriminate;
        unfold getOpP in *;
        rewrite_nat;
        lia
      ).
  }
  (*all: (
      assert_nat (getOpP a > getOpP b) as H_pAGtpB;

      rewrite inverse_has_same_P with (a:=a) in H_pAGtpB;
      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB;
      auto
  ).
  Qed.*)
  Admitted.

  Lemma rebaseWithA': ∀ a b a', simplifyOperations a b = Swap b a' → (Some a' ↷ Some b)%OO = Some a'.
  (*intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H.
  
  destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
  destruct (getOperationType b) eqn:opTypeB.
  all: (
      assert_nat (getOpP a > getOpP b) as H_pAGtpB;

      rewrite inverse_has_same_P with (a:=a) in H_pAGtpB;
      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB;
      auto
  ).
  Qed.*)
  Admitted.

  Lemma swapAfterRebase: ∀ a b a' a0 b0 a'0 c, simplifyOperations a b = Swap b a' → 
                                                   (Some a  ↷ Some c)%OO = Some a0 →
                                                   (Some b  ↷ Some c)%OO = Some b0 →
                                                   (Some a' ↷ Some c)%OO = Some a'0 →
                                                   simplifyOperations a0 b0 = Swap b0 a'0.
  Admitted.

  (*Lemma rebaseWithAInverse2: ∀ a b a', simplifyOperations a b = Swap b a' → (Some a ↷ Some (b⁻¹)%O)%OO = Some b.
  intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H.
  
  destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
  destruct (getOperationType b) eqn:opTypeB.
  all: (
      assert_nat (getOpP b > getOpP a) as H_pAGtpB;

      rewrite inverse_has_same_P with (a:=b) in H_pAGtpB;
      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB;
      auto
  ).
  Qed.

  (*Lemma rebaseWithAInverse1: ∀ a b a' b0, (Some b ↷ Some (a⁻¹)%O)%OO = Some b0 → simplifyOperations a b = Swap b a' → simplifyOperations a b0 = Swap b a'.*)
  intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H0.
  
  destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
  destruct (getOperationType b) eqn:opTypeB.
  all: (
      assert_nat (getOpP a > getOpP b) as H_pAGtpB;

      rewrite inverse_has_same_P with (a:=a) in H_pAGtpB;
      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB as H_baInvRebase;
      autounfold in *;
      unfold Operation in *;
      rewrite H_baInvRebase in H;
      inversion H;
      inversion H0;
      rewrite <-H2;
      rewrite H3;
      assumption
    ).
  Qed.

  Lemma rebaseWithAInverse2: ∀ a b a' b0, (Some a ↷ Some (b⁻¹)%O)%OO = Some a0 → simplifyOperations a b = Swap b a' → simplifyOperations a b = Swap b a'.
  intros.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H0.
  
  destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
  destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
  destruct (getOperationType b) eqn:opTypeB.
  all: (
      assert_nat (getOpP a > getOpP b) as H_pAGtpB;

      rewrite inverse_has_same_P with (a:=a) in H_pAGtpB;
      apply ops_unmodified_by_larger_op_in_rebase in H_pAGtpB as H_baInvRebase;
      autounfold in *;
      unfold Operation in *;
      rewrite H_baInvRebase in H;
      inversion H;
      inversion H0;
      rewrite <-H2;
      rewrite H3;
      assumption
    ).
  Qed.*)

  Lemma rewriteOpRebaseToCs: ∀x y z, (Some x ↷ Some y)%OO = Some z → (opToCs z) = (opToCs x)  ↷ (opToCs y).
    intros.
    unfold opToCs.
    unfold rebaseChangeSet.
    unfold operations.
    unfold operations_reduced.
    unfold rebaseChangeSetOps.
    unfold rebaseOperationWithChangeSet.
    unfold fold_left.
    unfold map.
    unfold operations.
    rewrite H.
    now cbv.
  Qed.

  Lemma convertRebaseToCs: ∀a b : Operations, ∃o, (Some a ↷ Some b)%OO = Some o ∧ (opToCs o) = (opToCs a)  ↷ (opToCs b).
  intros.
  set (x := (Some a ↷ Some b)%OO).
  destruct x eqn:H_x.
  2: { apply noErrorsDuringRebase in H_x; contradiction. }
  exists o.
  split; auto.
  apply rewriteOpRebaseToCs; auto.
  Qed.

  Lemma rebaseOperation_leftAssociativity: ∀a b c a', simplifyOperations a b = Swap b a' → (Some a' ↷ Some (b⁻¹)%O ↷ Some c ↷ (Some b ↷ Some c)%OO = (Some a' ↷ Some c))%OO.
  intros.
  unfold Operation in *.

  assert (simplifyOperations a b = Swap b a') as H1'. auto.
  unfold simplifyOperations in H.
  
  assert (getOpP a' >= getOpP b). {
    destruct (Op_eqb (a⁻¹)%O) eqn:H_abNotInverses; try discriminate.
    destruct (getOpP a <=? getOpP b) eqn:H_not_pALepB; try discriminate.
    destruct (getOperationType b) eqn:opTypeB.
    - inversion H.
      unfold getOpP.
      unfold updateOpPosition.
      unfold createOperation.
  
      destruct (getOperationType a) eqn:opTypeA.
      all: (
        rewrite_nat_all ( (1 >? 0)%Z = true);
        destruct b; try discriminate;
        destruct a; try discriminate;
        unfold getOpP in *;
        rewrite_nat;
        lia
      ).
    - inversion H.
      unfold getOpP.
      unfold updateOpPosition.
      unfold createOperation.
  
      destruct (getOperationType a) eqn:opTypeA.
      all: (
        rewrite_nat_all ( (-1 >? 0)%Z = false);
        destruct b; try discriminate;
        destruct a; try discriminate;
        unfold getOpP in *;
        rewrite_nat;
        lia
      ).
  }

  destruct (getOpP b <? getOpP a') eqn:H_bLta'.
  - assert_nat (getOpP a' > getOpP b) as H_a'Gtb.
    specialize ops_unmodified_by_larger_op_in_rebase with (1:=H_a'Gtb).*)


  Ltac convertRebaseToCs a1 b1 :=
    let H1 := (fresh "H_rebA") in
    let H2 := (fresh "H_rebB") in
    let x := (fresh "x") in
    specialize convertRebaseToCs with (a:=a1) (b:=b1) as H1; destruct H1 as [x H1]; destruct H1 as ( H1 & H2 ); rewrite H1; clear H1; unfold Operation.

  repeat match goal with
    |- context [(Some ?a ↷ Some ?b)%OO] => convertRebaseToCs a b
  end.

  enough (opToCs x2 = opToCs x3).
  - unfold opToCs in H0.
    now inversion H0.
  - rewrite H_rebB3.
    rewrite H_rebB2.
    rewrite H_rebB1.
    rewrite H_rebB0.
    rewrite H_rebB.
    symmetry.
    specialize rebaseLeftDistibutivity with (A:=opToCs b) (B:=opToCs a') (C:=opToCs c) as H_leftDistrib.
    repeat rewrite rebaseRightDistibutivity in H_leftDistrib.
  Admitted.
    (*apply rebaseLeftDistibutivity.

  specialize convertRebaseToCs with (a:=a) (b:= (b⁻¹)%O) as H_reb1. destruct H_reb1. destruct H as ( H_reb1A & H_reb1b ). rewrite H_reb1A.
  specialize convertRebaseToCs with (a:=a) (b:= (b⁻¹)%O) as H_reb1. destruct H_reb1. destruct H as ( H_reb1A & H_reb1b ). rewrite H_reb1A.
  specialize convertRebaseToCs with (a:=a) (b:= (b⁻¹)%O) as H_reb1. destruct H_reb1. destruct H as ( H_reb1A & H_reb1b ). rewrite H_reb1A.
  specialize convertRebaseToCs with (a:=a) (b:= (b⁻¹)%O) as H_reb1. destruct H_reb1. destruct H as ( H_reb1A & H_reb1b ). rewrite H_reb1A.


  set (x''':= (Some a ↷ Some (b⁻¹)%O)%OO).
  set (x'':= (Some b ↷ Some c)%OO).
  destruct x'' eqn:H_x''. 2: { apply noErrorsDuringRebase in H_x''; contradiction. } apply rewriteOpRebaseToCs in H_x''.

  set (x':= (Some x''' ↷ Some c)%OO).

  set (y'':=(Some b ↷ Some c)%OO).
  set (y':=(y'' ↷ Some d)%OO).

  destruct x'' eqn:H_x''. 2: { apply noErrorsDuringRebase in H_x''; contradiction. } apply rewriteOpRebaseToCs in H_x''.
  destruct x'  eqn:H_x'.  2: { apply noErrorsDuringRebase in H_x' ; contradiction. } apply rewriteOpRebaseToCs in H_x'.
  destruct y'' eqn:H_y''. 2: { apply noErrorsDuringRebase in H_y''; contradiction. } apply rewriteOpRebaseToCs in H_y''.
  destruct y'  eqn:H_y'.  2: { apply noErrorsDuringRebase in H_y' ; contradiction. } apply rewriteOpRebaseToCs in H_y'.
  
  enough (opToCs o0 = opToCs o2).
  - unfold opToCs in H.
    now inversion H.
  - rewrite H_x'.
    rewrite H_x''.
    rewrite H_y'.
    rewrite H_y''.
    rewrite <-rebaseRightDistibutivity.
    rewrite <-rebaseRightDistibutivity.
  assert (∀x, (opToCs x)))) as H_convertToOp. { now cbv. }

  Qed.*)

(*  ((invertOperationOption ((Some A) ↷  (Some B)))  = (invertOperationOption (Some A)) ↷ (invertOperationOption (Some A)) ↷ (Some B) ↷ ((Some A) ↷ (Some B)) *)

  Lemma rebaseSwap: ∀ a b a' b' a0 b0 c0 a'0 b'0, simplifyOperations a b = Swap b' a' →
                                                  (Some a ↷ Some c0)%OO = Some a0 →
                                                  (Some b ↷ Some (InsertRemoveOperationDefinition.invert a) ↷ Some c0 ↷ (Some a ↷ Some c0))%OO = Some b0 →
                                                  (Some b' ↷ Some c0)%OO = Some b'0 →
                                                  (Some a' ↷ Some (InsertRemoveOperationDefinition.invert b') ↷ Some c0 ↷ (Some b' ↷ Some c0))%OO = Some a'0 →
                                                  simplifyOperations a0 b0 = Swap b'0 a'0.
  intros.
  apply simplifyOperations_right_argument_preserved_in_swap in H as H_b'.
  rewrite <-H_b' in *.
  clear H_b' b'.

  remember (Some a' ↷ Some c0)%OO as a''0.
  destruct a''0 as [a''0|].
  all: symmetry in Heqa''0.
  2: {apply noErrorsDuringRebase in Heqa''0. contradiction. }
  rewrite rebaseWithAInverse1 with (1:=H) in *.

  specialize swapAfterRebase with (1:=H) (2:=H0) (3:=H2) (4:=Heqa''0) (c:=c0) as H_simplifyOperationsRebasedWithC; auto.
  rewrite H0 in H1.
  rewrite H2 in H1.

  rewrite rebaseSwapWithA with (1:=H_simplifyOperationsRebasedWithC) in *.
  inversion H1.

  rewrite H5 in H_simplifyOperationsRebasedWithC.
  enough (Some a'0 = Some a''0).
  - inversion H4.
    apply H_simplifyOperationsRebasedWithC.
  - rewrite <-H3.
    rewrite <-Heqa''0.
    apply rebaseOperation_leftAssociativity with (1:=H).
  Qed.

  rewrite rebaseWithA'Inverse1 with (1:=H) in *.
  rewrite Heqa''0 in H3.
  rewrite H2 in H3.

  rewrite rebaseWithA' with (1:=H_simplifyOperationsRebasedWithC) in *.
  inversion H3.

  rewrite H5 in H_simplifyOperationsRebasedWithC.
  now rewrite H6 in H_simplifyOperationsRebasedWithC.
  Qed.

End InsertRemoveOperationSimplificationDefinition.
  destruct (getOpP a <=? getOpP b); try discriminate.
