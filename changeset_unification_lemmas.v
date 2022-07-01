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
  Inductive sameSimplification: Operation → Operation → Operation → Operation → Prop := 
    | sameSimplificationKeep: ∀a b A B, simplifyOperations a b = Keep → simplifyOperations A B = Keep → sameSimplification a b A B
    | sameSimplificationSwap (b' a' B' A': Operation): ∀a b a' b' A B A' B', simplifyOperations a b = Swap b' a' → simplifyOperations A B = Swap B' A' → sameSimplification a b A B
    | sameSimplificationRemove: ∀a b A B, simplifyOperations a b = Remove → simplifyOperations A B = Remove → sameSimplification a b A B.

  Axiom simplifyOperations_transitive: ∀a b c, sameSimplification a b b c → sameSimplification a b a c.
  Axiom simplifyOperations_swap_preserved_under_swap_to_right: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification c a c' a.
  Axiom simplifyOperations_swap_preserved_under_swap_to_left: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification a c a c'.

  Axiom simplifyOperations_keep_preserves_opposites: ∀a b, (simplifyOperations a b) = Keep → (simplifyOperations a (AlgebraSig.invert b)) = Keep.
  Axiom simplifyOperationRemoveIffOpposites : ∀ A B, (simplifyOperations A B) = Remove <-> A = (AlgebraSig.invert B).
  Axiom opposites_swap_to_opposites: ∀a b a' b', simplifyOperations a b = Swap b' a' → simplifyOperations (AlgebraSig.invert a) b' = Swap b (AlgebraSig.invert a').
  Axiom opposites_swap_to_opposites2: ∀a b a' b', simplifyOperations a b = Swap b' a' → simplifyOperations a' (AlgebraSig.invert b) = Swap (AlgebraSig.invert b') a.

End OperationSimplificationDef.


Module SimplificationLemmas (simplificationDef: OperationSimplificationDef) (AlgebraSig: SingleOperationAlgebraSig).
  Module simplification := simplificationDef AlgebraSig.
  Module Algebra := SingleOperationAlgebra AlgebraSig.
  Import AlgebraSig.
  Import Algebra.
  Import simplification.

  Import Algebra.GroupLemmas.
  Import OperationGroup.

  (* Some additional lemmas on the behaviour of the swap function *)
  Lemma swap_inversion: ∀a b, (AlgebraSig.invert a) = b → a = (AlgebraSig.invert b).
  Proof.
  intros.
  rewrite <-H.
  now rewrite opInvertInvolution with (a:=a).
  Qed.

  Lemma resolveSameSimplificationKeep: ∀a b A B, simplifyOperations a b = Keep → (sameSimplification a b A B) → simplifyOperations A B = Keep.
  intros.
  destruct H0.
  - assumption.
  - rewrite H in H0. discriminate.
  - rewrite H in H0. discriminate.
  Qed. 

  Lemma resolveSameSimplificationSwap: ∀a b A B a' b', simplifyOperations a b = Swap b' a' →  (sameSimplification a b A B) →  ∃A' B',simplifyOperations A B = Swap B' A'.
  intros.
  destruct H0.
  - rewrite H in H0. discriminate.
  - exists A'0. exists B'0. assumption.
  - rewrite H in H0. discriminate.
  Qed. 

  Lemma resolveSameSimplificationRemove: ∀a b A B, simplifyOperations a b = Remove → (sameSimplification a b A B) → simplifyOperations A B = Remove.
  intros.
  destruct H0.
  - rewrite H in H0. discriminate.
  - rewrite H in H0. discriminate.
  - assumption.
  Qed.

  Lemma sameSimplificationSymmetric: ∀a b A B, (sameSimplification a b A B) → (sameSimplification A B a b).
  intros.
  destruct H.
  - apply sameSimplificationKeep; auto.
  - apply sameSimplificationSwap with (a':=A'0) (b':=B'0) (A':=a'0) (B':=b'0); auto.
  - apply sameSimplificationRemove; auto.
  Qed.

  Lemma sameSimplificationTransitive: ∀a1 b1 a2 b2 a3 b3, (sameSimplification a1 b1 a2 b2) → (sameSimplification a2 b2 a3 b3) → (sameSimplification a1 b1 a3 b3).
  intros.
  destruct H.
  - apply resolveSameSimplificationKeep in H0; auto. apply sameSimplificationKeep; auto.
  - apply resolveSameSimplificationSwap with (A:=a3) (B:=b3) in H1; auto. 
    destruct H1 as [A'1 [B'1 H3]].
    apply sameSimplificationSwap with (a':=a'0) (b':=b'0) (A':=A'1) (B':=B'1); auto.
  - apply resolveSameSimplificationRemove in H0; auto. apply sameSimplificationRemove; auto.
  Qed.

  Lemma simplifyOperationsSwapStable: ∀a b c a' b' c'' a'', simplifyOperations a b = Swap b' a' →
                                                             simplifyOperations b c = Keep →
                                                             simplifyOperations a' c = Swap c'' a'' →
                                                             simplifyOperations b' c'' = Keep.
  intros.
  apply simplifyOperations_swap_preserved_under_swap_to_right  with (a:=c) in H as H2.
  apply simplifyOperations_swap_preserved_under_swap_to_left  with (a:=b') in H1 as H3.
  apply resolveSameSimplificationKeep in H2; auto.
  apply resolveSameSimplificationKeep in H3; auto.
  Qed.

  Lemma simplifyOperationsSwapStable2 : ∀ a b c x a' x', 
             (simplifyOperations a b = Keep) →
             (simplifyOperations b c = Keep) →
             (simplifyOperations x a = Swap a' x') →
             (simplifyOperations a' c) = Keep.
  intros.
  apply simplifyOperations_swap_preserved_under_swap_to_right with (a:=c) in H1 .
  apply sameSimplificationKeep with (A:=b) (B:=c) in H as H3; auto.
  apply simplifyOperations_transitive in H3.
  apply resolveSameSimplificationKeep in H3; auto.
  apply resolveSameSimplificationKeep in H1; auto.
  Qed.

  Lemma simplifyOperationRemovedImpliesOpposite: ∀A B, simplifyOperations A B = Remove → A = (AlgebraSig.invert B).
  apply simplifyOperationRemoveIffOpposites.
  Qed.

  Lemma simplifyOperationResultReduced : ∀ A B, (simplifyOperations A B) = Keep → A ≠ (AlgebraSig.invert B).
  intros.
  intuition.
  apply simplifyOperationRemoveIffOpposites in H0.
  rewrite H in H0.
  discriminate.
  Qed.

  Lemma simplifyOperationOppositesRemoved : ∀ A, (simplifyOperations (AlgebraSig.invert A) A) = Remove.
  intros.
  now apply <-simplifyOperationRemoveIffOpposites.
  Qed.

  Lemma simplifyOperationsRemoveStable: ∀ a b c d,  simplifyOperations a b = Keep →
                                                    simplifyOperations b c = Remove →
                                                    simplifyOperations c d = Keep →
                                                    simplifyOperations a d = Keep.
  intros.
  apply simplifyOperationRemovedImpliesOpposite in H0.
  rewrite H0 in H.
  fold OperationsGroupImpl.opposite in H.
  fold OperationGroup.opposite in H.
  apply simplifyOperations_keep_preserves_opposites in H.
  rewrite opposite_involution in H.
  apply sameSimplificationKeep with (A:=c) (B:=d) in H as H2; auto.
  apply simplifyOperations_transitive in H2.
  apply resolveSameSimplificationKeep with (a:=a) (b:=c); auto.
  Qed.


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
           apply simplifyOperationsSwapStable with (a:=a0) (b:=a1) (c:=b) (a':=A0) (a'':=A1) (b':=B) (c'':=B0); auto.
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
              apply simplifyOperationsSwapStable2 with (x:=a0) (a:=a) (b:=b) (x':=A0); auto.
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
  Inductive opLists_equivalent : opList -> opList -> Prop :=
  | opLists_equivalent_remove:   ∀ A B a b, 
      (simplifyOperations a b) = Remove → opLists_equivalent (A ++ B) (A ++ a :: b :: B)
  | opLists_equivalent_swap:     ∀ A B a b a' b',
      (simplifyOperations a b) = Swap b' a' → opLists_equivalent (A ++ [a;b] ++ B) (A ++ [b'; a'] ++ B)
  | opLists_equivalent_refl:     ∀ A, 
      opLists_equivalent A A
  | opLists_equivalent_sym:      ∀ A B, 
      opLists_equivalent A B -> opLists_equivalent B A
  | opLists_equivalent_trans:   ∀ A B C,
      opLists_equivalent A B -> opLists_equivalent B C ->
      opLists_equivalent A C.

  Notation "S ~ T" := (opLists_equivalent S T) (at level 80).

  Add Parametric Relation: opList opLists_equivalent
    reflexivity proved by opLists_equivalent_refl
    symmetry proved by opLists_equivalent_sym
    transitivity proved by opLists_equivalent_trans
    as opLists_equivalent_rel.

  Create HintDb opListsEquivalence.
  Hint Resolve opLists_equivalent_remove : opListsEquivalence.
  Hint Resolve opLists_equivalent_swap : opListsEquivalence.
  Hint Resolve opLists_equivalent_refl : opListsEquivalence.
  Hint Resolve opLists_equivalent_sym : opListsEquivalence.
  Hint Resolve opLists_equivalent_trans : opListsEquivalence.
  Hint Extern 4 (_ ~ _) => apply opLists_equivalent_remove; auto : opListsEquivalence.

  Lemma cons_respects_opLists_equivalent: ∀ a A B, A ~ B → (a :: A) ~ (a :: B).
  Proof.
  intros.
  induction H; try auto with opListsEquivalence.
  - pose proof (opLists_equivalent_remove (a :: A) B a0 b).
    simpl in H0.
    apply H0; auto.
  - pose proof (opLists_equivalent_swap (a :: A) B a0 b a' b').
    simpl in H0.
    apply H0; auto.
  - transitivity (a::B); assumption.
  Qed.

  Add Parametric Morphism: (@cons Operation) with signature
    (@eq Operation) ==> (opLists_equivalent) ==> (opLists_equivalent) as
    cons_opList_mor.
  Proof.
  intros.
  apply cons_respects_opLists_equivalent.
  assumption.
  Qed.

  Lemma concat_respects_opLists_equivalent: ∀ A A' B B', A ~ A' → B ~ B' → (A ++ B) ~ (A' ++ B').
  Proof.
  intros.
  transitivity (A' ++ B).
  induction H; try repeat rewrite app_ass; auto with opListsEquivalence; auto.
  - transitivity (B0++B); auto.
  - induction H0; try repeat rewrite app_ass; auto with opListsEquivalence; auto.
    + specialize opLists_equivalent_remove with (A:=A'++A0) (B:=B) (a:=a) (b:=b) as H1; auto.
      repeat rewrite app_ass in H1.
      apply H1; auto.
    + specialize opLists_equivalent_swap with (A:=A'++A0) (B:=B) (a:=a) (b:=b) (a':=a') (b':=b') as H1; auto.
      repeat rewrite app_ass in H1.
      apply H1; auto.
    + transitivity (A' ++ B); auto.
  Qed.

  Add Parametric Morphism: (@app Operation) with signature
    (opLists_equivalent) ==> (opLists_equivalent) ==> (opLists_equivalent) as
    concat_opList_mor.
  Proof.
  intros.
  apply concat_respects_opLists_equivalent.
  assumption.
  assumption.
  Qed.

  Lemma tail_simplified: ∀a A T, opList_simplified A →  a::T = A → opList_simplified T.
  intros.
  destruct H.
   - discriminate.
   - inversion H0.
     apply empty_oplist_simplified.
   - inversion H0; auto.
  Qed.

  Lemma tail_of_simplify_simplified: ∀a A T,  a::T = (simplifyOpList A) → opList_simplified T.
  intros.
  specialize simplifyOpList_simplified with (A:=A) as H_simplified.
  apply tail_simplified in H; auto.
  Qed.

  Lemma tail_simplified2: ∀a A, opList_simplified (a::A) → opList_simplified A.
  intros.
  remember (a::A) as A'. 
  destruct H.
   - discriminate.
   - inversion HeqA'.
     apply empty_oplist_simplified.
   - now inversion HeqA'. 
  Qed.

  Lemma simplify_op_list_le_length: ∀ A, length (simplifyOpList A) ≤ length A.
  intros.
  remember (length A) as lenA.
  rewrite HeqlenA.
  assert_nat (length A ≤ lenA) as H_leLenA.
  clear HeqlenA.
  revert H_leLenA.
  revert A.
  induction lenA.
  - intros.
    assert_nat (Datatypes.length A = 0).
    apply length_zero_iff_nil in H.
    rewrite H in *.
    simpl.
    lia.
  - destruct A; try (simpl;lia).
    intros.
    unfold simplifyOpList.
    destruct A.
    + simpl; lia.
    + fold simplifyOpList.
      assert ((insertOpInSimplifiedOpList o0 (simplifyOpList A)) = simplifyOpList (o0 :: A)). { now cbv. }
      rewrite H.
      remember (simplifyOpList (o0 :: A)) as Y.
      destruct Y.
      * simpl.
        lia.
      * unfold insertOpInSimplifiedOpList.
        specialize IHlenA with (A:=Y) as H_IHY.
        simpl in H_leLenA.
        assert (Datatypes.length (simplifyOpList (o0 :: A)) ≤ S (length A)). { apply IHlenA. simpl. lia. }
        assert (Datatypes.length (simplifyOpList (o0 :: A)) ≤ lenA). {
          specialize IHlenA with (A:=o0 :: A). 
          lia. 
        }
        assert (S (length Y) ≤ lenA). { rewrite <-HeqY in H0. simpl in H0. lia. }
        assert (Datatypes.length (simplifyOpList Y) ≤ lenA). { 
          lia.
        }
        assert (S (length Y) ≤ (length (simplifyOpList (o0 :: A)))). {
          assert_nat (length (o1 :: Y) ≤ length (o1 :: Y)).
          rewrite HeqY in H4 at 2.
          simpl (Datatypes.length (o1 :: Y)) in H4.
          lia.
        }
        assert_nat ((length Y) ≤ (length A)). 

        destruct (simplifyOperations o o1); try (simpl; lia).

        fold insertOpInSimplifiedOpList.
        assert (insertOpInSimplifiedOpList A0 Y = simplifyOpList (A0::Y)). {
          rewrite <-simplifyOpList_fixes_simplified with (A:=Y) at 1.
          now cbv.
          apply tail_of_simplify_simplified with (a:=o1) (A:=o0::A); auto.
        }
        rewrite H6.
        remember (simplifyOpList (A0 :: Y)) as Z.
        simpl.
        assert ((length Z) ≤ S (length Y)). {
          specialize IHlenA with (A:= A0::Y).
          rewrite <-HeqZ in IHlenA.
          simpl (length (A0 :: Y)) in IHlenA.
          lia.
        }
        lia.
  Qed. 
 
  Lemma simplifyOpList_equiv: ∀ A, simplifyOpList A ~ A.
  Proof.
  intro.
  unfold simplifyOpList.
  remember (length A) as lenA.
  assert_nat (length A ≤ lenA) as HleLenA.
  clear HeqlenA.
  revert HleLenA.
  revert A.
  induction lenA.
  - intros.
    assert_nat (length A = 0).
    apply length_zero_iff_nil in H.
    rewrite H.
    reflexivity.
  - intros.
    fold simplifyOpList in *.
    destruct A.
    + now cbv.
    + unfold simplifyOpList.
      fold simplifyOpList.
      remember (simplifyOpList A) as simplA.
      destruct simplA.
      * specialize IHlenA with (A:=A).
        rewrite <-HeqsimplA in IHlenA.
        rewrite <-IHlenA.
        2: { simpl in HleLenA. lia. }
        now cbv.
      * unfold insertOpInSimplifiedOpList.
        assert (o0::simplA ~ A) as H_simplA. {
          rewrite HeqsimplA.
          apply IHlenA.
          simpl in HleLenA.
          lia.
        }
        destruct (simplifyOperations o o0 ) eqn:H_simplifyOperations.
        -- now rewrite H_simplA.
        -- fold insertOpInSimplifiedOpList.
           assert (insertOpInSimplifiedOpList A0 (simplifyOpList simplA) = simplifyOpList (A0:: simplA)). { now unfold simplifyOpList. }

           apply tail_of_simplify_simplified in HeqsimplA as H_simplA_simplified.
           rewrite simplifyOpList_fixes_simplified in H; auto.
           rewrite H.
           rewrite IHlenA.
           2: { 
             simpl in HleLenA.
             specialize simplify_op_list_le_length with (A:=A) as simplifyOp_smaller_or_equal_length.
             assert (length (o0 :: simplA) = length (simplifyOpList A)). { now rewrite HeqsimplA. }
             simpl in H0.
             simpl.
             lia.
           }
           apply opLists_equivalent_swap with (A:=[]) (B:=simplA) in H_simplifyOperations.
           simpl in H_simplifyOperations.
           rewrite <-H_simplifyOperations.
           now rewrite H_simplA.
        -- rewrite <-H_simplA.

           apply opLists_equivalent_remove with (A:=[]) (B:= simplA) in H_simplifyOperations.
           simpl in H_simplifyOperations.
           now rewrite <-H_simplifyOperations.
  Qed.

  Lemma simplify_takes_concat_to_composition:
    ∀ A B,
      simplifyOpList (A ++ (simplifyOpList (B))) =
      simplifyOpList (A ++ B).
  Proof.
  intros.
  induction A.
  simpl.
  rewrite simplifyOpList_idempotent.
  reflexivity.
  simpl.
  rewrite IHA.
  reflexivity.
  Qed.

  Lemma simplify_will_remove_opposites: ∀a A, simplifyOpList ((opposite a)::a::A) = simplifyOpList A.
  intros.
  unfold simplifyOpList at 1.
  fold simplifyOpList.
  revert a.
  remember (simplifyOpList A) as Z.
  specialize simplifyOpList_simplified with(A:=A) as H_ASimplified.
  rewrite <-HeqZ in H_ASimplified.
  clear HeqZ.
  revert H_ASimplified.
  revert A.
  induction Z.
  - intros.
    cbv.
    now rewrite simplifyOperationOppositesRemoved.
  - intros.
    remember (a::Z) as X.
    unfold insertOpInSimplifiedOpList at 1 2.
    destruct X eqn:H_X.
    + now rewrite simplifyOperationOppositesRemoved.
    + destruct (simplifyOperations a0 o) eqn:H_simplifyOperations.
      * now rewrite simplifyOperationOppositesRemoved.
      * apply opposites_swap_to_opposites in H_simplifyOperations.
        fold OperationsGroupImpl.opposite in H_simplifyOperations.
        fold OperationGroup.opposite in H_simplifyOperations.
        rewrite H_simplifyOperations.
        inversion HeqX.
        fold insertOpInSimplifiedOpList.
        inversion HeqX.
        rewrite IHZ with (a:=A0); auto.
        rewrite HeqX in H_ASimplified.
        remember (a :: Z) as A'.
        destruct H_ASimplified.
        -- discriminate.
        -- inversion HeqA'.
            apply empty_oplist_simplified.
        -- now inversion HeqA'.
      * apply simplifyOperationRemovedImpliesOpposite in H_simplifyOperations.
        assert ((opposite a0) = o). {
          specialize opposite_involution with (a:=o) as H.
          fold OperationsGroupImpl.opposite in H_simplifyOperations.
          autounfold in *.
          rewrite <-H.
          rewrite <-H_simplifyOperations.
          now unfold opposite.
        }
        rewrite H.
        apply simplifyOpList_fixes_simplified in H_ASimplified as H_simplifyOpEq.
        cbn in H_simplifyOpEq.
        remember (o :: l) as Y.
        destruct H_ASimplified.
        -- discriminate.
        -- now inversion HeqY.
        -- assert ((simplifyOpList l) = l). {
             inversion HeqY.
             rewrite H3 in *.
             rewrite simplifyOpList_fixes_simplified; auto.
           }
           rewrite H1 in H_simplifyOpEq.
           unfold insertOpInSimplifiedOpList in H_simplifyOpEq.
           assumption.
  Qed.
  
  Lemma simplify_equal_for_swaps: ∀a b a' b' A, (simplifyOperations a b) = Swap b' a' → simplifyOpList ([a; b] ++ A) = simplifyOpList ([b'; a'] ++ A).
  intros.
  rewrite <-simplify_takes_concat_to_composition.
  rewrite <-simplify_takes_concat_to_composition with (A:=[b';a']).
  remember (simplifyOpList A) as Z.
  specialize simplifyOpList_simplified with (A:=A) as H_Zsimplified.
  rewrite <-HeqZ in H_Zsimplified.
  rewrite <-app_comm_cons.
  rewrite <-cons_to_app.
  rewrite <-app_comm_cons.
  rewrite <-cons_to_app.
  unfold simplifyOpList.
  fold simplifyOpList.
  rewrite simplifyOpList_fixes_simplified; auto.
  revert H.
  revert a b a' b'.
  clear HeqZ.
  induction Z as [ | c Z' ].
  - cbv.
    intros.
    rewrite H.
    apply simplifyOperationsInvolutive in H.
    rewrite H.
    reflexivity.
  - intros.
    unfold insertOpInSimplifiedOpList.
    destruct (simplifyOperations b c) as [ | c'' b'' | ] eqn:H_simplifyOperations.
    + rewrite H.
      apply simplifyOperationsInvolutive in H as H_simplifyOperations_b'a'.
      destruct (simplifyOperations a' c) as [ | c'' a'' | ] eqn:H_simplifyOperations2.
      * now rewrite H_simplifyOperations_b'a'.
      * fold insertOpInSimplifiedOpList.
        rewrite simplifyOperationsSwapStable with (a:=a) (b:=b) (c:=c) (a':=a') (c'':=c'') (a'':=a''); auto.
      * destruct Z' as [|d Z''].
        -- easy.
        -- rewrite simplifyOperationsRemoveStable with (b:=a') (c:=c); auto.
           remember (c :: d :: Z'') as Z'''.
           destruct H_Zsimplified; try discriminate.
           inversion HeqZ'''.
           rewrite H2 in *.
           now rewrite H3 in *.
    + fold insertOpInSimplifiedOpList.

      simplifyOperations a b = Swap b' a' 
      simplifyOperations a c = Swap c' a'' 
      simplifyOperations a' c = Swap c' a'' 


      simplifyOperations a b = Swap b' a'      = a > b
      simplifyOperations b c = Swap c'' b''    = b > c
      
      simplifyOperations a c'' = Swap c''' a'''      = a > c

      simplifyOperations a' c = Swap c_r a_r         = a > c

      simplifyOperations b' c_r = Swap c''' a_r2     = b > c
      simplifyOperations a''' b'' = Swap a_r2 a_r    = a > b


      assert (∃a''' c''', simplifyOperations a c'' = Swap c''' a'''). { give_up. }
      destruct H0 as [a''' [c''' H0]].
      assert (∃a_r c_r, simplifyOperations a' c = Swap c_r a_r). { give_up. }
      destruct H1 as [a_r [c_r H1]].
      assert (∃a_r2, simplifyOperations b' c_r = Swap c''' a_r2). { give_up. }
      destruct H2 as [a_r2 H2].
      assert (simplifyOperations a''' b'' = Swap a_r2 a_r). { give_up. }
      rewrite H0.
      rewrite H1.
      unfold insertOpInSimplifiedOpList at 3.
      rewrite H2.
      f_equal.
      apply IHZ'; auto.
      now apply tail_simplified2 in H_Zsimplified.
    + fold insertOpInSimplifiedOpList.
      apply simplifyOperationsInvolutive in H as H_Keep_b'a'.
      apply simplifyOperationRemovedImpliesOpposite in H_simplifyOperations.
      rewrite H_simplifyOperations in H.
      apply opposites_swap_to_opposites2 in H as H_simplifyOperationsa'c.
      rewrite opInvertInvolution in H_simplifyOperationsa'c.
      symmetry in H_simplifyOperations.
      apply swap_inversion in H_simplifyOperations as H_cEqInvB.
      rewrite H_simplifyOperationsa'c.
      unfold insertOpInSimplifiedOpList at 2.
      rewrite <-opInvertInvolution with (a:=b') at 1.
      now rewrite simplifyOperationOppositesRemoved.
  Admitted.

  Lemma equiv_opLists_have_same_simplification:
    ∀ A B,
    A ~ B -> simplifyOpList (A) =
             simplifyOpList (B).
  Proof.
  intros.
  induction H; auto with opListsEquivalence.
  - rewrite <- simplify_takes_concat_to_composition with (A:=A) (B:=(a :: b :: B)).
    apply simplifyOperationRemovedImpliesOpposite in H.
    rewrite H.
    fold OperationsGroupImpl.opposite.
    fold OperationGroup.opposite.
    rewrite simplify_will_remove_opposites.
    rewrite simplify_takes_concat_to_composition with (A:=A) (B:=B).
    reflexivity.
  - rewrite <- simplify_takes_concat_to_composition with (A:=A) (B:=[b'; a']++B).
    rewrite <-simplify_equal_for_swaps with (a:=a) (b:=b) (a':=a') (b':=b'); auto.
    rewrite simplify_takes_concat_to_composition with (A:=A) (B:=[a; b]++B).
    reflexivity.
  - transitivity (simplifyOpList B); auto.
  Qed.

  Lemma simplifyOpList_swaps_with_concat: ∀A B, simplifyOpList (A ++ B) =
                                                simplifyOpList (simplifyOpList A ++ simplifyOpList B).
  intros.
  apply equiv_opLists_have_same_simplification.
  rewrite simplifyOpList_equiv with (A:=A).
  rewrite simplifyOpList_equiv with (A:=B).
  reflexivity.
  Qed.

  Lemma str_equiv_implies_same_reduction: ∀A B, A ~~ B → (simplifyOpList A) = (simplifyOpList B).
  intros.
  induction H.
  - rewrite simplifyOpList_swaps_with_concat with (B:=opposite a :: a :: T).
    rewrite simplify_will_remove_opposites.
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


