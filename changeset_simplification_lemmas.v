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


  Axiom simplifyOperationsSwapCompatibleWithRebase : ∀ A B A' B' C, (simplifyOperations A B) = (Swap B' A') → 
                                                                 ((Some C) ↷ (Some A) ↷ (Some B) = (Some C) ↷ (Some B') ↷ (Some A'))%OO.
  Axiom rebaseSwap: ∀ a b a' b' a0 b0 c0 a'0 b'0, simplifyOperations a b = Swap b' a' →
                                                  (Some a ↷ Some c0)%OO = Some a0 →
                                                  (Some b ↷ Some (AlgebraSig.invert a) ↷ Some c0 ↷ (Some a ↷ Some c0))%OO = Some b0 →
                                                  (Some b' ↷ Some c0)%OO = Some b'0 →
                                                  (Some a' ↷ Some (AlgebraSig.invert b') ↷ Some c0 ↷ (Some b' ↷ Some c0))%OO = Some a'0 →
                                                  simplifyOperations a0 b0 = Swap b'0 a'0.
  Axiom simplifyOperationsRemoveCompatibleWithRebase : ∀ A B C, (simplifyOperations A B) = Remove → 
                                                             ((Some C) ↷ ((Some A) ↷ (Some B)) = (Some C))%OO.
  Inductive sameSimplification: Operation → Operation → Operation → Operation → Prop := 
    | sameSimplificationKeep: ∀a b A B, simplifyOperations a b = Keep → simplifyOperations A B = Keep → sameSimplification a b A B
    | sameSimplificationSwap (b' a' B' A': Operation): ∀a b a' b' A B A' B', simplifyOperations a b = Swap b' a' → simplifyOperations A B = Swap B' A' → sameSimplification a b A B
    | sameSimplificationRemove: ∀a b A B, simplifyOperations a b = Remove → simplifyOperations A B = Remove → sameSimplification a b A B.

  Axiom simplifyOperations_transitive: ∀a b c, sameSimplification a b b c → sameSimplification a b a c.
  Axiom simplifyOperations_swap_preserved_under_swap_to_right: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification c a c' a.
  Axiom simplifyOperations_swap_preserved_under_swap_to_left: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification a c a c'.
  Axiom simplifyOperations_double_swap: ∀a b c a' b' c'' b'', simplifyOperations a b = Swap b' a' → simplifyOperations b c = Swap c'' b'' → ∃b''', simplifyOperations a' c = Swap c b'''.
  Axiom simplifyOperations_right_argument_preserved_in_swap: ∀a b a' b', simplifyOperations a b = Swap b' a' → b = b'.

  (*a_r = a ↷ b ↷ c
  a_r' = a ↷ c ↷ (b ↷ c)*)
  Axiom simplifyOperations_swap_over_inverses: ∀a b c b_a a_b c_a a_c c_b b_c c_a_b a_b_c, simplifyOperations a b = Swap b_a a_b → simplifyOperations a c = Swap c_a a_c → simplifyOperations b c = Swap c_b b_c → 
                                                              simplifyOperations a_b c = Swap c_a_b a_b_c → simplifyOperations a_c b_c = Swap b_c a_b_c.

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

      apply sameSimplificationSwap with (a:=a) (b:=b) (a':=a') (b':=b') in H_simplifyOperations as H_sameSimpl; auto.
      apply simplifyOperations_transitive in H_sameSimpl.
      apply simplifyOperations_swap_preserved_under_swap_to_left with (a:=a) in H_simplifyOperations as H_sameSimplification_a_c_a_c'.
      specialize sameSimplificationTransitive with (1:=H_sameSimpl) (2:=H_sameSimplification_a_c_a_c') as H_ac''.
      apply resolveSameSimplificationSwap with (1:=H) in H_ac''.
      destruct H_ac'' as [a''' [c''' H_ac'']]. 

      specialize simplifyOperations_double_swap with (1:=H) (2:=H_simplifyOperations) as H1.
      destruct H1 as [a_r H1].

      apply simplifyOperations_swap_preserved_under_swap_to_right with (a:=c) in H as H2.
      apply resolveSameSimplificationSwap with (1:=H_simplifyOperations) in H2.
      destruct H2 as [b_r2 [c_r2 H2]].

      apply simplifyOperations_right_argument_preserved_in_swap in H_simplifyOperations as H_c_c''.
      apply simplifyOperations_right_argument_preserved_in_swap in H_ac'' as H_c'_c'''.
      rewrite <-H_c_c'' in *.
      rewrite <-H_c'_c''' in *.

      apply simplifyOperations_right_argument_preserved_in_swap in H2 as H2_c_c_r2.
      rewrite <-H2_c_c_r2 in *.

       assert (simplifyOperations a''' b'' = Swap b_r2 a_r). {
         apply simplifyOperations_right_argument_preserved_in_swap in H as H2_b_b'.
         rewrite <-H2_b_b' in *.
         rewrite H_simplifyOperations in H2.
         inversion H2.
         rewrite <-H3 in *.
      (*a b c => a c b''  => c a''' b'' => c b_r2 a_r'
      b' a' c => b' c a_r => c b_r2 a_r*)

      (*a_r = a ↷ b ↷ c
      a_r' = a ↷ c ↷ (b ↷ c)*)
        specialize simplifyOperations_swap_over_inverses with (1:=H) (2:=H_ac'') (3:=H_simplifyOperations) (4:=H1).
        auto.
      }

      rewrite H_ac''.
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
  Qed.

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

  Definition rebaseOperationWithOpList (a: Operation) (ops: opList) := 
    match (fold_left rebaseOperation ((map (λ x: Operation, Some x)) ops) (Some a)) with
      | Some op => [op]
      | None => []
    end.

  Fixpoint rebaseOpListWithOpList (A B : opList) {struct A}:= 
    match A with
      | [] => []
      | opA::Atail =>
          match Atail with
          | nil => (rebaseOperationWithOpList opA B)
          | _ =>
             let R1 := (rebaseOperationWithOpList opA B) in 
             let R2 := (rebaseOpListWithOpList Atail (squashOpList (inverse_str [opA]) (squashOpList B R1) )) in 
             (squashOpList R1 R2)
          end
  end.

  Lemma fold_left_no_error: ∀ A a, ∃ y, fold_left rebaseOperation (map (λ x : Operation, Some x) A) (Some a) = Some y.
      induction A.
      - cbv.
        intros.
        now exists a.
      - rewrite map_cons.
        simpl.
        intros.
        destruct (Some a0 ↷ Some a)%OO eqn:H_reb.
        + destruct IHA with (a:=o).
          rewrite H.
          now exists x.
        + apply noErrorsDuringRebase in H_reb. contradiction H_reb.
  Qed.

  Lemma rebaseOperationWithOpList_equal_to_rebaseOperationWithChangeSet: ∀a A, 
    ∃ red, (rebaseOperationWithChangeSet a (CSet A)) = (CSet {|
      operations := rebaseOperationWithOpList a (operations A);
      operations_reduced := red;
  |}).
  intros.
  unfold rebaseOperationWithChangeSet.
  unfold rebaseOperationWithOpList.
  specialize fold_left_no_error with (a:=a) (A:=operations A) as H_noError.
  destruct H_noError.
  rewrite H.
  exists (single_letter_reduced x).
  now cbv.
  Qed.

  Lemma simplify_squash: ∀A B redA redB,
    CSet {|operations:=A; operations_reduced:=redA |} ○ CSet {|operations:=B; operations_reduced:=redB |} =
    CSet {|operations:=squashOpList A B ; 
           operations_reduced:=squashIsReduced A B redA redB |}.
    intros.
    now cbv.
  Qed.

  Lemma rebaseOpListWithOpList_equal_to_rebaseChangeSetOps: ∀A A_reduced B, 
    ∃ red, (rebaseChangeSetOps A A_reduced (CSet B)) = (CSet {|
      operations := rebaseOpListWithOpList A (operations B);
      operations_reduced := red;
  |}).
  intros.
  
  Ltac rewrite_rebase_operations :=
    match goal with 
    |- context [rebaseOperationWithChangeSet ?O (CSet ?X)] => 
      let H_rewrite := (fresh) in 
      let idCset := (fresh "red") in 
      specialize rebaseOperationWithOpList_equal_to_rebaseOperationWithChangeSet with (a:=O) (A:=X) as H_rewrite;
      destruct H_rewrite as (idCset & H_rewrite);
      rewrite H_rewrite;
      clear H_rewrite
   end.
  Ltac simplify :=
    repeat rewrite_rebase_operations;
    repeat rewrite simplify_squash;
    unfold opToCs;
    unfold invert;
    unfold operations;
    unfold operations_reduced.

  remember (length A) as lenA.
  assert_nat(length A ≤ lenA) as H_lenA.
  clear HeqlenA.
  revert H_lenA.
  revert A_reduced.
  revert B.
  revert A.
  induction lenA.
  all: (
    intros;
    destruct A;
    simpl in H_lenA; 
    try lia
  ).
  - exists empty_str_reduced.
    now cbv.
  - simpl.
    exists empty_str_reduced.
    now cbv. 
  - unfold rebaseChangeSetOps.
    fold rebaseChangeSetOps.
    unfold rebaseOpListWithOpList.
    fold rebaseOpListWithOpList.

    destruct A.
    + rewrite_rebase_operations.
      now exists red.
    + rewrite squashAssociative.
      destruct B.
      repeat simplify.
      match goal with 
         |- context [rebaseChangeSetOps ?X ?red (CSet ?Z)] => 
        specialize IHlenA with 
          (A:=X) 
          (A_reduced:=red)
          (B:=Z)
      end.
      destruct IHlenA; try lia.
      rewrite H.
      repeat simplify.
      now match goal with 
        |- context [{| operations := _; operations_reduced:= ?R |}] => exists R
      end.
  Qed.

  Lemma remove_inverses_from_fold_left_rebaseOperation: ∀ y a0 B, fold_left rebaseOperation
      (map (λ x : Operation, Some x) (a0 :: (a0⁻¹)%O :: B)) (Some y) = fold_left rebaseOperation
      (map (λ x : Operation, Some x) B) (Some y). 
        intros.
        do 2 rewrite map_cons.
        simpl.
        specialize rebaseOperatrionRightDistibutivity with (A:=y) (B:=a0) as H_duplicates.
        replace (Some (a0⁻¹)%O) with ((Some a0)⁻¹)%OO. 2: { now cbv. }
        destruct H_duplicates.
        - now rewrite H.
        - destruct ( (Some y) ↷ (Some a0))%OO eqn:H_reb.
            + apply noErrorsDuringRebase in H. contradiction H.
            + apply noErrorsDuringRebase in H_reb. contradiction H_reb.
  Qed.

  Lemma rebaseOperationWithOplist_equiv: ∀a A A', A ~ A' →
                                            rebaseOperationWithOpList a A ~ 
                                            rebaseOperationWithOpList a A'.
  intros.
  induction H; auto with opListsEquivalence.
  3: transitivity (rebaseOperationWithOpList a B); auto.
  all: (
    unfold rebaseOperationWithOpList;
    unfold rebaseOperationWithChangeSet;
    unfold operations
  ).
  - do 2 rewrite map_app.
    do 2 rewrite fold_left_app.
    apply simplifyOperationRemoveIffOpposites in H.
    symmetry in H.
    apply swap_inversion in H.
    rewrite H.


    specialize fold_left_no_error with (a:=a) (A:=A) as H_fold.
    destruct H_fold. rewrite H0.
    now rewrite remove_inverses_from_fold_left_rebaseOperation.
  - do 4 rewrite map_app.
    do 4 rewrite fold_left_app.

    specialize fold_left_no_error with (a:=a) (A:=A) as H_fold.
    destruct H_fold. rewrite H0.

    simpl.
    now rewrite simplifyOperationsSwapCompatibleWithRebase with (1:=H).
  Qed.

  Add Parametric Morphism: (@rebaseOperationWithOpList) with signature
    (@eq Operation) ==> (opLists_equivalent) ==> (opLists_equivalent) as
    revaseOperationWithOpList_mor.
  intros.
  apply rebaseOperationWithOplist_equiv.
  assumption.
  Qed.

  Add Parametric Morphism: (@squashOpList) with signature
    (@opLists_equivalent) ==> (opLists_equivalent) ==> (opLists_equivalent) as
    squashOpList_mor.
  intros.
  rewrite <-simplifyOpList_equiv with (A:=squashOpList x x0).
  rewrite <-simplifyOpList_equiv with (A:=squashOpList y y0).
  unfold squashOpList.
  unfold reduced_string_product.
  do 2 rewrite simplifyOpList_reduces.
  do 2 rewrite simplifyOpList_equiv.
  rewrite H.
  rewrite H0.
  reflexivity.
  Qed.

  Lemma rebaseOperationWithChangeSet_param2_equiv: ∀A B B', B ~ B' →
                                                   rebaseOpListWithOpList A B ~ 
                                                   rebaseOpListWithOpList A B'.
  intros.
  revert H.
  revert B.
  revert B'.
  induction A.
  - reflexivity.
  - intros.
    unfold rebaseOpListWithOpList.
    fold rebaseOpListWithOpList.
    
    destruct A.
    + now rewrite H.
    + rewrite H at 1.
      rewrite IHA with (B':=(squashOpList (inverse_str [a]) (squashOpList B' (rebaseOperationWithOpList a B')))).
      reflexivity.
      * now repeat rewrite H.
  Qed.

  Lemma squashOpList_app_equiv: ∀ A B, (squashOpList A B) ~ A++B.
  intros.
  rewrite <-simplifyOpList_equiv with (A:=squashOpList A B).
  unfold squashOpList.
  unfold reduced_string_product.
  rewrite simplifyOpList_reduces.
  rewrite simplifyOpList_equiv with (A:=A++B).
  reflexivity.
  Qed.

  Lemma rebaseOperationWithOpList_cons: ∀a b c B, (Some a ↷ Some b)%OO = Some c → rebaseOperationWithOpList a (b::B) = rebaseOperationWithOpList c B.
  intros.
  unfold rebaseOperationWithOpList.
  unfold fold_left.
  unfold map.
  rewrite H.
  auto.
  Qed.

  Lemma opposites_empty_equiv: ∀a, [opposite a; a] ~ []. 
  intros.
  specialize opLists_equivalent_remove with (A:=[]) (B:=[]) as H.
  simpl in H.
  rewrite <-H.
  reflexivity.
  apply simplifyOperationRemoveIffOpposites.
  now cbv.
  Qed.

  Lemma rebase_pair_equiv: ∀a b a0 b0 c0 C,   (Some a ↷ Some c0)%OO = Some a0 → 
                                                 (((Some b ↷ Some (opposite a)) ↷ Some c0) ↷ (Some a ↷ Some c0)%OO)%OO = Some b0 → 
                                                 (rebaseOpListWithOpList [a; b] (c0::C) ) ~ rebaseOperationWithOpList a0 C ++ rebaseOperationWithOpList b0 (opposite a0 :: C ++ rebaseOperationWithOpList a0 C).
  intros.
  unfold rebaseOpListWithOpList.
  repeat rewrite squashOpList_app_equiv.

  unfold inverse_str.
  repeat rewrite app_nil_l.

  rewrite cons_to_app.
  rewrite <-app_assoc.
  repeat rewrite <-cons_to_app.

  Ltac rewriteRebaseOperationWithOpList op1 op2 :=
    let rebasedName := (fresh "X") in
    let rebasedNameEqn := (fresh "H_eq" op1) in
    let rebasedNameDestructEqn := (fresh "X3") in
    let newName := (fresh op1) in
    remember (Some op1 ↷ Some op2)%OO as rebasedName eqn:rebasedNameEqn;
    symmetry in rebasedNameEqn;
    destruct rebasedName as [newName|];
    only 2: ( apply noErrorsDuringRebase in rebasedNameEqn; contradiction );
    rewrite rebaseOperationWithOpList_cons with (c:=newName) (1:=rebasedNameEqn); auto.

  rewriteRebaseOperationWithOpList a c0.

  assert (∀ x o : Operation, x :: c0 :: C ~ x :: c0 :: o :: (opposite o) :: C) as H_insert_opposites. {
    intros.
    rewrite cons_to_app.
    rewrite cons_to_app with (a:=c0).
    rewrite cons_to_app with (l:=c0 :: o :: opposite o :: C).
    rewrite cons_to_app with (l:= o :: opposite o :: C).
    apply opLists_equivalent_remove with (A:=[x]++[c0]) (B:=C).
    specialize opInvertInvolution with (a:=o) as H_inv.
    unfold opposite.
    unfold OperationsGroupImpl.opposite.
    rewrite <-H_inv.
    rewrite H_inv at 2.
    apply simplifyOperationOppositesRemoved.
  }

  do 2 rewrite app_comm_cons.
  rewrite H_insert_opposites with (x:=opposite a) (o:=a1).
  repeat rewrite <-app_comm_cons.


  rewriteRebaseOperationWithOpList b (opposite a).
  rewriteRebaseOperationWithOpList b1 c0.
  rewriteRebaseOperationWithOpList b2 a1.

  inversion H.
  now inversion H0.
  Qed.

  Lemma rebase_opposite_eqiv: ∀a C, (rebaseOpListWithOpList [(opposite a); a] C) ~ [].
  intros.

  remember (length C) as lenC.
  revert a.
  revert HeqlenC.
  revert C.
  induction lenC.
  - intros.
    destruct C; try ( simpl in HeqlenC; lia).
    unfold rebaseOpListWithOpList.
    replace (rebaseOperationWithOpList (opposite a) []) with [opposite a]. 2: { now cbv. }
    assert (squashOpList (inverse_str [opposite a]) (squashOpList [] (rebaseOperationWithOpList (opposite a) [])) ~ []). {
      unfold inverse_str.
      repeat rewrite squashOpList_app_equiv.
      replace (rebaseOperationWithOpList (opposite a) []) with [opposite a]. 2: {now cbv. }
      simpl.
      apply opposites_empty_equiv.
    }
    rewrite H.
    replace (rebaseOperationWithOpList a []) with [a]. 2: {now cbv. }
    repeat rewrite squashOpList_app_equiv.
    apply opposites_empty_equiv.

  - intros.
    destruct C as [|c0 C]. 1: {simpl  in HeqlenC. lia. }
    remember ((Some (opposite a) ↷ Some c0)%OO) as a'.
    symmetry in Heqa'.
    destruct a' as [a'|].
    2: { apply noErrorsDuringRebase in Heqa'. contradiction. } 

    remember ( (((Some a ↷ Some a) ↷ Some c0) ↷ (Some (opposite a) ↷ Some c0)%OO)%OO ) as a''.
    destruct a'' as [a''|].
    2: resolveRebaseNotNone Heqa''.

    specialize rebaseOperatrionLeftDistibutivity with (A:=opposite a) (B:=c0) as H_inverse.
    destruct H_inverse as [ H_inverse|H_inverse ].
    2: resolveRebaseNotNone H_inverse.

    unfold opposite in Heqa''.
    unfold OperationsGroupImpl.opposite in Heqa''.
    autounfold in *.
    assert (Some a'' = (Some a')⁻¹)%OO. {
      unfold opposite in H_inverse.
      unfold OperationsGroupImpl.opposite in H_inverse.
      unfold invertOperationOption at 2 3 in H_inverse.
      rewrite opInvertInvolution in H_inverse.
      rewrite <-H_inverse in Heqa''.
      rewrite Heqa''.
      rewrite <-Heqa'.
      unfold opposite.
      unfold OperationsGroupImpl.opposite.
      reflexivity.
    }
    inversion H.

    specialize (IHlenC) with (C:=C) (a:=(opposite a')%O).
    unfold rebaseOpListWithOpList in IHlenC.
    repeat rewrite squashOpList_app_equiv in IHlenC.
    rewrite opposite_involution in IHlenC.

    rewrite rebase_pair_equiv with (1:=Heqa') (b0:=a''); auto.
    rewrite H1.
    apply IHlenC.
    * simpl in HeqlenC. lia.
    * rewrite opposite_involution. auto.
  Qed.

  Lemma rebase_swap_eqiv: ∀a b a' b' C, simplifyOperations a b = Swap b' a' → (rebaseOpListWithOpList [a; b] C) ~ (rebaseOpListWithOpList [b'; a'] C).
  intros.

  remember (length C) as lenC.
  revert H.
  revert a b a' b'.
  revert HeqlenC.
  revert C.
  induction lenC.
  - intros.
    unfold rebaseOpListWithOpList.
    repeat rewrite squashOpList_app_equiv.

    unfold inverse_str.
    repeat rewrite app_nil_l.
    destruct C; try ( simpl in HeqlenC; lia).
    cbn.
    do 2 rewrite opposites_empty_equiv.
    cbn.
    apply opLists_equivalent_swap with (A:=[]) (B:=[]).
    auto.
  - intros.
    destruct C as [|c0 C]. 1: {simpl  in HeqlenC. lia. }

    remember ((Some a ↷ Some c0)%OO) as a0.
    symmetry in Heqa0.
    destruct a0 as [a0|].
    2: { apply noErrorsDuringRebase in Heqa0. contradiction. } 

    remember ( (((Some b ↷ Some (opposite a)) ↷ Some c0) ↷ (Some a ↷ Some c0)%OO)%OO ) as b0.
    symmetry in Heqb0.
    destruct b0 as [b0|].
    2: { 
      set (x:=(Some a ↷ Some c0)%OO) in *.
      destruct x eqn:H_x; try (apply noErrorsDuringRebase in H_x; contradiction).
      set (x':=(Some b ↷ Some (opposite a))%OO) in *.
      destruct x' eqn:H_x'; try (apply noErrorsDuringRebase in H_x'; contradiction).
      set (x'':=(Some o0 ↷ Some c0)%OO) in *.
      destruct x'' eqn:H_x''; try (apply noErrorsDuringRebase in H_x''; contradiction).
      apply noErrorsDuringRebase in Heqb0.
      contradiction.
    }

    rewrite rebase_pair_equiv with (a0:=a0) (b0:=b0); auto.


    remember ((Some b' ↷ Some c0)%OO) as b'0.
    symmetry in Heqb'0.
    destruct b'0 as [b'0|].
    2: { apply noErrorsDuringRebase in Heqb'0. contradiction. } 

    remember ( (((Some a' ↷ Some (opposite b')) ↷ Some c0) ↷ (Some b' ↷ Some c0)%OO)%OO ) as a'0.
    symmetry in Heqa'0.
    destruct a'0 as [a'0|].
    2: { 
      set (x:=(Some b' ↷ Some c0)%OO) in *.
      destruct x eqn:H_x; try (apply noErrorsDuringRebase in H_x; contradiction).
      set (x':=(Some a' ↷ Some (opposite b'))%OO) in *.
      destruct x' eqn:H_x'; try (apply noErrorsDuringRebase in H_x'; contradiction).
      set (x'':=(Some o0 ↷ Some c0)%OO) in *.
      destruct x'' eqn:H_x''; try (apply noErrorsDuringRebase in H_x''; contradiction).
      apply noErrorsDuringRebase in Heqa'0.
      contradiction.
    }

    rewrite rebase_pair_equiv with (a0:=b'0) (b0:=a'0); auto.
    specialize rebaseSwap with (1:=H) (2:=Heqa0) (3:=Heqb0) (4:=Heqb'0) (5:=Heqa'0) as H_simplifyOperations2.

    specialize (IHlenC) with (C:=C) (2:=H_simplifyOperations2).

    unfold rebaseOpListWithOpList in IHlenC.
    repeat rewrite squashOpList_app_equiv in IHlenC.
    unfold inverse_str in IHlenC.
    repeat rewrite app_nil_l in IHlenC.
    rewrite <-cons_to_app in IHlenC.
    rewrite <-cons_to_app in IHlenC.
    apply IHlenC.
    simpl in HeqlenC.
    lia.
  Qed.

  Lemma rebase_invert_eqiv: ∀a b a' b', simplifyOperations a b = Swap b' a' → (inverse_str [a; b]) ~ (inverse_str [b'; a']).
  intros.
  unfold inverse_str.
  simpl.
  apply opposites_swap_to_opposites in H.
  apply opposites_swap_to_opposites2 in H.
  unfold opposite.
  unfold OperationsGroupImpl.opposite.
  symmetry.
  apply opLists_equivalent_swap with (A:=[]) (B:=[]); auto.
  Qed.

Lemma rebaseOpList_left_distributivity: ∀ A B C, rebaseOpListWithOpList (A++B) C ~ (squashOpList (rebaseOpListWithOpList A C) (rebaseOpListWithOpList B (squashOpList (inverse_str A) (squashOpList C (rebaseOpListWithOpList A C))))).
  intros.
  revert C.
  induction A.
  - intros.
    unfold inverse_str.
    repeat rewrite squashOpList_app_equiv.
    simpl ([] ++ B).
    simpl ((rebaseOpListWithOpList [] C)).
    repeat rewrite squashOpList_app_equiv.
    rewrite rebaseOperationWithChangeSet_param2_equiv with (B:=(squashOpList [] (squashOpList C []))) (B':=C).
    2: { repeat rewrite squashOpList_app_equiv. simpl. rewrite app_nil_r. reflexivity. }
    simpl.
    reflexivity.
  - intros.
    rewrite <-app_comm_cons.
    unfold rebaseOpListWithOpList at 1.
    fold rebaseOpListWithOpList.
    destruct (A++B) eqn:H_A_B.
    + apply app_eq_nil in H_A_B.
      destruct H_A_B as (H_A & H_B).
      rewrite H_A.
      rewrite H_B.
      unfold rebaseOpListWithOpList at 2.
      rewrite squashOpList_app_equiv.
      simpl.
      now rewrite <-app_nil_end.
    + set (X':=(squashOpList (inverse_str [a]) (squashOpList C (rebaseOperationWithOpList a C)))).
      specialize IHA with (C:=X') as IHA_X'.
      rewrite IHA_X'.
      unfold rebaseOpListWithOpList at 4.
      fold rebaseOpListWithOpList.
      unfold rebaseOpListWithOpList at 6.
      fold rebaseOpListWithOpList.
      fold X'.
      destruct A.
      * simpl (rebaseOpListWithOpList [] X').
        repeat rewrite squashOpList_app_equiv.
        unfold X'.
        repeat rewrite squashOpList_app_equiv.
        rewrite rebaseOperationWithChangeSet_param2_equiv with 
          (B:=(squashOpList (inverse_str [])
     (squashOpList
        (squashOpList (inverse_str [a])
           (squashOpList C (rebaseOperationWithOpList a C))) [])))
          (B':=(squashOpList (inverse_str [a])
        (squashOpList C (rebaseOperationWithOpList a C)))).
        rewrite squashOpList_app_equiv with (A:=(rebaseOperationWithOpList a C)).
        rewrite app_assoc.
        rewrite app_nil_r.
        reflexivity.
        repeat rewrite squashOpList_app_equiv.
        unfold inverse_str.
        repeat rewrite app_assoc.
        repeat rewrite app_nil_r.
        reflexivity.
      * unfold inverse_str.
        fold inverse_str.
        rewrite rebaseOperationWithChangeSet_param2_equiv with (B:=(squashOpList ((inverse_str A ++ [opposite o0]) ++ [opposite a])
        (squashOpList C
           (squashOpList (rebaseOperationWithOpList a C)
              (rebaseOpListWithOpList (o0 :: A) X'))))) (B':=(squashOpList (inverse_str A ++ [opposite o0])
           (squashOpList X' (rebaseOpListWithOpList (o0 :: A) X')))).
        set (Y':=(squashOpList X' (rebaseOpListWithOpList (o0 :: A) X'))).
        set (Y'':=(rebaseOpListWithOpList B (squashOpList (inverse_str A ++ [opposite o0]) Y'))).
        repeat rewrite squashOpList_app_equiv.
        repeat rewrite app_assoc.
        unfold X'.
        reflexivity.
        rewrite squashOpList_app_equiv.
        rewrite squashOpList_app_equiv with (A:=(inverse_str A ++ [opposite o0])).
        unfold X' at 2.
        unfold inverse_str at 3.
        repeat rewrite squashOpList_app_equiv.
        simpl ([] ++ [opposite a]).
        repeat rewrite app_assoc.
        reflexivity.
  Qed.

  Lemma rebaseOpListWithOpList_equiv: ∀A A' B B', A ~ A' → B ~ B' →
                                                  rebaseOpListWithOpList A B ~ 
                                                  rebaseOpListWithOpList A' B'.
  intros.
  rewrite rebaseOperationWithChangeSet_param2_equiv with (B:=B') (B':=B). 2: symmetry; assumption.
  
  induction H; auto with opListsEquivalence.
  - do 2 rewrite rebaseOpList_left_distributivity.
    apply simplifyOperationRemoveIffOpposites in H.
    rewrite H.
    set (Z:=(squashOpList (inverse_str A) (squashOpList B (rebaseOpListWithOpList A B)))).
    replace ((b⁻¹)%O :: b :: B0) with ([opposite b; b]++B0). 2: { now simpl. }
    rewrite rebaseOpList_left_distributivity.
    repeat rewrite squashOpList_app_equiv.
    assert ((inverse_str [opposite b; b]) ~ []). {
      unfold inverse_str.
      simpl.
      rewrite opposite_involution.
      apply opposites_empty_equiv.
    }
    rewrite rebase_opposite_eqiv with (a:=b) (C:=Z) at 1.

    rewrite rebaseOperationWithChangeSet_param2_equiv with (A:=B0) 
      (B:=(squashOpList (inverse_str [opposite b; b]) (squashOpList Z (rebaseOpListWithOpList [opposite b; b] Z))))
      (B':=Z).
    now simpl.
    rewrite H1.
    rewrite rebase_opposite_eqiv with (a:=b) (C:=Z) at 1.
    repeat rewrite squashOpList_app_equiv.
    simpl.
    now rewrite app_nil_r.
  - repeat rewrite rebaseOpList_left_distributivity.
    set (Z':=  (squashOpList (inverse_str A) (squashOpList B (rebaseOpListWithOpList A B)))).
    rewrite rebase_swap_eqiv with (1:=H) at 1.
    rewrite rebaseOperationWithChangeSet_param2_equiv with 
      (B:=(squashOpList (inverse_str [a; b]) (squashOpList Z' (rebaseOpListWithOpList [a; b] Z')))) 
      (B':=(squashOpList (inverse_str [b'; a']) (squashOpList Z' (rebaseOpListWithOpList [b'; a'] Z')))).
    reflexivity.
    rewrite rebase_invert_eqiv with (1:=H).
    rewrite rebase_swap_eqiv with (1:=H).
    reflexivity.
  - transitivity (rebaseOpListWithOpList B0 B); assumption.
  Qed.


End SimplificationLemmas.
        
      (*a b => b' a'
      b c => c'' b''
      a' c => c a'

      b' a => b' a

      c a'' => c a''
      b c => c'' b''

      Axiom simplifyOperations_swap_preserved_under_swap_to_right: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification c a c' a.
      Axiom simplifyOperations_swap_preserved_under_swap_to_left: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification a c a c'.

      simplifyOperations b' a' = Keep

      b' a' c => b' c a_r => c b_r a_r

      simplifyOperations b b = Swap x' b'
      simplifyOperations a' c = Swap c b''' => a:=b' c:=c
      simplifyOperations b' c = Swap c a_r2
      specialize simplifyOperations_double_swap with (1:=H) (2:=H_simplifyOperations) as H1.
      destruct H1 as [a_r H1].

      assert (∃a_r2, simplifyOperations b' c = Swap c a_r2). { give_up. }
      destruct H2 as [a_r2 H2].

      assert (∃a_r, simplifyOperations a' c = Swap c a_r). { 
        specialize simplifyOperations_double_swap with (1:=H) (2:=H_simplifyOperations) as H3.
        destruct H3 as [a_r H3].
        exists a_r. 
        assumption.
      }
        apply simplifyOperations_swap_preserved_under_swap_to_right with (a:=a)  in H as H_sameSimpl2; auto.

        a > b
        b > c
        a > c

        a c = Swap

        give_up.
      }

  Axiom simplifyOperations_transitive: ∀a b c, sameSimplification a b b c → sameSimplification a b a c.
  Axiom simplifyOperations_swap_preserved_under_swap_to_right: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification c a c' a.
  Axiom simplifyOperations_swap_preserved_under_swap_to_left: ∀a b c b' c', simplifyOperations b c = Swap c' b' → sameSimplification a c a c'.
        
      }
      (*simplifyOperations a b = Swap b' a' 
        simplifyOperations a c = Swap c' a'' 
        simplifyOperations a' c = Swap c' a'' 


      simplifyOperations a b = Swap b' a'      = a > b
      simplifyOperations b c = Swap c'' b''    = b > c
      
      simplifyOperations a c'' = Swap c''' a'''      = a > c

      simplifyOperations a' c = Swap c_r a_r         = a > c

      simplifyOperations b' c_r = Swap c''' a_r2     = b > c
      simplifyOperations a''' b'' = Swap a_r2 a_r    = a > b*)


      (*destruct H0 as [a''' [c''' H0]].*)
      assert (∃a_r c_r, simplifyOperations a' c = Swap c_r a_r). { give_up. }
      destruct H1 as [a_r [c_r H1]].
      assert (∃a_r2, simplifyOperations b' c_r = Swap c''' a_r2). { give_up. }
      destruct H2 as [a_r2 H2].*)

      (*a b c => a c b''  => c a''' b'' => c b_r2 a_r
      b' a' c => b' c a_r => c b_r2 a_r*)