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
From Coq Require Import List. Import ListNotations.

Require Import BinPos BinInt BinNat Pnat Nnat.

Scheme Equality for list.

Module Type SingleOperationAlgebraSig.
Parameter (Operation : Type).
Axiom (Operation_eq_dec: ∀ a b:Operation,{a=b} + {a<>b}).

Parameter (invert: Operation->Operation).
Axiom (opInvertInvolution: ∀ a:Operation, invert (invert a) = a).


Parameter applyOperation: string->Operation->string.

Parameter rebaseOperation: (option Operation) -> (option Operation) -> (option Operation).
Declare Scope OptionOperation.
Delimit Scope OptionOperation with OO.

Infix "↷" := rebaseOperation (at level 57, left associativity) : OptionOperation.
Definition invertOperationOption (op: option Operation) := 
match op with
  | Some o => (Some (invert o))
  | None => None
end.

Axiom rebaseOperatrionLeftDistibutivity: ∀A B, ((invertOperationOption ((Some A) ↷  (Some B)))  = (invertOperationOption (Some A)) ↷ (invertOperationOption (Some A)) ↷ (Some B) ↷ ((Some A) ↷ (Some B)) ∨
                                         (invertOperationOption ((Some A) ↷ (Some B))) = None)%OO.

Axiom rebaseOperatrionRightDistibutivity: ∀A B, ((Some A) ↷ (Some B) ↷ (invertOperationOption (Some B)) = (Some A) ∨
                                                 (Some A) ↷ (Some B) ↷ (invertOperationOption (Some B)) = None)%OO.

Axiom rebaseNone: ∀ a, (None ↷ Some a)%OO = None.
Axiom noErrorsDuringRebase: ∀A B, (Some A ↷ Some B)%OO = None → False.

End SingleOperationAlgebraSig.

Module SingleOperationAlgebra (ops: SingleOperationAlgebraSig).

Declare Scope Operation.
Declare Scope OptionOperation.
Declare Scope ChangeSet.
Delimit Scope Operation with O.
Delimit Scope OptionOperation with OO.
Delimit Scope ChangeSet with CS.

Notation "a ⁻¹" := (ops.invert a) (at level 55, no associativity, format "a '⁻¹'") : Operation.

Module Import FreeGroupsSig.
End FreeGroupsSig.
Module OperationsGroupImpl <: FreeGroupsSig.
  Definition alphabet := ops.Operation.
  Definition opposite := ops.invert.
  Definition opposite_involution := ops.opInvertInvolution. 
  Definition alphabet_eq_dec := ops.Operation_eq_dec. 
End OperationsGroupImpl.


(*Module OperationGroup := FreeGroups OperationsGroupImpl.*)
Module GroupLemmas := AdditionalGroupLemmas OperationsGroupImpl.
Import GroupLemmas.
Check OperationGroup.reduced_string_product.

Notation "a ⁻¹" := (ops.invertOperationOption a) (at level 55, no associativity, format "a '⁻¹'") : OptionOperation.


(*Scheme Equality for OperationType.*)

Definition Op_eqb  (a : ops.Operation) (b: ops.Operation) := 
  if (ops.Operation_eq_dec a b) then true else false.

Lemma Op_eqb_refl: ∀ op, Op_eqb op op = true.
  intros.
  unfold Op_eqb.
  destruct ops.Operation_eq_dec.
  - auto.
  - contradiction. 
Qed.

Lemma Op_eqb_eq: ∀ x y : ops.Operation, (((Op_eqb x y) = true) → x = y).
intros.
unfold Op_eqb in H.
destruct (ops.Operation_eq_dec x y) eqn:H_eq; auto.
discriminate.
Qed.

Create HintDb HelperLemmas.
Hint Resolve Op_eqb_refl : HelperLemmas.


(* ChangeSets *)
Definition opList := list ops.Operation.

Definition non_reduced := OperationGroup.non_reduced.

Definition reduced := OperationGroup.reduced.

Record reducedOpList : Type := mkReducedOpList {
  operations: opList; 
  operations_reduced: reduced(operations)
}.

Definition singleOpListIsReduced := OperationGroup.single_letter_reduced.

Definition emptyOpListIsReduced := OperationGroup.empty_str_reduced.

Hint Unfold OperationGroup.alphabet.
Hint Unfold OperationsGroupImpl.alphabet.


Inductive ChangeSet :=
  | CSet (ops: reducedOpList)
  | InvalidCSet.

Definition emptyChangeSet := (CSet {| 
         operations := [];
         operations_reduced := emptyOpListIsReduced
     |}).

Notation "⊘" := emptyChangeSet.
Notation "⦻" := InvalidCSet.

Definition opToCs (op:ops.Operation) := 
  (CSet {| 
         operations := [op];
         operations_reduced := singleOpListIsReduced op
      |}).

Definition applyChangeSet (str:string) (cs: ChangeSet) := match cs with 
  | CSet ops =>
    (fold_left ops.applyOperation ops.(operations) str)
  | InvalidCSet =>
    str
end.

(* Squash Operation *)
Definition squashOpList := OperationGroup.reduced_string_product.

Lemma squashIsReduced: ∀(A B: opList), reduced(A) -> reduced(B) → reduced(squashOpList A B).
intros.
unfold squashOpList.
unfold OperationGroup.reduced_string_product.
apply OperationGroup.reduction_is_reduced.
Qed.

Program Definition squash (a b : ChangeSet) := match a, b with 
    | CSet opsA, CSet opsB => 
      (CSet ({| 
         operations := (squashOpList opsA.(operations) opsB.(operations));
         operations_reduced := (squashIsReduced opsA.(operations) opsB.(operations) opsA.(operations_reduced) opsB.(operations_reduced) )
      |}))
    | _, _ => InvalidCSet
end.


Definition changeset_eqb (A B : ChangeSet) : bool :=
  match A,B with
    | CSet opsA, CSet opsB => list_beq ops.Operation Op_eqb opsA.(operations) opsB.(operations)
    | CSet _, InvalidCSet => false
    | InvalidCSet, CSet _ => false
    | InvalidCSet, InvalidCSet => true
end.

Lemma list_neq_beq_refl: ∀(l: list nat), (list_beq nat Nat.eqb l l) = true.
intros.
unfold list_beq.
induction l; auto.
rewrite IHl.
now rewrite Nat.eqb_refl.
Qed.
Hint Resolve list_neq_beq_refl : HelperLemmas.

Lemma list_op_beq_refl: ∀(l: opList), (list_beq ops.Operation Op_eqb l l) = true.
intros.
unfold list_beq.
induction l; auto.
rewrite IHl.
now rewrite Op_eqb_refl.
Qed.
Hint Resolve list_op_beq_refl : HelperLemmas.

Lemma changeset_eqb_refl: ∀A, changeset_eqb A A = true.
intros.
unfold changeset_eqb.
destruct A; auto.
auto with HelperLemmas.
Qed.
Hint Resolve changeset_eqb_refl : HelperLemmas.

Lemma ProofIrrelevanceForChangeSets: ∀ A B : ChangeSet, is_true (changeset_eqb A B) <-> A = B.
intros.
intuition.
- unfold changeset_eqb in H.
  destruct A.
  + destruct B.
    f_equal.
    apply internal_list_dec_bl in H; auto.
    * destruct ops.
      destruct ops0.
      simpl in H.
      generalize operations_reduced1.
      rewrite <-H.
      intros.

      replace operations_reduced2 with operations_reduced0; only 2: apply proof_irrelevance.
      auto.
    * apply Op_eqb_eq.
    * cbv in H.
      discriminate.
  + destruct B.
    * cbv in H.
      discriminate.
    * auto.
- rewrite H.
  apply changeset_eqb_refl.
Qed.
Hint Resolve ProofIrrelevanceForChangeSets : HelperLemmas.

Infix "○" := squash (at level 60).

Lemma squashWithInvalid1: ∀X, (X ○ ⦻) = ⦻.
  intros.
  unfold squash.
  destruct X; auto.
Qed.

Lemma squashWithInvalid2: ∀X, (⦻ ○ X) = ⦻.
  intros.
  now unfold squash.
Qed.

Lemma squashEmptyLeft:  ∀X, ⊘ ○ X  = X.
intros.
unfold squash.
destruct X; auto.
unfold squashOpList.
f_equal.
destruct ops.
induction operations0.
all: apply ProofIrrelevanceForChangeSets; auto.
simpl.
unfold OperationGroup.reduced_string_product.
rewrite app_nil_l.
rewrite OperationGroup.reduction_fixes_reduced; auto.
now rewrite list_op_beq_refl.
Qed.

Lemma squashEmptyRight: ∀X, X ○ ⊘  = X.
intros.
unfold squash.
destruct X; auto.
unfold squashOpList.
f_equal.
destruct ops.
induction operations0.
all: apply ProofIrrelevanceForChangeSets; auto.
simpl.
unfold OperationGroup.reduced_string_product.
rewrite app_nil_r.
rewrite OperationGroup.reduction_fixes_reduced; auto.
now rewrite list_op_beq_refl.
Qed.

Create HintDb changeset_simplificaton.
Hint Rewrite squashWithInvalid1 : changeset_simplificaton.
Hint Rewrite squashWithInvalid2 : changeset_simplificaton.
Hint Rewrite squashEmptyLeft : changeset_simplificaton.
Hint Rewrite squashEmptyRight : changeset_simplificaton.

Lemma squashAssociative: ∀X Y Z, (X ○ Y) ○ Z = X ○ (Y ○ Z).
intros.
destruct X.
destruct Y.
destruct Z.
all: autorewrite with changeset_simplificaton; auto.

unfold squash.
apply ProofIrrelevanceForChangeSets; auto.
simpl.
unfold squashOpList.
rewrite <-OperationGroup.reduced_string_product_assoc.
now rewrite list_op_beq_refl.
Qed.

(* Invert operation *)
Definition invert (a: ChangeSet) := match a with 
    | CSet opsA => (CSet {| 
         operations := (OperationGroup.inverse_str opsA.(operations));
         operations_reduced := (invertIsReduced opsA.(operations) opsA.(operations_reduced))
      |})
    | _ => InvalidCSet
end.

Notation "a ⁻¹" := (invert a) (at level 55, no associativity, format "a '⁻¹'") : ChangeSet.

Open Scope CS.
Lemma squashInverseLeft: ∀X, X ≠ ⦻ → X ○ X⁻¹  = ⊘.
intros.
unfold squash.
destruct X; try contradiction.
simpl.
f_equal.
unfold squashOpList.
apply ProofIrrelevanceForChangeSets; auto.
simpl.

rewrite OperationGroup.inverse_str_is_right_inverse.
auto.
Qed.

Lemma changeSetInvertInvolution: ∀ X:ChangeSet, (X⁻¹)⁻¹ = X.
intros.
unfold invert.
destruct X; try contradiction.
simpl.
destruct ops.
apply ProofIrrelevanceForChangeSets; auto.
simpl.
rewrite OperationGroup.inverse_str_involution.
all: auto with HelperLemmas.
Qed.

Lemma squashInverseRight: ∀X:ChangeSet, X ≠ ⦻ → X⁻¹ ○ X  = ⊘.
intros.
rewrite <-changeSetInvertInvolution with (X:=X) at 2.
rewrite squashInverseLeft; auto.
unfold invert.
destruct X.
- discriminate.
- contradiction.
Qed.

Hint Rewrite squashInverseLeft using (easy): changeset_simplificaton.
Hint Rewrite squashInverseRight using (easy) : changeset_simplificaton.
Hint Rewrite changeSetInvertInvolution : changeset_simplificaton.

Close Scope CS.

Fixpoint removeFirst (n : nat) (l:list nat) := 
  match l with
    | [] => []
    | x :: t => if (x =? n) then
        t
      else
        x::(removeFirst n t)
  end.

(* Rebase logic for a single operation *)

Open Scope nat.

Infix "↷" := ops.rebaseOperation (at level 57, left associativity) : OptionOperation.

Definition rebaseOperationWithChangeSet (a:ops.Operation) (b : ChangeSet) := match b with
  | CSet ops => match (fold_left ops.rebaseOperation ((map (λ x:ops.Operation, Some x)) ops.(operations)) (Some a)) with
                  | Some result => (opToCs result)
                  | None => InvalidCSet
                end
  | InvalidCSet => InvalidCSet
end.

Fixpoint rebaseChangeSetOps (a : list ops.Operation) (a_reduced : reduced(a)) (b : ChangeSet) {struct a}:= 
    match a as a' return (a' = a → ChangeSet) with
      | [] => match b with 
        | CSet _ => (fun x => ⊘)
        | InvalidCSet => (fun x => InvalidCSet)
       end
      | opA::Atail => fun x => (
          match Atail with
          | nil => (rebaseOperationWithChangeSet opA b)
          | _ =>
            let ATailIsReduced := (tailIsReduced2 a Atail opA x a_reduced) in
             let csA := (opToCs opA) in 
             let csA' := (CSet {|
                operations := Atail;
                operations_reduced := ATailIsReduced
              |}) in 
             let R1 := (rebaseOperationWithChangeSet opA b) in 
             let R2 := (rebaseChangeSetOps Atail ATailIsReduced (csA⁻¹ ○ b ○ R1)%CS ) in 
             (R1 ○ R2)%CS
          end)
  end eq_refl.

Definition rebaseChangeSet (a b : ChangeSet) := match a with 
    | CSet opsA => (rebaseChangeSetOps opsA.(operations) opsA.(operations_reduced) b) 
    | _ => InvalidCSet
end.

Infix "↷" := rebaseChangeSet (at level 57, left associativity) : ChangeSet.

Open Scope CS.
Lemma proofIrrelevanceEmpty: ∀P, CSet {|operations:=[]; operations_reduced:=P|} = ⊘.
intros.
apply ProofIrrelevanceForChangeSets.
auto.
Qed.

Lemma rebaseWithInvalid1: ∀X, (X ↷ ⦻) = ⦻.
  intros.
  unfold rebaseChangeSet.
  destruct X; auto.
  unfold rebaseChangeSetOps.
  destruct ops.
  induction operations0.
  - auto.
  - destruct operations0.
    + unfold rebaseOperationWithChangeSet; auto.
    + unfold rebaseOperationWithChangeSet. unfold squash. auto.
Qed.

Lemma rebaseWithInvalid2: ∀X, (⦻ ↷ X) = ⦻.
  intros.
  now unfold rebaseChangeSet.
Qed.

Lemma rebaseEmptyLeft: ∀X, X ≠ ⦻ → ⊘ ↷ X  = ⊘.
intros.
cbn.
destruct X; auto.
contradiction.
Qed.

Lemma rebaseOperationEmpty: ∀op:ops.Operation, (rebaseOperationWithChangeSet op ⊘) = (opToCs op).
intros.
unfold rebaseOperationWithChangeSet.  
unfold fold_left. 
now simpl.
Qed.

Lemma emptyInverse: ⊘⁻¹ = ⊘.
intros.
cbv.
now apply ProofIrrelevanceForChangeSets.
Qed.

Create HintDb changeset_simplificaton.
Hint Rewrite rebaseWithInvalid1 : changeset_simplificaton.
Hint Rewrite rebaseWithInvalid2 : changeset_simplificaton.
Hint Rewrite rebaseOperationEmpty : changeset_simplificaton.
Hint Rewrite rebaseEmptyLeft using (easy) : changeset_simplificaton.
Hint Rewrite rebaseOperationEmpty : changeset_simplificaton.
Hint Rewrite emptyInverse : changeset_simplificaton.
Hint Rewrite proofIrrelevanceEmpty : changeset_simplificaton.

Ltac autoChangeSetSimplification := autorewrite with changeset_simplificaton; auto with HelperLemmas bool; try discriminate.

Lemma changeSetInvertReverseSquash: ∀ X Y:ChangeSet, (X ○ Y)⁻¹ = (Y⁻¹ ○ X⁻¹).
intros.
unfold invert.
unfold squash.
destruct X; autoChangeSetSimplification.
all: destruct Y; autoChangeSetSimplification.
- unfold operations.
  unfold operations_reduced.
  apply ProofIrrelevanceForChangeSets.
  simpl.
  unfold squashOpList.
  destruct ops.
  destruct ops0.
  enough ((OperationGroup.inverse_str
        (OperationGroup.reduced_string_product operations0 operations1)) =
     (OperationGroup.reduced_string_product (OperationGroup.inverse_str operations1)
        (OperationGroup.inverse_str operations0))).
  + rewrite H.
    auto with HelperLemmas.
  + apply operationGroupIsRightInjective with (A:=OperationGroup.reduced_string_product operations0 operations1).
    {
      apply invertIsReduced.
      unfold OperationGroup.reduced_string_product.
      apply OperationGroup.reduction_is_reduced.
    }
    {
      unfold OperationGroup.reduced_string_product.
      apply OperationGroup.reduction_is_reduced.
    }
    rewrite OperationGroup.inverse_str_is_right_inverse.
    rewrite OperationGroup.reduced_string_product_assoc.
    rewrite <-OperationGroup.reduced_string_product_assoc with (S1:=operations1).
    rewrite OperationGroup.inverse_str_is_right_inverse.
    rewrite OperationGroup.empty_str_is_left_id.
    2: { now apply invertIsReduced. }
    now rewrite OperationGroup.inverse_str_is_right_inverse.
Qed.

Lemma rebaseEmptyRight: ∀X, X ≠ ⦻ → X ↷ ⊘  = X.
intros.
unfold rebaseChangeSet.
destruct X; auto.
unfold rebaseChangeSetOps.
destruct ops.
induction operations0; auto.
- apply ProofIrrelevanceForChangeSets.
  simpl.
  auto.
- apply ProofIrrelevanceForChangeSets.
  auto.
  unfold operations.
  unfold operations_reduced.
  autorewrite with changeset_simplificaton in *.
  unfold operations in IHoperations0.
  unfold operations_reduced in IHoperations0.
  fold rebaseChangeSetOps in *.
  rewrite IHoperations0.
  destruct operations0.
  + unfold opToCs.
    unfold changeset_eqb.
    auto with HelperLemmas.
  + unfold opToCs.
    unfold squash.
    unfold changeset_eqb.
    unfold operations.
    specialize reducedImpliesNoOpposites with (a:=a) (b:=o) (t:=operations0) as H_notOpposites.
    destruct H_notOpposites as [H_AneqOppO H_notOpposites]; auto.
    assert( (squashOpList [a] (o :: operations0)) = (a :: o :: operations0)). {
      cbn.
      unfold OperationGroup.letter_action.
      destruct operations0.
      - simpl. 
        now rewrite H_notOpposites.
      - specialize reducedImpliesNoOpposites with (a:=o) (b:=o0) (t:=operations0) as H_notOpposites2.
        destruct H_notOpposites2 as [H_OneqOppO0 H_notOpposites2]. {
          now apply tailIsReduced with (op:=a).
        }

        rewrite group_str_app_reduced_nop. 2: {
          apply tailIsReduced with (op:=o).
          now apply tailIsReduced with (op:=a).
        }
        rewrite H_notOpposites2.
        now rewrite H_notOpposites.
    }
    rewrite H0.
    auto with HelperLemmas.
  + intuition.
    discriminate H0.
Qed.

Hint Rewrite rebaseEmptyRight using (easy) : changeset_simplificaton.

Lemma fold_left_rebaseOperation_squashOpList: ∀ (a:ops.Operation) (ops0 ops1: list ops.Operation),
  reduced(ops0++ops1) →
  fold_left ops.rebaseOperation (map (λ x : ops.Operation, (Some x)) (squashOpList ops0 ops1)) (Some a) = 
  fold_left ops.rebaseOperation ((map (λ x : ops.Operation, (Some x)) ops0) ++ (map (λ x : ops.Operation, (Some x)) ops1)) (Some a).
intros.
unfold squashOpList.
unfold OperationGroup.reduced_string_product.
rewrite OperationGroup.reduction_fixes_reduced; auto.
now rewrite map_app.
Qed.

Lemma invalid_squash_implies_invalid_input: ∀X Y, (X ○ Y) = ⦻ → X = ⦻ ∨ Y = ⦻.
intros.
unfold squash in H.
destruct X.
all: destruct Y; auto.
discriminate.
Qed.

Lemma fold_left_rebaseOperation_With_None: ∀ (ops: list ops.Operation), fold_left ops.rebaseOperation (map (λ x : ops.Operation, (Some x)) ops) None = None.
intros.
induction ops.
- now simpl.
- rewrite map_cons.
  unfold fold_left in *.
  replace (None ↷ (Some a))%OO with (None : (option ops.Operation)).
  2: (symmetry; apply ops.rebaseNone).
  now rewrite IHops.
Qed.

Definition tailFromCS (X: ChangeSet) := match X with
| CSet ops => match ops.(operations) with
    | [] => fun x => ⊘
    | opA::Atail => fun x => (
          let ATailIsReduced := (tailIsReduced2 ops.(operations) Atail opA x ops.(operations_reduced)) in
          (CSet {|
              operations := Atail;
              operations_reduced := ATailIsReduced
          |})
      )
    end eq_refl
| ⦻ => ⦻
end.

Hint Rewrite revEmpty : changeset_simplificaton.

Lemma decomposeCSetLeft: ∀(X:ChangeSet) redOps op l, X = (CSet redOps) → (operations(redOps) = op::l) → X = (opToCs op) ○ (tailFromCS X).
intros.
unfold squash.
apply ProofIrrelevanceForChangeSets.
destruct X. 2: {
  autorewrite with changeset_simplificaton; auto.
}
destruct ops.
simpl.
unfold operations.
assert ( (operations redOps) = operations0). {
  injection H as H_inj.
  rewrite <-H_inj.
  now cbv.
}
destruct operations0 eqn:H_operations0.
- rewrite H0 in H1.
  discriminate H1.
- unfold squashOpList.
  unfold OperationGroup.reduced_string_product.
  assert(op = o). { rewrite H0 in H1. now injection H1 as H2. }
  rewrite H2.
  rewrite OperationGroup.reduction_fixes_reduced. 2: {
    now rewrite <-cons_to_app.
  }
  rewrite <-cons_to_app.
  auto with HelperLemmas.
Qed.

Definition removeLastFromCS (X: ChangeSet) := match X with
| CSet ops => match rev(ops.(operations)) with
    | [] => fun x => ⊘
    | opA::Atail => fun x => (
          let RemoveTailIsReduced := (tailIsReduced2 (rev ops.(operations)) Atail opA x (reverseIsReduced ops.(operations) ops.(operations_reduced))) in
          let RevRemoveTailIsReduced := (reverseIsReduced Atail RemoveTailIsReduced) in
          (CSet {|
              operations := (rev Atail);
              operations_reduced := RevRemoveTailIsReduced
          |})
      )
    end eq_refl
| ⦻ => ⦻
end.

Lemma decomposeCSetRight: ∀(X:ChangeSet) redOps op l, X = (CSet redOps) → (operations(redOps) = (l ++ [op])) → X = (removeLastFromCS X) ○ (opToCs op).
intros.
unfold squash.
apply ProofIrrelevanceForChangeSets.
destruct X eqn:H_X. 2: {
  autorewrite with changeset_simplificaton; auto.
}
destruct ops.
assert ( (operations redOps) = operations0). {
  injection H as H_inj.
  rewrite <-H_inj.
  now cbv.
}

destruct (operations0) eqn:H_operations0.
- unfold operations.
  rewrite H0 in H1.
  apply app_eq_nil in H1.
  destruct H1.
  discriminate.
- assert (∃ P, (removeLastFromCS X) = CSet {|operations := l; operations_reduced:=P|}). {
    unfold removeLastFromCS.
    rewrite H_X.
    unfold operations.
    eexists ?[P].

    autounfold.
    set (revO:=rev (o :: o0)).
    set (sub_fun := fun opA' Atail' => (fun x : @eq (list ops.Operation) (@cons ops.Operation opA' Atail') revO =>
         CSet
           (mkReducedOpList (@rev ops.Operation Atail')
              (reverseIsReduced Atail'
                 (tailIsReduced2 revO Atail' opA' x
                    (reverseIsReduced (@cons ops.Operation o o0)
                       (operations_reduced
                          (mkReducedOpList (@cons ops.Operation o o0)
                             operations_reduced0)))))))).
    assert (match revO as x return (x = revO → ChangeSet) with
      | [] => λ _ : [] = revO, ⊘
      | opA :: Atail =>
          λ x : opA :: Atail = revO,
            CSet
              {|
                operations := rev Atail;
                operations_reduced :=
                  reverseIsReduced Atail
                    (tailIsReduced2 revO Atail opA x
                       (reverseIsReduced (o :: o0)
                          (operations_reduced
                             {|
                               operations := o :: o0;
                               operations_reduced := operations_reduced0
                             |})))
              |}
      end = (match revO as x return (x = revO → ChangeSet) with
      | [] => λ _ : [] = revO, ⊘
      | opA :: Atail => sub_fun opA Atail
      end)).
    unfold sub_fun.
    reflexivity.
    rewrite H2.

    refine (match revO as x return (revO=x → match revO as x return (x = revO → ChangeSet) with
        | [] => λ _ : [] = revO, ⊘
        | opA :: Atail => sub_fun opA Atail
      end eq_refl = CSet {| operations := l; operations_reduced := ?P |}) with
        | [] => _
        | a'::t' => _
      end eq_refl).
    + intros.
      unfold revO in H3.
      assert((rev []:list ops.Operation) = (rev [])) as H_rev_contradiction. reflexivity.
      rewrite <-H3 in H_rev_contradiction at 1.
      rewrite rev_involutive in H_rev_contradiction.
      rewrite revEmpty in H_rev_contradiction.
      discriminate.
    + intros. 
      assert (∃ P, match revO as x return (x = revO → ChangeSet) with
        | [] => λ _ : [] = revO, ⊘
        | opA :: Atail => sub_fun opA Atail
        end eq_refl = sub_fun a' t' P). {
        generalize sub_fun.
        rewrite H3.
        intros.
        exists eq_refl.
        reflexivity.
      }
      destruct H4.
      rewrite H4. clear H4.
      unfold sub_fun.
      apply ProofIrrelevanceForChangeSets.
      simpl.
      assert(l=(rev t')). {
        rewrite H1 in H0.
        unfold revO in H3.
        rewrite H0 in H3.
        rewrite rev_app_distr in H3.
        rewrite revSingle in H3.
        rewrite <-cons_to_app in H3.
        inversion H3.
        now rewrite rev_involutive.
     }
     rewrite H4.
     auto with HelperLemmas bool.
     Unshelve.
     rewrite H1 in H0.
     apply reverseIsReduced in operations_reduced0 as H_lReduced.
     rewrite H0 in H_lReduced.
     rewrite rev_app_distr in H_lReduced.
     rewrite revSingle in H_lReduced.
     apply tailIsReduced in H_lReduced.
     apply reverseIsReduced in H_lReduced.
     now rewrite rev_involutive in H_lReduced.
   }

  rewrite <-H_X.

   destruct H2.
   rewrite H2.
   simpl.
   unfold changeset_eqb.
   rewrite H_X.
   unfold operations.
   unfold squashOpList.
   unfold OperationGroup.reduced_string_product.
   rewrite H1 in H0.
   autounfold.
  
   rewrite <-H0.

   rewrite OperationGroup.reduction_fixes_reduced with (S:=o :: o0); auto with HelperLemmas.
Qed.

Lemma noErrorsDuringRebaseCS: ∀A B, (A ≠ ⦻) → (B ≠ ⦻) → (A ↷ B) ≠ ⦻.
intros.
unfold rebaseChangeSet.
destruct A; autoChangeSetSimplification.
destruct B; autoChangeSetSimplification.
destruct ops.
destruct ops0.
unfold operations.
unfold operations_reduced.
remember (length operations0) as lenOps0.
revert HeqlenOps0.
revert H.
revert H0.
revert operations_reduced0.
revert operations0.
revert operations_reduced1.
revert operations1.
revert lenOps0.
induction lenOps0.
- intros.
  symmetry in HeqlenOps0.
  apply length_zero_iff_nil in HeqlenOps0.
  generalize operations_reduced0.
  rewrite HeqlenOps0.
  intros.
  cbv.
  discriminate.
- intros.
  destruct operations0.
  + cbv.
    discriminate.
  + unfold rebaseChangeSetOps.
    fold rebaseChangeSetOps.
    assert (∃E, rebaseOperationWithChangeSet o (CSet {| operations := operations1; operations_reduced := operations_reduced1 |}) = CSet E) as H_rebaseOperationWithChangeSet. {
      unfold rebaseOperationWithChangeSet.
      assert( ∀ a', ∃O, fold_left ops.rebaseOperation (map (λ x : ops.Operation, Some x) (operations {| operations := operations1; operations_reduced := operations_reduced1 |})) (Some a') = Some O). {
        induction operations1.
        * intros.
          cbv.
          now exists a'.
        * intros.
          unfold map.
          unfold fold_left.
          unfold operations in *.
          destruct ((Some a' ↷ Some a)%OO) eqn:H_rebaseOp.
          -- apply tailIsReduced in operations_reduced1 as H_reduced2.
             specialize IHoperations1 with (operations_reduced1 := H_reduced2) (a':=o0).
             destruct IHoperations1; try autoChangeSetSimplification.
             unfold fold_left in H1.
             unfold map in H1.
             rewrite H1.
             now exists x.
          -- now apply ops.noErrorsDuringRebase in H_rebaseOp.
      }
      specialize H1 with (a':=o).
      destruct H1.
      rewrite H1.
      unfold opToCs.
      now exists ({| operations := [x]; operations_reduced := singleOpListIsReduced x |}).
    }
    destruct ((opToCs o⁻¹
          ○ CSet {| operations := operations1; operations_reduced := operations_reduced1 |})
         ○ rebaseOperationWithChangeSet o
             (CSet {| operations := operations1; operations_reduced := operations_reduced1 |})) eqn:H_remainder.
    * autounfold in *.
      destruct (rebaseChangeSetOps operations0
        (tailIsReduced2 (o :: operations0) operations0 o eq_refl operations_reduced0) 
        (CSet ops)) eqn: H_recursiveRebase.
      -- autounfold in *.
         rewrite H_recursiveRebase.
         destruct H_rebaseOperationWithChangeSet.
         rewrite H1.
         destruct operations0; try discriminate.
      -- destruct ops.
         specialize IHlenOps0 with (operations0:=operations0) (operations_reduced0:=(tailIsReduced2 (o :: operations0) operations0 o eq_refl operations_reduced0))
                                   (operations1:=operations2) (operations_reduced1:=operations_reduced2).
         destruct IHlenOps0; try autoChangeSetSimplification.
    * apply invalid_squash_implies_invalid_input in H_remainder.
      destruct H_remainder.
      -- apply invalid_squash_implies_invalid_input in H1.
         destruct H1.
         ++ cbv in H1; discriminate.
         ++ discriminate.
      -- destruct H_rebaseOperationWithChangeSet.
         rewrite H2 in H1.
         discriminate.
Qed.

Lemma rightDistributivitySingleOperation: ∀a b c : ops.Operation, (opToCs a) ↷ ((opToCs b) ○ (opToCs c)) = ((opToCs a) ↷ (opToCs b)) ↷ (opToCs c).
intros.
destruct (OperationGroup.alphabet_eq_dec b (OperationGroup.opposite c)) eqn:H_bInvc.
- rewrite e.
  assert ((opToCs (OperationGroup.opposite c)) = (opToCs c)⁻¹). {
    cbv.
    apply ProofIrrelevanceForChangeSets.
    simpl.
    auto with HelperLemmas bool.
  }
  rewrite H at 1. clear H.
  rewrite squashInverseRight.
  2: { unfold opToCs. discriminate. }
  autoChangeSetSimplification.
  unfold opToCs.
  unfold rebaseChangeSet.
  unfold rebaseChangeSetOps.
  unfold operations.
  unfold rebaseOperationWithChangeSet.
  unfold operations.
  unfold map.
  unfold fold_left.
  autounfold.
  destruct (((Some a) ↷ (Some ((OperationGroup.opposite c) : ops.Operation)))%OO) eqn:H_aRebaseCInv.
  + unfold opToCs.
    destruct ((Some o ↷ Some c)%OO) eqn:H_oRebasedC.
    * rewrite <-H_aRebaseCInv in H_oRebasedC.
      unfold OperationGroup.opposite in H_oRebasedC.
      unfold OperationsGroupImpl.opposite in H_oRebasedC.
      rewrite <-ops.opInvertInvolution with (a:=c) in H_oRebasedC.
      set (x := (c⁻¹)%O).
      fold x in H_oRebasedC.
      rewrite ops.opInvertInvolution with (a:=x) in H_oRebasedC.
      specialize ops.rebaseOperatrionRightDistibutivity with (A:=a) (B:=x) as H_rightDistributivityOp.
      destruct H_rightDistributivityOp.
      -- unfold ops.invertOperationOption in H.
        rewrite H in H_oRebasedC.
        now inversion H_oRebasedC.
      -- destruct ( (Some a ↷ Some x)%OO) eqn:H1.
         ++now apply ops.noErrorsDuringRebase in H.
         ++now apply ops.noErrorsDuringRebase in H1.
    * now apply ops.noErrorsDuringRebase in H_oRebasedC.
  + now apply ops.noErrorsDuringRebase in H_aRebaseCInv.
- assert (∃ P, (opToCs b ○ opToCs c) = (CSet {|operations:=[b;c]; operations_reduced:= P|})). {
    cbn.
    eexists ?[P].
    apply ProofIrrelevanceForChangeSets.
    simpl.
    rewrite H_bInvc.
    [P]: {
      apply OperationGroup.join_reduced.
      - apply OperationGroup.single_letter_reduced.
      - apply n.
    }
    auto with HelperLemmas.
  }
  destruct H. rewrite H.
  unfold opToCs.
  unfold rebaseChangeSet.
  unfold rebaseChangeSetOps.
  unfold operations.
  unfold rebaseOperationWithChangeSet.
  unfold map.
  unfold operations.
  unfold fold_left.
  destruct ((Some a ↷ Some b)%OO) eqn:H_aRebasedB.
  + destruct ((Some o ↷ Some c)%OO) eqn:H_oRebasedC.
    * unfold opToCs.
      rewrite H_oRebasedC.
      auto.
    * now apply ops.noErrorsDuringRebase in H_oRebasedC.
  + now apply ops.noErrorsDuringRebase in H_aRebasedB.
Qed.

Lemma recomposeCSetLeft: ∀ (a:ops.Operation) (B: reducedOpList) (reduced_aB : (reduced (a::(operations B)))), 
            ((opToCs a) ○ (CSet B)) = (CSet {|operations:=(a::(operations B)); operations_reduced:= reduced_aB |}).
  intros.
  cbv beta fix zeta iota delta -[OperationGroup.reduction].
  apply ProofIrrelevanceForChangeSets.
  simpl.
  rewrite OperationGroup.reduction_fixes_reduced; auto.
  auto with HelperLemmas.
Qed.

Ltac rewriteCSets H :=
          multimatch goal with |- context[CSet {|operations := ?x; operations_reduced := ?y|}] => (
            let rewrittenX := fresh "rewrittenX" in
            let H_rewrittenX := fresh "H_rewrittenX" in
            let H_rewrittenCS := fresh "rewrittenCS" in
            let H_reducedRewX := fresh "H_reducedRewX" in
            let H_reduced := fresh "H_reduced" in
            pose (rewrittenX:=x);
            assert(rewrittenX = rewrittenX) as H_rewrittenX; auto;
            unfold rewrittenX at 2 in H_rewrittenX;
            idtac "found" x;
            rewrite H in H_rewrittenX;
            match goal with
            | H1 : rewrittenX = ?rewX|- _ => (
             assert(∃ P', CSet {|operations := x; operations_reduced := y|} = CSet {|operations := rewX; operations_reduced := P'|}) as H_rewrittenCS;
              only 1: (
                assert(reduced rewX) as H_reducedRewX;
                only 1: (
                  first [ (
                      rewrite <-H;
                      exact y
                    ) |
                    (
                      rewrite H in y;
                      idtac "found exact y" y rewX;
                      exact y
                    )
                  ]
                );
                
                exists H_reducedRewX;
                apply ProofIrrelevanceForChangeSets;
                (*simpl; This might do too much...*)
                unfold changeset_eqb;
                unfold operations;
                rewrite H;
                auto with HelperLemmas bool
              );
              destruct H_rewrittenCS as [H_reduced H_rewrittenCS];
              rewrite H_rewrittenCS;
              clear H_rewrittenCS;
              clear H_rewrittenX;
              clear rewrittenX
            )
            end
          )
        end.

Lemma splitOffSingleRebaseOperation: ∀ (a b:ops.Operation) (l:list ops.Operation) (reduced_bl : (reduced (b::l))), 
            (opToCs a)
             ↷ (CSet
                  {|
                    operations := b :: l;
                    operations_reduced := reduced_bl
                  |}) = (opToCs a) ↷ (opToCs b)
             ↷ (CSet
                  {|
                    operations := l;
                    operations_reduced := (tailIsReduced b l reduced_bl)
                  |}).
  intros.
  cbv beta iota fix delta [opToCs rebaseChangeSet].
  unfold rebaseChangeSetOps at 1.
  unfold operations.
  destruct ((Some a ↷ Some b)%OO) eqn:H_a0Rebb0.
  - unfold rebaseChangeSetOps at 1.
    unfold operations.
    unfold rebaseOperationWithChangeSet.
    unfold fold_left.
    unfold map.
    unfold operations.
    rewrite H_a0Rebb0.
    unfold opToCs.
    unfold rebaseChangeSetOps.
    unfold rebaseOperationWithChangeSet.
    auto.
  - assert (rebaseOperationWithChangeSet a (CSet {| operations := b :: l; operations_reduced := reduced_bl |}) = ⦻). {
      unfold rebaseOperationWithChangeSet.
      unfold operations.
      assert (∀l, fold_left ops.rebaseOperation (map (λ x : ops.Operation, Some x) (b :: l)) (Some a) = None). {
        unfold map.
        unfold fold_left.
        rewrite H_a0Rebb0.
        induction l0; auto.
        rewrite ops.rebaseNone.
        auto.
      }
      now rewrite H.
    }
    rewrite H.
    unfold rebaseChangeSetOps at 1.
    unfold rebaseOperationWithChangeSet.
    unfold opToCs.
    unfold operations.
    unfold map.
    unfold fold_left.
    rewrite H_a0Rebb0.
    auto.
Qed.

 
Lemma rightDistributivitySingleOperationWithCS: ∀ (a b : ops.Operation) (C: ChangeSet), (opToCs a) ↷ ((opToCs b) ○ C) = ((opToCs a) ↷ (opToCs b)) ↷ C.
intros.
destruct C.
2: autoChangeSetSimplification.
destruct ops.
remember (length operations0) as lenOps0.
revert HeqlenOps0.
revert operations_reduced0.
revert operations0.
revert a.
revert b.
induction lenOps0.
- intros.
  symmetry in HeqlenOps0.
  apply length_zero_iff_nil in HeqlenOps0.
  rewriteCSets HeqlenOps0.
  autoChangeSetSimplification.
  rewrite rebaseEmptyRight.
  reflexivity.
  cbv beta iota fix delta -[ops.rebaseOperation].
  destruct ((Some a) ↷ (Some b))%OO eqn:H_rebase.
  + intuition.
    discriminate H.
  + now apply ops.noErrorsDuringRebase in H_rebase.
- intros.
  destruct operations0 eqn:H_ops0. { simpl in HeqlenOps0. lia. }

  destruct (OperationGroup.alphabet_eq_dec b (OperationGroup.opposite o)) eqn:H_bInvc.
  + rewrite decomposeCSetLeft with (X:=CSet {| operations := o :: o0; operations_reduced := operations_reduced0 |}) (redOps:={| operations := o :: o0; operations_reduced := operations_reduced0 |}) (op:=o) (l:=o0) in *; auto.
    unfold tailFromCS.
    unfold operations.
    unfold operations_reduced.
    assert(∃ aRb, (opToCs aRb) = (opToCs a) ↷ (opToCs b)) as H_aRb. {
      unfold opToCs.
      unfold rebaseChangeSet.
      unfold operations.
      unfold rebaseChangeSetOps.
      unfold rebaseOperationWithChangeSet.
      unfold operations.
      unfold fold_left.
      unfold map.
      destruct (((Some a) ↷ (Some b))%OO) eqn:H_aRebB.
      - exists o1.
        now unfold opToCs.
      - now apply ops.noErrorsDuringRebase in H_aRebB.
    }
    destruct H_aRb as [aRb H_aRb].
    rewrite <-H_aRb.
    specialize IHlenOps0 with (operations0:=o0) (a:=aRb) (b:=o) (operations_reduced0:=tailIsReduced2 (o :: o0) o0 o eq_refl operations_reduced0).
    autounfold in *.
    rewrite IHlenOps0.
    2: { simpl in HeqlenOps0. lia. }
    rewrite H_aRb.
    rewrite <-rightDistributivitySingleOperation.
    rewrite e.
    replace (opToCs (OperationGroup.opposite o)) with ((opToCs o)⁻¹).
    2: { cbn. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl. auto with HelperLemmas bool. }
    rewrite <-squashAssociative at 1.
    rewrite squashInverseRight. 2: { unfold opToCs. discriminate. }
    autoChangeSetSimplification.
  + assert (reduced (b::o::o0)) as H_reduced_boo0. {
      apply OperationGroup.join_reduced; auto.
    }
    rewrite recomposeCSetLeft with (a:=b) (B:=({| operations := o :: o0; operations_reduced := operations_reduced0 |})) (reduced_aB:=H_reduced_boo0).
    rewrite splitOffSingleRebaseOperation.
    unfold operations.
    replace (CSet {| operations := o :: o0; operations_reduced := tailIsReduced b (o :: o0) H_reduced_boo0 |}) with (CSet {| operations := o :: o0; operations_reduced := operations_reduced0 |}).
    auto.
    apply ProofIrrelevanceForChangeSets.
    simpl.
    auto with HelperLemmas bool.
Qed.

Lemma rightDistributivitySingleOperationWithTwoCS: ∀ (a : ops.Operation) (B C: ChangeSet), (opToCs a) ↷ (B ○ C) = ((opToCs a) ↷ B) ↷ C.
intros.
destruct B.
2 :{ autoChangeSetSimplification. }

destruct ops.
revert a.
induction operations0.
- intros.
  autoChangeSetSimplification.
- intros.
  rewrite decomposeCSetLeft with (X:=(CSet {| operations := a :: operations0; operations_reduced := operations_reduced0 |})) (op:=a) (l:=operations0) (redOps:=({| operations := a :: operations0; operations_reduced := operations_reduced0 |})); auto.
  unfold tailFromCS.
  unfold operations.
  unfold operations_reduced.
  set (X:=(CSet
          {|
            operations := operations0;
            operations_reduced := tailIsReduced2 (a :: operations0) operations0 a eq_refl operations_reduced0
          |})).
  rewrite squashAssociative.
  rewrite rightDistributivitySingleOperationWithCS.
  assert (∃a', (opToCs a') = (opToCs a0) ↷ (opToCs a)). {
    unfold opToCs.
    unfold rebaseChangeSet.
    unfold rebaseChangeSetOps.
    unfold operations.
    unfold rebaseOperationWithChangeSet.
    unfold map.
    unfold operations.
    unfold fold_left.
    destruct (((Some a0) ↷ (Some a))%OO) eqn:H_rebase.
    - exists o.
      now cbn.
    - now apply ops.noErrorsDuringRebase in H_rebase.
  }
  destruct H.
  rewrite <-H.
  specialize IHoperations0 with (a:=x) (operations_reduced0:=tailIsReduced2 (a :: operations0) operations0 a eq_refl operations_reduced0).
  unfold OperationGroup.alphabet at 2 in IHoperations0.
  fold X in IHoperations0.
  autounfold in *.
  rewrite IHoperations0.
  rewrite H.
  now rewrite <-rightDistributivitySingleOperationWithCS.
Qed.

Section distributivityProofsChangeSet.
  Variable A: ChangeSet.
  Variable B: ChangeSet.
  Variable C: ChangeSet.

  Lemma SquashOpListMaxLength: ∀A B, (length (squashOpList A B)) ≤ (length A) + (length B).
  intros.
  unfold squashOpList.
  unfold OperationGroup.reduced_string_product.
  specialize ReductionMaxLength with (A0 ++ B0) as H_lenA0B0.
  now rewrite app_length in H_lenA0B0.
  Qed.

  Lemma rebaseLeftDistibutivity: (A ○ B) ↷ C  = (A ↷ C) ○ (B ↷ (A⁻¹ ○ C ○ (A ↷ C))).
  intros.
  destruct A.
  destruct B.
  destruct C.
  
  all: autoChangeSetSimplification.
  destruct ops.
  destruct ops0.
  destruct ops1.

  remember ((length operations0) + (length operations1)) as len.
  assert ( (length operations0) + (length operations1) ≤ len) as H_LeLenOps. lia.
  revert H_LeLenOps.
  clear Heqlen.
  revert operations_reduced0.
  revert operations_reduced1.
  revert operations_reduced2.
  revert operations0.
  revert operations1.
  revert operations2.
  revert len.
  induction (len).
  - intros.
    assert_nat (Datatypes.length operations0 = 0) as H_ops0.
    assert_nat (Datatypes.length operations1 = 0) as H_ops1.
    apply length_zero_iff_nil in H_ops0.
    apply length_zero_iff_nil in H_ops1.
    generalize operations_reduced0.
    generalize operations_reduced1.
    rewrite H_ops0.
    rewrite H_ops1.
    intros.
    autoChangeSetSimplification.
  - intros.

    generalize operations_reduced0.
    generalize operations_reduced1.
    destruct operations0 eqn:H_operations0Split. 1: {
      intros.
      autorewrite with changeset_simplificaton; auto.
    }

    destruct operations1 eqn:H_operations1.
    + intros.
      autoChangeSetSimplification.
      set (t:=((((CSet {| operations := (o :: o0); operations_reduced := operations_reduced4 |})⁻¹)
        ○ (CSet {| operations := operations2; operations_reduced := operations_reduced2 |}))
       ○ ((CSet {| operations := (o :: o0); operations_reduced := operations_reduced4 |})
          ↷ (CSet {| operations := operations2; operations_reduced := operations_reduced2 |})))).
      destruct t eqn:H_t.
      * autoChangeSetSimplification.
      * unfold t in H_t.
        apply invalid_squash_implies_invalid_input in H_t.
        destruct H_t.
        -- apply invalid_squash_implies_invalid_input in H.
            destruct H; discriminate.
        -- rewrite H. 
           autoChangeSetSimplification.
    + destruct (n <? 2) eqn:H_nge2.
      * intros.
        simpl in H_LeLenOps.
        assert(Datatypes.length o0 = 0) as H_o0. solve_nat.
        assert(Datatypes.length o2 = 0) as H_o2. solve_nat.
        apply length_zero_iff_nil in H_o0.
        apply length_zero_iff_nil in H_o2.
        unfold squash at 1.
        unfold operations.

        repeat rewriteCSets H_o0.
        repeat rewriteCSets H_o2.

        destruct (OperationGroup.alphabet_eq_dec o (OperationGroup.opposite o1)) eqn:H_oInvO1.
        ++ assert (squashOpList [o] [o1] = []). {
             cbn.
             now rewrite H_oInvO1.
           }
           rewriteCSets H. clear H.
           autoChangeSetSimplification.
           remember (length operations2) as lenOps2.
           revert operations_reduced2.
           revert HeqlenOps2.
           revert operations2.
           replace (CSet {| operations := [o1]; operations_reduced := H_reduced2 |}) with (CSet {| operations := [o]; operations_reduced := H_reduced0 |}⁻¹).
           2: { simpl. apply ProofIrrelevanceForChangeSets. simpl. rewrite e. rewrite OperationGroup.opposite_involution. auto with HelperLemmas bool. }
           clear H_operations0Split.
           clear operations_reduced0.
           clear operations_reduced4.
           clear H_reduced.
           revert H_reduced0.
           clear H_reduced1.
           clear H_oInvO1.
           clear e.

           revert o.
           induction (lenOps2).
           -- intros.
              symmetry in HeqlenOps2.
              apply length_zero_iff_nil in HeqlenOps2.
              rewriteCSets HeqlenOps2.
              autoChangeSetSimplification.
           -- intros.
              destruct operations2 as [| a operations2]. { simpl in HeqlenOps2. lia. }
              set (O := CSet {| operations := [o]; operations_reduced := H_reduced0 |}) in *.
              rewrite decomposeCSetLeft with (X:=CSet {| operations := a :: operations2; operations_reduced := operations_reduced2 |}) (redOps:={| operations := a :: operations2; operations_reduced := operations_reduced2 |}) (op:=a) (l:=operations2) in *; auto.
              rename A into AA.
              set (A := (opToCs a)) in *.
              unfold tailFromCS.
              unfold operations.
              unfold operations_reduced.
              specialize IHn0 with (operations2:=operations2) (operations_reduced2:=tailIsReduced2 (a :: operations2) operations2 a eq_refl operations_reduced2).
              autounfold in *.
              set (A':=CSet
                 {|
                   operations := operations2;
                   operations_reduced :=
                     tailIsReduced2 (a :: operations2) operations2 a (@eq_refl (list ops.Operation)
                       (@cons ops.Operation a operations2)) operations_reduced2
                 |}) in *.

             specialize rightDistributivitySingleOperationWithCS with (a:=o) (b:=a) (C:=A') as H_splitOff1.
             replace (opToCs o) with O in H_splitOff1. 2: { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
             replace (opToCs a) with A in H_splitOff1. 2: { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
             rewrite H_splitOff1.
             rewrite squashAssociative.
             specialize rightDistributivitySingleOperationWithCS with (a:=(OperationGroup.opposite o)) (b:=(OperationGroup.opposite o)) (C:=((A ○ A') ○ O ↷ A ↷ A')) as H_splitOff2.
             replace (opToCs (OperationGroup.opposite o)) with (O⁻¹) in H_splitOff2. 2: { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
             rewrite H_splitOff2.

             rewrite squashAssociative.
             assert (∀(A:ChangeSet) (a:ops.Operation), (A = (opToCs a)) → A⁻¹ = (opToCs (OperationGroup.opposite a))) as SingleOperationCSInvert. {
               intros.
               rewrite H.
               cbv beta iota fix zeta delta -[OperationGroup.opposite].
               apply ProofIrrelevanceForChangeSets.
               simpl.
               auto with HelperLemmas bool.
             }
             assert (∀(A B:ChangeSet) (a b:ops.Operation), (A = (opToCs a)) → B = (opToCs b) → ∃oRebB, (Some oRebB) = ((Some a) ↷ (Some b))%OO ∧ (A ↷ B) = (opToCs oRebB)) as SingleOperationCSRebaseWithAssignment. {
               intros.
               rewrite H.
               rewrite H0.
               unfold O.
               unfold opToCs.
               unfold operations.
               unfold rebaseChangeSet.
               unfold operations.
               unfold rebaseChangeSetOps.
               unfold operations_reduced.
               unfold rebaseOperationWithChangeSet.
               unfold operations.
               unfold map.
               unfold fold_left.
               set (x:= (((Some a0)) ↷ (Some b))%OO).
               destruct x eqn:H_x.
               - exists o3.
                 now unfold opToCs.
               - now apply ops.noErrorsDuringRebase in H_x.
             }
             assert (∀(A B:ChangeSet) (a b:ops.Operation), (A = (opToCs a)) → B = (opToCs b) → ∃oRebB, (A ↷ B) = (opToCs oRebB)) as SingleOperationCSRebase. {
               intros.
               specialize SingleOperationCSRebaseWithAssignment with (A:=A0) (B:=B0) (a:=a0) (b:=b) as H_withAssignment.
               destruct H_withAssignment; auto.
               exists x.
               destruct H1.
               auto.
             }
             assert(∃o1Rebo1, (opToCs o1Rebo1) = O⁻¹ ↷ O⁻¹). {
                rewrite SingleOperationCSInvert with (a:=o).
                2:  { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
                intros.
                specialize SingleOperationCSRebase with (a:=(OperationGroup.opposite o)) (b:=(OperationGroup.opposite o)) 
                                                        (A:=opToCs (OperationGroup.opposite o)) (B:=opToCs (OperationGroup.opposite o)) as H.
                destruct H; auto.
                rewrite H.
                now exists x.
             }
             destruct H as [o1Rebo1 H_o1Rebo1].
             rewrite <-H_o1Rebo1. 
             
             specialize rightDistributivitySingleOperationWithCS with (a:=(o1Rebo1)) (b:=a) (C:=(A' ○ O ↷ A ↷ A')) as H_splitOff3.
             replace (opToCs a) with (A) in H_splitOff3. 2: { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
             rewrite H_splitOff3.
             rewrite H_o1Rebo1.
             replace (O⁻¹ ↷ O⁻¹ ↷ A) with ((O ↷ A)⁻¹ ↷ (O ↷ A)⁻¹).
             2: {
               specialize SingleOperationCSRebaseWithAssignment with (a:=o) (b:=a) 
                                                        (A:=O) (B:=A) as H.
               destruct H; auto.
               { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
               destruct H as [H_x H_OrebA].
               rewrite H_OrebA.
               assert ((Some (x⁻¹)%O = (Some o)⁻¹ ↷ (Some o)⁻¹ ↷ (Some a) ↷ ((Some o) ↷ (Some a)))%OO). {
                 replace (Some (x⁻¹)%O) with (((Some x)⁻¹)%OO).
                 2: { now cbn. }
                 rewrite H_x.
                 specialize ops.rebaseOperatrionLeftDistibutivity with (A:=o) (B:=a) as H_rightDistributivity.
                 destruct H_rightDistributivity.
                 - rewrite H.
                   clear H.
                   auto.
                 - rewrite <-H_x in H.
                   discriminate H.
               }
               assert (((opToCs x)⁻¹ = O⁻¹ ↷ O⁻¹ ↷ A  ↷ (O ↷ A))%CS). {
                 rewrite SingleOperationCSInvert with (a:=x); auto.
                 rewrite <-H_x in H.
                 specialize SingleOperationCSRebaseWithAssignment with (A:=opToCs (o⁻¹)%O) (B:=opToCs (o⁻¹)%O) (a:=(o⁻¹)%O) (b:=(o⁻¹)%O) as H_Rebase1.
                 destruct H_Rebase1; auto.
                 destruct H0.
                 replace ((Some o⁻¹)%OO) with ((Some (o⁻¹)%O)) in H. 2: { now cbn. }
                 rewrite <-H0 in H.

                 specialize SingleOperationCSRebaseWithAssignment with (A:=opToCs x0) (B:=opToCs a) (a:=x0) (b:=a) as H_Rebase2.
                 destruct H_Rebase2; auto.
                 destruct H2.
                 rewrite <-H2 in H.

                 specialize SingleOperationCSRebaseWithAssignment with (A:=opToCs x1) (B:=opToCs x) (a:=x1) (b:=x) as H_Rebase3.
                 destruct H_Rebase3; auto.
                 destruct H4.
                 rewrite <-H4 in H.
                 inversion H.
                 rewrite <-H3 in H5.
                 rewrite <-H1 in H5.
                 unfold OperationGroup.opposite.
                 unfold OperationsGroupImpl.opposite.
                 rewrite H7.
                 rewrite <-H5.
                 rewrite <-H_OrebA.
                 fold A.
                 replace (opToCs (o⁻¹)%O) with (O⁻¹).
                 auto.
                 { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
               }
               rewrite H0 at 1.
               rewrite <-H_OrebA.
               assert (∃x, (opToCs x) = O⁻¹ ↷ O⁻¹ ↷ A) as H_singleOpLeft. {
                 rewrite SingleOperationCSInvert with (a:=o).
                  2:  { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
                  intros.
                  specialize SingleOperationCSRebase with (a:=(OperationGroup.opposite o)) (b:=(OperationGroup.opposite o)) 
                                                        (A:=opToCs (OperationGroup.opposite o)) (B:=opToCs (OperationGroup.opposite o)) as H1.
                  destruct H1; auto.
                  rewrite H1.

                  specialize SingleOperationCSRebase with (a:=x0) (b:=a) 
                                                          (A:=opToCs x0) (B:=A) as H2.
                  destruct H2; auto.
                  rewrite H2.

                  now exists x1.
               }
               destruct H_singleOpLeft as [singleOp H_singleOpLeft].
               rewrite <-H_singleOpLeft.
               rewrite H_OrebA.
               assert ((opToCs x⁻¹) = (opToCs (x⁻¹)%O)) as H_xInv.  { unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool. }
               rewrite H_xInv.
               rewrite <-rightDistributivitySingleOperation.
               rewrite H_singleOpLeft.
               rewrite <-H_xInv.
               rewrite <-H_OrebA.
               rewrite squashInverseLeft.
               rewrite rebaseEmptyRight; auto.
               - rewrite <-H_singleOpLeft.
                 discriminate. 
               - rewrite H_OrebA.
                 discriminate.
             }
             set (y:=(O ↷ A)).


             assert(∃oRebo, (opToCs oRebo) = O ↷ A). {
                specialize SingleOperationCSRebase with (a:=o) (b:=a) 
                                                        (A:=O) (B:=A) as H.
                destruct H; auto.
                - unfold O. unfold opToCs. apply ProofIrrelevanceForChangeSets. simpl.  auto with HelperLemmas bool.
                - rewrite H.
                  now exists x.
             }
             destruct H as [oRebo H_oRebo].
             specialize IHn0 with (o:=oRebo) (H_reduced0:=OperationGroup.single_letter_reduced oRebo).
             replace (CSet {| operations := [oRebo]; operations_reduced := OperationGroup.single_letter_reduced oRebo |}) with y in IHn0.

             assert(∃Yinv, (opToCs Yinv) = y⁻¹). {
               rewrite SingleOperationCSInvert with (a:=oRebo).
                2:  { unfold y. auto with HelperLemmas bool. }
               now exists (OperationGroup.opposite oRebo).
             }
             destruct H as [Yinv H_Yinv].
             rewrite <-H_Yinv in IHn0.
             rewrite squashAssociative in IHn0.

             specialize rightDistributivitySingleOperationWithCS with (a:=Yinv) (b:=Yinv) (C:=(A' ○ y ↷ A')) as H_splitOff4.
             rewrite H_splitOff4 in IHn0.
             rewrite H_Yinv in IHn0.
             apply IHn0.
             simpl in HeqlenOps2.
             lia.

        ++ assert (squashOpList [o] [o1] = [o; o1]). {
             cbn.
             now rewrite H_oInvO1.
           }
           rewriteCSets H. clear H.
           unfold rebaseChangeSet.
           unfold rebaseChangeSetOps at 1.
           unfold operations.
           unfold rebaseChangeSetOps.
           unfold opToCs.
           assert (CSet {| operations := [o]; operations_reduced := singleOpListIsReduced o |} = CSet {| operations := [o]; operations_reduced := H_reduced0 |}). {
            apply ProofIrrelevanceForChangeSets.
            simpl.
            auto with HelperLemmas bool.
           }
           now rewrite H.

      * intros.
        (* These warnings are triggered by the tactic below. I haven't been able to find a way
           to specify the intro patterns that does not cause the warning. *)
        Local Set Warnings "-unused-intro-pattern".
        Ltac applyIH inpA inpB inpC IHn := 
          let opsA := fresh "opsA" in 
          let opsA2 := fresh "opsA" in 
          let H_opsA := fresh "H_opsA" in 
          destruct inpA as [opsA | opsA2] eqn:H_opsA;
          try autorewrite with changeset_simplificaton; auto;
          only 1: destruct opsA;

          let opsB := fresh "opsB" in 
          let opsB2 := fresh "opsB" in 
          let H_opsB := fresh "H_opsB" in 
          destruct inpB as [opsB | opsB2] eqn:H_opsB;
          try autorewrite with changeset_simplificaton; auto;
          only 1: destruct opsB;

          let opsC := fresh "opsC" in 
          let opsC2 := fresh "opsC" in 
          let H_opsC := fresh "H_opsC" in 
          destruct inpC as [opsC | opsC2] eqn:H_opsC;
          try autorewrite with changeset_simplificaton; auto;
          only 1: destruct opsC;
          try discriminate;

          try rewrite IHn;
          try lia;

          try rewrite <-H_opsA in *;
          try rewrite <-H_opsB in *;
          try rewrite <-H_opsC in *;

          let H_opsA2 := fresh "H_opsA2" in
          try unfold inpA in H_opsA;
          try unfold opToCs in H_opsA;
          try injection H_opsA as H_opsA2;

          let H_opsB2 := fresh "H_opsB2" in
          try unfold inpB in H_opsB;
          try unfold opToCs in H_opsB;
          try injection H_opsB as H_opsB2;

          let H_opsC2 := fresh "H_opsC2" in
          try unfold inpC in H_opsC;
          try unfold opToCs in H_opsC;
          try injection H_opsC as H_opsC2;
          try rewrite <-H_opsA2;
          try rewrite <-H_opsB2;
          try rewrite <-H_opsC2; 
          try solve [
            simpl;
            autounfold;
            lia
          ].
        (* Determine all cases we can solve by splitting a single element off from the left of A*)
        destruct ( (if (OperationGroup.reduced_dec (operations0 ++ operations1)) then true else false) || 
                    ((length operations1) <? (length operations0))) eqn:H_leftSplitAPossible.
          ++ assert (∃P, (((CSet {| operations := o :: o0; operations_reduced := operations_reduced4 |})
                            ○ (CSet {| operations := o1 :: o2; operations_reduced := operations_reduced3 |})) ) =
                              (CSet {| operations := o::(squashOpList o0 (o1::o2)); operations_reduced := P|})). {
                unfold squash at 1.
                unfold squashOpList.
                unfold OperationGroup.reduced_string_product.
                unfold operations.
                apply orb_prop in H_leftSplitAPossible.

                destruct H_leftSplitAPossible as [H_ops0ops1_reduced | H_AgtB].
                - destruct (OperationGroup.reduced_dec (operations0 ++ operations1)); try discriminate.
                  rewrite H_operations0Split in r.
                  rewrite H_operations1 in r.
                  rewrite <-app_comm_cons in r.
                  apply tailIsReduced in r as H_tailReduced.
                  assert (reduced (o :: OperationGroup.reduction (o0 ++ o1 :: o2))) as H_P. {
                    now rewrite OperationGroup.reduction_fixes_reduced.
                  }
                  exists H_P.
                  apply ProofIrrelevanceForChangeSets.
                  simpl.
                  repeat rewrite OperationGroup.reduction_fixes_reduced; auto with HelperLemmas.
                - assert(OperationGroup.reduction (o :: o0 ++ o1 :: o2) = (o :: OperationGroup.reduction (o0 ++ o1 :: o2))). {
                    specialize splitOffLeftFromReduction with (a:=o) (t:=o0) (A:=o::o0) (B:=o1::o2) as H_splitOff.
                    rewrite H_operations0Split in H_AgtB.
                    rewrite H_operations1 in H_AgtB.
                    destruct H_splitOff; auto.
                    + rewrite_nat.
                      intuition.
                    + destruct H.
                      autounfold in *.
                      solve_nat.
                  }
                  autounfold in *.
                  assert (reduced (o :: OperationGroup.reduction (o0 ++ o1 :: o2))) as H_P. {
                    rewrite <-H.
                    apply OperationGroup.reduction_is_reduced.
                  }
                  exists H_P.
                  apply ProofIrrelevanceForChangeSets.
                  simpl.
                  rewrite H; auto with HelperLemmas.
              }
              destruct H.
              rewrite H.
              clear H.

              clear A B C.
              set (A := (CSet {| operations := (o :: o0); operations_reduced := operations_reduced4 |})).
              set (B := (CSet {| operations := (o1 :: o2); operations_reduced := operations_reduced3 |})).
              set (C := (CSet {| operations := operations2; operations_reduced := operations_reduced2 |})).
              set (a := (opToCs o)).
              assert (∃P, (((CSet {| operations := o :: (squashOpList o0 (o1 :: o2)); operations_reduced := x |}) ↷ C) =
                           ((a ↷ C) ○ ((CSet {| operations := (squashOpList o0 (o1 :: o2)); operations_reduced := P |}) ↷ (a⁻¹ ○ C ○ (a ↷ C)))))). {
                unfold rebaseChangeSet at 1.
                unfold rebaseChangeSetOps.
                unfold operations.
                destruct o0. {
                  (* o0 empty *)
                  assert (reduced (squashOpList [] (o1 :: o2))) as H_o1o2reduced. {
                    cbv beta fix zeta iota delta -[OperationGroup.reduction reduced].
                    apply OperationGroup.reduction_is_reduced.
                  }
                  exists H_o1o2reduced.
                  assert (squashOpList ([]:list ops.Operation) (o1 :: o2) = (o1::o2)) as H_squashOpList. {
                    cbv beta fix zeta iota delta -[OperationGroup.reduction reduced].
                    now rewrite OperationGroup.reduction_fixes_reduced.
                  }
                  fold rebaseChangeSetOps.
                  set (my_fun := rebaseChangeSetOps (squashOpList (@nil ops.Operation) (@cons ops.Operation o1 o2))
                     (tailIsReduced2
                        (@cons ops.Operation o (squashOpList (@nil ops.Operation) (@cons ops.Operation o1 o2)))
                        (squashOpList (@nil ops.Operation) (@cons ops.Operation o1 o2)) o
                        (@eq_refl (list ops.Operation)
                           (@cons ops.Operation o (squashOpList (@nil ops.Operation) (@cons ops.Operation o1 o2))))
                        (operations_reduced
                           (mkReducedOpList
                              (@cons ops.Operation o (squashOpList (@nil ops.Operation) (@cons ops.Operation o1 o2)))
                              x)))
                     (squash (squash (invert (opToCs o)) C) (rebaseOperationWithChangeSet o C))).
                  rewrite H_squashOpList at 1.
                  replace (CSet {| operations := squashOpList ([]:list ops.Operation) (o1 :: o2); operations_reduced := H_o1o2reduced |}) with B. 2: {
                    unfold B.
                    unfold OperationGroup.alphabet.
                    unfold OperationsGroupImpl.alphabet.
                    apply ProofIrrelevanceForChangeSets.
                    simpl.
                    rewrite H_squashOpList.
                    auto with bool HelperLemmas.
                  }
                  assert (my_fun = (B ↷ (((a⁻¹) ○ C) ○ (a ↷ C)))). {
                    unfold my_fun.
                    unfold operations_reduced.
                    assert( (rebaseChangeSetOps (squashOpList ([]:list ops.Operation) (o1 :: o2))
                       (tailIsReduced2 (o :: (squashOpList ([]:list ops.Operation) (o1 :: o2))) (squashOpList ([]:list ops.Operation) (o1 :: o2)) o eq_refl x))
                       ((((opToCs o)⁻¹) ○ C) ○ (rebaseOperationWithChangeSet o C)) = (CSet {|
                         operations := squashOpList ([]:list ops.Operation) (o1 :: o2);
                         operations_reduced := (tailIsReduced2 (o :: (squashOpList [] (o1 :: o2))) (squashOpList ([]:list ops.Operation) (o1 :: o2)) o eq_refl x)
                        |}) ↷ ((((opToCs o)⁻¹) ○ C) ○ (rebaseOperationWithChangeSet o C))). {
                      unfold rebaseChangeSet.
                      unfold operations.
                      now unfold operations_reduced.
                    }
                    autounfold in *.
                    rewrite H. clear H.
                    assert ((CSet
                      {|
                        operations := squashOpList ([]:list ops.Operation) (o1 :: o2);
                        operations_reduced :=
                          tailIsReduced2 (o :: (squashOpList ([]:list OperationGroup.alphabet) (o1 :: o2))) (squashOpList ([]:list ops.Operation) (o1 :: o2)) o
                            eq_refl x
                      |}) = B). {
                        unfold B.
                        apply ProofIrrelevanceForChangeSets.
                        unfold changeset_eqb.
                        unfold operations.
                        rewrite H_squashOpList.
                        auto with HelperLemmas bool.
                    }
                    autounfold in *.
                    rewrite H. clear H.
                    unfold a.
                    unfold rebaseChangeSet at 3.
                    unfold opToCs at 3.
                    unfold operations.
                    now unfold rebaseChangeSetOps.
                  }
                  rewrite H.
                  now simpl.
                }

                remember (squashOpList (o0::o3) (o1 :: o2)) as t.
            
                unfold squashOpList in Heqt.
                unfold OperationGroup.reduced_string_product in Heqt.

                set (sub_fun:=(rebaseOperationWithChangeSet o C)
               ○ ((fix rebaseChangeSetOps
                     (a0 : list ops.Operation) (a_reduced : reduced a0) (b : ChangeSet) {struct a0} :
                       ChangeSet :=
                     match a0 as a' return ((a' = a0) → ChangeSet) with
                     | [] => match b with
                             | CSet _ => λ _ : [] = a0, ⊘
                             | ⦻ => λ _ : [] = a0, ⦻
                             end
                     | opA :: Atail =>
                         λ x0 : (opA :: Atail) = a0,
                           match Atail with
                           | [] => rebaseOperationWithChangeSet opA b
                           | _ :: _ =>
                               (rebaseOperationWithChangeSet opA b)
                               ○ (rebaseChangeSetOps Atail (tailIsReduced2 a0 Atail opA x0 a_reduced)
                                    ((((opToCs opA)⁻¹) ○ b) ○ (rebaseOperationWithChangeSet opA b)))
                           end
                     end eq_refl) t
                    (tailIsReduced2 (o :: t) t o eq_refl
                       (operations_reduced {| operations := o :: t; operations_reduced := x |}))
                    ((((opToCs o)⁻¹) ○ C) ○ (rebaseOperationWithChangeSet o C)))).

                  unfold sub_fun.
                  destruct (length t =? 0) eqn:H_lengthT. { rewrite_nat.
                    apply length_zero_iff_nil in H_lengthT.
                    rewrite Heqt in H_lengthT.
                    rewrite H_lengthT in Heqt.
                    subst t.
                    exists OperationGroup.empty_str_reduced.
                    destruct (changeset_eqb (a ↷ C) ⦻) eqn:H_aC.
                    - assert ((a ↷ C) = ⦻). { apply ProofIrrelevanceForChangeSets. rewrite H_aC. auto. }
                      rewrite H.
                      autoChangeSetSimplification.
                    - assert (((a⁻¹ ○ C) ○ a ↷ C) ≠ ⦻). {
                        intuition.
                        apply invalid_squash_implies_invalid_input in H.
                        destruct H.
                        - apply invalid_squash_implies_invalid_input in H.
                          destruct H; try discriminate.
                        - rewrite H in H_aC.
                          contradict H_aC.
                          auto with HelperLemmas bool.
                    }
                    autoChangeSetSimplification.
                  }

                  assert( (OperationGroup.reduction (@app OperationGroup.alphabet (o0 :: o3) (o1 :: o2))) = o0::(OperationGroup.reduction ((@app OperationGroup.alphabet o3 (o1 :: o2))))) as Heq2. {
                    apply orb_prop in H_leftSplitAPossible.
                    destruct H_leftSplitAPossible as [H_ops0ops1_reduced | H_AgtB].
                    - assert(∃ P, OperationGroup.reduced_dec (operations0 ++ operations1) = left P) as H_reduced. {
                        destruct (OperationGroup.reduced_dec (operations0 ++ operations1)).
                        - now exists r.
                        - discriminate.
                      }
                      destruct H_reduced as [H_ops0ops1_reduced2 _].
                      rewrite H_operations1 in H_ops0ops1_reduced2.
                      rewrite H_operations0Split in H_ops0ops1_reduced2.
                      rewrite <-app_comm_cons in H_ops0ops1_reduced2.
                      apply tailIsReduced in H_ops0ops1_reduced2.
                      rewrite OperationGroup.reduction_fixes_reduced; auto.
                      rewrite <-app_comm_cons in H_ops0ops1_reduced2.
                      apply tailIsReduced in H_ops0ops1_reduced2.
                      rewrite OperationGroup.reduction_fixes_reduced; auto.
                    - rewrite_nat.
                      specialize splitOffLeftFromReduction with (A:=(o0 :: o3)) (B:=o1 :: o2) (a:=o0) (t:=o3) as H_splitOffLeftFromReduction; auto.
                      destruct H_splitOffLeftFromReduction; auto.
                      1: now apply tailIsReduced in operations_reduced4 as H.
                      + rewrite H_operations0Split in H_AgtB.
                        rewrite H_operations1 in H_AgtB.
                        simpl in H_AgtB.
                        simpl.
                        intuition.
                      + destruct H.
                        rewrite <-Heqt in H0.
                        contradict H_lengthT.
                        now apply length_zero_iff_nil.
                  }
                  rewrite Heq2 in Heqt; auto.
                  subst t.
                  set (g:=OperationGroup.reduction (@app OperationGroup.alphabet o3 (@cons ops.Operation o1 o2))).
                  fold rebaseChangeSetOps.
                  Opaque rebaseChangeSetOps.
                  set (H_reduced_og :=  (tailIsReduced2 (o :: (o0 :: g)) (o0 :: g) o (@eq_refl (list ops.Operation)
                       (@cons ops.Operation o (@cons ops.Operation o0 g)))
                     (operations_reduced
                        {| operations := o :: (o0 :: g); operations_reduced := x |}))).
                  exists H_reduced_og.
                  set (A':=(CSet {| operations := o0 :: g; operations_reduced := H_reduced_og |})).
                  set (myfun := (rebaseOperationWithChangeSet o0
                        ((((opToCs o)⁻¹) ○ C) ○ (rebaseOperationWithChangeSet o C)))
                     ○ (rebaseChangeSetOps g (tailIsReduced2 (o0 :: g) g o0 (@eq_refl (list ops.Operation) (@cons ops.Operation o0 g)) H_reduced_og)
                          ((((opToCs o0)⁻¹) ○ ((((opToCs o)⁻¹) ○ C) ○ (rebaseOperationWithChangeSet o C)))
                           ○ (rebaseOperationWithChangeSet o0((((opToCs o)⁻¹) ○ C) ○ (rebaseOperationWithChangeSet o C)))))).
                  case_eq g.
                  + intros.
                    assert (reduced g) as H_reduced_g. { now apply tailIsReduced in H_reduced_og as H_red. }
                    assert (A' = (opToCs o0)). {
                      unfold A'.
                      unfold opToCs.
                      apply ProofIrrelevanceForChangeSets.
                      simpl.
                      rewrite H.
                      auto with HelperLemmas bool.
                    }
                    rewrite H0. clear H0.
                    now simpl.
                  + intros.
                    unfold myfun.
                    clear myfun.
                    clear sub_fun.
                    replace (rebaseOperationWithChangeSet o C) with (a ↷ C). 2: { now simpl. }
                    set (a' := opToCs o0).
                    replace (rebaseOperationWithChangeSet o0 ((((opToCs o)⁻¹) ○ C) ○ (a ↷ C))) with (a' ↷ (((a⁻¹) ○ C) ○ (a ↷ C))). 2: { now simpl. }
                    fold a.
                    set (t:= (((a'⁻¹) ○ (((a⁻¹) ○ C) ○ (a ↷ C))) ○ (a' ↷ (((a⁻¹) ○ C) ○ (a ↷ C))))).
                    set (A'':=CSet {| operations := g; operations_reduced := (tailIsReduced2 (o0 :: g) g o0 eq_refl H_reduced_og) |}).
                    replace (rebaseChangeSetOps g (tailIsReduced2 (o0 :: g) g o0 eq_refl H_reduced_og) t) with (A'' ↷ t). 2: { now simpl. }
                    replace A' with (a' ○ A''). 2: {
                      unfold A'.
                      apply ProofIrrelevanceForChangeSets.

                      simpl.
                      unfold squashOpList.
                      unfold OperationGroup.reduced_string_product.
                      specialize OperationGroup.reduction_fixes_reduced with (S:=[o0] ++ g) as H_fix.
                      autounfold in H_fix.
                      autounfold.
                      rewrite H_fix; auto.
                      auto with HelperLemmas.
                    }
                    unfold t.
                    applyIH a' A'' ((a⁻¹ ○ C) ○ a ↷ C) IHn.
                    2: {
                      rewrite H.
                      simpl.
                      assert ( (@Datatypes.length ops.Operation l) + 1 ≤ length (o3) + length(o1 :: o2)). {
                        specialize SquashOpListMaxLength with (A:=o3) (B:=o1::o2) as H1.
                        unfold squashOpList in H1.
                        unfold OperationGroup.reduced_string_product in H1.
                        fold g in H1.
                        assert(length g = (@Datatypes.length ops.Operation l) + 1). {
                          rewrite H. simpl. autounfold. 
                          lia.
                        }
                        rewrite <- H0.
                        assumption.
                      }
                      assert (Datatypes.length (o :: (o0 :: o3)) = length(o3) + 2). { simpl. lia. }
                      rewrite H1 in H_LeLenOps.
                      lia.
                    }
                    easy.
              }
              destruct H.
              rewrite H.
              
              apply tailIsReduced in operations_reduced0 as operations_reduced_o2.
              set (A':= CSet {| operations := o0; operations_reduced := operations_reduced_o2 |}).
              assert (CSet {| operations := squashOpList o0 (o1 :: o2); operations_reduced := x0 |} = (A' ○ B)). {apply ProofIrrelevanceForChangeSets.  simpl. auto with HelperLemmas. }
              rewrite H0. clear H0.

              assert (A = a ○ A'). {
                apply ProofIrrelevanceForChangeSets.
                simpl. 
                unfold squashOpList. 
                unfold OperationGroup.reduced_string_product.
                rewrite OperationGroup.reduction_fixes_reduced; auto. 
                simpl. 
                auto with HelperLemmas bool.
              }
              rewrite H0. clear H0.
              rewrite changeSetInvertReverseSquash with (X:=a) (Y:=A').
  
              autounfold in H_LeLenOps.
              simpl in H_LeLenOps.

              applyIH (a) (A')  C IHn.
              applyIH (A') (B)  ((a⁻¹ ○  C) ○ a ↷ C) IHn.

              now repeat rewrite squashAssociative.
        ++  generalize operations_reduced0.
            generalize operations_reduced1.
            generalize operations_reduced2.
            generalize operations_reduced4.
            rewrite <-H_operations0Split.
            rewrite <-rev_involutive with (l:=operations0) in *.
            set (invOps := (rev operations0)) in *.
            rename o into o_left.
            rename o0 into o0_left.
            rename o1 into o0.
            rename o2 into o1.

            destruct invOps eqn:H_invOps. 1: {
              rewrite revEmpty.
              intros.
              autorewrite with changeset_simplificaton; auto.
            }

            apply orb_false_elim in H_leftSplitAPossible.
            destruct H_leftSplitAPossible as [H_nonReduced_b H_lenAGtlenB].
            assert (non_reduced ((rev (o :: l)) ++ operations1)) as H_nonReduced. {
              destruct (OperationGroup.reduced_dec ((rev (o :: l)) ++ operations1)) eqn:H.
              - discriminate.
              - assumption.
            } 

            assert (∃ P, (OperationGroup.alphabet_eq_dec o (OperationGroup.opposite o0)) = left P) as H_opOppositeO2. {
              assert (o = (OperationGroup.opposite o0)) as H_O. {
                rewrite <-H_operations0Split in operations_reduced0.
                rewrite H_operations1 in H_nonReduced.
                assert(∀A B a b, reduced(A++[a]) → reduced([b]++B) → (non_reduced ((A++[a])++([b]++B))) → a = (OperationGroup.opposite b)) as NonreducedConcatOfReducedImpliesOpposites. {
                  intros.
                  induction A0.
                  - apply OperationGroup.split_non_reduced in H1.
                    destruct H1.
                    ++ contradiction.
                    ++ assumption.
                  - apply IHA0.
                    + now apply tailIsReduced in H.
                    + destruct A0.
                      * rewrite app_nil_l.
                        do 2 rewrite <-cons_to_app.
                        repeat rewrite <-app_assoc in H1.
                        do 3 rewrite <-cons_to_app in H1.
                        apply OperationGroup.split_non_reduced in H1.
                        destruct H1.
                        -- assumption.
                        -- specialize OperationGroup.intro_letter_inverse with (S:=[]) (a:=a) (T:=[]) as H_nonreduced.
                           rewrite <-H1 in H_nonreduced.
                           rewrite app_nil_l in H_nonreduced.
                           rewrite <-cons_to_app in H.
                           contradiction.
                     * repeat rewrite <-app_comm_cons in H1.
                       apply OperationGroup.split_non_reduced in H1.
                       destruct H1.
                       -- auto.
                       -- specialize OperationGroup.intro_letter_inverse with (S:=[]) (a:=a1) (T:=A0 ++ [a]) as H_nonreduced.
                          rewrite <-H1 in H_nonreduced.
                          contradiction.
                }
                rewrite cons_to_app in H_nonReduced.
                rewrite rev_app_distr in H_nonReduced.
                rewrite revSingle in H_nonReduced.
                apply NonreducedConcatOfReducedImpliesOpposites with (A:=(rev l)) (B:=o1); auto.
              }
              destruct (OperationGroup.alphabet_eq_dec o (OperationGroup.opposite o0)).
              - now exists e.
              - contradiction.
            } 
                
            assert (rev (o :: l) = (rev l) ++ [o]) as H_revOL. {
                rewrite cons_to_app.
                rewrite rev_app_distr.
                now rewrite revSingle.
            }
            rewrite H_revOL.
            intros.
            rewrite <-H_operations0Split in H_LeLenOps.

            set (X:=(CSet {| operations := (rev l) ++ [o]; operations_reduced := operations_reduced5 |})).
            rewrite decomposeCSetRight with (X:=X) (l:=(rev l)) (op:=o) (redOps:={| operations := (rev l) ++ [o]; operations_reduced := operations_reduced5 |}); auto.

            set (Y:=(CSet {| operations := o0 :: o1; operations_reduced := operations_reduced3 |})).
            rewrite decomposeCSetLeft with (X:=Y) (l:=o1) (op:=o0) (redOps:={| operations := o0 :: o1; operations_reduced := operations_reduced3 |}); auto.

            assert (∃P_A', (removeLastFromCS X) = CSet {| operations := (rev l); operations_reduced := P_A' |}). {
              unfold removeLastFromCS.
              unfold X.
              unfold operations.
              apply reverseIsReduced in operations_reduced8. 
              rewrite rev_app_distr in operations_reduced8.
              rewrite revSingle in operations_reduced8.
              rewrite <-cons_to_app in operations_reduced8.
              apply tailIsReduced in operations_reduced8.
              rewrite rev_involutive in operations_reduced8.
              apply reverseIsReduced in operations_reduced8.
              exists operations_reduced8.
              apply ProofIrrelevanceForChangeSets.
              set (cond:=rev ((rev l) ++ [o])).
              specialize rev_unit with (l:=(rev l)) (a:=o) (A:=ops.Operation) as H_cond.
              fold cond in H_cond.
              set (sub_fun := λ opA Atail, λ x : opA :: Atail = cond,
                CSet
                  {|
                    operations := rev Atail;
                    operations_reduced :=
                      reverseIsReduced Atail
                        (tailIsReduced2 cond Atail opA x
                           (reverseIsReduced (rev l ++ [o])
                              (operations_reduced {| operations := rev l ++ [o]; operations_reduced := operations_reduced5 |})))
                  |}).
              assert ((match cond as x return (x = cond → ChangeSet) with
                | [] => λ _ : [] = cond, ⊘
                | opA :: Atail =>
                    λ x : opA :: Atail = cond,
                      CSet
                        {|
                          operations := rev Atail;
                          operations_reduced :=
                            reverseIsReduced Atail
                              (tailIsReduced2 cond Atail opA x
                                 (reverseIsReduced (rev l ++ [o])
                                    (operations_reduced {| operations := rev l ++ [o]; operations_reduced := operations_reduced5 |})))
                        |}
              end eq_refl) = (match cond as x return (x = cond → ChangeSet) with
              | [] => λ _ : [] = cond, ⊘
              | opA :: Atail => sub_fun opA Atail
              end eq_refl)). { unfold sub_fun. auto. }
              autounfold in *.
              rewrite H. clear H.
              assert(∃ P, (match cond as x return (x = cond → ChangeSet) with
              | [] => λ _ : [] = cond, ⊘
              | opA :: Atail => sub_fun opA Atail
              end eq_refl) = sub_fun o (rev (rev l)) P). {
                generalize sub_fun.
                rewrite H_cond.
                intros.
                now exists eq_refl.
              }
              destruct H.
              rewrite H. clear H.
              unfold sub_fun.
              simpl.
              rewrite rev_involutive.
              auto with HelperLemmas.
            }
            destruct H.
            rewrite H.
            set (A' := (CSet {| operations := rev l; operations_reduced := x |})).
            assert (∃P_A', (tailFromCS Y) = CSet {| operations := o1; operations_reduced := P_A' |}). {
              unfold tailFromCS.
              unfold Y.
              unfold operations.
              apply tailIsReduced in operations_reduced1 as H_o1Reduced.
              exists H_o1Reduced.
              apply ProofIrrelevanceForChangeSets.
              simpl.
              auto with HelperLemmas bool.
            }
            destruct H0.
            rewrite H0.

            set (B' := (CSet {| operations := o1; operations_reduced := x0 |})).
            clear C.
            set (C := (CSet {| operations := operations2; operations_reduced := operations_reduced6 |})).
            set (a := (opToCs o)).
            set (b := (opToCs o0)).
            assert (a = b⁻¹) as H_aInvb. {
              destruct H_opOppositeO2 as [H_aBOpposite _].
              unfold a. unfold b. rewrite H_aBOpposite.
              unfold invert.
              unfold opToCs.
              simpl.
              apply ProofIrrelevanceForChangeSets.
              simpl.
              set (y:=(OperationGroup.opposite o0)).  
              rewrite Op_eqb_refl.
              auto with HelperLemmas.
            }
            rewrite H_aInvb.

            (* Cancel b⁻¹ ○ b *)
            rewrite squashAssociative at 1.
            rewrite <-squashAssociative with (X:=b⁻¹).
            autorewrite with changeset_simplificaton; auto.
            
            (* use induction hypothesis *)
            unfold A' at 1.
            unfold B' at 1.
            unfold C at 1.
            rewrite IHn. 2: {
              rewrite rev_length.
              rewrite rev_length in H_LeLenOps.
              rewrite cons_to_app in H_LeLenOps.
              rewrite app_length in H_LeLenOps.
              simpl in H_LeLenOps.
              lia.
            }
            fold A'.
            fold B'.
            fold C.

            (* transform the term *)
            rewrite <-squashEmptyRight with (X:=A') at 3.
            rewrite <-squashInverseRight with (X:=b). 2: { cbv. discriminate. }

            rewrite <-squashAssociative with (X:=A').
            unfold b at 2.
            unfold opToCs.
            set (A_bopp:=(A' ○ (b⁻¹))).
            destruct A_bopp eqn:H_Abopp.
            2: {
              unfold A_bopp in H_Abopp.
              apply invalid_squash_implies_invalid_input in H_Abopp.
              contradict H_Abopp.
              intuition.
              all: discriminate H2.
            }
            destruct ops eqn:H_ops.
            unfold C at 3.
            rewrite IHn. 2: {
              assert( (Datatypes.length operations3) ≤ Datatypes.length(l) + 1 ). {
                unfold A_bopp in H_Abopp.
                unfold A' in H_Abopp.
                unfold b in H_Abopp.
                unfold opToCs in H_Abopp.
                unfold invert in H_Abopp.
                unfold OperationGroup.inverse_str in H_Abopp.
                unfold operations in H_Abopp.
                unfold squash in H_Abopp.
                unfold operations.
                injection H_Abopp as H_operation3.
                specialize SquashOpListMaxLength with (A:=rev l) (B:=[OperationGroup.opposite o0]) as H_maxLengthOperations3.
                rewrite H_operation3 in H_maxLengthOperations3.
                rewrite rev_length in H_maxLengthOperations3.
                simpl in H_maxLengthOperations3.
                auto.
              }
              simpl. 
              rewrite_nat.
              rewrite <-H_operations1 in H_LeLenOps.
              rewrite rev_length in H_LeLenOps.
              rewrite rev_length in H_lenAGtlenB.
              simpl in H_lenAGtlenB.
              simpl in H_LeLenOps.
              lia.
            }


            fold C.
            rewrite <-H_Abopp.
            replace ((CSet {| operations := [o0]; operations_reduced := singleOpListIsReduced o0 |})) with b.
            2: {
              unfold b. 
              now unfold opToCs.
            }
            fold b.
            unfold A_bopp.

            rewrite <-squashEmptyRight with (X:=(A' ↷ C)).
            destruct (changeset_eqb (A' ↷ C) ⦻) eqn:H_aC. {
              applyIH A' (b⁻¹) C IHn. 2: {
                rewrite cons_to_app in H_LeLenOps.
                rewrite rev_app_distr in H_LeLenOps.
                rewrite revSingle in H_LeLenOps.
                rewrite app_length in H_LeLenOps.
                simpl in H_LeLenOps.
                simpl.
                solve_nat.
              }
              assert ((A' ↷ C) = ⦻). { apply ProofIrrelevanceForChangeSets. rewrite H_aC. auto. }
              rewrite H1.
              autoChangeSetSimplification.
            }

            rewrite <-rebaseEmptyLeft with (X:=(A'⁻¹ ○ C ○ (A' ↷ C))).
            2: {
              intuition.
              apply invalid_squash_implies_invalid_input in H1.
              destruct H1.
              - apply invalid_squash_implies_invalid_input in H1.
                destruct H1; try discriminate.
              - rewrite H1 in H_aC.
                contradict H_aC.
                auto with HelperLemmas bool.
            }
            rewrite <-squashInverseRight with (X:=b). 2: { cbv. discriminate. }

            rewrite <-squashEmptyRight with (X:=A') at 4.
            rewrite <-squashInverseRight with (X:=b). 2: {cbv. discriminate. }
            rewrite <-squashAssociative with (X:=A').
            
            rewrite changeSetInvertReverseSquash.

            (* use induction hypothesis 2 *)
            rewrite <-H_aInvb at 1.
            unfold a at 1.
            unfold b at 1.
            unfold opToCs.
            remember ((A'⁻¹ ○ C) ○ (A' ↷ C)) as C'.
            destruct C' eqn:H_C'.
            2: {
              autoChangeSetSimplification.
              symmetry in HeqC'.
              apply invalid_squash_implies_invalid_input in HeqC'.
              destruct HeqC'.
              - apply invalid_squash_implies_invalid_input in H1.
                destruct H1; try discriminate.
              - rewrite H1 in H_aC.
                contradict H_aC.
                auto with HelperLemmas bool.
            }
            destruct ops0.
            rewrite IHn. 2: {
              simpl.
              rewrite rev_length in H_LeLenOps.
              rewrite cons_to_app in H_LeLenOps.
              rewrite app_length in H_LeLenOps.
              simpl in H_LeLenOps.
              solve_nat.
            }
            rewrite HeqC'.
            replace (CSet {| operations := [o]; operations_reduced := singleOpListIsReduced o |}) with a. 2: {
              unfold a.
              now unfold opToCs.
            }
            replace (CSet {| operations := [o0]; operations_reduced := singleOpListIsReduced o0 |}) with b. 2: {
              unfold b.
              now unfold opToCs.
            }
            
            (* use induction hypothesis on RHS *)
            unfold A' at 12.
            rewrite <-H_aInvb at 6.
            unfold a at 4.
            unfold C at 12.
            unfold opToCs.
            rewrite IHn. 2: {
              rewrite rev_length.
              rewrite rev_length in H_LeLenOps.
              rewrite cons_to_app in H_LeLenOps.
              rewrite app_length in H_LeLenOps.
              simpl in H_LeLenOps.
              simpl.
              lia.
            }
            fold C.
            fold A'.
            replace (CSet {| operations := [o]; operations_reduced := singleOpListIsReduced o |}) with a. 2: {
              unfold a.
              now unfold opToCs.
            }

            (* use induction hypothesis 2 on RHS *)
            unfold B' at 2.
            unfold b at 8.
            unfold opToCs.
            remember (((((A' ○ (b⁻¹))⁻¹) ○ C) ○ ((A' ○ (b⁻¹)) ↷ C))) as C''.
            destruct C'' eqn:H_C''.
            2: autorewrite with changeset_simplificaton; auto.

            destruct ops0.
            rewrite IHn. 2: {
              simpl.
              rewrite rev_length in H_LeLenOps.
              rewrite cons_to_app in H_LeLenOps.
              rewrite app_length in H_LeLenOps.
              simpl in H_LeLenOps.
              lia.
            }
            rewrite HeqC''.
            replace (CSet {| operations := [o0]; operations_reduced := singleOpListIsReduced o0 |}) with b. 2: {
              unfold b.
              now unfold opToCs.
            }
            fold B'.

            (* use induction hypothesis 3 on RHS *)
            unfold A' at 16.
            rewrite <-H_aInvb at 7. 
            unfold a at 5. 
            unfold C at 16. 
            unfold opToCs.
            rewrite IHn. 2: {
              simpl.
              rewrite rev_length in H_LeLenOps.
              rewrite cons_to_app in H_LeLenOps.
              rewrite app_length in H_LeLenOps.
              simpl in H_LeLenOps.
              rewrite rev_length.
              lia.
            }
            fold C.
            fold A'.
            replace (CSet {| operations := [o]; operations_reduced := singleOpListIsReduced o |}) with a. 2: {
              unfold a.
              now unfold opToCs.
            }
            
            (* Normalize result *)
            repeat rewrite changeSetInvertReverseSquash.
            repeat rewrite squashAssociative.
            repeat rewrite H_aInvb.
            auto.
  Qed.
End distributivityProofsChangeSet.
  
Transparent rebaseChangeSetOps.
Section distributivityProofsChangeSet2.
  Variable A: ChangeSet.
  Variable B: ChangeSet.
  Variable C: ChangeSet.
  Lemma rebaseRightDistibutivity: A ↷ (B ○ C)  = A ↷ B ↷ C.
    destruct A eqn:H_A.
    destruct B eqn:H_B.
    destruct C eqn:H_C.

    (* solve cases with invalid changesets *)
    2-4: now (
       try unfold squash;
       repeat first [
         rewrite rebaseWithInvalid1 |
         rewrite rebaseWithInvalid2
       ]
     ).
    destruct ops.
    remember ((length operations0)) as len.
    assert ( (length operations0) ≤ len) as H_LeLenOps. lia.
    revert H_LeLenOps.
    clear Heqlen.
    clear H_A H_B H_C.
    clear A B C.
    revert operations_reduced0.
    revert operations0.
    revert ops0.
    revert ops1.
    revert len.
    induction (len).

    - intros.
      assert_nat (Datatypes.length operations0 = 0) as H_len0.
      apply length_zero_iff_nil in H_len0.
      rewriteCSets H_len0.
      autorewrite with changeset_simplificaton in *; try discriminate; auto.
    - intros.
      destruct operations0 eqn:H_ops.
      + autorewrite with changeset_simplificaton in *; try discriminate; auto.
      + destruct (n =? 0) eqn:H_len1. {
          rewrite_nat.
          simpl in H_LeLenOps.
          assert ((length o0) = 0). {
            lia.
          }
          apply length_zero_iff_nil in H.
          rewriteCSets H.
          assert ((CSet {| operations := [o]; operations_reduced := H_reduced |}) = (opToCs o)) as H_o. {
            unfold opToCs.
            apply ProofIrrelevanceForChangeSets.
            simpl.
            auto with HelperLemmas bool.
          }
          rewrite H_o.
          now rewrite rightDistributivitySingleOperationWithTwoCS.
        }
        assert( ∀ (X:ChangeSet), X ≠ ⦻ → (CSet {| operations := o::o0; operations_reduced := operations_reduced0 |}) ↷ X = 
                (let O' := (opToCs o) in
                let O0' := (CSet {| operations := o0; operations_reduced := tailIsReduced2 (o::o0) o0 o eq_refl operations_reduced0 |}) in
                (O' ↷ X) ○ (O0' ↷ (O'⁻¹ ○ X ○ (O' ↷ X))))) as unfoldSingleRebaseOp. {
          intros.
          rename H into H_XnotInvalid.
          unfold rebaseChangeSet at 1.
          unfold operations.
          unfold operations_reduced.
          unfold rebaseChangeSetOps.
          remember o0 as o0'.
          destruct o0.
          - rewriteCSets Heqo0'.
            rewrite Heqo0' at 1.
            autoChangeSetSimplification.
            rewrite rebaseEmptyLeft.
            2: {
              intuition.
              apply invalid_squash_implies_invalid_input in H.
              destruct H.
              - apply invalid_squash_implies_invalid_input in H.
                destruct H.
                + discriminate.
                + auto.
              - now apply noErrorsDuringRebaseCS in H.
            }
            autoChangeSetSimplification.
          - replace (rebaseOperationWithChangeSet o X) with (opToCs o ↷ X).
            2: {
              now cbv.
            }
            rewrite Heqo0' at 1.
            auto.
        }

        rewrite unfoldSingleRebaseOp.
        2: {
          intuition.
          apply invalid_squash_implies_invalid_input in H.
          destruct H; discriminate.
        }

        set (O':= opToCs o).
        set (O0' := CSet {| operations := o0; operations_reduced := tailIsReduced2 (o :: o0) o0 o eq_refl operations_reduced0 |}).
        cbv zeta.
        set (B:=CSet ops0).
        set (C:=CSet ops1).
        rewrite decomposeCSetLeft with (X:=CSet {| operations := o :: o0; operations_reduced := operations_reduced0 |}) (op:=o) (l:=o0)
                                       (redOps:={| operations := o :: o0; operations_reduced := operations_reduced0 |}); auto.
        fold O'.
        unfold tailFromCS.
        unfold operations.
        unfold operations_reduced.
        set (O'':=CSet
         {|
           operations := o0;
           operations_reduced :=
             tailIsReduced2 (o :: o0) o0 o eq_refl operations_reduced0
         |}).
        

        specialize IHn with (operations0:=[o]) (operations_reduced0:=OperationGroup.single_letter_reduced o) (ops0 := ops0) (ops1 := ops1) as IHn_O'.
        replace (CSet
             {|
               operations := [o];
               operations_reduced := OperationGroup.single_letter_reduced o
             |})  with O' in IHn_O'; auto.
        fold B in IHn_O'.
        fold C in IHn_O'.
        rewrite IHn_O'.
        2: {
          simpl.
          solve_nat.
        }

        rewrite <-squashEmptyRight with (X:=B) at 2.
        rewrite <-squashInverseLeft with (X:=O' ↷ B).
        2: {
          apply noErrorsDuringRebaseCS.
          - now cbv.
          - now cbv.
        }
        rewrite <-squashAssociative.
        rewrite <-squashAssociative.
        rewrite <-squashAssociative.
        set (XX:=((O'⁻¹ ○ B) ○ O' ↷ B)).
        rewrite squashAssociative.
        rewrite squashAssociative.
        set (YY:=((O' ↷ B)⁻¹ ○ (C ○ O' ↷ B ↷ C))).

        assert(∃opsXX, CSet opsXX = XX). { 
          assert (XX ≠ ⦻). {
            intuition.
            unfold XX in H.
            apply invalid_squash_implies_invalid_input in H.
            destruct H.
            - apply invalid_squash_implies_invalid_input in H.
              destruct H; discriminate.
            - now apply noErrorsDuringRebaseCS in H.
          }
          destruct XX.
          - now exists ops.
          - contradiction.
        }

        destruct H as [opsXX H_opsXX].
        assert(∃opsYY, CSet opsYY = YY). { 
          assert (YY ≠ ⦻). {
            intuition.
            unfold YY in H.
            apply invalid_squash_implies_invalid_input in H.
            destruct H.
            - assert(∀ U, U ≠ ⦻  → (U⁻¹)%CS ≠ ⦻ ) as invalid_inverse_implies_invalid. {
                intros.
                cbv.
                destruct U.
                - discriminate.
                - contradiction.
              }
              contradict H.
              apply invalid_inverse_implies_invalid. 
              now apply noErrorsDuringRebaseCS.
            - apply invalid_squash_implies_invalid_input in H.
              destruct H.
              + unfold C in H. discriminate H.
              + destruct (O' ↷ B) eqn:H1.
                * now apply noErrorsDuringRebaseCS in H.
                * now apply noErrorsDuringRebaseCS in H1.
          }
          destruct YY.
          - now exists ops.
          - contradiction.
        }
        destruct H as [opsYY H_opsYY].

        specialize IHn with (operations0:=o0) (operations_reduced0:=tailIsReduced2 (o :: o0) o0 o eq_refl operations_reduced0) (ops0 := opsXX) (ops1 := opsYY) as IHn_O0.
        fold O0' in IHn_O0.
        rewrite H_opsXX in IHn_O0.
        rewrite H_opsYY in IHn_O0.
        rewrite IHn_O0.
        2: {
          simpl.
          simpl in H_LeLenOps.
          lia.
        }
        unfold XX.
        unfold YY.
        set (X:=O0' ↷ ((O'⁻¹ ○ B) ○ O' ↷ B)).
        set (Y:=(O' ↷ B)).

        rewrite <-squashAssociative.
        rewrite <-rebaseLeftDistibutivity with (A:=Y) (B:=X) (C:=C).

        unfold X.
        unfold Y.

        now rewrite <-rebaseLeftDistibutivity with (A:=O') (B:=O0') (C:=B).

Qed.
 
Print Assumptions rebaseRightDistibutivity.
End distributivityProofsChangeSet2.
End SingleOperationAlgebra.


Close Scope nat.
