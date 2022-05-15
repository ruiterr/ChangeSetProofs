From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import ZArith.Znat.

Require Coq.Structures.OrdersFacts.
Require Import Unicode.Utf8.
Require Import Coq.Program.Wf.
Require Import Lia.
(*Add LoadPath "/Users/ruiterr/work/fluid/ChangeSetProofs" as ChangeSets.*)
Require Import NatHelper.
Require Import free_group.

Require Import BinPos BinInt BinNat Pnat Nnat.

Scheme Equality for list.


(* General definition of operations *)
Inductive Operation :=
  | Insert (i: nat) (p: nat) (e: ascii) (c : Z) (s : list nat)
  | Remove (i: nat) (p: nat) (e: ascii) (c : Z) (s : list nat).

Inductive OperationType := 
  | InsertOperation
  | RemoveOperation.

Definition eqOpType (a b : OperationType) := match a, b with
  | InsertOperation, InsertOperation => true
  | RemoveOperation, RemoveOperation => true
  | _, _ => false
end.

Definition getOperationType (op:Operation) := match op with
  | Insert _ _ _ _ _ => InsertOperation
  | Remove _ _ _ _ _ => RemoveOperation
end.

Definition getOpI (op: Operation) := match op with
  | Insert i _ _ _ _ => i
  | Remove i _ _ _ _ => i
end.

Definition getOpP (op: Operation) := match op with
  | Insert _ p _ _ _ => p
  | Remove _ p _ _ _ => p
end.

Definition getOpE (op: Operation) := match op with
  | Insert _ _ e _ _ => e
  | Remove _ _ e _ _ => e
end.

Definition getOpC (op: Operation) := match op with
  | Insert _ _ _ c _ => c
  | Remove _ _ _ c _ => c
end.

Definition getOpS (op: Operation) := match op with
  | Insert i _ _ _ s => s
  | Remove i _ _ _ s => s
end.

Definition createOperation (type: OperationType) (i: nat) (p:nat) (e:ascii) (c:Z) (s:list nat) := match type with
  | InsertOperation => (Insert i p e c s)
  | RemoveOperation => (Remove i p e c s)
end.

Definition invertOperation (op: Operation) := match op with
  | Insert i p e c s => Remove i p e c s
  | Remove i p e c s => Insert i p e c s
end.

Declare Scope Operation.
Declare Scope OptionOperation.
Declare Scope ChangeSet.
Delimit Scope Operation with O.
Delimit Scope OptionOperation with OO.
Delimit Scope ChangeSet with CS.

Notation "a ⁻¹" := (invertOperation a) (at level 55, no associativity, format "a '⁻¹'") : Operation.
Lemma opInvertInvolution: ∀ op:Operation, ((op⁻¹)⁻¹) % O = op.
intros.
destruct op.
all: now cbv.
Qed.

Definition operation_eq_dec: forall a b:Operation, {a=b} + {a<>b}.
intros.
decide equality.
all: decide equality.
all: decide equality.
Defined.

Module Import FreeGroupsSig.
Module OperationsGroupImpl <: FreeGroupsSig.
  Definition alphabet := Operation.
  Definition opposite := invertOperation.
  Definition opposite_involution := opInvertInvolution. 
  Definition alphabet_eq_dec := operation_eq_dec. 
End OperationsGroupImpl.


Module OperationGroup := FreeGroups OperationsGroupImpl.

Check OperationGroup.reduced_string_product.

Definition invertOperationOption (op: option Operation) := 
match op with
  | Some o =>
    match o with
      | Insert i p e c s => Some (Remove i p e c s)
      | Remove i p e c s => Some (Insert i p e c s)
    end
  | None => None
end.


Notation "a ⁻¹" := (invertOperationOption a) (at level 55, no associativity, format "a '⁻¹'") : OptionOperation.


Scheme Equality for OperationType.

Definition Op_eqb  (a : Operation) (b: Operation) := 
  if (operation_eq_dec a b) then true else false.
(*Definition Op_eqb (a : Operation) (b: Operation) := 
  (eqOpType (getOperationType a) (getOperationType b)) &&
  (Nat.eqb (getOpI a) (getOpI b)) &&
  (Nat.eqb (getOpP a) (getOpP b)) &&
  (Ascii.eqb (getOpE a) (getOpE b)) &&
  (Z.eqb (getOpC a) (getOpC b)) &&
  (list_beq nat Nat.eqb (getOpS a) (getOpS b)).*)

Lemma Op_eqb_refl: ∀ op, Op_eqb op op = true.
  intros.
  unfold Op_eqb.
  destruct operation_eq_dec.
  - auto.
  - contradiction. 
Qed.

Create HintDb HelperLemmas.
Hint Resolve Op_eqb_refl : HelperLemmas.

Eval compute in (Op_eqb (Insert 0 0 "a" 0 []) (Remove 0 0 "a" 0 [])).

Open Scope string.
Definition applyOperation (str:string) (op:Operation) := match op with
  | Insert i p e c s => 
      if (Z.eqb c 0) then 
        (substring 0 p str) ++ (String e EmptyString) ++ (substring p (String.length str) str)
      else 
        str 
  | Remove i p e c s => 
      if (Z.eqb c 0) then 
        (substring 0 p str) ++ (substring (p + 1) 1000 str)
      else
        str 
  end.
Close Scope string.

Eval compute in (applyOperation "test" (Insert 0 1 "-" 0 [])).

(* ChangeSets *)
Definition opList := list Operation.

Definition non_reduced := OperationGroup.non_reduced. (*opList -> Prop :=
  | non_reducedOpList: forall (S T: opList) (a: Operation),
    non_reduced (S ++ (a⁻¹)%O :: a :: T).*)

Definition reduced := OperationGroup.reduced.

Record reducedOpList : Set := mkReducedOpList {
  operations: opList
  ; operations_reduced: reduced(operations)
}.

Definition singleOpListIsReduced := OperationGroup.single_letter_reduced.

Definition emptyOpListIsReduced := OperationGroup.empty_str_reduced.

Lemma tailIsReduced: ∀ (op:Operation) (l: opList), reduced(op::l) → reduced(l).
  intros.
  unfold reduced.
  unfold OperationGroup.reduced.
  intuition.
  unfold reduced in H.
  unfold OperationGroup.reduced in H.
  inversion H0.
  rewrite <-H1 in H.
  rewrite app_comm_cons in H.
  contradict H.
  apply OperationGroup.intro_letter_inverse.
Qed.

Lemma tailIsReduced2: ∀ (l l': opList) (op:Operation), op::l'=l → reduced(l) → reduced(l').
intros.
apply tailIsReduced with (op:=op).
now rewrite H.
Qed.


Inductive ChangeSet :=
  | CSet (ops: reducedOpList)
  | InvalidCSet.

Definition emptyChangeSet := (CSet {| 
         operations := [];
         operations_reduced := emptyOpListIsReduced
     |}).

Notation "⊘" := emptyChangeSet.
Notation "⦻" := InvalidCSet.

Definition opToCs (op:Operation) := 
  (CSet {| 
         operations := [op];
         operations_reduced := singleOpListIsReduced op
      |}).

Definition applyChangeSet (str:string) (cs: ChangeSet) := match cs with 
  | CSet ops =>
    (fold_left applyOperation ops.(operations) str)
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
    | CSet opsA, CSet opsB => list_beq Operation Op_eqb opsA.(operations) opsB.(operations)
    | CSet _, InvalidCSet => false
    | InvalidCSet, CSet _ => false
    | InvalidCSet, InvalidCSet => true
end.

Axiom ProofIrrelevanceForChangeSets: ∀ A B : ChangeSet, is_true (changeset_eqb A B) <-> A = B. 
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

Lemma list_neq_beq_refl: ∀(l: list nat), (list_beq nat Nat.eqb l l) = true.
intros.
unfold list_beq.
induction l; auto.
rewrite IHl.
now rewrite Nat.eqb_refl.
Qed.
Hint Resolve list_neq_beq_refl : HelperLemmas.

Lemma list_op_beq_refl: ∀(l: opList), (list_beq Operation Op_eqb l l) = true.
intros.
unfold list_beq.
induction l; auto.
rewrite IHl.
now rewrite Op_eqb_refl.
Qed.
Hint Resolve list_op_beq_refl : HelperLemmas.

Lemma cons_to_app: ∀(X:Type) (a : X) (l:list X), a::l = [a] ++ l.
intros.
now unfold app.
Qed.

Lemma revEmpty: ∀ A, (rev ([] : list A)) = [].
intros.
unfold rev.
auto.
Qed.

Lemma revSingle: ∀A x, (rev ([x] : list A)) = [x].
intros.
unfold rev.
auto.
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
Lemma reducedImpliesFirstTwoOpeartionsNotInverses: ∀A T x y, reduced(A) → A = (x::y::T) → (x ≠ y⁻¹)%O.
intros.
intuition.
unfold reduced in H.
unfold OperationGroup.reduced in H.
contradict H.
rewrite H0.
rewrite cons_to_app at 1.
rewrite <-app_nil_l.
rewrite H1.
apply OperationGroup.intro_letter_inverse.
Qed.

Lemma reverseIsReduced: ∀A, reduced(A) → reduced(rev A).
intros.
unfold reduced.
unfold OperationGroup.reduced.
intuition.
inversion H0.
assert(A = (rev (rev A))). { now rewrite rev_involutive. }
rewrite <-H2 in H1.
rewrite cons_to_app in H1 at 1.
rewrite cons_to_app with (l:=T) in H1.
repeat rewrite rev_app_distr in H1.
repeat rewrite revSingle in H1.
set (x:=(OperationGroup.opposite a : OperationGroup.alphabet)) in *.
rewrite <-OperationGroup.opposite_involution with (a:=a) in H1.
fold OperationGroup.opposite in H1.
fold x in H1.
rewrite app_assoc_reverse in H1.
rewrite app_assoc_reverse in H1.
rewrite <-cons_to_app in H1.
rewrite <-cons_to_app in H1.
set (S':=rev T) in *.
set (T':=rev S) in *.
specialize OperationGroup.intro_letter_inverse with (S:=S') (T:=T') (a:=x) as H_AnonReduced.
assert((@app OperationGroup.alphabet S'
          (@cons OperationGroup.alphabet (OperationGroup.opposite x) (@cons OperationsGroupImpl.alphabet x T')) =
(@app OperationGroup.alphabet S'
                     (@cons OperationsGroupImpl.alphabet (OperationGroup.opposite x) (@cons OperationGroup.alphabet x T'))))).
auto.
rewrite <-H3 in H_AnonReduced.
rewrite <-H1 in H_AnonReduced.
auto.
Qed.


Lemma invertIsReduced: ∀(opsA: opList), reduced(opsA) -> reduced(OperationGroup.inverse_str opsA).
intros.
unfold OperationGroup.inverse_str.
induction opsA.
- apply OperationGroup.empty_str_reduced.
- apply tailIsReduced in H as H_opsAreduced.
  fold OperationGroup.inverse_str in *.
  destruct opsA.
  + simpl.
    apply OperationGroup.single_letter_reduced.
  + apply reducedImpliesFirstTwoOpeartionsNotInverses with (A:=a :: o :: opsA) (T:=opsA) (x:=a) (y:=o) in H; auto.

    assert(∀A t x y, reduced(A) → (rev A) = (y::t) → y ≠ x⁻¹ → reduced(A ++ [x]))%O. {
      intros.
      apply reverseIsReduced in H0.
      rewrite H1 in H0.
      assert(rev(A ++ [x]) = rev(A ++ [x])) as HeqA'_rev. auto.
      remember (rev(A ++ [x])) as A'_rev.
      rewrite HeqA'_rev0 in HeqA'_rev at 2.
      rewrite rev_app_distr in HeqA'_rev0.
      rewrite revSingle in HeqA'_rev0.
      rewrite <-cons_to_app in HeqA'_rev0.
      rewrite H1 in HeqA'_rev0.
      assert(reduced A'_rev). {
        unfold reduced.
        unfold OperationGroup.reduced.
        intuition.
        rewrite HeqA'_rev0 in H3.
        apply OperationGroup.split_non_reduced in H3.
        destruct H3.
        - contradiction.
        - rewrite H3 in H2.
          rewrite opInvertInvolution in H2.
          now contradiction H2.
      }
      apply reverseIsReduced in H3.
      rewrite HeqA'_rev in H3.
      rewrite rev_involutive in H3.
      auto.
    }
    unfold OperationGroup.inverse_str.
    fold OperationGroup.inverse_str.
    apply H0 with (y:=OperationGroup.opposite o) (t:=(rev (OperationGroup.inverse_str opsA))).
    * unfold OperationGroup.inverse_str in IHopsA.
      auto.
    * rewrite rev_app_distr.
      rewrite revSingle.
      now rewrite <-cons_to_app.
    * rewrite opInvertInvolution.
      auto.
Qed.

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

(*Lemma changeSetInvertReverseSquash: ∀ X Y:ChangeSet, (X ○ Y)⁻¹ = (Y⁻¹ ○ X⁻¹).
intros.
unfold squash.
unfold invert.
destruct X; autorewrite with changeset_simplificaton in *.
destruct Y; autorewrite with changeset_simplificaton in *.

apply ProofIrrelevanceForChangeSets; auto.
simpl.
unfold squashOpList.
destruct X; try contradiction.
simpl.
destruct ops.
simpl.
rewrite OperationGroup.inverse_str_involution.
all: auto with HelperLemmas.
Qed.*)

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

(* Helper function to create ChangeSets for ranges *)
Definition InsertRange (i: nat) (p: nat) (t: string) := 
  (fst (fold_left (fun x y => (
      (fst x) ○ (opToCs (Insert (i + (snd x)) (p + (snd x)) y 0 []) ), 
      (snd x) + 1 )
    ) (list_ascii_of_string t) (⊘, 0))).


Definition RemoveRange (i:nat) (p:nat) (l:nat) (str: string) :=
  (fst (fold_left (fun x y => (
      (fst x) ○ (opToCs (Remove (i + (snd x)) p y 0 []) ), 
      (snd x) + 1 )
    ) (list_ascii_of_string (substring p l str)) (⊘, 0))).

Eval compute in (InsertRange 0 5 "test").
Eval compute in (RemoveRange 0 2 2 "test").
 
Eval compute in (applyChangeSet "Hello World" (InsertRange 0 6 "cruel ")).
Eval compute in (applyChangeSet "Hello cruel World" (RemoveRange 0 6 6 "Hello cruel World")).

Eval compute in (squash (InsertRange 0 6 "cruel ") (RemoveRange 0 6 6 "Hello cruel World")).
Eval compute in (applyChangeSet "Hello World" ( (InsertRange 0 6 "cruel ") ○ (RemoveRange 0 6 6 "Hello cruel World"))).

Definition testInsertCS := (InsertRange 0 6 "cruel ").
Eval compute in (testInsertCS ○ testInsertCS⁻¹)%CS.


Eval compute in (applyChangeSet "test" ((opToCs (Insert 0 1 "-" 0 [])) ○ (opToCs (Remove 0 2 "e" 0 [])))).

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
Definition rebaseOperation (oA oB : option Operation) := 
  match oA with
    | Some A => 
    match oB with
      | Some B => 
      let opTypeA := (getOperationType A) in
      let i_A := (getOpI A) in
      let p_A := (getOpP A) in
      let e_A := (getOpE A) in
      let c_A := (getOpC A) in
      let s_A := (getOpS A) in

      match B with 
        | Insert i_B p_B e_B c_B s_B =>
            if p_B <? p_A then
                (*  Is this a canceled operation? *)
                if (c_B =? 0)%Z  then
                    (* All operations at a higher position are just shifted *)
                    (Some (createOperation opTypeA i_A (p_A + 1) e_A c_A s_A))
                else
                    (* Canceled operations don't affect the position *)
                    (Some A)
            else if p_A <? p_B then
                (* Operations at a lower position remain unchanged *)
                (Some A)
            else 
                (* If operations are at the same position, we have to distinguish
                   whether they are the same operation (based on their ID) *)
                if i_A =? i_B then
                    (* If this is the same operation, we have to increase the cancelation counter *)
                    (Some (createOperation opTypeA i_A p_A e_A (c_A + 1) s_A))
                else
                    (* These are different operations. Is this a canceled operation? *)
                    if (c_B =? 0)%Z then
                        if (existsb (fun x:nat => x =? i_B) s_A) then
                            (* Remove the scaffolding entry, but keep position *)
                            (Some (createOperation opTypeA i_A p_A e_A c_A (removeFirst i_B s_A) ))
                        else
                            (* No scaffolding, so we shift position by one *)
                            (Some (createOperation opTypeA i_A (p_A + 1) e_A c_A s_A))
                    else 
                        (* Canceled operations don't affect the scaffolding *)
                        (Some A)
        | Remove i_B p_B e_B c_B s_B =>
            if (negb (p_A =? p_B)) && ((i_A =? i_B) || (existsb (fun x:nat => x =? i_B) s_A)) then
              None
            else
              if p_B <? p_A then
                  (*  Is this a canceled operation? *)
                  if (c_B =? 0)%Z  then
                      (* All operations at a higher position are just shifted *)
                      (Some (createOperation opTypeA i_A (p_A - 1) e_A c_A s_A))
                  else
                      (* Canceled operations don't affect the position *)
                      (Some A)
              else if p_A <? p_B then
                  (* Operations at a lower position remain unchanged *)
                  (Some A)
              else 
                  (* If operations are at the same position, we have to distinguish
                     whether they are the same operation (based on their ID) *)
                  if i_A =? i_B then
                      (* If this is the same operation, we have to decrease the cancelation counter *)
                      (Some (createOperation opTypeA i_A p_A e_A (c_A - 1) s_A))
                  else
                      (* These are different operations. Is this a canceled operation? *)
                      if (c_B =? 0)%Z then
                          (* We add the ID to the scaffolding *)
                          (Some (createOperation opTypeA i_A p_A e_A c_A (i_B::s_A)))
                      else 
                          (* Canceled operations don't affect the scaffolding *)
                          (Some A)
    end
    | None => None
    end
  |None => None
end.

Infix "↷" := rebaseOperation (at level 57, left associativity) : OptionOperation.

Definition rebaseOperationWithChangeSet (a:Operation) (b : ChangeSet) := match b with
  | CSet ops => match (fold_left rebaseOperation ((map (λ x:Operation, Some x)) ops.(operations)) (Some a)) with
                  | Some result => (opToCs result)
                  | None => InvalidCSet
                end
  | InvalidCSet => InvalidCSet
end.

Fixpoint rebaseChangeSetOps (a : list Operation) (a_reduced : reduced(a)) (b : ChangeSet) {struct a}:= 
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


Lemma removeInsert: ∀(i:nat) (s: list nat), (i :: (removeFirst i s)) = s.
give_up.
Admitted.

Create HintDb solve_rebase.
Hint Rewrite Nat.eqb_refl : solve_rebase.
Hint Rewrite Nat.ltb_irrefl : solve_rebase.
Hint Rewrite Z.add_simpl_r : solve_rebase.
Hint Rewrite andb_true_r : solve_rebase.
Hint Rewrite orb_false_r : solve_rebase.
Hint Rewrite removeInsert : solve_rebase.
Hint Rewrite Nat.add_sub : solve_rebase.
Hint Rewrite Z.sub_add : solve_rebase.


Check Nat.eq_dec.
Print nat_rec.

Eval compute in (Nat.eq_dec 1 1).

Ltac assert_bool exp name := 
  first [
    (assert (exp = false) as name; only 1: solve_nat)|
    (assert (exp = true) as name; only 1: solve_nat)
  ].

Ltac try_solve := repeat (
  try multimatch goal with
      | [ |- context[if ?X then _ else _] ] => 
          let Y := fresh in
          assert_bool X Y;
          rewrite Y
      | [ |- context[if (negb ?X) then _ else _] ] => 
          let Y := fresh in
          assert_bool X Y;
          rewrite Y;
          unfold negb
      | [ |- context[if (negb ?X) && ?Y then _ else _] ] => 
          let X_n := fresh in
          let Y_n := fresh in
          assert_bool X X_n;
          try assert_bool Y Y_n;
          rewrite X_n;
          try rewrite Y_n;
          unfold negb
  end; 
  simpl;
  try autorewrite with solve_rebase;
  auto
).

Tactic Notation "assert_bool" constr(exp) ident(name) := assert_bool exp name.

Section distributivityProofs.
  Variable A:Operation.
  Variable B:Operation.
  Let sA := Some A.
  Let sB := Some B.

  Open Scope OO.

  Lemma rebaseOperatrionLeftDistibutivity: (sA ↷ sB)⁻¹  = sA⁻¹ ↷ sA⁻¹ ↷ sB ↷ (sA ↷ sB) ∨
                                           (sA ↷ sB)⁻¹ = None.
  intros.
  destruct B eqn:H_B.
  all: (
    unfold invertOperation;
    destruct A eqn:H_A;

    destruct (p ?= p0) eqn:H_pCmpP0;
    try apply nat_compare_eq in H_pCmpP0 as H_pRelP0;
    try apply nat_compare_Lt_lt in H_pCmpP0 as H_pRelP0;
    try apply nat_compare_Gt_gt in H_pCmpP0 as H_pRelP0
  ).


  all: (
    destruct (c ?= c0)%Z eqn:H_cCmpC0;
    try apply Z.compare_eq in H_cCmpC0 as H_cRelC0;
    try apply Z.compare_lt_iff in H_cCmpC0 as H_cRelC0;
    try apply Z.compare_gt_iff in H_cCmpC0 as H_cRelC0;
    try rewrite Z.compare_gt_iff in H_cCmpC0;
    try rewrite Z.compare_lt_iff in H_cRelC0
  ).


  all: (
    unfold rebaseOperation;
    unfold getOpI;
    unfold getOpP;
    unfold getOpC;
    unfold getOpS
  ).

  all: destruct (i0 =? i) eqn:H_i0Eqi.


  all: try_solve.

  all: destruct (c0 =? 0)%Z eqn:H_cEq0.
  all: destruct (existsb (λ x : nat, x =? i) s0) eqn:H_iInS0.
  all: try rewrite H_iInS0.

  all: try_solve.
  all: try rewrite H_iInS0.
  all: try_solve.

  all: try_solve.

  all: try match goal with 
    | [ |- context[?X + 1 =? ?Y]] => 
      destruct (X + 1 =? Y) eqn:H_eqP1;
      try try_solve
  end.

  all: try match goal with 
    | [ |- context[(?X =? 0)%Z]] => 
      destruct (X =? 0)%Z;
      try try_solve
  end.
  all: try rewrite H_iInS0.
  all: try_solve.

  Qed.

  Lemma rebaseOperatrionRightDistibutivity: sA ↷ sB ↷ sB⁻¹ = sA ∨
                                            sA ↷ sB ↷ sB⁻¹ = None.
  intros.
  destruct B eqn:H_B.
  all: (
    unfold invertOperation;
    destruct A eqn:H_A;

    destruct (p ?= p0) eqn:H_pCmpP0;
    try apply nat_compare_eq in H_pCmpP0 as H_pRelP0;
    try apply nat_compare_Lt_lt in H_pCmpP0 as H_pRelP0;
    try apply nat_compare_Gt_gt in H_pCmpP0 as H_pRelP0
  ).


  all: (
    destruct (c ?= c0)%Z eqn:H_cCmpC0;
    try apply Z.compare_eq in H_cCmpC0 as H_cRelC0;
    try apply Z.compare_lt_iff in H_cCmpC0 as H_cRelC0;
    try apply Z.compare_gt_iff in H_cCmpC0 as H_cRelC0;
    try rewrite Z.compare_gt_iff in H_cCmpC0;
    try rewrite Z.compare_lt_iff in H_cRelC0
  ).


  all: (
    unfold rebaseOperation;
    unfold getOpI;
    unfold getOpP;
    unfold getOpC;
    unfold getOpS
  ).

  all: destruct (i0 =? i) eqn:H_i0Eqi.


  all: try_solve.

  all: destruct (c0 =? 0)%Z eqn:H_cEq0.
  all: destruct (existsb (λ x : nat, x =? i) s0) eqn:H_iInS0.
  all: try rewrite H_iInS0.

  all: try_solve.
  all: try rewrite H_iInS0.
  all: try_solve.

  all: try_solve.

  all: try match goal with 
    | [ |- context[?X + 1 =? ?Y]] => 
      destruct (X + 1 =? Y) eqn:H_eqP1;
      try try_solve
  end.

  all: try match goal with 
    | [ |- context[(?X =? 0)%Z]] => 
      destruct (X =? 0)%Z;
      try try_solve
  end.
  all: try rewrite H_iInS0.
  all: try_solve.

  all: destruct (p <? p0 -1) eqn:H_pGtp0; rewrite Nat.sub_add; try lia; auto.
  Qed.

  Close Scope OO.
End distributivityProofs.

Section distributivityProofsChangeSet.
  Variable A: ChangeSet.
  Variable B: ChangeSet.
  Variable C: ChangeSet.

  Open Scope CS.
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

  Lemma rebaseOperationEmpty: ∀op:Operation, (rebaseOperationWithChangeSet op ⊘) = (opToCs op).
  intros.
  unfold rebaseOperationWithChangeSet.  
  unfold fold_left. 
  now simpl.
  Qed.
  
  Create HintDb changeset_simplificaton.
  Hint Rewrite rebaseWithInvalid1 : changeset_simplificaton.
  Hint Rewrite rebaseWithInvalid2 : changeset_simplificaton.
  Hint Rewrite rebaseOperationEmpty : changeset_simplificaton.
  Hint Rewrite rebaseEmptyLeft using (easy) : changeset_simplificaton.
  Hint Rewrite rebaseOperationEmpty : changeset_simplificaton.

  Lemma reducedImpliesNoOpposites: ∀a b t, reduced(a::b::t) →
                                    ∃ X, (OperationGroup.alphabet_eq_dec a (OperationGroup.opposite b)) = (right X).
  intros.
  unfold reduced in H.
  unfold OperationGroup.reduced in H.
  assert (a ≠ (OperationGroup.opposite b)). {
    intuition.
    apply H.
    rewrite <-app_nil_l.
    rewrite H0.
    apply OperationGroup.intro_letter_inverse.
  }
  destruct (OperationGroup.alphabet_eq_dec a (OperationGroup.opposite b)) eqn:H2.
  - contradiction.
  - now exists n.
  Qed.

  Lemma group_str_app_reduced_nop: ∀ops, reduced(ops) → (OperationGroup.group_str_action (ops) []) = ops.
  intros.
  induction ops.
  - now cbv.
  - unfold OperationGroup.group_str_action.
    fold OperationGroup.group_str_action.
    unfold OperationGroup.letter_action.
    rewrite IHops. 2: {
      now apply tailIsReduced with (op:=a).
    }
    destruct ops.
    + auto.
    + apply reducedImpliesNoOpposites in H.
      destruct H as [H_aneqOppa0 H_notOpposites].
      now rewrite H_notOpposites.
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

  Lemma fold_left_rebaseOperation_squashOpList: ∀ (a:Operation) (ops0 ops1: list Operation),
    fold_left rebaseOperation (map (λ x : Operation, (Some x)) (squashOpList ops0 ops1)) (Some a) = 
    fold_left rebaseOperation ((map (λ x : Operation, (Some x)) ops0) ++ (map (λ x : Operation, (Some x)) ops1)) (Some a).
  Admitted.

  Lemma invalid_squash_implies_invalid_input: ∀X Y, (X ○ Y) = ⦻ → X = ⦻ ∨ Y = ⦻.
  intros.
  unfold squash in H.
  destruct X.
  all: destruct Y; auto.
  discriminate.
  Qed.

  Lemma fold_left_rebaseOperation_With_None: ∀ (ops: list Operation), fold_left rebaseOperation (map (λ x : Operation, (Some x)) ops) None = None.
  intros.
  induction ops.
  - now simpl.
  - rewrite map_cons.
    unfold fold_left in *.
    replace (None ↷ (Some a))%OO with (None : (option Operation)).
    2: now cbv.
    now rewrite IHops.
  Qed.
  
  Lemma decomposeCSetLeft: ∀ op l, (CSet (op::l) ) = (CSet [op]) ○ (CSet l).
  intros.
  unfold squash.
  unfold squashOpList. 
  destruct l;auto.
  destruct (Op_eqb (last [op] (Insert 0 0 "a" 0 [])) (o⁻¹)%O).
  - give_up. (* we need to proof that this does not happen *)
  - auto.
  Admitted.

  Lemma decomposeCSetRight: ∀ op l, (CSet (l ++ [op]) ) = (CSet l) ○ (CSet [op]).
  intros.
  unfold squash.
  unfold squashOpList. 
  destruct l;auto.
  destruct (Op_eqb (last (o :: l) (Insert 0 0 "a" 0 [])) (op⁻¹)%O).
  - give_up. (* we need to proof that this does not happen *)
  - auto.
  Admitted.
  
  Definition CSLength (X: ChangeSet) := match X with
    | CSet ops => length ops 
    | InvalidCSet => 0
  end.
  
  Notation "‖ x ‖" := (CSLength x) (at level 40, no associativity, format "'‖' x '‖'").
  Lemma squashLength: ∀X Y, ‖ X ○ Y ‖ ≤ ‖X‖ + ‖Y‖.
  Admitted.

  Lemma CSetLength0: ∀X, ‖X‖ = 0 → X = ⊘ ∨ X = ⦻.
  intros.
  destruct X; auto.
  apply length_zero_iff_nil in H.
  rewrite H; auto.
  Qed.
  
  Lemma squash_first: ∀X Y, X ≠ ⦻ ∧ Y ≠ ⦻ → (X ○ Y) = ⊘ ∨
                                            ∃op t ops, X=CSet (op::t) ∧ Y=CSet ops ∧ 
                                                       (X ○ Y) = CSet ( op :: (squashOpList t ops)).
  intros.
  destruct H.
  destruct H0.
  destruct X; try contradiction.
  destruct Y; try contradiction.
  (*exists ops.
  exists ops0.
  repeat split; auto.
  unfold squash.*)
  Admitted.

  Lemma squashAssociativeForInverses: ∀X Y, X ○ (X⁻¹ ○ Y) = Y.
  Admitted.

  Lemma squashEmptyImpliesInverse: ∀X Y, X ○ Y = ⊘ → Y = X⁻¹.
  Admitted.

  Lemma squashAssociative: ∀X Y Z, (X ○ Y) ○ Z = X ○ (Y ○ Z).
  intros.
  destruct X.
  destruct Y.
  destruct Z.
  all: autorewrite with changeset_simplificaton; auto.

  set (X:=(CSet ops)).
  set (Y:=(CSet ops0)).
  set (Z:=(CSet ops1)).
  specialize squash_first with (X:=X) (Y:=Y).
  intros.
  destruct H.
  - split; discriminate.
  - rewrite H.
    apply squashEmptyImpliesInverse in H.
    rewrite H.
    rewrite squashAssociativeForInverses.
    now autorewrite with changeset_simplificaton.
  - repeat destruct H.
    destruct H0.
    rewrite H0.
    specialize squash_first with (X:=(CSet (x :: squashOpList x0 x1))) (Y:=Z).
    intros.
    destruct H1; try (split;discriminate).
    + rewrite H1.
      apply squashEmptyImpliesInverse in H1.
      rewrite H1.
      rewrite <-H0.
      rewrite squashAssociativeForInverses.
      now autorewrite with changeset_simplificaton.
    
  Lemma squashAssociative: ∀X Y Z, (X ○ Y) ○ Z = X ○ (Y ○ Z).
  intros.
  (*destruct X.
  destruct Y.
  destruct Z.
  all: autorewrite with changeset_simplificaton; auto.*)
  
  remember (‖X‖ + ‖Y‖ + ‖Z‖) as len.
  assert ( (‖X‖ + ‖Y‖ + ‖Z‖) ≤ len) as H_LeLenOps. lia.
  revert H_LeLenOps.
  clear Heqlen.
  revert X.
  revert Y.
  revert Z.
  revert len.
  induction (len).
  - intros.
    assert_nat (‖X‖ = 0) as H_X.
    apply CSetLength0 in H_X.
    destruct H_X.
    all: rewrite H.
    all: autorewrite with changeset_simplificaton; auto.
  - intros.
    destruct X.
    destruct Y.
    all: autorewrite with changeset_simplificaton; auto.
    rewrite <-rev_involutive with (l:=ops).
    set (invOps := (rev ops)).
    destruct invOps.
    all: autorewrite with changeset_simplificaton; auto.
    destruct ops0.
    all: autorewrite with changeset_simplificaton; auto.
    unfold squash at 2.
    unfold squashOpList.
    destruct (rev (o :: invOps)).
    all: autorewrite with changeset_simplificaton; auto.
    destruct (Op_eqb (last (o1 :: l) (Insert 0 0 "a" 0 [])) (o0⁻¹)%O).
    + fold squashOpList.
      fold squash.

    rewrite decomposeCSetLeft.
    set (X':=(CSet ops)).
    set (x:=(CSet [o])).

    rewrite IHn with (X:= x).
    rewrite IHn with (Z:= Z).
    rewrite IHn with (X:= x).
    rewrite IHn with (X:= X').
    auto.

    all: assert(‖X'‖ + 1 = ‖CSet (o :: ops)‖) as H_X'len; try (simpl; lia).
    all: rewrite <-H_X'len in H_LeLenOps.
    + lia.
    + specialize squashLength with (X:=Y) (Y:=Z) as H_YZlen. lia.

  Hint Rewrite revEmpty : changeset_simplificaton.

  Lemma rebaseLeftDistibutivity: (A ○ B) ↷ C  = (A ↷ C) ○ (B ↷ (A⁻¹ ○ C ○ (A ↷ C))).
  intros.
  destruct A.
  destruct B.
  destruct C.
  
  all: autorewrite with changeset_simplificaton; auto.

  remember ((length ops) + (length ops0)) as len.
  assert ( (length ops) + (length ops0) ≤ len) as H_LeLenOps. lia.
  revert H_LeLenOps.
  clear Heqlen.
  revert ops.
  revert ops0.
  revert ops1.
  revert len.
  induction (len).
  - intros.
    assert_nat (Datatypes.length ops = 0) as H_ops.
    assert_nat (Datatypes.length ops0 = 0) as H_ops0.
    apply length_zero_iff_nil in H_ops.
    apply length_zero_iff_nil in H_ops0.
    rewrite H_ops.
    rewrite H_ops0.
    autorewrite with changeset_simplificaton; auto.
  - intros.
    rewrite <-rev_involutive with (l:=ops).
    set (invOps := (rev ops)).
    destruct invOps.
    autorewrite with changeset_simplificaton; auto.
    destruct ops0.
    autorewrite with changeset_simplificaton; auto.
    set (t:=((CSet (rev (o :: invOps))⁻¹ ○ CSet ops1) ○ CSet (rev (o :: invOps)) ↷ CSet ops1)).
    destruct t eqn:H_t.
    + autorewrite with changeset_simplificaton; auto.
    + unfold t in H_t.
      apply invalid_squash_implies_invalid_input in H_t.
      destruct H_t.
      * apply invalid_squash_implies_invalid_input in H.
        destruct H; discriminate.
      * autorewrite with changeset_simplificaton; auto.
   + rewrite cons_to_app.
     rewrite rev_app_distr.
     rewrite revSingle.
     destruct (Op_eqb o (o0⁻¹)%O) eqn:H_abInverse.
     * rewrite decomposeCSetLeft.
       rewrite decomposeCSetRight.
       clear A B C.
       set (A' := (CSet (rev invOps))).
       set (B' := (CSet ops0)).
       set (C := (CSet ops1)).
       set (a := (CSet [o])).
       set (b := (CSet [o0])).

  rewrite <-rev_involutive with (l:=ops).
  set (invOps:=rev ops).
  unfold squash at 1.
  set (t := (squashOpList (rev invOps) ops0)).
  set (lenAplusB := (length (rev invOps)) + (length ops0) ).
  assert (length (rev invOps) + (length ops0) = lenAplusB) as H_lenAPlusB. auto.
  induction (lenAplusB).
  - assert_nat (Datatypes.length (rev invOps) = 0) as H_invOps.
    assert_nat (Datatypes.length ops0 = 0) as H_ops0.
    apply length_zero_iff_nil in H_invOps.
    apply length_zero_iff_nil in H_ops0.
    unfold t.
    rewrite H_invOps.
    rewrite H_ops0.
    unfold squashOpList.
    autorewrite with changeset_simplificaton; auto.
  - specialize IHn with (invOps := []).
apply length_zero_iff_nil in H_lenT.
    rewrite H_lenT.
    assert ( (CSet (rev invOps)) = (CSet ops0)⁻¹) as H_inv. give_up.
    rewrite H_inv.
    autorewrite with changeset_simplificaton; auto.


  induction invOps.
  - all: autorewrite with changeset_simplificaton; auto.
    (*unfold t in H_t. 
    apply invalid_squash_implies_invalid_input in H_t.
    destruct H_t.
    + apply invalid_squash_implies_invalid_input in H.
      destruct H; discriminate.
    + assumption.*)
  - induction ops0. 
    +  autorewrite with changeset_simplificaton; auto.
       set (t:=((((CSet (rev (a :: invOps)))⁻¹) ○ (CSet ops1)) ○ ((CSet (rev (a :: invOps))) ↷ (CSet ops1)))).
       destruct t eqn:H_t.
       all: autorewrite with changeset_simplificaton; auto.
       unfold t in H_t.
       apply invalid_squash_implies_invalid_input in H_t.
       destruct H_t.
       * apply invalid_squash_implies_invalid_input in H.
         destruct H; discriminate.
       * assumption.
    + unfold squash at 1.
      unfold squashOpList.
      set (t:=rev (a :: invOps)).
      case_eq t.
      * intros. 
        unfold t in H.
        rewrite cons_to_app in H.
        rewrite rev_app_distr in H.
        unfold rev at 2 in H.
        rewrite app_nil_l in H.
        apply app_eq_nil in H.
        destruct H.
        discriminate.
      * intros.
        destruct (Op_eqb (last (o :: l) (Insert 0 0 "a" 0 [])) (a0⁻¹)%O) eqn:H_opEqual.
        -- fold squashOpList.
         
    destruct t eqn:H_t.
    2: { 
      unfold t in H_t. 
      apply invalid_squash_implies_invalid_input in H_t. 
      destruct H_t; 
      discriminate. 
    }
    unfold squash in t.

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
    induction ops.

    - autorewrite with changeset_simplificaton in *; try discriminate; auto.
    - (*unfold rebaseChangeSet.
      unfold rebaseChangeSetOps.*)
      destruct ops eqn:H_ops.
      + unfold rebaseChangeSet.
        unfold rebaseChangeSetOps.
        unfold rebaseOperationWithChangeSet.
        unfold squash.
        destruct (fold_left rebaseOperation (map (λ x : Operation, (Some x)) ops0) (Some a)) eqn:H_left_rebase.
        * rewrite <-H_left_rebase.
          rewrite <-fold_left_app.
          now rewrite fold_left_rebaseOperation_squashOpList.
        * rewrite fold_left_rebaseOperation_squashOpList.
          rewrite fold_left_app.
          rewrite H_left_rebase.
          now rewrite fold_left_rebaseOperation_With_None.
      + unfold rebaseChangeSet at 1.
        cbv delta [rebaseChangeSetOps].
        set (v := o::l).
        cbn -[rebaseChangeSetOps rebaseOperationWithChangeSet squash v].
        destruct (a :: (o :: l)) eqn:H_a_o_l; try discriminate.
        
        cbn -[rebaseChangeSetOps rebaseOperationWithChangeSet squash].
          
           
  


Check rebaseOperatrionRightDistibutivity.
Close Scope nat.