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

Module InsertRemoveOperationDefinition <: SingleOperationAlgebraSig.
(* General definition of operations *)
Inductive Operations :=
  | Insert (i: nat) (p: nat) (e: ascii) (c : Z) (s : multiset)
  | Remove (i: nat) (p: nat) (e: ascii) (c : Z) (s : multiset).

Definition Operation := Operations.
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

Definition createOperation (type: OperationType) (i: nat) (p:nat) (e:ascii) (c:Z) (s:multiset) := match type with
  | InsertOperation => (Insert i p e c s)
  | RemoveOperation => (Remove i p e c s)
end.

Definition invert (op: Operation) := match op with
  | Insert i p e c s => Remove i p e c s
  | Remove i p e c s => Insert i p e c s
end.

Definition invertOperationOption (op: option Operation) := 
match op with
  | Some o => (Some (invert o))
  | None => None
end.
Notation "a ⁻¹" := (invert a) (at level 55, no associativity, format "a '⁻¹'") : Operation.

Declare Scope Operation.
Declare Scope OptionOperation.
Declare Scope ChangeSet.
Delimit Scope Operation with O.
Delimit Scope OptionOperation with OO.
Delimit Scope ChangeSet with CS.

Lemma opInvertInvolution: ∀ op: Operation, ((op⁻¹)⁻¹) % O = op.
intros.
destruct op.
all: now cbv.
Qed.

Definition Operation_eq_dec: forall a b:Operation, {a=b} + {a<>b}.
intros.
decide equality.
all: decide equality.
all: try decide equality.
1-2: apply m_t_nat_eq_dec.
Defined.
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
            if (negb (p_A =? p_B)) && ((i_A =? i_B) || ((ms_contains i_B s_A) && (c_B =? 0)%Z)) then
              (Some A)
            else
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
                          if (ms_contains i_B s_A) then
                              (* Remove the scaffolding entry, but keep position *)
                              (Some (createOperation opTypeA i_A p_A e_A c_A (ms_remove i_B s_A) ))
                          else
                              (* No scaffolding, so we shift position by one *)
                              (Some (createOperation opTypeA i_A (p_A + 1) e_A c_A s_A))
                      else 
                          (* Canceled operations don't affect the scaffolding *)
                          (Some A)
        | Remove i_B p_B e_B c_B s_B =>
            if (negb (p_A =? p_B)) && ((i_A =? i_B) || ((ms_contains i_B s_A) && (c_B =? 0)%Z)) then
              (Some A)
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
                          (Some (createOperation opTypeA i_A p_A e_A c_A (ms_insert i_B s_A)))
                      else 
                          (* Canceled operations don't affect the scaffolding *)
                          (Some A)
    end
    | None => None
    end
  |None => None
end.

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

(*Lemma removeInsert: ∀(i:nat) (s: list nat), (i :: (removeFirst i s)) = s.
give_up.
Admitted.*)

Create HintDb solve_rebase.
#[export] Hint Rewrite Nat.eqb_refl : solve_rebase.
#[export] Hint Rewrite Nat.ltb_irrefl : solve_rebase.
#[export] Hint Rewrite Z.add_simpl_r : solve_rebase.
#[export] Hint Rewrite andb_true_r : solve_rebase.
#[export] Hint Rewrite orb_false_r : solve_rebase.
#[export] Hint Rewrite multiset_insert_remove : solve_rebase.
#[export] Hint Rewrite multiset_remove_insert : solve_rebase.
#[export] Hint Rewrite multiset_contains_insert : solve_rebase.
#[export] Hint Rewrite Nat.add_sub : solve_rebase.
#[export] Hint Rewrite Z.sub_add : solve_rebase.



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
Infix "↷" := rebaseOperation (at level 57, left associativity) : OptionOperation.
Notation "a ⁻¹" := (invertOperationOption a) (at level 55, no associativity, format "a '⁻¹'") : OptionOperation.

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
    unfold invert;
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
  all: destruct (ms_contains i s0) eqn:H_iInS0.
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
    unfold invert;
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
  all: destruct (ms_contains i s0) eqn:H_iInS0.
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

Lemma rebaseNone: ∀ a, (None ↷ Some a)%OO = None.
intros.
now cbv.
Qed.

Lemma noErrorsDuringRebase: ∀A B, (Some A ↷ Some B)%OO = None → False.
intros.
destruct A.
all: destruct B.
all: unfold rebaseOperation in H.
all: contradict H.
Ltac destructIf := try match goal with
    | [ |- context[if ?X then _ else _ ] ] => 
        destruct X;
        try discriminate
end.

all: repeat destructIf.
Qed.

Close Scope nat.
End InsertRemoveOperationDefinition.


Module InsertRemoveChangeSetAlgebra := SingleOperationAlgebra InsertRemoveOperationDefinition.


Print Assumptions InsertRemoveChangeSetAlgebra.rebaseLeftDistibutivity.
Print Assumptions InsertRemoveChangeSetAlgebra.rebaseRightDistibutivity.

Import InsertRemoveOperationDefinition.
Import InsertRemoveChangeSetAlgebra.

(* Helper function to create ChangeSets for ranges *)
Definition InsertRange (i: nat) (p: nat) (t: string) := 
  (fst (fold_left (fun x y => (
      (fst x) ○ (InsertRemoveChangeSetAlgebra.opToCs (Insert (i + (snd x)) (p + (snd x)) y 0 (ms_create_from_list [])) ), 
      (snd x) + 1 )
    ) (list_ascii_of_string t) (⊘, 0))).


Definition RemoveRange (i:nat) (p:nat) (l:nat) (str: string) :=
  (fst (fold_left (fun x y => (
      (fst x) ○ (opToCs (Remove (i + (snd x)) p y 0 (ms_create_from_list [])) ), 
      (snd x) + 1 )
    ) (list_ascii_of_string (substring p l str)) (⊘, 0))).


(*Eval compute in (InsertRange 0 5 "test").
Eval compute in (RemoveRange 0 2 2 "test").
 
Eval compute in (applyChangeSet "Hello World" (InsertRange 0 6 "cruel ")).
Eval compute in (applyChangeSet "Hello cruel World" (RemoveRange 0 6 6 "Hello cruel World")).

Eval compute in (squash (InsertRange 0 6 "cruel ") (RemoveRange 0 6 6 "Hello cruel World")).
Eval compute in (applyChangeSet "Hello World" ( (InsertRange 0 6 "cruel ") ○ (RemoveRange 0 6 6 "Hello cruel World"))).


Definition BaseChange := (InsertRange 0 0 "abcde").

Definition ChangeClient1 :=  (RemoveRange 1 0 5 "abcde"). 
Eval compute in applyChangeSet "" (BaseChange ○ ChangeClient1).
Definition ChangeClient2_1 :=  (InsertRange 6 3 "y").
Eval compute in applyChangeSet "" (BaseChange ○ ChangeClient2_1).
Definition ChangeClient2_2 :=  (InsertRange 7 1 "w").
Eval compute in applyChangeSet "" (BaseChange ○ ChangeClient2_1 ○ ChangeClient2_2).
Definition ChangeClient3_1 :=  (InsertRange 8 4 "z").
Eval compute in applyChangeSet "" (BaseChange ○ ChangeClient3_1).
Definition ChangeClient3_2 :=  (InsertRange 9  2 "x").
Eval compute in applyChangeSet "" (BaseChange ○ ChangeClient3_1 ○ ChangeClient3_2).

Fixpoint rebaseChangeSets (CSets : list ChangeSet)  (base : ChangeSet) := match CSets with
  | [] => []
  | A::tail => (A ↷ base) :: (rebaseChangeSets tail (A⁻¹ ○ base ○ (A ↷ base)))
end.


Definition ChangesFromClient1 := ChangeClient1.
Definition rebasedChangesClient2 := (rebaseChangeSets [ChangeClient2_1; ChangeClient2_2] ChangesFromClient1).
Definition RebasedChangesFromClient2 := (nth 0 rebasedChangesClient2 ⦻) ○ (nth 1 rebasedChangesClient2 ⦻).
Eval compute in applyChangeSet "" (BaseChange ○ ChangesFromClient1 ○ RebasedChangesFromClient2).


Definition rebasedChangesClient3 := (rebaseChangeSets [ChangeClient3_1; ChangeClient3_2] (ChangesFromClient1 ○ RebasedChangesFromClient2)).
Definition RebasedChangesFromClient3 := (nth 0 rebasedChangesClient3 ⦻) ○ (nth 1 rebasedChangesClient3 ⦻).

Eval compute in applyChangeSet "" (BaseChange ○ ChangesFromClient1 ○ RebasedChangesFromClient2 ○ RebasedChangesFromClient3).

Definition rebasedWithInverse := (rebaseChangeSets [RebasedChangesFromClient2; RebasedChangesFromClient3] (ChangesFromClient1⁻¹)).
Eval compute in applyChangeSet "" (BaseChange ○ (nth 0 rebasedWithInverse ⦻) ○ (nth 1 rebasedWithInverse ⦻)).*)


