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

Definition invertOperationOption (op: option Operation) := 
match op with
  | Some o =>
    match o with
      | Insert i p e c s => Some (Remove i p e c s)
      | Remove i p e c s => Some (Insert i p e c s)
    end
  | None => None
end.

Declare Scope Operation.
Declare Scope OptionOperation.
Declare Scope ChangeSet.
Delimit Scope Operation with O.
Delimit Scope OptionOperation with OO.
Delimit Scope ChangeSet with CS.

Notation "a ⁻¹" := (invertOperation a) (at level 55, no associativity, format "a '⁻¹'") : Operation.
Notation "a ⁻¹" := (invertOperationOption a) (at level 55, no associativity, format "a '⁻¹'") : OptionOperation.


Scheme Equality for OperationType.

Definition Op_eqb (a : Operation) (b: Operation) := 
  (eqOpType (getOperationType a) (getOperationType b)) &&
  (Nat.eqb (getOpI a) (getOpI b)) &&
  (Nat.eqb (getOpP a) (getOpP b)) &&
  (Ascii.eqb (getOpE a) (getOpE b)) &&
  (Z.eqb (getOpC a) (getOpC b)) &&
  (list_beq nat Nat.eqb (getOpS a) (getOpS b)).



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
Inductive ChangeSet :=
  | CSet (ops: list Operation)
  | InvalidCSet.

Definition applyChangeSet (str:string) (cs: ChangeSet) := match cs with 
  | CSet ops =>
    (fold_left applyOperation ops str)
  | InvalidCSet =>
    str
end.

(* Squash Operation *)
Fixpoint squashOpList (opsA opsB: list Operation) {struct opsB} := 
  match opsA, opsB with
    | [], _ => opsB
    | _, [] => opsA
    | _, hdB :: tailB => 
        let lastA := (last opsA (Insert 0 0 "a" 0 [])) in 
        if (Op_eqb lastA (invertOperation(hdB))) then
          (squashOpList (removelast opsA) tailB)
        else
          (opsA ++ opsB)
end.

Definition squash (a b : ChangeSet) := match a, b with 
    | CSet opsA, CSet opsB => (CSet (squashOpList opsA opsB))
    | _, _ => InvalidCSet
end.


Infix "○" := squash (at level 60).

(* Invert operation *)
Definition invert (a: ChangeSet) := match a with 
    | CSet opsA => (CSet (map invertOperation (rev opsA)))
    | _ => InvalidCSet
end.

Notation "a ⁻¹" := (invert a) (at level 55, no associativity, format "a '⁻¹'") : ChangeSet.

(* Helper function to create ChangeSets for ranges *)
Definition InsertRange (i: nat) (p: nat) (t: string) := 
  (CSet (fst (fold_left (fun (x : ((list Operation) * nat)) (y : ascii) => (
      (fst x) ++ [ (Insert (i + (snd x)) (p + (snd x)) y 0 []) ], 
      (snd x) + 1 )
    ) (list_ascii_of_string t) ([], 0)))).

Definition RemoveRange (i:nat) (p:nat) (l:nat) (str: string) :=
  (CSet (fst (fold_left (fun (x : ((list Operation) * nat)) (y : ascii) => (
      (fst x) ++ [ (Remove (i + (snd x)) p y 0 []) ], 
      (snd x) + 1 )
    ) (list_ascii_of_string (substring p l str)) ([], 0)))).

Eval compute in (InsertRange 0 5 "test").
Eval compute in (RemoveRange 0 2 2 "test").
 
Eval compute in (applyChangeSet "Hello World" (InsertRange 0 6 "cruel ")).
Eval compute in (applyChangeSet "Hello cruel World" (RemoveRange 0 6 6 "Hello cruel World")).

Eval compute in (squash (InsertRange 0 6 "cruel ") (RemoveRange 0 6 6 "Hello cruel World")).
Eval compute in (applyChangeSet "Hello World" ( (InsertRange 0 6 "cruel ") ○ (RemoveRange 0 6 6 "Hello cruel World"))).

Definition testInsertCS := (InsertRange 0 6 "cruel ").
Eval compute in (testInsertCS ○ testInsertCS⁻¹)%CS.


Eval compute in (applyChangeSet "test" (CSet [(Insert 0 1 "-" 0 []); (Remove 0 2 "e" 0 [])])).

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
  | CSet ops => match (fold_left rebaseOperation ((map (λ x:Operation, Some x)) ops) (Some a)) with
                  | Some result => (CSet [result])
                  | None => InvalidCSet
                end
  | InvalidCSet => InvalidCSet
end.

Fixpoint rebaseChangeSetOps (a : list Operation) (b : ChangeSet) {struct a}:= 
    match a with
      | [] => match b with 
        | CSet _ => (CSet [])
        | InvalidCSet => InvalidCSet
        end
      | [opA] => (rebaseOperationWithChangeSet opA b)
      | opA::Atail => 
           let csA := (CSet [opA]) in 
           let csA' := (CSet Atail) in 
           let R1 := (rebaseOperationWithChangeSet opA b) in 
           let R2 := (rebaseChangeSetOps Atail (csA⁻¹ ○ b ○ R1)%CS ) in 
           (R1 ○ R2)%CS
  end.

Definition rebaseChangeSet (a b : ChangeSet) := match a with 
    | CSet opsA => (rebaseChangeSetOps opsA b) 
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

  Notation "⊘" := (CSet []).
  Notation "⦻" := InvalidCSet.

  Open Scope CS.
  Lemma rebaseWithInvalid1: ∀X, (X ↷ ⦻) = ⦻.
    intros.
    unfold rebaseChangeSet.
    destruct X; auto.
    unfold rebaseChangeSetOps.
    induction ops.
    - auto.
    - destruct ops.
      + unfold rebaseOperationWithChangeSet; auto.
      + unfold rebaseOperationWithChangeSet. unfold squash. auto.
  Qed.

  Lemma rebaseWithInvalid2: ∀X, (⦻ ↷ X) = ⦻.
    intros.
    now unfold rebaseChangeSet.
  Qed.

  Lemma squashEmptyLeft:  ∀X, ⊘ ○ X  = X.
  intros.
  unfold squash.
  destruct X; auto.
  unfold squashOpList.
  f_equal.
  induction ops; auto.
  Qed.

  Lemma squashEmptyRight: ∀X, X ○ ⊘  = X.
  intros.
  unfold squash.
  destruct X; auto.
  unfold squashOpList.
  f_equal.
  induction ops; auto.
  Qed.

  Lemma opInvertInvolution: ∀ op:Operation, ((op⁻¹)⁻¹) % O = op.
  intros.
  destruct op.
  all: now cbv.
  Qed.

  Lemma cons_to_app: ∀(X:Type) (a : X) (l:list X), a::l = [a] ++ l.
  intros.
  now unfold app.
  Qed.

  Lemma list_neq_beq_refl: ∀(l: list nat), (list_beq nat Nat.eqb l l) = true.
  intros.
  unfold list_beq.
  induction l; auto.
  rewrite IHl.
  now rewrite Nat.eqb_refl.
  Qed.

  Lemma Op_eqb_refl: ∀ op, Op_eqb op op = true.
  intros.
  unfold Op_eqb.
  destruct op.
  all: (
    cbn;
    repeat rewrite Nat.eqb_refl;
    repeat rewrite Z.eqb_refl;
    repeat rewrite Ascii.eqb_refl;
    now repeat rewrite list_neq_beq_refl
  ).
  Qed.

  Lemma squashInverseLeft: ∀X, X ≠ ⦻ → X ○ X⁻¹  = ⊘.
  intros.
  unfold squash.
  destruct X; try contradiction.
  simpl.
  f_equal.
  unfold squashOpList.
  rewrite <-rev_involutive with (l:=ops).
  set (t:=(rev ops)) in *.
  induction t.
  - rewrite rev_involutive.
    unfold map. 
    now unfold rev at 1.
  - rewrite rev_involutive.
    rewrite map_cons.
    destruct (rev (a :: t)) eqn:H_ops.
    + contradict H_ops.
      rewrite cons_to_app.
      rewrite rev_app_distr.
      unfold rev at 2.
      rewrite app_nil_l.
      auto with datatypes.
    + rewrite opInvertInvolution.
      rewrite <-H_ops.
      rewrite cons_to_app at 1.
      rewrite rev_app_distr.
      unfold rev at 2.
      rewrite app_nil_l.
      rewrite last_last.
      rewrite Op_eqb_refl.
      rewrite cons_to_app.
      rewrite rev_app_distr.
      unfold rev at 2.
      rewrite app_nil_l. 
      rewrite removelast_last.
      rewrite rev_involutive in IHt.
      rewrite IHt; auto.
  Qed.

  Lemma changeSetInvertInvolution: ∀ X:ChangeSet, (X⁻¹)⁻¹ = X.
  intros.
  unfold invert.
  destruct X; auto.
  rewrite <-map_rev.
  rewrite rev_involutive.
  f_equal.
  induction ops.
  - now cbv.
  - do 2 rewrite map_cons.
    rewrite opInvertInvolution.
    now rewrite IHops.
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

  Lemma rebaseEmptyLeft: ∀X, X ≠ ⦻ → ⊘ ↷ X  = ⊘.
  intros.
  cbn.
  destruct X; auto.
  contradiction.
  Qed.

  Lemma rebaseOperationEmpty: ∀op:Operation, (rebaseOperationWithChangeSet op ⊘) = (CSet [op]).
  intros.
  unfold rebaseOperationWithChangeSet.  
  unfold fold_left. 
  now simpl.
  Qed.
  
  Create HintDb changeset_simplificaton.
  Hint Rewrite squashEmptyLeft : changeset_simplificaton.
  Hint Rewrite squashEmptyRight : changeset_simplificaton.
  Hint Rewrite squashInverseLeft : changeset_simplificaton.
  Hint Rewrite squashInverseRight : changeset_simplificaton.
  Hint Rewrite rebaseOperationEmpty : changeset_simplificaton.
  Hint Rewrite rebaseEmptyLeft : changeset_simplificaton.
  Hint Rewrite rebaseOperationEmpty : changeset_simplificaton.

  Lemma rebaseEmptyRight: ∀X, X ≠ ⦻ → X ↷ ⊘  = X.
  intros.
  unfold rebaseChangeSet.
  destruct X; auto.
  unfold rebaseChangeSetOps.
  induction ops; auto.
  destruct ops.
  - unfold rebaseOperationWithChangeSet. 
    unfold fold_left. cbn. auto.
  - 
    autorewrite with changeset_simplificaton in *.
    rewrite IHops.
    all: try discriminate.
    unfold squash.
    unfold squashOpList.
    unfold last.
    (* TODO: Within a changeset there are no adjacent inverse operations in the list *)
    assert (Op_eqb a (o⁻¹)%O = false). give_up.
    rewrite H0.
    auto with *.
  Admitted.

  Lemma fold_left_rebaseOperation_squashOpList: ∀ (a:Operation) (ops0 ops1: list Operation),
    fold_left rebaseOperation (map (λ x : Operation, (Some x)) (squashOpList ops0 ops1)) (Some a) = 
    fold_left rebaseOperation ((map (λ x : Operation, (Some x)) ops0) ++ (map (λ x : Operation, (Some x)) ops1)) (Some a).
  Admitted.

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

  Lemma rebaseLeftDistibutivity: A ↷ (B ○ C)  = A ↷ B ↷ C.
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
          
           
  Lemma rebaseRightDistibutivity: (A ○ B) ↷ C  = sA ∨
                                          sA ↷ sB ↷ sB⁻¹ = None.


Check rebaseOperatrionRightDistibutivity.
Close Scope nat.