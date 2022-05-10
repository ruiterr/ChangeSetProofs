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

Notation "a ⁻¹ᵒ" := (invertOperation a) (at level 55, no associativity, format "a '⁻¹ᵒ'").


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
  | CSet (ops: list Operation).

Definition applyChangeSet (str:string) (cs: ChangeSet) := 
  let (ops) := cs in 
  (fold_left applyOperation ops str).

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

Definition squash (a b : ChangeSet) :=
  let (opsA) := a in 
  let (opsB) := b in 
  (CSet (squashOpList opsA opsB)).

Infix "○" := squash (at level 60).

(* Invert operation *)
Definition invert (a: ChangeSet) := 
  let (opsA) := a in
  (CSet (map invertOperation (rev opsA))).

Notation "a ⁻¹" := (invert a) (at level 55, no associativity, format "a '⁻¹'").

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
Eval compute in (testInsertCS ○ testInsertCS⁻¹).


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

Infix "↷ₒ" := rebaseOperation (at level 57, no associativity).

Eval compute in (((Some (Insert 0 1 "a" 0 [1])) ↷ₒ (Some (Remove 1 1 "a" 0 []))) ↷ₒ (Some (Insert 1 1 "a" 0 [])) ).
Eval compute in (((Some (Insert 0 1 "a" 0 [1])) ↷ₒ (Some (Remove 1 1 "a" 0 [])))).
Eval compute in ((Some (Insert 0 1 "a" 0 [1; 1])) ↷ₒ (Some (Insert 1 1 "a" 0 [])) ).

Eval compute in (remove Nat.eq_dec 1 [1;1]).
Eval compute in (((Some (Insert 0 3 "a" 0 [])) ↷ₒ (Some (Insert 1 1 "a" 0 []))) ↷ₒ (Some (Remove 1 1 "a" 0 [])) ).


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

Lemma rebaseOperatrionLeftDistibutivity: ∀(A B: Operation), ((((Some A) ↷ₒ (Some B)) ↷ₒ (Some (B⁻¹ᵒ))) = (Some A) ∨
                                          (((Some A) ↷ₒ (Some B)) ↷ₒ (Some (B⁻¹ᵒ))) = None).
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

all: try match goal with 
  | [ |- context[existsb (λ x : nat, x =? ?Y) (remove Nat.eq_dec ?Y ?X)]] => 
    destruct (existsb (λ x : nat, x =? Y) (remove Nat.eq_dec Y X))
end.

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

all: try match goal with 
  | [ |- context[existsb (λ x : nat, x =? ?Y) (remove Nat.eq_dec ?Y ?X)]] => 
    destruct (existsb (λ x : nat, x =? Y) (remove Nat.eq_dec Y X));
    try try_solve
end.

all: destruct (p <? p0 -1) eqn:H_pGtp0; rewrite Nat.sub_add; try lia; auto.
Qed.



Eval compute in (((Some (Insert 0 3 "a" 0 [])) ↷ₒ (Some (Insert 1 1 "a" 0 [])))).

Eval compute in (((Some (Insert 0 3 "a" 0 [])) ↷ₒ (Some (Insert 1 1 "a" 0 []))) ↷ₒ (Some (Remove 1 1 "a" 0 [])) ).

Eval compute in (negb (p0 =? p)).
Eval compute in (((Some (Insert 0 1 "a" 0 [1])) ↷ₒ (Some (Remove 1 1 "a" 0 []))) ↷ₒ (Some (Insert 1 1 "a" 0 [])) ).
Eval compute in (((Some (Insert 0 1 "a" 0 [1])) ↷ₒ (Some (Remove 1 1 "a" 0 [])))).

Eval compute in (remove Nat.eq_dec 1 [1;1]).

assert ( (if (Nat.eq_dec i i) then A else B) = A).
Check (Nat.eq_dec i i).
autorewrite with solve_rebase.

try match goal with 
  | [ |- context[?X + 1 =? ?Y]] => 
    idtac X
end.

all: repeat (
  autorewrite with solve_rebase;
  try rewrite H_pltP0;
  try rewrite H_p0ltP;
  try rewrite H_iCmpi0;
  try rewrite H_p0ltP;
  try rewrite H_p0eqP;
  try rewrite H_pltP0;
  try rewrite H_iCmpi0;
  try unfold negb;
  try simpl;
  auto
).

all: destruct (c =? 0)%Z eqn:H_cEqC0.

all: repeat (
  autorewrite with solve_rebase;
  try rewrite H_pltP0;
  try rewrite H_p0ltP;
  try rewrite H_iCmpi0;
  try rewrite H_p0ltP;
  try rewrite H_p0eqP;
  try rewrite H_pltP0;
  try rewrite H_iCmpi0;
  try unfold negb;
  try simpl;
  auto
).

all: destruct (existsb (λ x : nat, x =? i) s0) eqn:H_iInS0.
all: repeat (
  autorewrite with solve_rebase;
  try rewrite H_pltP0;
  try rewrite H_p0ltP;
  try rewrite H_iCmpi0;
  try rewrite H_p0ltP;
  try rewrite H_p0eqP;
  try rewrite H_pltP0;
  try rewrite H_iCmpi0;
  try rewrite H_iInS0;
  try unfold negb;
  try simpl;
  auto
).
all: destruct ((p0 + 1) =? p) eqn:H_p0Plus1Eqp.
all: destruct (p <? p0+1) eqn:H_pLtpPlus1Eqp.

all: repeat (
  autorewrite with solve_rebase;
  try rewrite H_pltP0;
  try rewrite H_p0ltP;
  try rewrite H_iCmpi0;
  try rewrite H_p0ltP;
  try rewrite H_p0eqP;
  try rewrite H_pltP0;
  try rewrite H_iCmpi0;
  try rewrite H_iInS0;
  try unfold negb;
  try simpl;
  auto
).

(* try rewrite Nat.eqb_refl.
try rewrite Nat.eqb_refl.
try rewrite Nat.ltb_irrefl.*)
unfold negb.
simpl.
rewrite H_pltP0.
rewrite H_p0ltP.
rewrite H_iCmpi0.
rewrite H_p0ltP.
rewrite H_p0eqP.
simpl.
rewrite H_pltP0.
rewrite H_iCmpi0.
rewrite Z.add_simpl_r.
auto.
crush.

all: destruct ( (Nat.eqb p p) ) eqn:H_pEqp.
all: destruct ( (Nat.eqb i i) ) eqn:H_iEqi.
assert ( (Nat.eqb p p) = true). auto with solve_nat.
assert ( (Nat.eqb i i) = true). auto with solve_nat.
assert ( (Nat.ltb p p) = false). auto with solve_nat.
simpl.
rewrite ->H1.
destruct B.
destruct ( (p0<?p)).
destruct ( (c0 =? 0)%Z).
- auto.
destrcut 

Close Scope nat.

