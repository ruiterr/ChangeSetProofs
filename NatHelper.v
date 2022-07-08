From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
Require Coq.Structures.OrdersFacts.
Require Import Unicode.Utf8.
Require Import Lia.

#[export] Hint Rewrite Nat.eqb_eq : nat_bool.
#[export] Hint Rewrite Nat.eqb_neq : nat_bool.
#[export] Hint Rewrite Nat.ltb_nlt : nat_bool.
#[export] Hint Rewrite Nat.ltb_lt : nat_bool.
#[export] Hint Rewrite Nat.leb_nle : nat_bool.
#[export] Hint Rewrite Nat.leb_le : nat_bool.
(*#[export] Hint Rewrite nat_compare_eq using easy : nat_bool.
#[export] Hint Rewrite nat_compare_Gt_gt using easy : nat_bool.
#[export] Hint Rewrite nat_compare_Lt_lt using easy : nat_bool.*)


Lemma bool_eq_symmetry_true: ∀ (b:bool), true = b -> b = true.
auto.
Qed.
Lemma bool_eq_symmetry_false: ∀ (b:bool), false = b -> b = false.
auto.
Qed.

(*Hint Rewrite bool_eq_symmetry_true : nat_bool.
Hint Rewrite bool_eq_symmetry_false : nat_bool.*)


Ltac rewrite_nat :=
  (* Normalize position of boolean in hypothesises *)
  repeat repeat match goal with
  |  H : true = _
  |- _ => symmetry in H
  end;
  repeat repeat match goal with
  |  H : false = _
  |- _ => symmetry in H
  end;

  (* Normalize position of boolean in goal *)
  try match goal with
  |- false = _ => symmetry
  end;
  try match goal with
  |- true = _ => symmetry
  end;

  (* Perform automatic rewriting to eliminate boolean comparisons *)
  autorewrite with nat_bool in *.

Ltac solve_nat :=
 rewrite_nat; lia.

Ltac assert_nat exp :=
  assert exp; only 1: solve_nat.

Ltac assert_nat_name exp name :=
  assert exp as name; only 1: solve_nat.

Ltac rewrite_nat_all exp :=
  let a := fresh in 
  assert exp as a; only 1: solve_nat;
  rewrite a in *;
  clear a.

Tactic Notation "assert_nat" constr(exp) := assert_nat exp.
Tactic Notation "assert_nat" constr(exp) "as" ident(name) := assert_nat_name exp name.

Create HintDb solve_nat.
#[export]
Hint Extern 4 (true = (_ <? _) ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 (false = (_ <? _) ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 (true = (_ <=? _) ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 (false = (_ <=? _) ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 (true = (_ =? _) ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 (false = (_ =? _) ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 ((_ <? _) = true ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 ((_ <? _) = false) => solve_nat : solve_nat.
#[export]
Hint Extern 4 ((_ <=? _) = true ) => solve_nat : solve_nat.
#[export]
Hint Extern 4 ((_ <=? _) = false) => solve_nat : solve_nat.
#[export]
Hint Extern 4 ((_ =? _) = true) => solve_nat : solve_nat.
#[export]
Hint Extern 4 ((_ =? _) = false) => solve_nat : solve_nat.

(*Lemma test: ∀ (n m: nat), true = (n =? m + 5) ∧ true = (n - 5 =? m) → true = (m <? n).
intros.
destruct H as [H1 H2].

auto with solve_nat.


assert_nat ((m <> n)) as H_test.
rewrite_nat.
autorewrite with nat_bool in *. *)