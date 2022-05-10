From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Arith.PeanoNat.
Require Coq.Structures.OrdersFacts.
Require Import Unicode.Utf8.
Require Import Coq.Program.Wf.
Require Import Lia.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Require Import
  Coq.FSets.FMapFacts.

Inductive test :=
  | Zero
  | Next (n : nat) (prev : test).

Print test.

Inductive test2 :=
  | Zero2 : test2
  | Next2 : nat -> test2->test2.

Require Export SetoidList Morphisms OrdersTac.
Set Implicit Arguments.

(** NB: This file is here only for compatibility with earlier version of
     [FSets] and [FMap]. Please use [Structures/Orders.v] directly now. *)

(** * Ordered types *)

Inductive Compare (X : Type) (lt eq : X -> X -> Prop) (x y : X) : Type :=
  | LT : lt x y -> Compare lt eq x y
  | EQ : eq x y -> Compare lt eq x y
  | GT : lt y x -> Compare lt eq x y.

Arguments LT [X lt eq x y] _.
Arguments EQ [X lt eq x y] _.
Arguments GT [X lt eq x y] _.

Print test2.

Check nat_compare_eq.


Definition TestCompare := Compare Nat.lt Nat.eq.


Definition compare x y : Compare lt eq x y.
Proof.
  case_eq (Nat.compare x y); intro.
  - apply EQ. now apply nat_compare_eq.
  - apply LT. now apply nat_compare_Lt_lt.
  - apply GT. now apply nat_compare_Gt_gt.
Defined.

Print compare.
Print eq_refl.

Eval compute in (compare 0 0).
Print eq_refl.
Check ((nat_compare_eq 0 0 (@eq_refl comparison Eq))).
Check (@eq_refl comparison Eq).

Print compare.
Print eq_refl.


Definition test3 := fun (x y : nat) (z : comparison) =>
(match Nat.compare x y as c return (forall _ : @eq comparison (Nat.compare x y) c, @Compare nat lt (@eq nat) x y) with
 | Eq => fun H : @eq comparison (Nat.compare x y) Eq => @EQ nat lt (@eq nat) x y (nat_compare_eq x y H)
 | Lt => fun H : @eq comparison (Nat.compare x y) Lt => @LT nat lt (@eq nat) x y (nat_compare_Lt_lt x y H)
 | Gt => fun H : @eq comparison (Nat.compare x y) Gt => @GT nat lt (@eq nat) x y (nat_compare_Gt_gt x y H)
 end).
Check test3.

Lemma test_eq: ∀(i:nat), (match (i ?= i) with
          | Eq => 1
          | Lt => 2
          | Gt => 3
        end) = 1.
intros.
remember (i ?= i) as t.
rewrite Nat.compare_refl in Heqt.
rewrite Heqt.
reflexivity.
Qed.
Print test_eq.

(*Inductive Le : nat -> nat -> Set :=
     | LeO : forall n:nat, Le 0 n
     | LeS : forall n m:nat, Le n m -> Le (S n) (S m).

Parameter P : nat -> nat -> Prop.

Goal forall n m:nat, Le (S n) m -> P n m.

intros n m H.

generalize_eqs H.*)

Lemma compareEq2: ∀(i j : nat), (i = j ) → ∃(H : (eq i j)), (compare i j) = (EQ H).
intros.
case (compare i j).
- intros. lia.
- intros. exists e. reflexivity.
- intros. lia.
Qed.

Eval compute in (Nat.compare_refl 0). 

Lemma compareEq: ∀(i : nat),  ∃(H : (eq i i)), (compare i i) = (EQ H).
intros.
case (compare i i).
- intros. lia.
- intros. exists e. reflexivity.
- intros. lia.
Qed.

Lemma testEq: ∀i:nat, (match (compare i i) with
  | EQ _ => 1 
  | LT _ => 2 
  | GT _ => 3
end = 1).
intros.

specialize compareEq with (i:=i).
destruct H.
rewrite H.
reflexivity.
Qed.

Lemma compareEq: ∀(i : nat), (compare i i) = (EQ (nat_compare_eq i i (Nat.compare_refl i))).
intros.
case (compare i i).
- intros. lia.
- intros. 
- intros. lia.

unfold compare.
elim_comp.

dep_destruct (i ?= i).


cbv beta.


refine ( (match (i ?= i) as c return (_) with
          | Eq => _
          | Lt => _
          | Gt => _
        end) _ = _).
- intros.
  rewrite x.

(*inversion t.*)
(*remember (i ?= i) as t.*)
(*dependent destruction t.*)
(*2: {
  rewrite H in x.
  inversion x.
}
2: {
  rewrite H in x.
  inversion x.
}
inversion t0.*)

set (EqBranch:=λ H0 : (i ?= i) = Eq, EQ (nat_compare_eq i i H0)).
set (LtBranch:=λ H0 : (i ?= i) = Lt, LT (nat_compare_Lt_lt i i H0)).
set (GtBranch:=fun H0 : @eq comparison (Nat.compare i i) Gt => @GT nat lt (@eq nat) i i (nat_compare_Gt_gt i i H0)).

(*set (t:=(i ?= i)).
fold t in EqBranch.
fold t in LtBranch.
fold t in GtBranch.*)
set (u := match i ?= i as c return ((i ?= i) = c → Compare lt eq i i) with
| Eq => EqBranch
| Lt => LtBranch
| Gt => GtBranch
end).
assert (u = EqBranch).

Lemma eq3and3: 3 = 3.
reflexivity.
Qed.

Print eq3and3.

Definition test_fun (i j:nat) := match (compare i j) with
  | EQ _ => 1
  | LT _ => 2
  | GT _ => 3
end.
Print EQ.
Eval compute in (test_fun 5 5).

Check (Compare nat Nat.lt Nat.eq).
