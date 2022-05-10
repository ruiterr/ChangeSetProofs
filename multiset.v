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
(*Add LoadPath "/Users/ruiterr/work/fluid/ChangeSetProofs" as ChangeSets.*)
Require Import NatHelper.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Require Import
  Coq.FSets.FMapFacts.

Module Import M := FMapList.Make(Nat_as_OT).
Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Inductive multiset :=
  | mset (X: M.t nat)
.

Definition empty_MultiSet :=
  (mset (M.empty nat)).

Definition ms_insert (i: nat) (ms: multiset) := 
  let (map) := ms in
  let entry := (M.find i map) in
  match entry with 
    | Some n =>
      (mset (M.add i (n + 1) map))
    | None =>
      (mset (M.add i 0 map))
end.

Definition ms_remove (i: nat) (ms: multiset) := 
  let (map) := ms in
  let entry := (M.find i map) in
  match entry with 
    | Some n => if (0 <? n) then
        (mset (M.add i (n - 1) map))
      else
        (mset (M.remove i map))
    | None =>
      (mset map)
end.

Definition ms_contains (i: nat) (ms: multiset) := 
  let (map) := ms in
  let entry := (M.find i map) in
  match entry with 
    | Some n =>
      true
    | None =>
      false
end.

Lemma duplicated_map_add: ∀(m: M.t nat) (i x y:nat), (Equal (add i x (add i y m)) (add i x m)).
unfold Equal.
intros.
destruct (i =? y0) eqn:H_ineqy0.
- apply beq_nat_true in H_ineqy0.
  repeat rewrite P.F.add_eq_o; auto.
- apply beq_nat_false in H_ineqy0.
  repeat rewrite P.F.add_neq_o; auto.
Qed.

Inductive Operation :=
  | Insert (s : M.t nat)
  | Remove (s : M.t nat).

Definition op1 := (Insert (add 1 5 (M.empty nat))).
Definition op2 := (Insert (add 1 5 (add 1 3 (M.empty nat)))).

(*Lemma test_op1_op2: op1 = op2.
unfold op1.
unfold op2.
f_equal.
rewrite duplicated_map_add.*)

Lemma test_lemma: (Equal (remove 1 (add 1 5 (add 1 3 (M.empty nat)))) (remove 1 (add 1 5 (M.empty nat)))).
rewrite duplicated_map_add.
reflexivity.
Qed.

Lemma duplicated_add: ∀(m: M.t nat) (i x y:nat), (add i x (add i y m)) = (add i x m).
intros.
unfold add.
set (this:= Raw.add i x (this {| this := Raw.add i y (this m); sorted := Raw.add_sorted (sorted m) i y |})).
set (sorted := Raw.add_sorted (sorted {| this := Raw.add i y (M.this m); sorted := Raw.add_sorted (sorted m) i y |}) i x).

assert( sorted = (Raw.add_sorted (M.sorted m) i x) ). give_up.
assert( this = Raw.add i x (M.this m)). give_up.

unfold Raw.add.
destruct m.
destruct this0 eqn:H_this0.
cbn.

assert( ∃x, (Nat_as_OT.compare i i) = (EQ x)). give_up.
destruct H.
set (t:=Nat_as_OT.compare i i).
fold t in H.
Check (Raw.add_sorted (Raw.add_sorted sorted0 i y) i x).
rewrite H at 1.
 
destruct (Nat_as_OT.compare i i).
(* assert(∀(x0 y0:nat), x0 = y0 → (Nat_as_OT.compare x0 y0) = (EQ (nat_compare_eq x0 y0))). *)
cbv delta [Nat_as_OT.compare].
cbv beta.
rewrite Nat.compare_refl with (x:=i).

set (t:= (i ?= i)).
assert(t=Eq).
subst t.
auto.
unfold t at 3.
unfold t at 3.
unfold t at 3.
unfold t at 3.
unfold t at 2.
simpl. 
rewrite H.
rewrite Nat.compare_refl with (x:=i) at 1.

Lemma multiset_insert_remove: ∀(ms:multiset) (i:nat), (ms_remove i (ms_insert i ms)) = ms.
intros.
unfold ms_remove.
unfold ms_insert.
destruct ms as [map].
destruct (find (elt:=nat) i map) eqn:H_map.
rewrite P.F.add_eq_o; auto.
rewrite_nat_all (0 <? n + 1 = true).
rewrite Nat.add_sub.
f_equal.
unfold @eq.

Eval compute in (
  (ms_contains 1
  (ms_remove 1
  (ms_remove 1
  (ms_insert 1
  (ms_insert 1 empty_MultiSet)))))
).