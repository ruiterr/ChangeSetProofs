From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Logic.ProofIrrelevance.
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

Lemma Equal_ProofIrrelevance: ∀(A B: M.t nat), (Equal A B) → A = B.
intros.
unfold Equal in H.
destruct A.
destruct B.
assert (this0 = this1). {
  induction this0.
  - assert (∀ y, (find (elt:=nat) y {| this := []; sorted := sorted0 |}) = None). {
      intros.
      auto.
    }
    destruct this1.
    + auto.
    + contradict H.
      intuition.
      destruct p as [p_k p_v].
      specialize H with (y:=p_k).
      rewrite H0 in H.
      assert ((find (elt:=nat) p_k
       {| this := (p_k, p_v) :: this1; sorted := sorted1 |}) = Some p_v). {
        unfold find.
        unfold Raw.find.
        simpl.
        specialize Raw.MX.elim_compare_eq with (x:=p_k) (y:=p_k) as H_EQ.
        destruct H_EQ; auto.
        now rewrite H1.
      }
      rewrite H1 in H.
      discriminate.
  - destruct this1.
    + destruct a as [a_k a_v].
      specialize H with (y:=a_k).
      assert ((find (elt:=nat) a_k
       {| this := (a_k, a_v) :: this0; sorted := sorted0 |}) = Some a_v). {
        unfold find.
        unfold Raw.find.
        simpl.
        specialize Raw.MX.elim_compare_eq with (x:=a_k) (y:=a_k) as H_EQ.
        destruct H_EQ; auto.
        now rewrite H0.
      }
      rewrite H0 in H. clear H0.
      assert ((find (elt:=nat) a_k {| this := []; sorted := sorted1 |}) = None). {
        intros.
        auto.
      }
      rewrite H0 in H.
      discriminate.
    + assert (a = p). {
        destruct 
    

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

assert(∀s,(Raw.add i x
      {|
        this := Raw.add i y m;
        sorted := s
      |}) = (Raw.add i x m)). {
  intros.
  destruct m.
  induction this0.
  - unfold Raw.add.
    simpl.
    specialize Raw.MX.elim_compare_eq with (x:=i) (y:=i) as H_EQ.
    destruct H_EQ; auto.
    now rewrite H.
  - unfold Raw.add.
    simpl.
    destruct a as [p_k p_v].
    destruct (Nat_as_OT.compare i p_k) eqn:H_k'.
    + rewrite H_k'.
      specialize Raw.MX.elim_compare_eq with (x:=i) (y:=i) as H_EQ.
      destruct H_EQ; auto.
      now rewrite H.
    + specialize Raw.MX.elim_compare_eq with (x:=i) (y:=i) as H_EQ.
      destruct H_EQ; auto.
      now rewrite H.
    + rewrite H_k'.
      f_equal.

      assert(Sorted (Raw.PX.ltk (elt:=nat)) this0) as H_sortedThis0. {
        apply Sorted_inv in sorted0 as sorted_tail.
        now destruct sorted_tail.
      }
      assert(Sorted (Raw.PX.ltk (elt:=nat)) (Raw.add i y {| this := this0; sorted := H_sortedThis0 |})) as H_sorted_sTail. {
        apply Raw.add_sorted.
        auto.
      }


      match goal with 
      | |- (_  _ _ ?t1) = ?t2 => set (inner:=t1); set (rhs:=t2)
      end.
      assert(rhs = Raw.add i x {| this := this0; sorted := H_sortedThis0 |}). {
        intros.
        unfold rhs.
        unfold Raw.add.
        now simpl.
      }

      assert(inner = Raw.add i y
                       {| this := this0; sorted := H_sortedThis0 |}). {
        intros.
        unfold inner.
        unfold Raw.add.
        now simpl.
      }
      rewrite H.
      rewrite H0.


      specialize IHthis0 with (sorted0 := H_sortedThis0) (s:=H_sorted_sTail).
      rewrite <-IHthis0.
      auto.
  }

  set (inner:=Raw.add i x
      {|
        this := Raw.add i y m;
        sorted := Raw.add_sorted (sorted m) i y
      |}).
  assert (inner = (Raw.add i x m)). {
    unfold inner.
    now rewrite H.
  }

  generalize (Raw.add_sorted
      (sorted
         {|
           this := Raw.add i y m;
           sorted := Raw.add_sorted (sorted m) i y
         |}) i x).
  fold inner.
  rewrite H0.
  generalize (Raw.add_sorted (sorted m) i x).
  intros.
  replace s with s0; auto.
  apply proof_irrelevance.
Qed.

Lemma multiset_insert_remove: ∀(ms:multiset) (i:nat), (ms_remove i (ms_insert i ms)) = ms.
intros.
unfold ms_remove.
unfold ms_insert.
destruct ms as [map].
destruct (find (elt:=nat) i map) eqn:H_map.
- rewrite P.F.add_eq_o; auto.
  rewrite_nat_all (0 <? n + 1 = true).
  rewrite Nat.add_sub.
  f_equal.
  rewrite duplicated_add with (m:=map) (i:=i) (x:=n) (y:=n+1).
  give_up.
- rewrite F.add_eq_o; auto.
  assert_nat(0<?0=false).
  rewrite H.
rewrite H_map.
unfold @eq.

Eval compute in (
  (ms_contains 1
  (ms_remove 1
  (ms_remove 1
  (ms_insert 1
  (ms_insert 1 empty_MultiSet)))))
).