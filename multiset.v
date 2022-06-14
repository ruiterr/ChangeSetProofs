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


Lemma keySmallerFindEqNone: ∀y_k y_v t0, (  HdRel (Raw.PX.ltk (elt:=nat)) (y_k, y_v) t0) → (Sorted (Raw.PX.ltk (elt:=nat)) t0) → (Raw.find (elt:=nat) y_k t0) = None.
  intros.
  induction t0.
  - now cbv.
  - apply Sorted_inv in H0 as H_sortedT0_2.
    destruct H_sortedT0_2 as [H_sortedT0_2 H_aLtT0].
    destruct a as [a_k a_v].
    apply HdRel_inv in H as H_yLtT0.
    cbv in H_yLtT0.
    specialize Raw.PX.MO.elim_compare_lt with (x:=y_k) (y:=a_k) as H_Tail.
    destruct H_Tail; try lia.
    simpl.
    now rewrite H1.
Qed.

Lemma keySmallerFindEqNoneSplit: ∀y_k (y_v:nat) p_k p_v t0, (y_k < p_k) → (Sorted (Raw.PX.ltk (elt:=nat)) ((p_k,p_v)::t0)) → (Raw.find (elt:=nat) y_k ((p_k,p_v)::t0)) = None.
  intros.
  apply Sorted_inv in H0 as H_sortedT0_2.
  destruct H_sortedT0_2 as [H_sortedT0_2 H_aLtT0].
  specialize Raw.PX.Inf_lt with (l:=t0) (x:=(y_k, y_v)) (x':=(p_k, p_v)) as H_HdRel.
  apply keySmallerFindEqNone with (y_v:=y_v).
  all: auto.
Qed.

Lemma Equal_ProofIrrelevance: ∀(A B: M.t nat), (Equal A B) → A = B.
intros.
unfold Equal in H.
destruct A.
destruct B.
assert (this0 = this1). {
  remember (length this0) as lenThis0.
  revert H.
  revert sorted0.
  revert sorted1.
  revert HeqlenThis0.
  revert this0.
  revert this1.
  induction lenThis0.
  - intros.
    symmetry in HeqlenThis0.
    apply length_zero_iff_nil in HeqlenThis0.
    rewrite HeqlenThis0.
    destruct this0 eqn:H_this0.
    2: { discriminate. }
    assert (∀ y, (find (elt:=nat) y {| this := []; sorted := sorted0 |}) = None). {
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
  - intros.
    destruct this0 eqn:H_this0.
    1: { discriminate. } 
    destruct this1.
    + destruct p as [a_k a_v].
      specialize H with (y:=a_k).
      assert ((find (elt:=nat) a_k
       {| this := (a_k, a_v) :: t0; sorted := sorted0 |}) = Some a_v). {
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
    + assert (p = p0). {
        destruct p as [p_k p_v].
        destruct p0 as [p0_k p0_v].
        destruct (p_k =? p0_k) eqn:H_p_kEqp0_k.
        2: {
          destruct (p_k <? p0_k) eqn:H_p_kltp0_k.
          - rewrite_nat.
            specialize H with (y:=p_k).

            assert (find (elt:=nat) p_k {| this := (p_k, p_v) :: t0; sorted := sorted0 |} = Some p_v) as H_findFirst. { 
              cbn.
              specialize Raw.MX.elim_compare_eq with (x:=p_k) (y:=p_k) as H_refl.
              destruct H_refl; auto.
              now rewrite H0.
            }
            rewrite H_findFirst in H.

            assert ((find (elt:=nat) p_k {| this := (p0_k, p0_v) :: this1; sorted := sorted1 |}) = None) as H_findSecond. {
              apply keySmallerFindEqNoneSplit; auto.
            }
            rewrite H_findSecond in H.
            discriminate.
         - assert_nat (p0_k < p_k) as H_p_kGt_p0.
            specialize H with (y:=p0_k).

            assert ((find (elt:=nat) p0_k {| this := (p0_k, p0_v) :: this1; sorted := sorted1 |}) = Some p0_v) as H_findFirst. { 
              cbn.
              specialize Raw.MX.elim_compare_eq with (x:=p0_k) (y:=p0_k) as H_refl.
              destruct H_refl; auto.
              now rewrite H0.
            }
            rewrite H_findFirst in H.

            assert ((find (elt:=nat) p0_k {| this := (p_k, p_v) :: t0; sorted := sorted0 |}) = None) as H_findSecond. { 
              apply keySmallerFindEqNoneSplit; auto.
            }
            rewrite H_findSecond in H.
            discriminate.
          }
          rewrite_nat.
          specialize H with (y:=p_k).
          rewrite <-H_p_kEqp0_k.

          assert ((find (elt:=nat) p_k {| this := (p_k, p_v) :: t0; sorted := sorted0 |}) = Some p_v) as H_findFirst. { 
            cbn.
            specialize Raw.MX.elim_compare_eq with (x:=p_k) (y:=p_k) as H_refl.
            destruct H_refl; auto.
            now rewrite H0.
          }
          rewrite H_findFirst in H.
          assert((find (elt:=nat) p_k {| this := (p0_k, p0_v) :: this1; sorted := sorted1 |}) = Some p0_v) as H_findSecond. {
            cbn.
            rewrite H_p_kEqp0_k.
            specialize Raw.MX.elim_compare_eq with (x:=p0_k) (y:=p0_k) as H_refl.
            destruct H_refl; auto.
            now rewrite H0.
          }
          rewrite H_findSecond in H.
          now inversion H.
      }
      rewrite <- H0 in *.
      apply Sorted_inv in sorted0 as H_sortedT0.
      destruct H_sortedT0 as [H_sortedT0 H_pLtT0 ].
      apply Sorted_inv in sorted1 as H_sortedThis1.
      destruct H_sortedThis1 as [H_sortedThis1 H_p0LtThis1 ].
      rewrite IHlenThis0 with (this0:=t0)  (this1:=this1) (sorted0:=H_sortedT0) (sorted1:=H_sortedThis1).
      * auto.
      * simpl in HeqlenThis0.
        lia.
      * intros.
        destruct p as [p_k p_v].
        destruct (y =? p_k) eqn:H_yEqp_k.
        ++ rewrite_nat.
          specialize H with (y:=p_k).
          rewrite H_yEqp_k.

          assert ((find (elt:=nat) p_k {| this := t0; sorted := H_sortedT0 |}) = None) as H_rewriteFirst. {
            apply keySmallerFindEqNone with (y_v:=p_v); auto.
          }
          rewrite H_rewriteFirst.

          assert ((find (elt:=nat) p_k {| this := this1; sorted := H_sortedThis1 |}) = None) as H_rewriteSecond. {
            rewrite <-H0 in H_p0LtThis1.
            apply keySmallerFindEqNone with (y_v:=p_v); auto.
          }
          now rewrite H_rewriteSecond.
        ++ rewrite_nat.
           cbn.
           destruct (Nat_as_OT.compare y p_k) eqn:H_compare.
           -- replace ((Raw.find (elt:=nat) y t0)) with (None : option nat).
              replace ((Raw.find (elt:=nat) y this1)) with (None : option nat); auto.
              all: (
                symmetry;
                apply keySmallerFindEqNone with (y_v:=0);
                auto
              ).
              ** apply Raw.PX.Inf_lt with (x:=(y, 0)) (x':=(p_k, p_v)); auto.
                 now rewrite H0.
              ** apply Raw.PX.Inf_lt with (x:=(y, 0)) (x':=(p_k, p_v)); auto.
          -- contradiction.
          -- specialize H with (y:=y).
             cbn in H.
             rewrite <-H0 in H.
             rewrite H_compare in H.
             assumption.
    }
    generalize sorted0.
    generalize sorted1.
    rewrite H0.
    intros.
    replace sorted2 with sorted3; auto.
    apply proof_irrelevance.
Qed.

Lemma duplicated_add: ∀(m: M.t nat) (i x y:nat), (add i x (add i y m)) = (add i x m).
intros.
apply Equal_ProofIrrelevance.
apply duplicated_map_add.
Qed.

Lemma redundant_add: ∀map i n, (find (elt:=nat) i map) = (Some n) → (add i n map) = map.
intros.
apply Equal_ProofIrrelevance.
unfold Equal.
intros.
destruct (y =? i) eqn:H_yEqi.
- rewrite_nat.
  rewrite H_yEqi in *.
  rewrite H.
  rewrite P.F.add_eq_o; auto.
- rewrite_nat.
  rewrite P.F.add_neq_o; auto.
Qed.

Lemma redundant_remove: ∀ i map, (find (elt:=nat) i map) = None → (remove (elt:=nat) i (add i 0 map)) = map.
intros.
apply Equal_ProofIrrelevance.
unfold Equal.
intros.
destruct (y =? i) eqn:H_yEqi.
- rewrite_nat.
  rewrite H_yEqi in *.
  rewrite H.
  rewrite P.F.remove_eq_o; auto.
- rewrite_nat.
  rewrite P.F.remove_neq_o; auto.
  rewrite P.F.add_neq_o; auto.
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
  apply redundant_add; auto.
- rewrite F.add_eq_o; auto.
  assert_nat(0<?0=false).
  rewrite H.
  f_equal.
  apply redundant_remove; auto.
Qed.

Eval compute in (
  (ms_contains 1
  (ms_remove 1
  (ms_remove 1
  (ms_insert 1
  (ms_insert 1 empty_MultiSet)))))
).