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
From Coq Require Import List. Import ListNotations.

Require Import BinPos BinInt BinNat Pnat Nnat.

Scheme Equality for list.

(* Generic helper lemmas *)
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


Module AdditionalGroupLemmas (GroupImpl: FreeGroupsSig).
Module Import FreeGroupsSig.
End FreeGroupsSig.


Module OperationGroup := FreeGroups GroupImpl.
Import OperationGroup.

Lemma tailIsReduced: ∀ (op: alphabet) (l: group_str), reduced(op::l) → reduced(l).
  intros.
  unfold reduced.
  unfold reduced.
  intuition.
  unfold reduced in H.
  unfold reduced in H.
  inversion H0.
  rewrite <-H1 in H.
  rewrite app_comm_cons in H.
  contradict H.
  apply intro_letter_inverse.
Qed.

Lemma tailIsReduced2: ∀ (l l': group_str) (op:alphabet), op::l'=l → reduced(l) → reduced(l').
intros.
apply tailIsReduced with (op:=op).
autounfold in *.
now rewrite H.
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
          (@cons OperationGroup.alphabet (OperationGroup.opposite x) (@cons GroupImpl.alphabet x T')) =
(@app OperationGroup.alphabet S'
                     (@cons GroupImpl.alphabet (OperationGroup.opposite x) (@cons OperationGroup.alphabet x T'))))).
auto.
rewrite <-H3 in H_AnonReduced.
rewrite <-H1 in H_AnonReduced.
auto.
Qed.

Lemma reducedImpliesFirstTwoOpeartionsNotInverses: ∀A T x y, reduced(A) → A = (x::y::T) → (x ≠ (opposite y)).
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


Lemma invertIsReduced: ∀(opsA: group_str), reduced(opsA) -> reduced(OperationGroup.inverse_str opsA).
intros.
unfold OperationGroup.inverse_str.
induction opsA.
- apply OperationGroup.empty_str_reduced.
- apply tailIsReduced in H as H_opsAreduced.
  fold OperationGroup.inverse_str in *.
  destruct opsA.
  + simpl.
    apply OperationGroup.single_letter_reduced.
  + apply reducedImpliesFirstTwoOpeartionsNotInverses with (A:=a :: a0 :: opsA) (T:=opsA) (x:=a) (y:=a0) in H; auto.

    assert(∀A t x y, reduced(A) → (rev A) = (y::t) → y ≠ (opposite x) → reduced(A ++ [x])). {
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
          rewrite OperationGroup.opposite_involution in H2.
          now contradiction H2.
      }
      apply reverseIsReduced in H3.
      rewrite HeqA'_rev in H3.
      rewrite rev_involutive in H3.
      auto.
    }
    unfold OperationGroup.inverse_str.
    fold OperationGroup.inverse_str.
    apply H0 with (y:=OperationGroup.opposite a0) (t:=(rev (OperationGroup.inverse_str opsA))).
    * unfold OperationGroup.inverse_str in IHopsA.
      auto.
    * rewrite rev_app_distr.
      rewrite revSingle.
      now rewrite <-cons_to_app.
    * rewrite OperationGroup.opposite_involution.
      auto.
Qed.

Lemma operationGroupIsRightInjective: ∀ A B C, (reduced B) → (reduced C) → (OperationGroup.reduced_string_product A B) = (OperationGroup.reduced_string_product A C) → B = C.
intros.
replace (B) with (OperationGroup.reduced_string_product (OperationGroup.inverse_str A) (OperationGroup.reduced_string_product A B)).
2: {
  rewrite <-OperationGroup.reduced_string_product_assoc.
  rewrite OperationGroup.inverse_str_is_left_inverse.
  rewrite OperationGroup.empty_str_is_left_id; auto.
}
rewrite H1.
rewrite <-OperationGroup.reduced_string_product_assoc.
rewrite OperationGroup.inverse_str_is_left_inverse.
rewrite OperationGroup.empty_str_is_left_id; auto.
Qed.

Lemma uniqueInverse: ∀A B, (reduced A) → (reduced B) → (OperationGroup.reduced_string_product A B) = [] → A = (OperationGroup.inverse_str B).
intros.
specialize OperationGroup.inverse_str_is_right_inverse with (S:=A) as H_inv.
rewrite <-H1 in H_inv.
apply operationGroupIsRightInjective in H_inv; auto.
rewrite <-H_inv.
now rewrite OperationGroup.inverse_str_involution.
now apply invertIsReduced.
Qed.

Lemma nestedReductions: ∀X Y, OperationGroup.reduction (X ++ Y) = OperationGroup.reduction ((OperationGroup.reduction X) ++ (OperationGroup.reduction Y)).
  intros.
  apply OperationGroup.equiv_strings_have_same_reductions.
  specialize OperationGroup.reduction_equiv with (S:=X) as H_reduction1.
  specialize OperationGroup.reduction_equiv with (S:=Y) as H_reduction2.
  rewrite H_reduction1.
  rewrite H_reduction2.
  apply OperationGroup.group_str_equiv_refl.
Qed.

Definition Op_eqb  (a : alphabet) (b: alphabet) := 
  if (alphabet_eq_dec a b) then true else false.

Lemma Op_eqb_refl: ∀ op, Op_eqb op op = true.
  intros.
  unfold Op_eqb.
  destruct alphabet_eq_dec.
  - auto.
  - contradiction. 
Qed.

Lemma Op_eqb_eq: ∀ x y : alphabet, (((Op_eqb x y) = true) → x = y).
intros.
unfold Op_eqb in H.
destruct (alphabet_eq_dec x y) eqn:H_eq; auto.
discriminate.
Qed.

Lemma  splitOffLeftFromReduction: ∀A B a t, (reduced A) → (reduced B) → ((length A) ≥ (length B)) → A = (a::t) → (
  OperationGroup.reduction (A++B) = (a::(OperationGroup.reduction (t++B))) ∨ 
  ((length A) = (length B) ∧ OperationGroup.reduction (A++B) = [])).
intros.
destruct (OperationGroup.reduced_dec (A++B)) eqn:H_AplusBReduced.
- rewrite OperationGroup.reduction_fixes_reduced; auto.
  rewrite H2.
  assert (OperationGroup.reduced (t ++ B)). {
    clear H_AplusBReduced.
    rewrite H2 in r.
    rewrite <-app_comm_cons in r.
    now apply tailIsReduced in r.
  }
  rewrite OperationGroup.reduction_fixes_reduced; auto.
- revert H.
  revert H1.
  revert H2.
  clear H_AplusBReduced.
  revert n.
  revert a.
  revert A.
  induction t.
  + intros.
    destruct B.
    * rewrite H2.
      simpl.
      rewrite OperationGroup.reduction_fixes_reduced; auto.
      apply OperationGroup.single_letter_reduced.
    * rewrite H2 in H1.
      simpl in H1.
      assert ((Datatypes.length B) = 0). { lia. }
      apply length_zero_iff_nil in H3.
      rewrite H3 in *.
      rewrite H2 in *.
      simpl in n.
      apply OperationGroup.split_non_reduced in n.
      destruct n. { contradict H4. apply OperationGroup.single_letter_reduced. }
      right.
      split.
      ++ now simpl.
      ++ rewrite H4.
         assert ([OperationGroup.opposite a0:OperationGroup.alphabet] = (OperationGroup.inverse_str [a0])); auto.
         rewrite H5.
         specialize OperationGroup.inverse_str_is_left_inverse with (S:=[a0]) as H_inv.
         unfold OperationGroup.reduced_string_product in H_inv.
         now rewrite H_inv.
  + intros.
    destruct (Datatypes.length A =? Datatypes.length B) eqn:H_equalLength.
    {
      rewrite_nat.
      destruct (list_beq alphabet Op_eqb (OperationGroup.reduction (A ++ B)) []) eqn:H_squashEmpty.
      - apply internal_list_dec_bl in H_squashEmpty.
        rewrite H_squashEmpty.
        right.
        auto.
        + apply Op_eqb_eq.
      - assert ((OperationGroup.reduction (A ++ B)) ≠ []). {
          intuition.
          rewrite H3 in H_squashEmpty.
          contradict H_squashEmpty.
          intuition.
        }
        left.
        assert(∀A B, (reduced A) → (reduced B) → (length A) = (length B) → (OperationGroup.reduction (A ++ B)) ≠ [] → ∃a b ta sb, (A=(a::ta)) ∧ (B=sb ++ [b]) ∧ (OperationGroup.reduction (A ++ B)) = a::(OperationGroup.reduction (ta ++ sb))++[b]). {
          intro A0.
          induction A0.
          - intros.
            simpl in H6.
            symmetry in H6.
            apply length_zero_iff_nil in H6.
            rewrite H6 in H7.
            simpl in H7.
            rewrite OperationGroup.reduction_fixes_reduced in H7.
            2: { apply OperationGroup.empty_str_reduced. }
            contradiction.
          - intros.
            exists a1.
            destruct (rev B0) as [ | b sb] eqn:H_revB0. {
              destruct B0.
              - simpl in H6.
                lia.
              - rewrite cons_to_app in H_revB0.
                rewrite rev_app_distr in H_revB0.
                simpl in H_revB0.
                apply app_eq_nil in H_revB0.
                destruct H_revB0.
                discriminate.
            }
            assert (B0 = ((rev sb) ++ [b])) as H_B0. {
              rewrite <-rev_involutive with (l:=B0).
              rewrite H_revB0.
              rewrite cons_to_app.
              rewrite rev_app_distr.
              rewrite revSingle.
              easy.
            }

            exists b.
            exists A0.
            exists (rev sb).
            intros.
            do 2 split; auto.

            rewrite H_B0.
            rewrite cons_to_app.
            rewrite <-app_assoc.
            rewrite app_assoc with (l:=A0).

            rewrite nestedReductions at 1.
            rewrite nestedReductions with (X:=A0++(rev sb)) at 1.
            destruct (list_beq alphabet Op_eqb (OperationGroup.reduction (A0 ++ (rev sb))) []) eqn:H_innerEmpty. {
              apply internal_list_dec_bl in H_innerEmpty.
              rewrite H_innerEmpty.
              rewrite OperationGroup.reduction_fixes_reduced with (S:=[a1]).
              2: { apply OperationGroup.single_letter_reduced. }
              rewrite OperationGroup.reduction_fixes_reduced with (S:=[b]).
              2: { apply OperationGroup.single_letter_reduced. }
              simpl.
              rewrite OperationGroup.reduction_fixes_reduced with (S:=[b]).
              2: { apply OperationGroup.single_letter_reduced. }
              simpl.
              destruct (Op_eqb (OperationGroup.opposite a1) b) eqn:H_opposites.
              - rewrite H_B0 in H7.
                rewrite cons_to_app in H7.
                rewrite <-app_assoc in H7.
                rewrite app_assoc with (l:=A0) in H7.
                rewrite nestedReductions in H7.
                rewrite nestedReductions with (X:=A0++(rev sb)) in H7.
                rewrite H_innerEmpty  in H7.
                rewrite OperationGroup.reduction_fixes_reduced with (S:=[a1])  in H7.
                2: { apply OperationGroup.single_letter_reduced. }
                rewrite OperationGroup.reduction_fixes_reduced with (S:=[b])  in H7.
                2: { apply OperationGroup.single_letter_reduced. }
                simpl in H7.
                rewrite OperationGroup.reduction_fixes_reduced with (S:=[b])  in H7.
                2: { apply OperationGroup.single_letter_reduced. }
                simpl in H7.
                apply Op_eqb_eq in H_opposites.
                rewrite <-H_opposites in H7.
                replace (OperationGroup.reduction [a1: OperationGroup.alphabet; OperationGroup.opposite a1:OperationGroup.alphabet]) with 
                        (OperationGroup.reduced_string_product [a1] (OperationGroup.inverse_str [a1])) in H7.
                2: { 
                  unfold OperationGroup.reduced_string_product.
                  unfold OperationGroup.inverse_str.
                  now simpl.
                }
                rewrite OperationGroup.inverse_str_is_right_inverse in H7.
                contradiction.
              - rewrite OperationGroup.reduction_fixes_reduced; auto.
                apply OperationGroup.join_reduced with (S:=[]).
                + apply OperationGroup.single_letter_reduced.
                + intuition.
                  rewrite H8 in H_opposites.
                  rewrite OperationGroup.opposite_involution in H_opposites.
                  rewrite Op_eqb_refl in H_opposites.
                  discriminate.
              - apply Op_eqb_eq.
            }
            specialize IHA0 with (B:=(rev sb)).
            destruct IHA0.
            + apply tailIsReduced with (op:=a1); auto.
            + rewrite H_B0 in H5.
              apply reverseIsReduced in H5.
              rewrite rev_app_distr in H5.
              rewrite revSingle in H5.
              rewrite <-cons_to_app in H5.
              apply tailIsReduced in H5.
              apply reverseIsReduced.
              now rewrite rev_involutive in H5. 
            + rewrite H_B0 in H6.
              rewrite app_length in H6.
              simpl in H6.
              lia.
            + intuition.
              contradict H_innerEmpty.
              rewrite H8.
              intuition.
            + destruct H8 as [b' [ta [tb H8]]].
              destruct H8.
              destruct H9.
              rewrite H10.
              rewrite <-nestedReductions.
              rewrite OperationGroup.reduction_fixes_reduced with (S := [b]).
              2: { apply OperationGroup.single_letter_reduced. }
              rewrite OperationGroup.reduction_fixes_reduced at 1.
              now rewrite <-cons_to_app.
              assert (reduced (x :: ((OperationGroup.reduction (ta ++ tb)) ++ [b']))) as H_red1. {
                specialize OperationGroup.reduction_is_reduced with (S:=A0 ++ (rev sb)) as H_red.
                now rewrite H10 in H_red.
              }
              assert (reduced (((x :: ((OperationGroup.reduction (ta ++ tb)) ++ [b'])) ++ [b]))) as H_red2. {
                rewrite <-rev_involutive with (l:=(x :: ((OperationGroup.reduction (ta ++ tb)) ++ [b'])) ++ [b]).
                apply reverseIsReduced.
                rewrite rev_app_distr.
                rewrite revSingle.
                rewrite <-cons_to_app.
                rewrite app_comm_cons.
                rewrite rev_app_distr.
                rewrite revSingle.
                rewrite <-cons_to_app.
                apply OperationGroup.join_reduced.
                - apply reverseIsReduced in H_red1.
                  rewrite app_comm_cons in H_red1.
                  rewrite rev_app_distr in H_red1.
                  rewrite revSingle in H_red1.
                  now rewrite <-cons_to_app in H_red1.
                - rewrite H_B0 in H5.
                  rewrite H9 in H5.
                  apply reverseIsReduced in H5.
                  repeat rewrite rev_app_distr in H5.
                  repeat rewrite revSingle in H5.
                  repeat rewrite <-cons_to_app in H5.
                  intuition.
                  contradict H5.
                  specialize OperationGroup.intro_letter_inverse with (S:=[]) (a:=b') (T:=rev tb) as H_nr.
                  rewrite <-H11 in H_nr.
                  simpl in H_nr.
                  auto.
              }
              rewrite <-cons_to_app.
              apply OperationGroup.join_reduced.
              * auto.
              * rewrite H8 in H4.
                intuition.
                contradict H4.
                specialize OperationGroup.intro_letter_inverse with (S:=[]) (a:=x) (T:=ta) as H_nr.
                rewrite <-H11 in H_nr.
                simpl in H_nr.
                auto.
        }
        specialize H4 with (A:=A) (B:=B) as H4'.
        destruct H4' as [a' [b [ ta  [sb H4']] ] ]; auto.
        destruct H4' as [H_eqA [H_eqB H_reductionSplit] ].
        rewrite H_reductionSplit.
        rewrite H2 in H_eqA.
        inversion H_eqA.
        rewrite <-OperationGroup.reduction_fixes_reduced with (S:=(OperationGroup.reduction ((a :: t) ++ sb)) ++ [b]).
        2: {
          rewrite <-rev_involutive.
          apply reverseIsReduced.
          rewrite rev_app_distr.
          rewrite revSingle.
          rewrite <-cons_to_app.
          assert (∀ x y : alphabet, ((x = y) → (Op_eqb x y) = true)) as Op_eq_eqb. {
            intros.
            rewrite H5.
            apply Op_eqb_refl.
          }
          destruct (list_eq_dec alphabet Op_eqb Op_eqb_eq Op_eq_eqb (OperationGroup.reduction ((a :: t) ++ sb)) []) eqn:H_emptyInner.
          - rewrite e.
            simpl.
            apply OperationGroup.single_letter_reduced.
          - specialize H4 with (A:=a::t) (B:=sb) as H4''.
            destruct H4'' as [a'' [b' [ ta'  [sb' H4'']] ] ]; auto.
            + rewrite H2 in H.
              now apply tailIsReduced with (op:=a0).
            + rewrite H_eqB in H0.
              apply reverseIsReduced in H0.
              rewrite rev_app_distr in H0.
              rewrite revSingle in H0.
              rewrite <-cons_to_app in H0.
              apply tailIsReduced in H0.
              apply reverseIsReduced in H0.
              now rewrite rev_involutive in H0.
            + rewrite H2 in H_equalLength.
              rewrite H_eqB in H_equalLength.
              rewrite app_length in H_equalLength.
              simpl in H_equalLength.
              simpl.
              lia.
            + destruct H4'' as [H_eqA' [H_eqB' Hsplit'']].
              rewrite Hsplit''.
              rewrite app_comm_cons.
              rewrite rev_app_distr.
              rewrite revSingle.
              rewrite <-cons_to_app.
              apply OperationGroup.join_reduced.
              * specialize OperationGroup.reduction_is_reduced with (S:=(a :: t) ++ sb) as H_reduced.
                rewrite Hsplit'' in H_reduced.
                apply reverseIsReduced in H_reduced.
                rewrite app_comm_cons in H_reduced.
                rewrite rev_app_distr in H_reduced.
                rewrite revSingle in H_reduced.
                now rewrite <-cons_to_app in H_reduced.
              * rewrite H_eqB in H0.
                rewrite H_eqB' in H0.
                apply reverseIsReduced in H0.
                do 2 rewrite rev_app_distr in H0.
                do 2 rewrite revSingle in H0.
                do 2 rewrite <-cons_to_app in H0.
                intuition.
                contradict H0.
                rewrite H5.
                specialize OperationGroup.intro_letter_inverse with (S:=[]) (a:=b') (T:=rev sb') as H_nonreduced.
                now simpl in H_nonreduced.
        }
        rewrite <-OperationGroup.reduction_fixes_reduced with (S:=[b]).
        2: { apply OperationGroup.single_letter_reduced. }
        rewrite <-nestedReductions.
        rewrite H_eqB.
        now rewrite app_assoc.
    }
    specialize IHt with (A:=a::t) (a:=a).
    destruct IHt; auto.
    * rewrite H2 in n.
      do 2 rewrite <-app_comm_cons in n.
      apply OperationGroup.split_non_reduced in n.
      destruct n.
      -- auto.
      -- rewrite H2 in H.
         specialize OperationGroup.intro_letter_inverse with (S:=[]) (T:=t) (a:=a) as H_nonReducedA.
         rewrite <-H3 in H_nonReducedA.
         simpl in H_nonReducedA.
         contradiction.
    * simpl. 
      rewrite H2 in H1. 
      simpl in H1.
      rewrite H2 in H_equalLength.
      rewrite_nat.
      simpl in H_equalLength.
      lia. 
    * rewrite H2 in H.
      apply tailIsReduced with (op:=a0); auto.
    * rewrite H2.
      rewrite <-app_comm_cons.
      assert(OperationGroup.reduction (a0 :: (a :: t) ++ B) = OperationGroup.reduction (a0 :: (OperationGroup.reduction ((a :: t) ++ B)))) as H_additionReduction. {
        rewrite cons_to_app.
        rewrite nestedReductions.
        rewrite OperationGroup.reduction_fixes_reduced with (S:=[a0]); try apply OperationGroup.single_letter_reduced.
        now rewrite <-cons_to_app.
      }
      rewrite H_additionReduction.
      destruct (OperationGroup.reduced_dec (a0 :: OperationGroup.reduction ((a :: t) ++ B))).
      -- rewrite OperationGroup.reduction_fixes_reduced; auto.
      -- rewrite H3 in n0.
         apply OperationGroup.split_non_reduced in n0.
         destruct n0.
         ++ rewrite <-H3 in H4.
            contradict H4.
            apply OperationGroup.reduction_is_reduced.
         ++ rewrite H2 in H.
            specialize OperationGroup.intro_letter_inverse with (S:=[]) (T:=t) (a:=a) as H_nonReducedA.
            rewrite <-H4 in H_nonReducedA.
            simpl in H_nonReducedA.
            contradiction.
    * left.
      rewrite H2.
      rewrite cons_to_app at 1.
      rewrite <-app_assoc.
      rewrite nestedReductions.
      destruct H3.
      rewrite H4.
      do 2 rewrite OperationGroup.reduction_fixes_reduced; auto.
      all: simpl; apply OperationGroup.single_letter_reduced.
Qed.

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

Lemma ReductionMaxLength: ∀X, (length (OperationGroup.reduction X)) ≤ (length X).
intros.
induction X.
- auto.
- destruct (OperationGroup.reduced_dec (a::X)).
  + rewrite OperationGroup.reduction_fixes_reduced; auto.
 
  + unfold OperationGroup.reduction.
    unfold OperationGroup.group_str_action.
    unfold OperationGroup.letter_action at 1.
      set (Y  :=  (fix group_str_action (S T : OperationGroup.group_str) {struct S} :
       OperationGroup.group_str :=
     match S with
     | [] => T
     | a0 :: S0 => OperationGroup.letter_action a0 (group_str_action S0 T)
     end) X []).
    destruct Y eqn:H_Y.
    ++ simpl. lia.
    ++ assert(OperationGroup.reduction (X) = Y) as H_YreductionX. { auto. }
       rewrite H_YreductionX in IHX.
       rewrite H_Y in IHX.
       simpl in IHX.
       destruct (OperationGroup.alphabet_eq_dec a (OperationGroup.opposite a0)).
       -- simpl.
          lia.
       -- simpl.
          lia.
Qed.

End AdditionalGroupLemmas.