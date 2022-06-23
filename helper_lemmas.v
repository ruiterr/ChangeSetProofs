From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Lists.List.
Require Import Unicode.Utf8.
From Coq Require Import List. Import ListNotations.


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
