From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import List. Import ListNotations.
Require Import Unicode.Utf8.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import Lia.

Inductive id : Type := 
  | Id  (n : nat).

Inductive value : Type := 
  | Val  (n : nat).

Inductive listEntry : Type := 
  | LE  (id : id) (v : value).

Notation "$ i" := (Id i) (at level 60, format "'$' i").
Notation "< $ i , v >" := (LE (Id i) (Val v)) (at level 50, i at next level, v at next level, format "'<' '$' i ',' v '>'").

Inductive sequence : Type := 
  | Seq (entries : (list listEntry)).

Definition sequenceEntries (s : sequence) : (list listEntry)  := 
  match s with 
    | Seq entries => entries
  end.

Eval compute in <$1, 1>.

Eval compute in Seq [<$1, 1>; <$2, 2>].

Inductive side: Type :=
  | left
  | right.

Definition smallerSide (s1:side) (s2:side) := match s1,s2 with
  |right, right => right
  | _, _ => left
  end.

Inductive anchor : Type :=
  | An (i : id) (s : side).


(* Notation "§ i , s §" := (An (Id i) s) (at level 50, i at next level, s at next level).*)

Notation "§ i '<'" := (An (Id i) left) (at level 50, i at next level, format "'§' i '<'").
Notation "§ i '>'" := (An (Id i) right) (at level 50, i at next level, format "'§' i '>'").

Definition anchorPos (a : anchor) : nat  := 
  match a with 
    | An (Id i) _ => i
  end.

Check An (Id 5) left.
Check $ 3.

Check §2>.

Inductive rangeType : Type :=
  | set
  | slice.
Inductive range : Type := 
  | Ra (f : anchor) (l : anchor) (t : rangeType).


Check [ 1 ; 2 ].

Notation "| f -> t |" := (Ra f t slice) (at level 60, f at next level, t at next level).
Notation "{ f -> t }" := (Ra f t set) (at level 60, f at next level, t at next level).

Check (Ra (An (Id 5) left) (An (Id 10) right) set).

Inductive Operation : Type :=
  | Skip (amount : nat) (side : side)
  | Insert (entries : sequence) (side : side)
  | Remove (entries : sequence) (side : side).

Notation "'Skip>' n" :=  (Skip n right) (at level 50, n at next level).
Notation "'Skip<' n" :=  (Skip n left ) (at level 50, n at next level).

Notation "'Insert>' s" :=  (Insert (Seq s) right) (at level 50, s at next level).
Notation "'Insert<' s" :=  (Insert (Seq s) left) (at level 50, s at next level).

Notation "'Remove>' s" :=  (Remove (Seq s) right) (at level 50, s at next level).
Notation "'Remove<' s" :=  (Remove (Seq s) left) (at level 50, s at next level).

Check Skip> 2.
Check Insert> [ <$4, 5>; <$5, 6>] .
Check Remove> [ <$4, 5>; <$5, 6>] .

Definition opLength (x : Operation) := match x with 
   | Skip x _ => x
   | Insert (Seq x) _ => (length x)
   | Remove (Seq x) _ => (length x)
end.

Inductive operationList : Type := 
  | OList (entries : (list Operation)).

(* Definition operationListLength (l : operationList) := match l with
  | OList x => fold_left (fun b0 x => ( (opLength x) + b0)) x 0
end. *)

Definition getOListLength (l : operationList) := match l with
  | OList x => (length x)
end.

Definition getOListEntries (l : operationList) := match l with
  | OList x => x
end.

Fixpoint createTestListInternal (n : nat) (next : nat) (i : id) : (list listEntry) := 
  match n with
    | 0 => [ ]
    | S m => [ LE i (Val next) ] ++ (createTestListInternal m (next + 1) (match i with |Id k => (Id (k+1)) end))
  end.

Definition createTestList (n : nat) (i : id) : sequence := 
  Seq (createTestListInternal n 0 i).

Definition testList := createTestList 5 ($ 0).

Eval compute in testList.

Fixpoint applyOpListToSequenceInternal (ops : list Operation) (entries : list listEntry) : option (list listEntry) := 
  match ops with
    | [] => Some entries
    | op::t => match op with 
      | Skip n side => if ((length entries) <? n ) then 
            None 
          else
            match (applyOpListToSequenceInternal t (skipn n entries)) with
              | Some s => Some ((firstn n entries) ++ s)
              | None => None
            end 
      | Insert (Seq s1) side => 
            match (applyOpListToSequenceInternal t entries) with
              | Some s2 => Some (s1 ++ s2)
              | None => None
            end 
      | Remove (Seq s1) s => 
          if ((length entries) <? (length s1) ) then 
            None 
          else
            applyOpListToSequenceInternal t (skipn (length s1) entries) 
      end
  end.

Definition applyOpListToSequence (ops : operationList) (entries : sequence) : option sequence := 
  match ops, entries with
    |OList o, Seq s => match (applyOpListToSequenceInternal o s) with
       |Some s2 => (Some (Seq s2))
       |None => None
    end
  end.

Eval compute in applyOpListToSequence 
    (OList [ (Skip> 2); (Insert< [<$7, 9>; <$8, 9>])])
    testList.

Eval compute in applyOpListToSequence 
    (OList [ (Skip> 2); (Remove< [<$2, 2>; <$3,3>])])
    testList.

Eval compute in applyOpListToSequence 
    (OList [ 
      (Skip> 2); 
      (Insert< [<$7, 9>; <$8, 9>]); 
      (Remove< [<$2, 2>; <$3,3>])
    ])
    testList.

Inductive BasicOperation : Type :=
  | BasicInsert (n : nat) (entries : sequence)
  | BasicRemove (n : nat) (entries : sequence).

Definition convertBasicOperation (op : BasicOperation) : operationList :=
  match op with
    | BasicInsert n (Seq entries) => (OList [ Skip> n; Insert> entries ])
    | BasicRemove n (Seq entries) => (OList [ Skip> n; Remove> entries ])
  end.

Definition applyBasicOperations (commands : list BasicOperation) (s0 : sequence): (option sequence) :=
  (fold_left (fun s op => match s with 
    |Some s1 => applyOpListToSequence (convertBasicOperation op) s1
    |None => None
   end) commands (Some s0)).

Eval compute in applyBasicOperations 
    [ 
      (BasicInsert 2 (Seq [<$7, 9>; <$8, 9>])); 
      (BasicInsert 3 (Seq [<$10, 10>; <$11, 10>]))
    ]
    testList.

Record IterationDefinition : Set := mkIterationDefinition {
  getLengthInSequenceA : Operation -> (nat * side);
  getLengthInSequenceB : Operation -> (nat * side);

  splitOperation : Operation -> nat -> side -> (Operation * (list Operation));
  splitOperationSequenceLength_cond: forall o x s, (length (snd (splitOperation o x s))) <= 1;

  computeResultingOperation : Operation -> Operation  -> Operation;
}.

Definition getLengthInSequenceASquash (op : Operation) : nat := 1.

Definition SplitHelper (f1 : nat -> side -> Operation)  (f2 : nat -> side-> Operation) n x is s := if n <? x then
           (pair (f1 n is)) ([f2 n s])
         else (if n <? x then
             (pair (f1 x s) ([]))
            else
             (match s, is with 
                | right, left => ( ((f1 x is), ([(f2 x right)])))
                | _, _ => (pair (f1 x s) ([]))
              end)).

Definition getSplitOpLength (iterDef : IterationDefinition) (o : Operation) :=
  let (x, y) := (iterDef.(splitOperation) o 2 left) in
  (length y).

Lemma concat_length: forall (o : Operation) (t : list Operation), length(o::t) = (length(t)) + 1.
Proof.
intros.
unfold length.
lia.
Qed.

Lemma SplitHelper_length: forall f1 f2 n x is s,  (length (snd (SplitHelper f1 f2 n x is s))) <= 1.
intros.
unfold SplitHelper.
case_eq (n <? x).
- auto.
- destruct s.
  + auto.
  + destruct is.
    * auto.
    * auto.
Qed.

Program Fixpoint iterateOverOperationLists (iterDef : IterationDefinition) (ol1 : list Operation) (ol2 : list Operation) 
  {measure ((length ol1) + (length ol2)) } : (list Operation) :=
  match ol1 with
    | o1::t1 => match ol2 with
      | o2::t2 => 
        let SAInfo := iterDef.(getLengthInSequenceA) o1 in
        let SBInfo := iterDef.(getLengthInSequenceB) o2 in

        let len1 := (fst SAInfo) in
        let len2 := (fst SBInfo) in
        let s1 := (snd SAInfo) in
        let s2 := (snd SBInfo) in
        let splitOpA := if len2 =? len1 then match s1 with |right => true | left => false end else len2 <? len1 in

        let splitOp     := if splitOpA then o1 else o2 in
        let splitLength := if splitOpA then len2 else len1 in
        let splitSide   := if splitOpA then s2 else s1 in

        let splitOp := (iterDef.(splitOperation) splitOp splitLength splitSide) in
        let opA :=  if splitOpA then (fst splitOp) else o1 in
        let opB :=  if splitOpA then o2 else (fst splitOp) in
        let seqA := if splitOpA then (snd splitOp) ++ t1 else t1 in
        let seqB := if splitOpA then t2 else (snd splitOp) ++ t2 in

        let resultingOp := iterDef.(computeResultingOperation) opA opB in

        resultingOp::(iterateOverOperationLists iterDef seqA seqB)
      | nil => ol1
      end
    | nil => ol2
  end.
Obligation Tactic := auto.
Next Obligation.
intros.
destruct (splitOpA);
  intros;
  subst seqA seqB;
  rewrite app_length;
  subst splitOp ol1 ol2;
  repeat rewrite concat_length;
  specialize splitOperationSequenceLength_cond with (i := iterDef) (o :=splitOp0) (x := splitLength) (s := splitSide) as H1;
  lia.
Qed.
Obligation Tactic := Tactics.program_simpl.

Program Definition SquashIterationDefinition :=  
  {| 
     getLengthInSequenceA := fun (op : Operation) => match op with 
       | Skip x s => (x, s)
       | Insert (Seq x) s => ( (length x), s)
       | Remove (Seq x) s => (0, s)
       end;

     getLengthInSequenceB := fun (op : Operation) => match op with 
       | Skip x s => (x, s)
       | Insert (Seq x) s => (0, s)
       | Remove (Seq x) s => ((length x), s)
       end;

     (* getLengthInSequence := fun (op : Operation) => match op with 
       | Skip x _ => x
       | Insert (Seq x) _ => 0
       | Remove (Seq x) _ => (length x)
       end; *)

     splitOperation := fun (op : Operation) (n : nat) (is : side)=> match op with 
       | Skip x s => SplitHelper (fun n s => Skip n s) (fun n s => Skip (x - n) s) n x is s
              
       | Insert (Seq el) s => 
          let x := length el in
          SplitHelper 
            (fun n s1 => Insert (Seq (firstn n el)) s1)
            (fun n s1 => Insert (Seq (skipn n el)) s1)
            n x is s
       | Remove (Seq el) s => 
          let x := length el in
          SplitHelper 
            (fun n s1 => Remove (Seq (firstn n el)) s1)
            (fun n s1 => Remove (Seq (skipn n el)) s1)
            n x is s
       end;

     computeResultingOperation := fun (opA : Operation) (opB : Operation) => match opA, opB with
       | Skip l s,      Skip l2 s2    => Skip l s
       | Skip l s,      Insert seq2 s2 => Insert seq2 s2
       | Skip l s,      Remove seq2 s2 => Remove seq2 s2
       | Insert seq1 s, Skip l2 s2    => Insert seq1 s
       (* In this case, we have to use seq2, insert always has length 0 in seqB, so if we have both insert, it will also be length 0 in seqA and thus the entry from B is correct*)
       | Insert seq1 s, Insert seq2 s2 => Insert seq2 s 
       (* insert and remove cancel out, we represent this by returning a skip 0, which is just a NOP*)
       | Insert seq1 s, Remove seq2 s2 => Skip 0 s
       | Remove seq1 s, Skip l2 s2 => Remove seq1 s
       (* This case is the most complex one, both insert and remove have length 0, but one of the two has actually been truncated the other not, we distinguish via the length of the sequence *)
       | Remove seq1 s, Insert seq s2 => if ((opLength opB) =? 0) then Remove seq1 s else Insert seq s2
       (* In this case, we have to use seq1, remove always has length 0 in seqA, so if we have both insert, it will also be length 0 in seqB and thus the entry from A is correct*)
       | Remove seq1 s, Remove seq s2 => Remove seq1 s
     end;
  |}.
Next Obligation.
destruct o; try destruct entries; apply SplitHelper_length.
Qed.

Print SquashIterationDefinition.

Eval compute in SquashIterationDefinition.(splitOperation) (Skip> 0) 0 left.
Eval compute in SquashIterationDefinition.(splitOperation) (Remove< [<$0, 0>; <$1, 1>; <$2, 2>]) 0 right.

Definition squash (OpsA : operationList) (OpsB : operationList) : operationList := match OpsA,OpsB with
  | OList lA, OList lB => OList (iterateOverOperationLists SquashIterationDefinition lA lB) 
  end.

(* Test some different squash scenarios *)
Eval compute in (squash 
  (OList [
       (Insert< [<$0, 0>; <$1, 1>; <$2, 2>])
  ])
  (OList [
       (Skip< 1);
       (Insert< [<$3, 3>; <$4, 4>])
  ])).

Eval compute in (squash 
  (OList [
       (Insert< [<$0, 0>; <$1, 1>; <$2, 2>])
  ])
  (OList [
       (Skip< 1);
       (Remove< [<$1, 1>])
  ])).

Eval compute in (squash 
  (OList [
       (Insert< [<$0, 0>; <$1, 1>; <$2, 2>])
  ])
  (OList [
       (Skip< 5);
       (Remove< [<$1, 1>])
  ])).
Eval compute in (squash 
  (OList [
       (Skip< 5);
       (Insert< [<$0, 0>; <$1, 1>; <$2, 2>])
  ])
  (OList [
       (Skip< 2);
       (Remove< [<$1, 1>])
  ])).

Eval compute in (squash 
  (OList [
       (Skip> 1);
       (Remove< [<$0, 0> ])
  ])
  (OList [
       (Skip< 1);
       (Insert< [<$1, 1>])
  ])).

Infix "○" := squash (at level 60).

Definition SplitOffLast (list : operationList) : (operationList * operationList).
give_up.
Admitted.

Lemma splitOffLastEquivalence: ∀ (A:operationList), let (A0, A1) := (SplitOffLast A) in A = (A0 ○ A1).
give_up.
Admitted.

Lemma splitOffLastResult0Length: ∀ (A:operationList), let (A0, A1) := (SplitOffLast A) in ((getOListLength A0) = ((getOListLength A) - 1)).
give_up.
Admitted.

Lemma splitOffLastResult1Structure: ∀ (A:operationList), ∃ (c:nat) (s:side) (o:Operation), let (A0, A1) := (SplitOffLast A) in (getOListEntries A1 = [ (Skip c s); o]).
give_up.
Admitted.

Definition splitOList (list:operationList) (n : nat) (s : side) : (operationList * operationList).
Admitted.

Lemma splitOListEquality: ∀ (A:operationList) (n:nat) (s : side), (OList ((getOListEntries (fst (splitOList A n s))) ++ (getOListEntries (snd (splitOList A n s))))) = A.
Admitted.

Lemma splitOListSquash: ∀ (A:operationList) (B: operationList) (n:nat) (s : side), (splitOList (A ○ B) n s) = 
                            ( ((fst (splitOList A n s)) ○ (fst ((splitOList B n s)))),
                            (  (snd (splitOList A n s)) ○ (snd ((splitOList B n s)))) ).
Admitted.

Lemma singleOpAssociativity: ∀ (A B : operationList) (o : Operation), 
  let (l, s) := (SquashIterationDefinition.(getLengthInSequenceA) o) in
  fst (splitOList (A ○ B) l s) ○ OList [o] = fst (splitOList A l s) ○ (fst (splitOList B l s) ○ OList [o]).
Admitted.

Theorem splitOListFirst: ∀ (A:operationList), ((getOListLength A) > 0) → (
       let (firstOP, t) := match A with 
         | OList (op::t) => (op, t)
         | OList [] => ((Skip 0 left), [])
       end in
       let (l, s) := (SquashIterationDefinition.(getLengthInSequenceA) firstOP) in
       (splitOList A l s) = ((OList [firstOP]), (OList t))).
Admitted.


Lemma singleSkipNop: ∀ (A : operationList) (n:nat) (s:side), (A ○ (OList [Skip n s]) = A).
Admitted.

Lemma emptyOListNop: ∀ (A : operationList), (A ○ (OList []) = A).
Admitted.

Lemma trivialOListAssoc: ∀ (B C :operationList),  ((OList []) ○ B) ○ C = (OList []) ○ (B ○ C).
intros.
  assert (∀ y, (OList []) ○ y = y) as H0.
  intros.
  unfold squash.
  destruct y.
  unfold iterateOverOperationLists.
  unfold iterateOverOperationLists_func.
  auto.

repeat rewrite H0.
reflexivity.
Qed.

(* Theorem simpleOListAssoc: ∀ (A B C :operationList), (∃ (c:nat) (s:side) (o:Operation), (getOListEntries A) = [ (Skip c s); o]) → (A ○ B) ○ C = A ○ (B ○ C).
intros.
destruct H.
destruct H.
destruct H.
unfold getOListEntries in H.
assert (A = (OList [Skip x x0; x1])). rewrite <-H. destruct A. auto.
rewrite H0. 
unfold squash.
destruct A.
destruct B.
destruct C.
unfold iterateOverOperationLists.
unfold iterateOverOperationLists_func.
auto.
give_up.
Admitted.*)

Theorem simpleOListAssoc: ∀ (A B C :operationList), ((∃ (cA:nat) (sA:side) (oA:Operation), A = OList[ (Skip cA sA); oA]) ∧ 
                                                     (∃ (cB:nat) (sB:side) (oB:Operation), B = OList[ (Skip cB sB); oB]) ∧ 
                                                     (∃ (cC:nat) (sC:side) (oC:Operation), C = OList[ (Skip cC sC); oC])) → (A ○ B) ○ C = A ○ (B ○ C).
intros.
destruct H as [[cA [sA [oA HA]]] H].
destruct H as [[cB [sB [oB HB]]] H].
destruct H as [cC [sC [oC HC]]].


(* Extract skip term *)
set (C0:=(fst (splitOList C cC sC))).
set (C1:=(snd (splitOList C cC sC))).

assert ((C0 = (OList [(Skip cC sC)])) ∧ C1 = (OList [oC])).
  specialize splitOListFirst with (A:= C). 
  rewrite HC. 
  intros. subst C0. subst C1. subst C. rewrite H; intuition. destruct H as [C0List C1List].

rewrite <-splitOListEquality with (A:=(A ○ B) ○ C) (n:=cC) (s:=sC).
rewrite <-splitOListEquality with (A:=A ○ (B ○ C)) (n:=cC) (s:=sC).

f_equal.
f_equal.
f_equal.

(* Proof equality for skip term *)

(* Simplify left side *)
rewrite splitOListSquash with (A:=(A ○ B)). 
  unfold fst at 1. 
  fold C0. 
  rewrite C0List. 
  rewrite singleSkipNop.

(* Simplify right side *)
rewrite splitOListSquash with (B:=(B ○ C)). 
  unfold fst at 2. 
  rewrite splitOListSquash with (A:=B).
  unfold fst at 3.
  fold C0. 
  rewrite C0List. 
  rewrite singleSkipNop.
  rewrite splitOListSquash with (A:=A).
  unfold fst. 
  auto.
  
(* Extract operations term and remainder *)
set (oCl := (fst (SquashIterationDefinition.(getLengthInSequenceA) oC))).
set (oCs := (snd (SquashIterationDefinition.(getLengthInSequenceA) oC))).
set (C1_0:=(fst (splitOList C1 oCl oCs))).
set (C1_1:=(snd (splitOList C1 oCl oCs))).

assert (C1_0 = (OList [oC]) ∧ C1_1 = (OList [])).
  specialize splitOListFirst with (A:= C1).
  rewrite C1List.  rewrite ->surjective_pairing with (p:= (SquashIterationDefinition.(getLengthInSequenceA) oC)). unfold getOListLength. unfold length.
  intros. subst C1_0. subst C1_1. rewrite C1List. unfold oCl. unfold oCs. rewrite H; intuition. destruct H as [C1_0List C1_1List].

(*Split proof into operations term and remainder *)
f_equal.

rewrite splitOListSquash with (A:=(A ○ B)).
unfold snd at 1.
fold C1.

rewrite splitOListSquash with (B:= (B ○ C)).
unfold snd at 2.

rewrite splitOListSquash with (B:= C).
unfold snd at 3.
fold C1.

rewrite splitOListSquash with (A:=(A)).
unfold snd at 1.
set (ARem := snd (splitOList A cC sC)).
set (BRem := snd (splitOList B cC sC)).

rewrite <-splitOListEquality with (A:=((ARem ○ BRem) ○ C1)) (n:=oCl) (s:=oCs).
rewrite <-splitOListEquality with (A:=(ARem ○ (BRem ○ C1))) (n:=oCl) (s:=oCs).

(* Proof equality for operation term *)
f_equal.
f_equal; f_equal.

(* Simplify left side *)
rewrite splitOListSquash with (A:=(ARem ○ BRem)). 
unfold fst at 1. 
fold C1_0. 
rewrite C1_0List. 


(* Simplify right side *)
rewrite splitOListSquash with (B:=(BRem ○ C1)). 
unfold fst at 2. 
rewrite splitOListSquash with (A:=BRem).
unfold fst at 3.
fold C1_0. 
rewrite C1_0List. 

specialize singleOpAssociativity with (A:= ARem) (B:=BRem) (o:=oC).
rewrite surjective_pairing with (p := (getLengthInSequenceA SquashIterationDefinition oC)).
intros.
assumption.
  

(* Proof equality for the remainder *)
rewrite splitOListSquash with (A:=(ARem ○ BRem)).
unfold snd at 1. 
fold C1_1.
rewrite C1_1List.
rewrite emptyOListNop.

rewrite splitOListSquash with (B:=(BRem ○ C1)).
unfold snd at 2.
rewrite splitOListSquash with (A:=BRem).
unfold snd at 3.
fold C1_1.
rewrite C1_1List.
rewrite emptyOListNop.

rewrite splitOListSquash with (A:=(ARem)).
unfold snd at 1.
reflexivity.
Qed.

Theorem squashAssociative: ∀ (A B C :operationList), (A ○ B) ○ C = A ○ (B ○ C).
intro A.
induction A as [A IHA] using (induction_ltof1 _ (@getOListLength)); unfold ltof in IHA.

specialize splitOffLastEquivalence with (A:=A).

set (SA := (SplitOffLast A)).
rewrite surjective_pairing with (p:=SA).
set (A0 := (fst SA)).
set (A1 := (snd SA)).
intros.

specialize splitOffLastResult0Length with (A := A).
fold SA.
rewrite surjective_pairing with (p:=SA).
fold A0.
intros.


specialize splitOffLastResult1Structure with (A := A).
fold SA.
rewrite surjective_pairing with (p:=SA).
fold A1.
intros.


assert ((getOListLength A = 0) ∨ (getOListLength A > 0)) as lA0Eq. lia. 

 destruct lA0Eq.
- assert (A = (OList [])) as ALen0.
    unfold getOListLength in H2.
    destruct A.
    assert (entries = []). apply length_zero_iff_nil. auto.
    rewrite H3. reflexivity.
  rewrite ALen0.
  apply trivialOListAssoc.

- assert (getOListLength A0 < getOListLength A). lia.
  rewrite H.
  rewrite IHA with (y:= A0) (B := A1) (C := B). 
  rewrite IHA with (y:= A0) (B := (A1 ○ B)) (C := C). 
  rewrite simpleOListAssoc.
  rewrite IHA with (y:= A0) (B := A1) (C := (B ○ C) ).
  all: auto.

Qed.






(*set (A0 := fst SA).
set (A1 := snd SA).*)

give_up.
Admitted.


(*Definition same_id (a : id) (b : id) : bool :=
  match a with
    | Id a1 =>   match b with
      | Id b1 => Nat.eqb a1 b1
    end
  end.

Definition anchor_getId (a : anchor) :=
  match a with
    | An i s =>  i
  end.

Inductive moveOp : Type :=
  | Move (r : range) (t : anchor).

Check [$ 5].

Fixpoint resolveAnchorImpl (a : anchor) (l : list id) (i : nat) : nat := 
  match l with
    | [ ] => 1000
    | h :: t => if ( same_id (anchor_getId a) h) then
        match a with 
          An _ side => match side with
            | left => i
            | right => i + 1
          end
        end
      else
        resolveAnchorImpl a t (i + 1)
  end.

Definition resolveAnchor (a : anchor) (l : list id) : nat := 
  resolveAnchorImpl a l 0.

Check § 3, left §.
Eval compute in resolveAnchor ( § 1, left § ) testList.

Definition moveOpApplyToList (m : moveOp) (l : list id) : option (list id) :=
  match m with Move (Ra s e _) t  =>
    let rangeStart := resolveAnchor s l in
    let rangeEnd := resolveAnchor e l in
    let insertPos := resolveAnchor t l in

    if  (rangeStart <? insertPos) && (insertPos <? rangeEnd) then None else
 
    if rangeEnd <? rangeStart then None else

    let extractedRange := firstn (rangeEnd - rangeStart) (skipn rangeStart l)  in
    let sequenceWithoutRange := (firstn rangeStart l) ++ (skipn rangeEnd l) in 
    let insertPositionInResult := if insertPos <? rangeStart then insertPos else insertPos - (rangeEnd - rangeStart) in
      Some ( (firstn insertPositionInResult sequenceWithoutRange) ++ extractedRange ++ (skipn insertPositionInResult sequenceWithoutRange) )
  end.

Eval compute in  testList.
Eval compute in moveOpApplyToList  (Move ( { § 2, left § -> § 4, right § } ) (§ 5, right §) ) testList.*)
