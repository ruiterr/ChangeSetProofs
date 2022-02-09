From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import List. Import ListNotations.
Require Import Unicode.Utf8.
Require Import Coq.Program.Wf.
Require Import Omega.

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
(*  getLengthInSequence : Operation -> nat;*)
  splitOperation : Operation -> nat -> side -> (Operation * (list Operation));
  splitOperationSequenceLength_cond: forall o x s, (length (snd (splitOperation o x s))) <= 1
}.

Definition getLengthInSequenceASquash (op : Operation) : nat := 1.

Definition SplitHelper (f1 : nat -> side -> Operation)  (f2 : nat -> side-> Operation) n x is s := if n <? x then
           (pair (f1 n is)) ([f2 n s])
         else (if n <? x then
             (pair (f1 x s) ([]))
            else
             (match s, is with 
                | right, left => ( ((f1 x s), ([(f2 x right)])))
                | _, _ => (pair (f1 x s) ([]))
              end)).

Definition getSplitOpLength (iterDef : IterationDefinition) (o : Operation) :=
  let (x, y) := (iterDef.(splitOperation) o 2 left) in
  (length y).

(* Definition testDef (n : nat) : (nat * nat) := (3, 1).

Lemma testDefFstCond: forall n:nat, (fst (testDef n)) > 0.
Proof.
intros.
unfold testDef.
unfold fst.
auto.
Qed.

Lemma testDefSndCond: forall n:nat, (snd (testDef n)) > 0.
Proof.
intros.
unfold testDef.
unfold snd.
auto.
Qed.

Definition testDef2 (n : nat) : nat := 
  let '(x,y) := (testDef n) in (x + y).

Lemma testDef2SumCond: forall n:nat, (testDef2 n) > 0.
Proof.
intros.
unfold testDef2.
pose testDefFstCond.
pose testDefSndCond.
set (A := (testDef n)).
rewrite surjective_pairing with (p:=A).
set (A1 := fst A).
set (A2 := snd A).
specialize g with (n:=n) as V.
fold A in V.
fold A1 in V.
specialize g0 with (n:=n) as V2.
fold A in V2.
fold A2 in V2.

(*pose (forall (A : Type)  (T : (A * A)), T = ( (fst T), (fst T))).*)
(* assert (forall (X : Type) (Y : Type)  (T : (X * Y)), T = ( (fst T), (snd T))).
intros.
unfold fst.
unfold snd.
destruct T.
trivial.*)
rewrite > H with (T:=A).
subst A.


(* apply V in A. *)
set (A := ((fst A), (fst A))).




Definition my_call {A B C} (f : A -> B * C) (a : A) : C :=
  let (b, c) := f a in c.

Lemma mycall_is_call {A B C} (f : A -> B * C) a :
  my_call f a = snd (f a).
Proof.
  unfold my_call.
  set (bx := (snd (f a))).
  (* unfold snd in bx. *)
  fold bx.
  trivial.
Qed. *)


(* Lemma splitOpLengthLength: forall (iterDef : IterationDefinition) (o:Operation), ((getSplitOpLength iterDef o) <= 1).
Proof.
intro.
intro.
unfold getSplitOpLength.
(* set (split := (snd (splitOperation iterDef o 2 left))).*)
destruct (splitOperation iterDef o 2 left) as (a, b).


(* destruct (splitOperation iterDef o 2 left) as (x, y). *)
apply splitOperationSequenceLength_cond.
Qed.*)

Lemma concat_length: forall (o : Operation) (t : list Operation), length(o::t) = (length(t)) + 1.
Proof.
intros.
unfold length.
omega.
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

        let splitOp     := if len2 <? len1 then o1 else o2 in
        let splitLength := if len2 <? len1 then len2 else len1 in
        let splitSide   := if len2 <? len1 then s2 else s1 in

        let splitOp := (iterDef.(splitOperation) splitOp splitLength splitSide) in
        (* let (truncatedOp, remSeq) := splitOp in *)
        let opA :=  if len2 <? len1 then (fst splitOp) else o1 in
        let opB :=  if len2 <? len1 then o2 else (fst splitOp) in
        let seqA := if len2 <? len1 then (snd splitOp) ++ t1 else t1 in
        let seqB := if len2 <? len1 then t2 else (snd splitOp) ++ t2 in

        (*let '(opA, opB, seqA, seqB) :=  (if len2 <? len1 then (
            (truncatedOp, o2, remSeq ++ t1, t2)
          )
          else (
            (o1, truncatedOp, t1, remSeq ++ t2)
          )) in*)

(*        let truncatedO2 := if len1 <? len2 then o2 else o2 in *)
        (iterateOverOperationLists iterDef seqA seqB)
      | nil => ol1
      end
    | nil => ol2
  end.
Next Obligation.
 (* intros.
  Set Printing All.*)

case_eq (fst (getLengthInSequenceB iterDef o2) <? fst (getLengthInSequenceA iterDef o1)).
- intros. 
  rewrite app_length.
  set (X := Datatypes.length (snd (splitOperation iterDef o1 (fst (getLengthInSequenceB iterDef o2)) (snd (getLengthInSequenceB iterDef o2))))).
  pose splitOperationSequenceLength_cond.
  specialize l with (i := iterDef) (o :=o1) (x := (fst (getLengthInSequenceB iterDef o2))) (s := (snd (getLengthInSequenceB iterDef o2))).
  fold X in l.
  rewrite concat_length.
  rewrite concat_length.
  omega.
- intros. 
  rewrite app_length.
  set (X := (Datatypes.length (snd (splitOperation iterDef o2 (fst (getLengthInSequenceA iterDef o1)) (snd (getLengthInSequenceA iterDef o1)))))).
  pose splitOperationSequenceLength_cond.
  specialize l with (i := iterDef) (o :=o2) (x := (fst (getLengthInSequenceB iterDef o1))) (s := (snd (getLengthInSequenceB iterDef o1))).
  fold X in l.
  rewrite concat_length.
  rewrite concat_length.
  omega.


  Set Printing All.

  (* fold SO2 in SO.
  rewrite surjective_pairing with (p:=SO2) in SO. *)
(* Program Fixpoint iterateOverOperationLists (iterDef : IterationDefinition) (ol1 : list Operation) (ol2 : list Operation) 
  {measure ((length ol1) + (length ol2)) } : (list Operation) :=
  match ol1 with
    | o1::t1 => match ol2 with
      | o2::t2 => 
        let '(len1, s1) := iterDef.(getLengthInSequenceA) o1 in
        let '(len2, s2) := iterDef.(getLengthInSequenceB) o2 in
        
        let '(opA, opB, seqA, seqB) :=  (if len2 <? len1 then (
            let (truncatedOp, remSeq) := (iterDef.(splitOperation) o1 len2 s2) in
            (truncatedOp, o2, remSeq ++ t1, t2)
          )
          else (
            let (truncatedOp, remSeq) := (iterDef.(splitOperation) o2 len1 s1) in
            (o1, truncatedOp, t1, remSeq ++ t2)
          )) in

(*        let truncatedO2 := if len1 <? len2 then o2 else o2 in *)
        [o1] ++ (iterateOverOperationLists iterDef seqA seqB)
      | nil => ol1
      end
    | nil => ol2
  end.
Next Obligation.
case_eq (len2 <? len1).
- intros. 
  replace (len2 <? len1) with true in Heq_anonymous.
  set (SO := (let (truncatedOp, remSeq) := splitOperation iterDef o1 len2 s2 in (truncatedOp, o2, remSeq ++ t1, t2))).
  fold SO in Heq_anonymous.
  set (SO2 := splitOperation iterDef o1 len2 s2).
  Set Printing All.*)

Definition SquashIterationDefinition :=  
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

(* (pair (Remove< [<$7, 9>; <$8, 9>]) (Some (Remove< [<$7, 9>; <$8, 9>])) ) *)
  |}.

Eval compute in SquashIterationDefinition.(splitOperation) (Skip> 9) 8 right.
Eval compute in SquashIterationDefinition.(splitOperation) (Remove< [<$0, 0>; <$1, 1>; <$2, 2>]) 0 right.



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
