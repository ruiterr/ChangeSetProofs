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
Require Import Omega.
Require Import Lia.
(*Add LoadPath "/Users/ruiterr/work/fluid/ChangeSetProofs" as ChangeSets.*)
Require Import NatHelper.


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

Eval compute in Seq [ <$1, 1>; <$2, 2>].

Inductive side: Type :=
  | left
  | right.

Definition smallerSide (s1:side) (s2:side) := match s1,s2 with
  |right, right => right
  | _, _ => left
  end.

Definition isLeft (s:side) := match s with |left => true | right => false end.


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

Eval compute in (opLength (Remove> [ <$4, 5>; <$5, 6>])).

Definition isInsert (op:Operation) := match op with
  | Insert _ _=> true
  | _ => false
end.

Definition isRemove (op:Operation) := match op with
  | Remove _ _=> true
  | _ => false
end.

Definition isSkip (op:Operation) := match op with
  | Skip _ _=> true
  | _ => false
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

  computeResultingOperation : Operation -> Operation  -> bool -> Operation;
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

     computeResultingOperation := fun (opA : Operation) (opB : Operation) (splitOpA:bool) => match opA, opB with
       | Skip l s,      Skip l2 s2    => Skip l s
       | Skip l s,      Insert seq2 s2 => Insert seq2 s2
       | Skip l s,      Remove seq2 s2 => Remove seq2 s2
       | Insert seq1 s, Skip l2 s2    => Insert seq1 s
       (* In this case, we have to use seq2, insert always has length 0 in seqB, so if we have both insert, it will also be length 0 in seqA and thus the entry from B is correct*)
       | Insert seq1 s, Insert seq2 s2 => Insert seq2 s2 
       (* insert and remove cancel out, we represent this by returning a skip 0, which is just a NOP*)
       | Insert seq1 s, Remove seq2 s2 => Skip 0 s
       | Remove seq1 s, Skip l2 s2 => Remove seq1 s
       (* This case is the most complex one, both insert and remove have length 0, but one of the two has actually been truncated the other not, we descide based on the splitOpA flag *)
       | Remove seq1 s, Insert seq s2 =>  if splitOpA then Insert seq s2 else Remove seq1 s
       (* In this case, we have to use seq1, remove always has length 0 in seqA, so if we have both insert, it will also be length 0 in seqB and thus the entry from A is correct*)
       | Remove seq1 s, Remove seq s2 => Remove seq1 s
     end;
  |}.
Next Obligation.
destruct o; try destruct entries; apply SplitHelper_length.
Qed.



  (*match goal with 
   |- context [ match ?term with 
                | (pair (p) (varC)) => match p with 
                    | pair (varA) (varB) => _ 
                  end
     end ] => idtac varA
  end.*)
Local Ltac resolveLet VarName := match goal with 
   |- context [ match ?term with 
                | (pair (p) (varC)) => match p with 
                    | pair (varA) (varB) => _ 
                  end
     end ] => set (VarName:=term); 
              rewrite surjective_pairing with (p:=VarName); 
              rewrite surjective_pairing with (p:=(fst VarName));
              let a := fresh varA in set (a:= (fst (fst VarName)));
              let b := fresh varB in set (b:= (snd (fst VarName)));
              let c := fresh varC in set (c:= (snd VarName))
  end.

Local Ltac resolveSimpleLet H := match H with 
  | (let varName := ?term in _) = ?y  => let a := fresh varName in set (a:=term)
  end.

Lemma swapLetEq: ∀ (A B:Type) (v1:A) (t1 : A -> B) (t2 : B), ((let var := v1 in (t1 var))=t2) <-> ((let var2 := v1 in (t1 var2)=t2)).
intros.
split.
auto.
auto.
Qed.

Section GetNextOperation.
  Variable iterDef : IterationDefinition.
  Variables o1 o2 : Operation.
  
  Let SAInfo := iterDef.(getLengthInSequenceA) o1.
  Let SBInfo := iterDef.(getLengthInSequenceB) o2.

  Let len1 := (fst SAInfo).
  Let len2 := (fst SBInfo).

  Let s1 := (snd SAInfo).
  Let s2 := (snd SBInfo).

  Definition opAGtB := if len2 =? len1 then match s1,s2 with |right,left => true | _,_ => false end else len2 <? len1.
  Definition opAEqB := if len2 =? len1 then match s1,s2 with |right,right => true |left,left=>true |_,_=>false end else false.
  Definition opAEmptyAndSameSide := ((opLength o1) =? 0) && (Bool.eqb (isLeft s1) (isLeft s2)).


  Let splitOpA := opAGtB.

  Definition getNextOperation : (Operation * (list Operation) * (list Operation)) := 

    let splitOp     := if splitOpA then o1 else o2 in
    let splitLength := if splitOpA then len2 else len1 in
    let splitSide   := if splitOpA then s2 else s1 in

    let splitOp := (iterDef.(splitOperation) splitOp splitLength splitSide) in
    let opA :=  if splitOpA then (fst splitOp) else o1 in
    let opB :=  if splitOpA then o2 else (fst splitOp) in
    let remA := if splitOpA then (snd splitOp) else [] in
    let remB := if splitOpA then [] else (snd splitOp) in

    let resultingOp := iterDef.(computeResultingOperation) opA opB splitOpA in

    (resultingOp, remA, remB).

  Let remA := (snd (fst getNextOperation)).
  Let remB := (snd getNextOperation).
  Lemma getNextOperationRemainderLentgh: (length remA) + (length remB) <= 1.
    set (nextOp:=getNextOperation).
    unfold remA. unfold remB.
    fold nextOp.
    
    cbv delta [getNextOperation] in nextOp.


    destruct (splitOpA).
    - unfold nextOp. simpl. specialize splitOperationSequenceLength_cond with (i:=iterDef) (o:=o1) (x:=len2) (s:=s2) as H. lia.
    - unfold nextOp. simpl. specialize splitOperationSequenceLength_cond with (i:=iterDef) (o:=o2) (x:=len1) (s:=s1) as H. lia.
  Qed.

End GetNextOperation.


Program Fixpoint iterateOverOperationLists (iterDef : IterationDefinition) (ol1 : list Operation) (ol2 : list Operation) 
  {measure ((length ol1) + (length ol2)) } : (list Operation) :=
  match ol1 with
    | o1::t1 => match ol2 with
      | o2::t2 => 
        let nextOperation := getNextOperation iterDef o1 o2 in
        let resultingOp := (fst (fst nextOperation)) in
        let remA := (snd (fst nextOperation)) in
        let remB := (snd nextOperation) in

        resultingOp::(iterateOverOperationLists iterDef (remA++t1) (remB++t2))
      | nil => ol1
      end
    | nil => ol2
  end.
Obligation Tactic := auto.
Next Obligation.
intros.
rewrite <-Heq_ol1.
rewrite <-Heq_ol2.
repeat rewrite app_length.
repeat rewrite concat_length.
(*rewrite surjective_pairing in Heq_anonymous.*)
Opaque getNextOperation.
(* injection Heq_anonymous as H. *)
(*assert(remA=(snd (fst nextOperation))) as H_remA. cbv. cbv in H0. assumption.
assert(remB=(snd nextOperation))  as H_remB. cbv. cbv in H1. assumption.*)
specialize getNextOperationRemainderLentgh with (iterDef:=iterDef) (o1:=o1) (o2:=o2) as H_lenRemAB.
fold nextOperation in H_lenRemAB.
fold remA in H_lenRemAB.
fold remB in H_lenRemAB.
lia.
Transparent getNextOperation.
Qed.
Obligation Tactic := Tactics.program_simpl.


Print SquashIterationDefinition.

Eval compute in SquashIterationDefinition.(splitOperation) (Skip> 0) 0 left.
Eval compute in SquashIterationDefinition.(splitOperation) (Remove< [<$0, 0>; <$1, 1>; <$2, 2>]) 0 right.
Eval compute in SquashIterationDefinition.(splitOperation) (Skip> 1) 3 right.

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

Eval compute in (    
  ((OList [(Skip> 0)]) ○ (OList [Insert< [<$0, 0>; <$1, 1>; <$2, 2>]])) ○ (OList [Skip< 0])).

Eval compute in (    
  (OList [(Skip> 0)]) ○ ((OList [Insert< [<$0, 0>; <$1, 1>; <$2, 2>]]) ○ (OList [Skip< 0]))).


Eval compute in (    
  ((OList [(Skip> 0)]) ○ (OList [Insert< []])) ○ (OList [Skip< 0])).

Eval compute in (    
  (OList [(Skip> 0)]) ○ ((OList [Insert< []]) ○ (OList [Skip< 0]))).


Eval compute in (    
  ((OList [(Skip> 0)]) ○ (OList [Insert< [<$0, 0>; <$1, 1>; <$2, 2>]]))).

Eval compute in (    
  ((OList [Insert< [<$0, 0>; <$1, 1>; <$2, 2>]]) ○ (OList [Skip< 0]))).

Lemma emptyOListNop: ∀ (A : operationList), (A ○ (OList []) = A).
intros.
unfold squash.
destruct A.
f_equal.
unfold iterateOverOperationLists.
cbv delta [iterateOverOperationLists_func].
rewrite fix_sub_eq. 
simpl. destruct entries; reflexivity. 
intros. destruct x. destruct s. destruct x. simpl. destruct x0. reflexivity. destruct l. reflexivity. 
intros. 

f_equal.
f_equal.
Qed.
 
Lemma emptyOListNop2: ∀ (A : operationList), (((OList []) ○ A) = A).
intros.
unfold squash.
destruct A.
f_equal.
Qed.

Lemma extractFirstSquashOp : ∀ (A B : (list Operation)), A <> [] ∧ B <> [] → let '(combinedOp, remainderA, remainderB) := (getNextOperation SquashIterationDefinition (hd (Skip< 0) A) (hd (Skip< 0) B)) in
  (OList A) ○ (OList B) = (OList (combinedOp::(getOListEntries ((OList (remainderA++(tail A))) ○ (OList (remainderB++(tail B))))))).
intros.
resolveLet nextOp.

set (LHS:=OList (combinedOp :: getOListEntries (OList (remainderA ++ tl A) ○ OList (remainderB ++ tl B)))).
cbv delta [squash iterateOverOperationLists iterateOverOperationLists_func]. 
cbv beta. cbv match.  cbv beta. cbv match.

rewrite fix_sub_eq. cbv beta. cbv match.
Opaque getNextOperation.
simpl.
destruct H.
destruct A eqn:H_A.
contradiction.

destruct B eqn:H_B.
contradiction.
simpl in nextOp.
fold nextOp.
fold combinedOp.
unfold LHS.
f_equal.

intros.
destruct x.
destruct s.
simpl.

destruct x0; auto.
destruct l; auto.
f_equal.
rewrite H0.
auto.
Qed.
Transparent getNextOperation.


Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Eval compute in getNextOperation SquashIterationDefinition (Skip< 5) (Insert< [<$0, 0>; <$1, 1>; <$2, 2>]).


Definition getOpFromArray (arrayOp : (list Operation)) := (hd (Skip< 0) arrayOp).

Notation "x ≫  y" := (opAGtB SquashIterationDefinition x y) (at level 65, no associativity).

Notation "x ⊕ y ⊖ splitOpA" := (computeResultingOperation SquashIterationDefinition x y splitOpA) (at level 65, no associativity).
Notation "x [≺ₐ y ]" := (fst (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceA SquashIterationDefinition y)) (snd (getLengthInSequenceA SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≫ₐ y ]" := (snd (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceA SquashIterationDefinition y)) (snd (getLengthInSequenceA SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≺ᵦ y ]" := (fst (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceB SquashIterationDefinition y)) (snd (getLengthInSequenceB SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≫ᵦ y ]" := (snd (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceB SquashIterationDefinition y)) (snd (getLengthInSequenceB SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≺≺ y ; z ]" := (fst (splitOperation SquashIterationDefinition x y z)) (at level 40, no associativity).
Notation "x [≫≫ y ; z ]" := (snd (splitOperation SquashIterationDefinition x y z)) (at level 40, no associativity).
Notation "⌈ x ⌉ₐ" := (fst (getLengthInSequenceA SquashIterationDefinition x)) (at level 40, no associativity, format "'⌈' x '⌉ₐ'").
Notation "⌊ x ⌋ₐ" := (snd (getLengthInSequenceA SquashIterationDefinition x)) (at level 40, no associativity, format "'⌊' x '⌋ₐ'").
Notation "⌈ x ⌉ᵦ" := (fst (getLengthInSequenceB SquashIterationDefinition x)) (at level 40, no associativity, format "'⌈' x '⌉ᵦ'").
Notation "⌊ x ⌋ᵦ" := (snd (getLengthInSequenceB SquashIterationDefinition x)) (at level 40, no associativity, format "'⌊' x '⌋ᵦ'").
Notation "‖ x ‖" := (opLength x) (at level 40, no associativity, format "'‖' x '‖'").

Notation "↩ x" := (getOpFromArray x) (at level 50, no associativity, format "'↩' x").

Eval compute in ((Insert< [<$0,0>; <$1,1>; <$2,2>]) ≫ (Skip< 0)).

Lemma resolveNonEmptyArray: ∀ (x:Operation) (y:(list Operation)), y = [x] → ↩y = x.
intros.
unfold getOpFromArray.
unfold hd.
rewrite H.
auto.
Qed.

Lemma destructAGreaterB: ∀(A B:Operation), (A≫B) = true → 
                          (⌈ B⌉ᵦ <? ⌈ A ⌉ₐ) = true ∨ ((⌈B⌉ᵦ =? ⌈A⌉ₐ) = true ∧ ⌊A⌋ₐ = right ∧ ⌊B⌋ᵦ = left).
intros.
unfold opAGtB in H.
destruct (⌈B⌉ᵦ =? ⌈A⌉ₐ).
- destruct (⌊A⌋ₐ) eqn:H_ASide. 
  + discriminate H.
  + right. repeat split; auto. 
  destruct (⌊B⌋ᵦ);auto. discriminate H. 
- left. assumption.
Qed.

Lemma AGtB_lenAGelenB: ∀(A B:Operation), (A≫B) = true → ⌈A⌉ₐ ≥ ⌈B⌉ᵦ.
intros.
unfold opAGtB in H.
destruct (⌈B⌉ᵦ =? ⌈A⌉ₐ) eqn:H_AeqB.
- rewrite Nat.eqb_eq in H_AeqB. lia. 
- rewrite Nat.ltb_lt in H. lia.
Qed.

Lemma ASplit_lenAGelenB: ∀(A B:Operation), (A≫B) = true → ⌈A⌉ₐ ≥ ⌈B⌉ᵦ.
intros.
unfold opAGtB in H.
destruct (⌈B⌉ᵦ =? ⌈A⌉ₐ) eqn:H_AeqB.
- rewrite Nat.eqb_eq in H_AeqB. lia. 
- rewrite Nat.ltb_lt in H. lia.
Qed.

Lemma ASplit_lenALelenB: ∀(A B:Operation), (A≫B) = false → ⌈A⌉ₐ ≤ ⌈B⌉ᵦ.
intros.
unfold opAGtB in H.
destruct (⌈B⌉ᵦ =? ⌈A⌉ₐ) eqn:H_AeqB.
- rewrite Nat.eqb_eq in H_AeqB. lia. 
- rewrite Nat.ltb_nlt in H. lia.
Qed.

Lemma  opGtImpliesSplit: ∀(A B:Operation), (A≫B) = true → (A ≫ B) = true.
Admitted.

Lemma swapCombineWithSplitOfA: ∀(A B C:Operation) (splitOpA:bool), (A≫C) = true ∧ (B≫C) = true → ↩( A[≺ᵦB] ⊕ B ⊖ splitOpA)[≫ᵦC] = (↩A[≫ᵦC])[≺ᵦ↩B[≫ᵦC]] ⊕ ↩B[≫ᵦC] ⊖ splitOpA.
Admitted.

Lemma swapCombineWithSplitOfB: ∀(A B C:Operation) (splitOpA:bool), (A≫C) = true ∧ (B≫C) = true → ↩(A ⊕ B[≺ₐA] ⊖ splitOpA)[≫ᵦC] = ↩A[≫ᵦC] ⊕ (↩B[≫ᵦC])[≺ₐ↩A[≫ᵦC]] ⊖ splitOpA.
Admitted.

Lemma swapSplitRemainderWithShorterSplitALen: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → A[≫ₐB] = (↩A[≫ᵦC])[≫ₐ↩B[≫ᵦC]].
Admitted.

Lemma swapSplitRemainderWithShorterSplitBLen: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → A[≫ᵦB] = (↩A[≫ᵦC])[≫ᵦ↩B[≫ᵦC]].
Admitted.

Lemma combineWithInsertIsInsert: ∀(A B:Operation), (isInsert B) = true → (A ⊕ B ⊖ true) = B.
intros.
cbv.
destruct B; try discriminate H.
destruct A; auto.
Qed.

Lemma combineWithRemoveIsRemove: ∀(A B:Operation) (splitA:bool), (isInsert A) = false ∧ (isRemove B) = true → (A ⊕ B ⊖ splitA) = (if (isRemove A) then A else B).
intros A B splitA [H_isInsertA H_isRemoveB].

cbv.
destruct B; try discriminate H_isRemoveB.
destruct A; try discriminate H_isInsertA.
all: auto.
Qed.

Eval compute in ( (Insert> [<$0,0>; <$0,0>; <$0,0>]) ≫ (Skip< 2)).
Eval compute in ( ⌈Insert> [<$0,0>; <$0,0>; <$0,0>]⌉ᵦ ).
Eval compute in (⌈Skip> 2⌉ᵦ).
Eval compute in (⌈Insert> [<$0,0>; <$0,0>; <$0,0>]⌉ᵦ - ⌈Skip> 2⌉ᵦ).

Lemma splitOperationLengthR1: ∀(A:Operation) (s : side) (y:nat), y < ‖A‖ → ‖ A[≺≺ y ; s] ‖ = y.
intros.
unfold splitOperation. simpl.
destruct A eqn:H_A; destruct s; try destruct side0.
all: unfold SplitHelper.
all: unfold opLength in H.
all: try destruct entries.
all: unfold opLength.
all: apply Nat.ltb_lt in H as H_bool.
all: rewrite H_bool.
all: simpl.
all: try rewrite firstn_length.
all: try lia.
Qed.

Lemma splitOperationLengthR2: ∀(A:Operation) (s : side) (y:nat), A[≫≫ y ; s] ≠ [] → ‖↩A[≫≫ y ; s] ‖ = ‖A‖ - y.
intros.
destruct(A [≫≫y; s]) eqn:H_splitEmpty.
- contradiction H; auto.
- unfold getOpFromArray; simpl.
  unfold splitOperation in H_splitEmpty. simpl in H_splitEmpty.
  destruct A eqn:H_A; destruct s; try destruct side0.
  all: unfold SplitHelper in H_splitEmpty.
  1-4: destruct (y <? amount) eqn:H_yLtAmount; simpl in H_splitEmpty; try discriminate H_splitEmpty; simpl in H_splitEmpty.
  1-5: injection H_splitEmpty; intros H_l H_o; rewrite <-H_o.
  1-5: unfold opLength; auto.
  rewrite Nat.ltb_nlt in H_yLtAmount.
  lia.

  all: destruct entries.
  all: destruct (y <? Datatypes.length entries) eqn:H_yLtAmount; simpl in H_splitEmpty; try discriminate H_splitEmpty; simpl in H_splitEmpty.  
  all: injection H_splitEmpty; intros H_l H_o; rewrite <-H_o.
  all: unfold opLength; auto.
  all: rewrite skipn_length; auto.

  all: rewrite Nat.ltb_nlt in H_yLtAmount; lia.
Qed.

Lemma splitOperationSide: ∀(A:Operation) (s : side) (y:nat),  ⌊A[≺≺ y ; s]⌋ₐ = if (y <? ‖A‖) then s else (smallerSide (⌊A⌋ₐ) s).
intros.
cbn -[getLengthInSequenceA Nat.ltb].
destruct (A) eqn:H_A.
all: unfold SplitHelper; unfold opLength.
1: destruct (y <? amount).
3-4: destruct entries; destruct (y <? length entries).
all: now try destruct side0; try destruct side1; try destruct s; cbv.
Qed.

Lemma splitOperationWith0Unchanged: ∀(A:Operation) (s : side), (‖A‖ > 0 ∨ (‖A‖ = 0 ∧ ⌊A⌋ᵦ = right ∧ s = left)) → A[≫≫0 ; s] = [A].
intros.
unfold splitOperation. simpl.
destruct A eqn:H_A; destruct s eqn:H_s; try destruct side0 eqn:H_side0.
all: unfold SplitHelper.
all: try destruct entries.
all: simpl.
all: simpl in H.

all: destruct H.
all: try (
  (assert(0 < amount) as H1; only 1: lia) +
  (assert(0 < Datatypes.length entries) as H1; only 1: lia);
  rewrite <-Nat.ltb_lt in H1;
  rewrite H1; 
  try rewrite Nat.sub_0_r; simpl; auto
).
all: try destruct H as [H_amount [H_left H_right]]; try discriminate H_left; try discriminate H_right.
all: try rewrite H_amount. 
all: simpl; auto.
Qed.

Lemma splitOperationWith0RightEmpty: ∀(A:Operation) (s : side), ((‖A‖ = 0 ∧ ⌊A⌋ᵦ = right ∧ s = right)) → A[≫≫0 ; s] = [].
intros.
unfold splitOperation. simpl.
destruct A eqn:H_A; destruct s eqn:H_s; try destruct side0 eqn:H_side0.
all: unfold SplitHelper.
all: try destruct entries.
all: simpl.
all: simpl in H.

all: try (
  (assert(0 < amount) as H1; only 1: lia) +
  (assert(0 < Datatypes.length entries) as H1; only 1: lia);
  rewrite <-Nat.ltb_lt in H1;
  rewrite H1; 
  try rewrite Nat.sub_0_r; simpl; auto
).
all: try destruct H as [H_amount [H_left H_right]]; try discriminate H_left; try discriminate H_right.
all: try rewrite H_amount. 
all: simpl; auto.
Qed.

Lemma splitOperationWith0Empty: ∀(A:Operation) (s : side), A[≺≺0 ; s] = match A with 
  | Insert _ s1 => Insert (Seq []) (if (0 <? ‖A‖) then s else (smallerSide s s1))
  | Remove _ s1 => Remove (Seq []) (if (0 <? ‖A‖) then s else (smallerSide s s1))
  | Skip _ s1 => Skip 0 (if (0 <? ‖A‖) then s else (smallerSide s s1))
end.
intros.
unfold splitOperation. simpl.
destruct A eqn:H_A; destruct s eqn:H_s; try destruct side0 eqn:H_side0.
all: unfold SplitHelper.
all: try destruct entries.
all: simpl.


(* Solve for skip *)
1-4: (
  destruct(0 <? amount) eqn:H_0LtAmount;
  simpl; auto;
  rewrite Nat.ltb_nlt in H_0LtAmount;
  assert(amount = 0); try lia;
  rewrite H;
  auto
).

(* Solve insert and remove *)
1-8: (
  destruct(0 <? length entries) eqn:H_0LtAmount;
  simpl; auto;
  rewrite Nat.ltb_nlt in H_0LtAmount;
  assert(length entries = 0); try lia;
  rewrite H;
  auto
).

Qed.

Lemma resultingOperationLengthLessThanNorms: ∀ (A B :Operation) (s: bool), ‖A ⊕ B ⊖ s‖ ≤ (max (‖A‖) (‖B‖) ).
intros.
unfold computeResultingOperation.
unfold SquashIterationDefinition at 1.
destruct A eqn:H_A; destruct B eqn:H_B.
all: try destruct entries; try destruct entries0; try destruct s.
all: unfold opLength.
all: try lia.
Qed.

(*Lemma nextOperationLength:  ∀ (A B :Operation), ‖fst (fst (getNextOperation SquashIterationDefinition A B))‖ ≤ (min (‖A‖) (‖B‖)).
intros.
unfold getNextOperation.
destruct ( A ≫ B ).*)

Lemma sidesEqual: ∀(A:Operation), ⌊A⌋ₐ = ⌊A⌋ᵦ.
intros.
all: destruct A; simpl; auto.
all: destruct entries; simpl; auto.
Qed.

Lemma seqALengthFromNorm: ∀(A:Operation), ⌈A⌉ₐ = ( if (isRemove A) then 0 else ‖A‖).
intros.
destruct A; unfold isRemove.
all: try destruct entries; simpl; auto.
Qed.

Lemma seqBLengthFromNorm: ∀(A:Operation), ⌈A⌉ᵦ = ( if (isInsert A) then 0 else ‖A‖).
intros.
destruct A; unfold isRemove.
all: try destruct entries; simpl; auto.
Qed.

Lemma seqALengthEqNorm: ∀(A:Operation), (isRemove A) = false → ⌈A⌉ₐ = ‖A‖.
intros. rewrite seqALengthFromNorm. rewrite H. reflexivity.
Qed.

Lemma seqBLengthEqNorm: ∀(A:Operation), (isInsert A) = false → ⌈A⌉ᵦ = ‖A‖.
intros. rewrite seqBLengthFromNorm. rewrite H. reflexivity.
Qed.

Lemma seqALengthEq0: ∀(A:Operation), ‖A‖ = 0 → ⌈A⌉ₐ = 0.
intros. rewrite seqALengthFromNorm. rewrite H. rewrite Tauto.if_same. reflexivity.
Qed.

Lemma seqBLengthEq0: ∀(A:Operation), ‖A‖ = 0 → ⌈A⌉ᵦ = 0.
intros. rewrite seqBLengthFromNorm. rewrite H. rewrite Tauto.if_same. reflexivity.
Qed.

Hint Rewrite sidesEqual : changeset.
Hint Rewrite seqALengthEqNorm using ( easy + solve_nat ) : changeset.
Hint Rewrite seqBLengthEqNorm using ( easy + solve_nat ) : changeset.
Hint Rewrite seqALengthEq0 using ( easy + solve_nat ) : changeset.
Hint Rewrite seqBLengthEq0 using ( easy + solve_nat ) : changeset.



Lemma combineEqualSides: ∀(A B:Operation) (splitA:bool), ⌊A⌋ₐ = ⌊B⌋ₐ → (⌊A ⊕ B ⊖ splitA⌋ₐ) = ⌊A⌋ₐ.
intros.
unfold computeResultingOperation.
unfold SquashIterationDefinition at 2.
now destruct A; destruct B; try destruct entries; try destruct entries1; try destruct splitA.
Qed.

Definition MyFun (A B C: Operation) := ((A≫C), (B≫C), ⌈↩B[≫ᵦC]⌉ᵦ, (⌈↩A[≫ᵦC]⌉ₐ), ⌈B⌉ᵦ,  ⌈A⌉ₐ).
Definition MyFun2 (A B C: Operation) := ((↩A[≫ᵦC] ≫ ↩B[≫ᵦC]), (A ≫ B)).
Transparent getLengthInSequenceB.
Transparent length.
Transparent leb.
Transparent minus.
Eval compute in (MyFun2 (Skip< 5) (Insert> [<$0,0>; <$0,0>;<$0,0>;<$0,0>;<$0,0>]) (Skip< 3)).

Lemma splitOpRemainsInsert: ∀ (A C: Operation), A[≫ᵦC] ≠ [] → (isInsert(↩A[≫ᵦC]) = (isInsert A)).
Admitted.

Lemma splitOpRemainsRemove: ∀ (A C: Operation), A[≫ᵦC] ≠ [] → (isRemove(↩A[≫ᵦC]) = (isRemove A)).
Admitted.

Lemma splitOpRemainsSkip: ∀ (A C: Operation), A[≫ᵦC] ≠ [] → (isSkip(↩A[≫ᵦC]) = (isSkip A)).
Admitted.

Definition notLargerLengthInsert (A C:Operation) := (isInsert A) = false ∨ (⌈C⌉ᵦ < ⌈A⌉ₐ).


Lemma splitOperationRemainder: ∀ A B : Operation, A ≫ B = true → ∃ C : Operation, A[≫ᵦB] = [C].
Admitted.

Lemma seqLengthPreservedUnderCut: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ 
                                                      (isInsert B) = false → ⌈↩B[≫ᵦC]⌉ᵦ ?= (⌈↩A[≫ᵦC]⌉ₐ) = (⌈B⌉ᵦ ?= ⌈A⌉ₐ).
intros.
destruct H as [H_AgtC [H_BgtC H_BisNotInsert]].
apply destructAGreaterB in H_AgtC as H_AgtC2.
apply destructAGreaterB in H_BgtC as H_BgtC2.
apply splitOperationRemainder in H_AgtC as H_ACutExists.
destruct H_ACutExists as [ACut H_ACut].
apply splitOperationRemainder in H_BgtC as H_BCutExists.
destruct H_BCutExists as [BCut H_BCut].

rewrite seqBLengthFromNorm.
rewrite splitOpRemainsInsert.
2: rewrite H_BCut; discriminate.
rewrite H_BisNotInsert.
rewrite seqBLengthFromNorm with (A:=B).
rewrite H_BisNotInsert.

rewrite seqALengthFromNorm.
rewrite splitOpRemainsRemove.
2: rewrite H_ACut; discriminate.
rewrite seqALengthFromNorm.

apply AGtB_lenAGelenB in H_AgtC as H_AgeC.
apply AGtB_lenAGelenB in H_BgtC as H_BgeC.
(* TODO: There is a lot of ducplication in this proof *)
destruct(isRemove A) eqn:H_isRemoveA.
- assert(⌈C⌉ᵦ = 0) as H_ClenBeq0. { 
   rewrite seqALengthFromNorm in H_AgeC.
   rewrite H_isRemoveA in H_AgeC.
   lia.
  }
  rewrite H_ClenBeq0.
  rewrite splitOperationWith0Unchanged. 
  2: {
    rewrite H_ClenBeq0 in H_BgtC2.
    rewrite seqALengthFromNorm in H_BgtC2.
    destruct (isRemove B) eqn:H_isRemoveB.
    1: assert (0 <? 0 = false) as H_0nlt0; only 1: ( rewrite Nat.ltb_nlt; lia ); rewrite H_0nlt0 in H_BgtC2.

    all: destruct(0 <? ‖B‖) eqn:H_0ltB;
      ( rewrite Nat.ltb_lt in H_0ltB; lia ) +
      (
        rewrite Nat.ltb_nlt in H_0ltB; right;
        destruct H_BgtC2 as [H_BgtC2 | H_BgtC2]; try discriminate H_BgtC2;
        destruct H_BgtC2 as [_ [H_sB H_sC]];
        rewrite sidesEqual in H_sB;
        rewrite H_sB; rewrite H_sC;
        assert(‖B‖ = 0) as H_Beq0; only 1:lia ;rewrite H_Beq0;
        auto
      ).
  }
  unfold getOpFromArray. simpl.
  reflexivity.
- destruct (isRemove B) eqn:H_isRemoveB.
  + assert(⌈C⌉ᵦ = 0) as H_ClenBeq0. { 
     rewrite seqALengthFromNorm in H_BgeC.
     rewrite H_isRemoveB in H_BgeC.
     lia.
    }
    rewrite H_ClenBeq0.
    rewrite splitOperationWith0Unchanged. 
    2: {
      rewrite H_ClenBeq0 in H_BgtC2.
      rewrite seqALengthFromNorm in H_BgtC2.
      rewrite H_isRemoveB in H_BgtC2.
      assert (0 <? 0 = false) as H_0nlt0; only 1: ( rewrite Nat.ltb_nlt; lia ); rewrite H_0nlt0 in H_BgtC2.

      all: destruct(0 <? ‖B‖) eqn:H_0ltB;
        ( rewrite Nat.ltb_lt in H_0ltB; lia ) +
        (
          rewrite Nat.ltb_nlt in H_0ltB; right;
          destruct H_BgtC2 as [H_BgtC2 | H_BgtC2]; try discriminate H_BgtC2;
          destruct H_BgtC2 as [_ [H_sB H_sC]];
          rewrite sidesEqual in H_sB;
          rewrite H_sB; rewrite H_sC;
          assert(‖B‖ = 0) as H_Beq0; only 1:lia ;rewrite H_Beq0;
          auto
        ).
    }
    
    rewrite splitOperationWith0Unchanged. 
    2: {
      rewrite H_ClenBeq0 in H_AgtC2.
      rewrite seqALengthFromNorm in H_AgtC2.
      rewrite H_isRemoveA in H_AgtC2.

      all: destruct(0 <? ‖A‖) eqn:H_0ltA;
        try ( rewrite Nat.ltb_lt in H_0ltA; lia) + 
        (
          rewrite Nat.ltb_nlt in H_0ltA; right;
          destruct H_AgtC2 as [H_AgtC2 | H_AgtC2]; try discriminate H_AgtC2;
          destruct H_AgtC2 as [_ [H_sB H_sC]];
          rewrite sidesEqual in H_sB;
          rewrite H_sB; rewrite H_sC;
          assert(‖A‖ = 0) as H_Aeq0; only 1:lia; rewrite H_Aeq0;
          auto
        ).
        
    }
    unfold getOpFromArray.
    unfold hd.
    reflexivity.
  + assert (‖A‖ = ⌈A⌉ₐ) as H_A_Norm. {
      rewrite seqALengthFromNorm with (A:=A).
      rewrite H_isRemoveA.
      auto.
    }
    assert (‖B‖ = ⌈B⌉ₐ) as H_B_Norm. {
      rewrite seqALengthFromNorm with (A:=B).
      rewrite H_isRemoveB.
      auto.
    }


    rewrite splitOperationLengthR2.
    2: rewrite H_BCut; discriminate.
    rewrite splitOperationLengthR2.
    2: rewrite H_ACut; discriminate.

    rewrite H_B_Norm.
    rewrite H_A_Norm.
    destruct(⌈B⌉ₐ ?= ⌈A⌉ₐ) eqn:H_BeqA.
    * apply Nat.compare_eq_iff.
      rewrite Nat.compare_eq_iff in H_BeqA; lia.
    * apply Nat.compare_lt_iff.
      rewrite Nat.compare_lt_iff in H_BeqA; lia.
    * apply Nat.compare_gt_iff.
      rewrite Nat.compare_gt_iff in H_BeqA; lia.
Qed.

Lemma seqLengthPreservedUnderCutEQ: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ (isInsert B) = false → ⌈↩B [≫ᵦC]⌉ᵦ =? (⌈↩A [≫ᵦC]⌉ₐ) = (⌈B⌉ᵦ =? ⌈A⌉ₐ).
intros.
specialize seqLengthPreservedUnderCut with (A:=A) (B:=B) (C:=C) as H_SLP.
destruct H as [H_AGtC [H_BGtC H_isInsertB]].
forward H_SLP; auto.
destruct (⌈B⌉ᵦ ?= ⌈A⌉ₐ) eqn:H_BcompA.
1: {
  apply Nat.compare_eq in H_BcompA. rewrite <-Nat.eqb_eq in H_BcompA. rewrite H_BcompA.
  apply Nat.compare_eq in H_SLP. rewrite <-Nat.eqb_eq in H_SLP. rewrite H_SLP.
  auto.
}
1: apply nat_compare_Lt_lt in H_BcompA; apply nat_compare_Lt_lt in H_SLP.
2: apply nat_compare_Gt_gt in H_BcompA; apply nat_compare_Gt_gt in H_SLP.
all: (
  assert(⌈B⌉ᵦ <> ⌈A⌉ₐ) as H_BAeq; try lia; rewrite <-Nat.eqb_neq in H_BAeq; rewrite H_BAeq;
  assert(⌈↩B [≫ᵦC]⌉ᵦ <> ⌈↩A [≫ᵦC]⌉ₐ) as H_BAeq2; try lia; rewrite <-Nat.eqb_neq in H_BAeq2; rewrite H_BAeq2;
  auto
).
Qed.

Lemma seqLengthPreservedUnderCutLT: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ (isInsert B) = false → ⌈↩B [≫ᵦC]⌉ᵦ <? (⌈↩A [≫ᵦC]⌉ₐ) = (⌈B⌉ᵦ <? ⌈A⌉ₐ).
intros.
specialize seqLengthPreservedUnderCut with (A:=A) (B:=B) (C:=C) as H_SLP.
destruct H as [H_AGtC [H_BGtC H_isInsertB]].
forward H_SLP; auto.
destruct (⌈B⌉ᵦ ?= ⌈A⌉ₐ) eqn:H_BcompA.
2: {
  apply nat_compare_Lt_lt in H_BcompA. rewrite <-Nat.ltb_lt in H_BcompA. rewrite H_BcompA.
  apply nat_compare_Lt_lt in H_SLP. rewrite <-Nat.ltb_lt in H_SLP. rewrite H_SLP.
  auto.
}
1: apply nat_compare_eq in H_BcompA; apply nat_compare_eq in H_SLP.
2: apply nat_compare_Gt_gt in H_BcompA; apply nat_compare_Gt_gt in H_SLP.
all: (
  assert(¬(⌈B⌉ᵦ < ⌈A⌉ₐ)) as H_BAeq; try lia; rewrite <-Nat.ltb_nlt in H_BAeq; rewrite H_BAeq;
  assert(¬(⌈↩B [≫ᵦC]⌉ᵦ < ⌈↩A [≫ᵦC]⌉ₐ)) as H_BAeq2; try lia; rewrite <-Nat.ltb_nlt in H_BAeq2; rewrite H_BAeq2;
  auto
).
Qed.

Lemma sideRemainsUnchanged: ∀(A C:Operation), A[≫ᵦC]<>[] → ⌊↩A[≫ᵦC]⌋ₐ = ⌊A⌋ₐ.
intros.
Opaque length.
cbv delta [getLengthInSequenceA splitOperation getOpFromArray]. cbv beta. cbv zeta. 
Transparent SplitHelper.
all: simpl; unfold SplitHelper; simpl.
destruct A eqn:H_A; destruct C eqn:H_C. 
all: simpl.
all: try destruct(amount0 <? amount) eqn:H_Amount; simpl; auto.
all: destruct side0 eqn:H_Side0; destruct side1 eqn:H_Side1; simpl; auto.
all: try destruct  entries; try destruct entries0; simpl.

all: simpl in H; unfold SplitHelper in H.

all: try destruct(0 <? amount); simpl; auto.
all: try destruct(Datatypes.length entries <? amount); simpl; auto.
all: try destruct(amount <? Datatypes.length entries); simpl; auto.
all: try destruct(0 <? Datatypes.length entries); simpl; auto.
all: try destruct(Datatypes.length entries0 <? Datatypes.length entries); simpl; auto.

all: try rewrite H_Amount in H; simpl in H.

all: solve [exfalso; apply H; auto].
Qed.

Lemma splitLengthPreservedUnderCut: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ isInsert B = false → (↩A[≫ᵦC] ≫ ↩B[≫ᵦC]) = (A ≫ B).
intros.
cbv delta [opAGtB]. cbv beta. cbv zeta.

destruct H as [H_AGtC [H_BGtC H_isInsertB]].
specialize splitOperationRemainder with (A:=A) (B:=C) as HAC_exists. forward HAC_exists; auto.
specialize splitOperationRemainder with (A:=B) (B:=C) as HBC_exists. forward HBC_exists; auto.
destruct HAC_exists as [Aop HAC_exists].
destruct HBC_exists as [Bop HBC_exists].
assert(A [≫ᵦC] <> []) as H_AC_notEmptySet. rewrite HAC_exists. intuition. discriminate H.
assert(B [≫ᵦC] <> []) as H_BC_notEmptySet. rewrite HBC_exists. intuition. discriminate H.
destruct(⌊↩A [≫ᵦC]⌋ₐ) eqn:side_AC; destruct(⌊A⌋ₐ) eqn:side_A. all:auto.
specialize seqLengthPreservedUnderCutEQ with (A:=A) (B:=B) (C:=C). intros. forward H; auto. 
all: rewrite seqLengthPreservedUnderCutEQ ; auto.

all: destruct(⌈B⌉ᵦ =? ⌈A⌉ₐ) eqn:H3. 
all: auto; specialize sideRemainsUnchanged with (A:=A) (C:=C) as H_Side; rewrite H_Side in side_AC; try rewrite side_A in side_AC; try discriminate.

all: try rewrite seqLengthPreservedUnderCutLT ; auto.
rewrite <-sidesEqual.
specialize sideRemainsUnchanged with (A:=B) (C:=C) as H_SideB.
rewrite H_SideB. 
rewrite sidesEqual.
destruct (⌊B⌋ₐ); auto.
assumption.
Qed.

Section SplitOpByLarger.
  Variable A B C : Operation.
  Let combinedOp := (fst (fst (getNextOperation SquashIterationDefinition A B))).

  Lemma removeBImpliesCombinedOpAEq0: (isRemove B) = true ∧  (isInsert A) = false → (⌈combinedOp⌉ₐ) = 0.
  intros [H_isRemoveB H_isInsertA].
  destruct (B) eqn:H_B; try discriminate H_isRemoveB.
  destruct entries.
  unfold combinedOp.
  unfold getNextOperation.
  destruct (A ≫ Remove (Seq entries) side0) eqn:H_AGtB.
  all: rewrite combineWithRemoveIsRemove.
  2: {
     rewrite H_isRemoveB.
     destruct A; try discriminate H_isInsertA.
     2: destruct entries0.
     all: cbn -[isInsert]; unfold SplitHelper.
     1: destruct (Datatypes.length entries <? amount).
     3: destruct (Datatypes.length entries <? Datatypes.length entries0).
     all: now (destruct side1;destruct side0).
  } 
  3: {
     rewrite H_isInsertA.
     split; auto.
     destruct A eqn:H_A; try discriminate H_isInsertA.
     2: destruct entries0.
     all: cbn -[isRemove]; unfold SplitHelper.
     1: destruct (amount <? Datatypes.length entries).
     3: destruct (0 <? Datatypes.length entries).
     all: now (destruct side1;destruct side0).
  } 
  - destruct (A) eqn:H_A; try discriminate H_isInsertA.
    assert (isRemove (Skip amount side1 [≺ᵦRemove (Seq entries) side0]) = false). {
      all: cbn; cbv delta [SplitHelper]; cbn -[Nat.ltb]; simpl; auto.
      all: destruct (Datatypes.length entries <? amount).
      all: destruct side1.
      all: destruct side0.
      all: simpl; auto.
    }
    rewrite H.
    auto.
    assert (isRemove (Remove entries0 side1 [≺ᵦRemove (Seq entries) side0]) = true). {
      destruct entries0.
      simpl. unfold SplitHelper.
      destruct (Datatypes.length entries <? Datatypes.length entries0).
      simpl. auto.
      all: destruct side1; simpl; auto.
      all: destruct side0; simpl; auto.
    }
    rewrite H.
    destruct entries0. 
    cbn. unfold SplitHelper. simpl. 
    destruct  (Datatypes.length entries <? Datatypes.length entries0).
    1-2: simpl; auto.  
    destruct side1;
    destruct side0; simpl; auto.
    
  - destruct (A) eqn:H_A; try discriminate H_isInsertA.
    all: unfold isRemove.
    set (lengthSkip := ⌈Skip amount side1⌉ₐ).
    all: rewrite seqALengthFromNorm.
    simpl. unfold SplitHelper.
    now destruct (lengthSkip <? Datatypes.length entries);
        destruct side1; 
        destruct side0.
    easy.
  Qed.

  Lemma splitByLargerOp: combinedOp ≫ C = true ∧ (isInsert B) = false ∧
                         ((isRemove B) && (0 <? ⌈B⌉ᵦ) && (isLeft (⌊B⌋ᵦ))) = false → A ≫ C = true ∧ B ≫ C = true.
  intros [H_combinedGtC [H_isInsertB H_BisNonEmptyLeftRemove]].
  destruct(isRemove A) eqn:H_isRemoveA.
  - destruct A eqn:H_A; unfold isRemove in H_isRemoveA; try discriminate H_isRemoveA.
    destruct entries.
    
    cbn -[getLengthInSequenceA getLengthInSequenceB computeResultingOperation splitOperation] in combinedOp.
    destruct (Remove (Seq entries) side0 ≫ B) eqn:H_AGtB.
    + cbn -[getLengthInSequenceA getLengthInSequenceB computeResultingOperation] in combinedOp.
      apply ASplit_lenAGelenB in H_AGtB as H_LAGeLB.
      cbn -[getLengthInSequenceB] in H_LAGeLB.
      unfold SplitHelper in combinedOp.
      set (x:=⌈B⌉ᵦ <? Datatypes.length entries).
      fold x in combinedOp.
      destruct (x) eqn:H_AEntries.
      all: (
        cbn -[getLengthInSequenceB computeResultingOperation] in combinedOp;
        unfold combinedOp in H_combinedGtC;
        replace (⌈B⌉ᵦ) with 0 in H_combinedGtC; try lia;
        try rewrite firstn_O in H_combinedGtC;
        try rewrite firstn_all in H_combinedGtC;
        cbn -[getLengthInSequenceB] in H_combinedGtC
      ).

      2: (
        unfold opAGtB in H_AGtB;
        cbn -[getLengthInSequenceB] in H_AGtB;
        replace (⌈B⌉ᵦ) with 0 in H_AGtB; try lia;
        cbn -[getLengthInSequenceB] in H_AGtB;
        destruct side0 eqn:H_side0; try discriminate H_AGtB;
        destruct (⌊B⌋ᵦ); try discriminate H_AGtB
      ).
      all: destruct B; try discriminate H_isInsertB.
      all: (
          unfold opAGtB in H_combinedGtC; cbn -[getLengthInSequenceB] in H_combinedGtC;
          unfold opAGtB;
          try destruct entries0;
          destruct (⌈C⌉ᵦ =? 0) eqn:H_lengthC; try discriminate H_combinedGtC;
          destruct( side1 ) eqn:H_side1; try discriminate H_combinedGtC;
          destruct(⌊C⌋ᵦ) eqn:H_sideC; try discriminate H_combinedGtC;
          rewrite Nat.eqb_eq in H_lengthC; rewrite H_lengthC; simpl;
          try assert ((length entries0) = 0) as H_amount;
          try assert (amount = 0) as H_amount; cbv in H_LAGeLB; try lia;
          cbv in H_AGtB;
          rewrite H_amount in H_AGtB;
          destruct (side0); discriminate H_AGtB
        ).
    + apply ASplit_lenALelenB in H_AGtB as H_LALeLB.
      subst combinedOp.
      replace (⌈Remove (Seq entries) side0⌉ₐ) with 0 in H_combinedGtC. 2:{ cbv. auto. }
      rewrite splitOperationWith0Empty in H_combinedGtC.
      cbn in H_combinedGtC.
      destruct B eqn:H_B.
      2: unfold isInsert in H_isInsertB; discriminate H_isInsertB.
      all: rewrite H_combinedGtC; split; auto.
      all: apply AGtB_lenAGelenB in H_combinedGtC as H_ALenGTCLen.
      all: unfold opAGtB.
      all: rewrite <-H_B.
      all: rewrite <-H_B in H_LALeLB.
      all: rewrite <-H_A in H_ALenGTCLen.
      all: rewrite <-H_A in H_LALeLB. 
      all: destruct(⌈C⌉ᵦ =? ⌈B⌉ₐ) eqn:H_LenCEqLenB.
  
      2: assert(⌈B⌉ₐ ≥ ⌈B⌉ᵦ) as H_BaEqBb.
      2: (
        rewrite seqALengthFromNorm;
        rewrite seqBLengthFromNorm; 
        rewrite H_B;
        cbn -[opLength]; lia
      ).

      2: (
        rewrite Nat.ltb_lt; rewrite Nat.eqb_neq in H_LenCEqLenB;
        lia
      ).

      3: { 
        rewrite H_A in H_ALenGTCLen.
        cbn -[getLengthInSequenceB] in H_ALenGTCLen.
        rewrite Nat.ltb_lt.
        rewrite Nat.eqb_neq in H_LenCEqLenB. 
        replace (⌈C⌉ᵦ) with 0; try lia.
      }
      
        * assert(⌈C⌉ᵦ = ⌈B⌉ᵦ) as H_CbEqBb. {
          rewrite seqALengthFromNorm in H_LenCEqLenB.
          rewrite seqBLengthFromNorm in H_LenCEqLenB.
          rewrite H_B in H_LenCEqLenB.
          unfold isRemove in H_LenCEqLenB.
          repeat rewrite seqBLengthFromNorm.
          rewrite H_B.
          destruct (isInsert C).
          - rewrite Nat.eqb_eq in H_LenCEqLenB.
            rewrite <-H_LenCEqLenB.
            cbv. auto.
          - rewrite Nat.eqb_eq in H_LenCEqLenB.
            rewrite <-H_LenCEqLenB.
            cbv. auto.
        }
        unfold opAGtB in H_AGtB.
        unfold opAGtB in H_combinedGtC.
        assert ((⌈C⌉ᵦ =? ⌈Remove (Seq entries) side0⌉ₐ) = true) as H_AEqC. {
          rewrite <-H_A.
          rewrite Nat.eqb_eq.
          lia.
        }

        assert( (⌈Skip amount side1⌉ᵦ =? ⌈Remove (Seq entries) side0⌉ₐ) = true) as H_AEqB. {
          rewrite <-H_A.
          rewrite <-H_B.
          rewrite Nat.eqb_eq.
          lia.
        }
        rewrite H_AEqC in H_combinedGtC.
        rewrite H_AEqB in H_AGtB.
        rewrite <-H_A in H_combinedGtC.
        rewrite <-H_A in H_AGtB.
        rewrite <-H_B in H_AGtB.
        rewrite sidesEqual.
        destruct (⌊A⌋ₐ) eqn:H_sideA;
        destruct (⌊B⌋ᵦ) eqn:H_sideB;
        destruct (⌊C⌋ᵦ) eqn:H_sideC;
        try discriminate H_combinedGtC;
        try discriminate H_AGtB.
        auto.

        * rewrite seqALengthFromNorm in H_LenCEqLenB.
        rewrite H_B in H_LenCEqLenB.
        cbn -[getLengthInSequenceB] in H_LenCEqLenB.
        rewrite Nat.eqb_eq in H_LenCEqLenB.
        unfold opAGtB in H_combinedGtC.
        rewrite H_LenCEqLenB in H_combinedGtC.
        cbn -[getLengthInSequenceB] in H_combinedGtC.
        destruct (side0) eqn:H_sideA; try discriminate H_combinedGtC.
        destruct (⌊C⌋ᵦ) eqn:H_sideC; try discriminate H_combinedGtC.
        unfold opAGtB in H_AGtB.
        cbn -[getLengthInSequenceB] in H_AGtB.
        destruct (⌈Remove entries0 side1⌉ᵦ =? 0) eqn:H_lenBB. rewrite <-H_B in H_AGtB.
        rewrite sidesEqual.
        destruct (⌊B⌋ᵦ) eqn:H_sideB; try discriminate H_AGtB.
        auto.
        rewrite seqBLengthFromNorm in H_lenBB.
        destruct entries0.
        cbn -[Nat.ltb] in H_BisNonEmptyLeftRemove.
        cbn in H_lenBB.
        assert (0 <? Datatypes.length entries0 = true) as H_LenBGt0. {
          rewrite Nat.ltb_lt.
          rewrite Nat.eqb_neq in H_lenBB.
          lia.
        }
        rewrite H_LenBGt0 in H_BisNonEmptyLeftRemove.
        destruct (⌊B⌋ₐ) eqn:H_sideB.
        ** rewrite H_B in H_sideB.
          cbn in H_sideB.
          rewrite H_sideB in H_BisNonEmptyLeftRemove.
          cbn in H_BisNonEmptyLeftRemove.
          discriminate H_BisNonEmptyLeftRemove.
        ** auto.

  - assert( ‖combinedOp‖ ≤ (min (‖A‖) (‖B‖))) as H_combinedOpNorm. {

      assert (‖B‖ = ⌈B⌉ᵦ) as H_B_Norm. {
        rewrite seqBLengthFromNorm with (A:=B).
        rewrite H_isInsertB.
        auto.
      }
      assert (‖A‖ = ⌈A⌉ₐ) as H_A_Norm. {
        rewrite seqALengthFromNorm with (A:=A).
        rewrite H_isRemoveA.
        auto.
      }
      
      unfold getNextOperation in combinedOp.
      destruct(A ≫ B) eqn:H_AGtB;
      unfold opAGtB in H_AGtB;
      rewrite <-H_A_Norm in H_AGtB; 
      rewrite <-H_B_Norm in H_AGtB.
      assert(‖B‖ = (min (‖A‖) (‖B‖))). 
      3: assert(‖A‖ = (min (‖A‖) (‖B‖))).
      1,3: destruct(‖B‖ =? ‖A‖) eqn:H_BeqA. 
      1,3: rewrite Nat.eqb_eq in H_BeqA; lia.
      1: rewrite Nat.ltb_lt in H_AGtB. lia.
      1: rewrite Nat.ltb_nlt in H_AGtB. lia.

      all: unfold combinedOp.
      all: unfold fst at 2.
      all: unfold fst at 1.

      all:unfold isRemove in H_isRemoveA.
      all:unfold isInsert in H_isInsertB.
      assert( (‖B‖ =? ‖A‖ = true) → ⌊A⌋ₐ = right ∧ ⌊B⌋ᵦ= left) as H_sides.
      3: assert( (‖B‖ =? ‖A‖ = true) → ⌊A⌋ₐ = left ∨ (⌊A⌋ₐ = right ∧ ⌊B⌋ᵦ= right)) as H_sides.
      1,3: intros H_ABNorm; rewrite H_ABNorm in H_AGtB.
      1,2: destruct (⌊A⌋ₐ); try discriminate H_AGtB.
      1-3: destruct (⌊B⌋ᵦ); try discriminate H_AGtB.
      1-4: auto.

      1,2: destruct(‖B‖ =? ‖A‖) eqn:H_BeqA.
      1,3: forward H_sides; auto.
      1: destruct H_sides as [H_sideA H_sideB].
      1,2: assert(‖B‖ <? ‖A‖ = false) as H_BLtA; only 1,3: (
       rewrite Nat.ltb_nlt; rewrite Nat.eqb_eq in H_BeqA; lia
      ).
      3: assert(‖B‖ <? ‖A‖ = true) as H_BLtA; try (
       rewrite Nat.ltb_lt; rewrite Nat.eqb_neq in H_BeqA; lia 
      ).
      4: assert(‖A‖ <? ‖B‖ = true) as H_BLtA; try (
       rewrite Nat.ltb_lt; rewrite Nat.eqb_neq in H_BeqA; lia 
      ).

      all: destruct A eqn:H_A; destruct  B eqn:H_B; try discriminate H_isRemoveA; try discriminate H_isInsertB.
      all: try destruct entries.
      all: try destruct entries0.
      all: simpl in H.
      all: simpl in H_BLtA.
      all: cbn; unfold SplitHelper.
      all: try simpl in H_sideA; try rewrite H_sideA.
      all: try simpl in H_sideB; try rewrite H_sideB.
      all: try rewrite H_BLtA; simpl.
      all: try replace (amount <? amount) with false; try lia.
      all: try rewrite firstn_all.
      all: try rewrite Nat.ltb_irrefl; auto.
      all: try simpl in H_BeqA; try rewrite Nat.eqb_eq in H_BeqA; try rewrite Nat.eqb_neq in H_BeqA; try rewrite H_BeqA; try lia.
      all: try rewrite Nat.ltb_irrefl.
      all: try (simpl in H_sides; destruct (H_sides); (rewrite H0) + (destruct H0; rewrite H0); destruct side1; simpl; try lia).
      all: rewrite firstn_le_length; lia.
     }
     
     assert (⌈C⌉ᵦ ≤ (min (‖A‖) (‖B‖))) as H_CLeMinAB. {

       unfold opAGtB in H_combinedGtC.
       rewrite seqALengthFromNorm in H_combinedGtC.
       destruct (isRemove combinedOp).
        - destruct(⌈C⌉ᵦ =? 0) eqn:H_Ceq0.
          + rewrite Nat.eqb_eq in H_Ceq0.
            rewrite H_Ceq0.
            lia.
          + rewrite Nat.ltb_lt in H_combinedGtC.
            lia.
        - destruct (⌈C⌉ᵦ =? ‖combinedOp‖) eqn:H_CeqCombinedOp.
          + rewrite Nat.eqb_eq in H_CeqCombinedOp.
            rewrite H_CeqCombinedOp.
            assumption.
          + rewrite Nat.ltb_lt in H_combinedGtC.
            lia.
      }
      
      assert( ⌊combinedOp⌋ᵦ = right → ( ((‖B‖ <=? ‖A‖ = true) → ⌊B⌋ᵦ = right) ∧  ((‖A‖ <=? ‖B‖ = true) → ⌊A⌋ᵦ = right))) as H_combinedOpRightImpliesAorBRight. {
        intros H_combinedOpRight.
        unfold combinedOp in H_combinedOpRight.
        unfold getNextOperation in H_combinedOpRight.
        destruct (A ≫ B) eqn:H_AGtB.
        - cbn [fst] in H_combinedOpRight.

          unfold opAGtB in H_AGtB.
          rewrite seqALengthFromNorm in H_AGtB.
          rewrite seqBLengthFromNorm in H_AGtB.
          rewrite H_isInsertB in H_AGtB.
          rewrite H_isRemoveA in H_AGtB.

          rewrite <-sidesEqual in H_combinedOpRight.
          rewrite combineEqualSides in H_combinedOpRight.
          rewrite splitOperationSide in H_combinedOpRight.
          rewrite seqBLengthFromNorm in H_combinedOpRight.
          rewrite H_isInsertB in H_combinedOpRight.

            
          unfold splitOperation in H_combinedOpRight.
          2: {
            rewrite splitOperationSide.
            rewrite seqBLengthFromNorm.
            rewrite H_isInsertB.

            destruct (‖B‖ =? ‖A‖) eqn:H_NAeqNB; auto.
            rewrite Nat.eqb_eq in H_NAeqNB.
            rewrite H_NAeqNB.
            rewrite sidesEqual with (A:=B).
            unfold smallerSide.
            replace (‖A‖ <? ‖A‖) with false; only 2: (symmetry; rewrite Nat.ltb_nlt; try lia ).
            now destruct (⌊A⌋ₐ); destruct (⌊B⌋ᵦ).
            rewrite H_AGtB.
            rewrite sidesEqual. auto.
          }

          destruct (‖B‖ <? ‖A‖) eqn:H_BLtA; auto.
          2: {
            unfold smallerSide in H_combinedOpRight.
            rewrite sidesEqual in H_combinedOpRight.
            now destruct (⌊A⌋ᵦ); destruct (⌊B⌋ᵦ).
          }
          split.
          now rewrite H_combinedOpRight.

          
          unfold opAGtB in H_AGtB.
          destruct (‖B‖ =? ‖A‖) eqn:H_BEqA.
          + rewrite <-sidesEqual.
            now destruct (⌊A⌋ₐ); destruct (⌊B⌋ᵦ); unfold smallerSide.
          + now replace (‖A‖ <=? ‖B‖) with false; only 2: (
              symmetry; 
              rewrite Nat.leb_nle; 
              rewrite Nat.ltb_lt in H_BLtA;
              rewrite Nat.eqb_neq in H_BEqA;
              lia
            ).
        - cbn [fst] in H_combinedOpRight.
          rewrite <-sidesEqual in H_combinedOpRight.

          unfold opAGtB in H_AGtB.
          rewrite seqALengthFromNorm in H_AGtB.
          rewrite seqBLengthFromNorm in H_AGtB.
          rewrite H_isInsertB in H_AGtB.
          rewrite H_isRemoveA in H_AGtB.
          destruct (‖B‖ <? ‖A‖) eqn:H_BltA.
          replace (‖B‖ =? ‖A‖) with false in H_AGtB; 
              only 1: discriminate;
              only 1: (symmetry; rewrite Nat.eqb_neq; rewrite Nat.ltb_lt in H_BltA; lia).

          rewrite combineEqualSides in H_combinedOpRight.
          2: {
            rewrite splitOperationSide.
            rewrite seqALengthFromNorm.
            rewrite H_isRemoveA.
            rewrite sidesEqual with (A:=B).
            destruct (‖B‖ =? ‖A‖) eqn:H_BeqA.
            - replace (‖A‖ <? ‖B‖) with false.
              + now destruct (⌊A⌋ₐ); destruct (⌊B⌋ᵦ); unfold smallerSide.
              + symmetry; rewrite Nat.eqb_eq in H_BeqA; rewrite Nat.ltb_nlt; lia.
            - replace (‖A‖ <? ‖B‖) with true.
              2: {
                symmetry; rewrite Nat.ltb_lt; rewrite Nat.ltb_nlt in H_BltA.
                rewrite Nat.eqb_neq in H_BeqA.
                lia.
              }
              auto.
          }
          split.
          destruct(‖B‖ =? ‖A‖) eqn:H_BeqA.
          + now rewrite H_combinedOpRight in H_AGtB; destruct (⌊B⌋ᵦ).
          + now replace (‖B‖ <=? ‖A‖) with false; only 2: (
              symmetry;
              rewrite Nat.leb_nle; 
              rewrite Nat.ltb_nlt in H_BltA;
              rewrite Nat.eqb_neq in H_BeqA; 
            lia).
          + rewrite <-sidesEqual.
            now rewrite H_combinedOpRight.
     }
        

      unfold opAGtB.
      rewrite seqALengthFromNorm.
      rewrite H_isRemoveA.
      split.
      + destruct (⌈C⌉ᵦ =? ‖A‖) eqn:H_CeqNA.
        * unfold opAGtB in H_combinedGtC.
          rewrite seqALengthFromNorm in H_combinedGtC.
          rewrite Nat.eqb_eq in H_CeqNA;
          assert(‖A‖ = Init.Nat.min (‖A‖) (‖B‖)) as H_AIsMin; try  lia;
          destruct (isRemove combinedOp) eqn:H_combinedIsRemove.
          1: destruct (⌈C⌉ᵦ =? 0); try discriminate H_combinedGtC.
          2: ( 
            rewrite <-H_AIsMin in H_combinedOpNorm;
            destruct (⌈C⌉ᵦ =? ‖combinedOp‖); try (rewrite Nat.ltb_lt in H_combinedGtC; lia )
          ).
            
          all: destruct (⌊combinedOp⌋ₐ) eqn:H_combinedOp; try discriminate H_combinedGtC.
          all: destruct (⌊C⌋ᵦ) eqn:H_sideC; try discriminate H_combinedGtC.
          all: rewrite sidesEqual in H_combinedOp.
          all: apply H_combinedOpRightImpliesAorBRight in H_combinedOp.
          all: replace (‖A‖ <=? ‖B‖) with true in H_combinedOp.
          2,4: (
            symmetry;
            rewrite Nat.leb_le;
            lia
          ).
          all: destruct H_combinedOp as [H1 H_combinedOp].
          all: now rewrite sidesEqual; rewrite H_combinedOp.

        * rewrite Nat.ltb_lt.
          rewrite Nat.eqb_neq in H_CeqNA.
          lia.
      + rewrite seqALengthFromNorm.
        destruct (isRemove B) eqn:H_isRemoveB.
        * destruct (0 <? ⌈B⌉ᵦ) eqn:H_BNormBigger0.
          -- unfold opAGtB in H_combinedGtC.
             destruct (isInsert A) eqn:H_isInsertA.
             ++ destruct (A) eqn:H_A; try discriminate.
                destruct (B) eqn:H_B; try discriminate.
                destruct entries; destruct entries0.
                cbn in combinedOp.
                destruct (Insert (Seq entries) side0 ≫ Remove (Seq entries0) side1) eqn:H_AGtB.
                all: unfold SplitHelper in combinedOp.
                all: unfold opAGtB in H_AGtB.
                all: cbn -[length Nat.ltb] in H_AGtB.
                1: destruct (Datatypes.length entries0 <? Datatypes.length entries) eqn:H_e0LtE.
                2: {
                  destruct (Datatypes.length entries0 =? Datatypes.length entries) eqn:H_E0eqE.
                  - destruct side0; destruct side1; try discriminate.
                  - discriminate H_AGtB.
                }

                2: destruct (Datatypes.length entries <? Datatypes.length entries0) eqn:H_e0LtE.
                3: {
                  destruct (Datatypes.length entries0 =? Datatypes.length entries) eqn:H_E0eqE.
                  - subst combinedOp.
                    repeat rewrite firstn_all in H_combinedGtC.
                    repeat rewrite skipn_all in H_combinedGtC.
                    destruct side0; destruct side1; cbn -[getLengthInSequenceB] in H_combinedGtC; 
                    try rewrite Tauto.if_same in H_combinedGtC; try discriminate.
                    now destruct (⌈C⌉ᵦ =? 0); destruct (⌊C⌋ᵦ).
                  - rewrite Nat.eqb_neq in H_E0eqE.
                    rewrite Nat.ltb_nlt in H_AGtB.
                    rewrite Nat.ltb_nlt in H_e0LtE.
                    lia.
                }

                all: simpl in combinedOp.
                all: unfold combinedOp in H_combinedGtC; cbn [getLengthInSequenceA SquashIterationDefinition fst snd] in H_combinedGtC.
                all: destruct (⌈C⌉ᵦ =? 0) eqn:H_CBeq0; try discriminate.
                now destruct side1; destruct (⌊C⌋ᵦ); simpl.
                destruct side0; destruct (⌊C⌋ᵦ); try discriminate H_combinedGtC.
                now destruct side1.
            ++ rewrite removeBImpliesCombinedOpAEq0 in H_combinedGtC; only 2: auto.
               destruct (⌈C⌉ᵦ) eqn:H_CB; try discriminate H_combinedGtC.
               rewrite <-sidesEqual in H_BisNonEmptyLeftRemove.
               destruct(⌊B⌋ₐ).
               ** discriminate H_BisNonEmptyLeftRemove.
               ** destruct (⌊combinedOp⌋ₐ); try discriminate H_combinedGtC.
                  destruct (⌊C⌋ᵦ); try discriminate H_combinedGtC.
                  auto.
          -- unfold opAGtB in H_combinedGtC.
             autorewrite * with changeset in *.
             rewrite_nat_all (⌈C⌉ᵦ = 0).
             destruct (⌊combinedOp⌋ᵦ) eqn:H_combinedOpSide; destruct (⌊C⌋ᵦ); try discriminate.

             destruct H_combinedOpRightImpliesAorBRight as [ H_combinedOpRightImpliesAorBRight _]; auto.
             now rewrite H_combinedOpRightImpliesAorBRight; auto with solve_nat.
        * destruct (⌈C⌉ᵦ =? ‖B‖) eqn:H_CeqNA.
          -- unfold opAGtB in H_combinedGtC.
             destruct (⌈C⌉ᵦ =? ⌈combinedOp⌉ₐ) eqn:H_combinedSame.
             ++ destruct (⌊combinedOp⌋ₐ) eqn:H_combinedOpSide; try discriminate.
                rewrite sidesEqual in H_combinedOpSide.
                forward H_combinedOpRightImpliesAorBRight; auto.
                destruct H_combinedOpRightImpliesAorBRight as [H_SideB].
                rewrite sidesEqual.
                rewrite H_SideB; auto with solve_nat.
            ++ assert_nat(‖B‖ ≤ ‖A‖) as H_BLeA.
               assert(⌈combinedOp⌉ₐ ≤ ‖combinedOp‖) as H_CombinedOpALeCombinedOpNorm. {
                 rewrite seqALengthFromNorm.
                 now destruct (isRemove combinedOp); lia.
               }
               solve_nat.
          -- auto with solve_nat.
Qed.

End SplitOpByLarger.

Section SwapProof.

Variables AHead BHead CHead : Operation.
Variables ATail BTail CTail : (list Operation).

Let lengthA_A := fst (getLengthInSequenceA SquashIterationDefinition AHead).
Let lengthB_A := fst (getLengthInSequenceA SquashIterationDefinition AHead).
Let lengthC_A := fst (getLengthInSequenceA SquashIterationDefinition AHead).
Let lengthA_B := fst (getLengthInSequenceB SquashIterationDefinition AHead).
Let lengthB_B := fst (getLengthInSequenceB SquashIterationDefinition AHead).
Let lengthC_B := fst (getLengthInSequenceB SquashIterationDefinition AHead).

Let OpResult1 :=  (getNextOperation SquashIterationDefinition AHead BHead).
Let CombinedOp := (fst (fst OpResult1)).
Let remainderA := (snd (fst OpResult1)).
Let remainderB := (snd OpResult1).

Let OpResult2 := (getNextOperation SquashIterationDefinition CombinedOp  CHead).
Let CombinedOp2 := (fst (fst OpResult2)).
Let remainderAB := (snd (fst OpResult2)).
Let remainderC := (snd OpResult2).

Let lengthOp := fst (getLengthInSequenceA SquashIterationDefinition CombinedOp).
Let lengthC  := fst (getLengthInSequenceB SquashIterationDefinition CHead).
Let sideC  := snd (getLengthInSequenceB SquashIterationDefinition CHead).

Definition minSplitLength (A B C : Operation) : nat := (min (min (min lengthA_A lengthB_B) lengthB_A) lengthC_B).
Definition splitOp (op:Operation) := snd (splitOperation SquashIterationDefinition op lengthC sideC).
Let splitOpC := opAGtB SquashIterationDefinition CombinedOp CHead.
 
Definition AHeadSplit := if splitOpC then if (isInsert BHead) then [AHead] else splitOp AHead else remainderA.
Definition BHeadSplit := if splitOpC then splitOp BHead else remainderB.
Definition CHeadSplit := remainderC.

Definition MyFun3 := (AHeadSplit, BHeadSplit, CombinedOp, remainderA, remainderB, remainderAB, getNextOperation SquashIterationDefinition (↩AHeadSplit) (↩BHeadSplit)).

Transparent length.
Transparent splitOperation.
Eval compute in ((Skip 0 right)[≫≫ 0 ; left ]).

(* Opaque computeResultingOperation. *)

Eval compute in (OList [Remove (Seq [<$1, 1>]) right]) ○ (OList [Insert (Seq []) right]).
(*
  ll (Remove< [<$1,1>]) (Insert< [])
  rl (Remove< []) (Insert< []); Remove> [<$1,1>]] <[] <[] -> Insert
  rr (Remove> []) (Insert> []); Remove> [<$1,1>] >[] >[] -> Insert
  lr (Remove< [<$1,1>]) (Insert< []); Insert> []]
*)
Eval compute in (OList [Remove (Seq []) left]) ○ (OList [Insert (Seq [<$1, 1>]) right]).
(*
  ll (Remove< []) (Insert< []); Insert< [<$1,1>]] -> <[] <[] -> Remove
  rl (Remove< []) (Insert< [<$1,1>]); Remove> []]
  rr (Remove> []) (Insert> [<$1,1>])]
  lr (Remove< []) (Insert< []); Insert> [<$1,1>]] -> <[] <[] -> Remove
*)

Eval compute in (getNextOperation SquashIterationDefinition (Skip> 0) (Insert> [])).


Lemma getNextOperationInsert: ∀(A B:Operation), (isInsert B) = true → (getNextOperation SquashIterationDefinition A B) =
                              if (A ≫ B) then 
                                (B, if (opAEmptyAndSameSide SquashIterationDefinition A B) then [] else [A], []) else 
                                (A ⊕ (Insert (Seq []) (⌊A⌋ᵦ)) ⊖ false, [], if (‖B‖ =? 0) && (Bool.eqb (isLeft (⌊A⌋ₐ)) (isLeft (⌊B⌋ₐ))) then [] else [B]).
intros.
unfold opAEmptyAndSameSide.
rewrite <-sidesEqual.
unfold getNextOperation.
destruct (A ≫ B) eqn:AGtB.
- apply ASplit_lenAGelenB in AGtB as H_AgeB.
  set (lenB:=⌈B⌉ᵦ).
  destruct B eqn:H_B; unfold isInsert in H; try discriminate H.
  destruct entries.
  cbv in lenB.
  unfold lenB.
  destruct ((‖A‖ =? 0) && (Bool.eqb (isLeft (⌊A⌋ₐ)) (isLeft (⌊B⌋ₐ)))) eqn:H_AEmptyBool.
  + apply andb_prop in H_AEmptyBool as H_AEmpty.
    destruct H_AEmpty as [H_lenA H_sideAB].
    rewrite Nat.eqb_eq in H_lenA.
    rewrite eqb_true_iff in H_sideAB.

    unfold opAGtB in AGtB.
    rewrite seqALengthFromNorm in AGtB. rewrite H_lenA in AGtB.
    rewrite seqBLengthFromNorm in AGtB. unfold isInsert in AGtB.
    rewrite Tauto.if_same in AGtB.
    rewrite H_B in H_sideAB.
    destruct side0 eqn:H_side0.
    all: destruct(⌊A⌋ₐ) eqn:H_sideA.
    all: cbv in H_sideAB; try discriminate H_sideAB.
    all: simpl in AGtB; try discriminate AGtB.

  + apply andb_false_iff in H_AEmptyBool as H_AEmpty.
   
    rewrite splitOperationWith0Empty.
    rewrite splitOperationWith0Unchanged.
    2: {
      destruct(0 <? ‖A‖) eqn:H_0ltNormA.
      - rewrite Nat.ltb_lt in H_0ltNormA.
        lia.
      - rewrite Nat.ltb_nlt in H_0ltNormA.
        assert(‖A‖ = 0) as H_normA. lia.
        right. split. lia.
        rewrite <-Nat.eqb_eq in H_normA.
        rewrite H_normA in H_AEmpty.
        destruct H_AEmpty as [H_AEmpty | H_AEmpty]; try discriminate H_AEmpty.
        rewrite eqb_false_iff in H_AEmpty.
        unfold isLeft in H_AEmpty.
        rewrite <-H_B.
        repeat rewrite <-sidesEqual.
        destruct (⌊A⌋ₐ) eqn:H_sideA.
        all: destruct (⌊B⌋ₐ) eqn:H_sideB; cbv in H_AEmpty.
        1: contradiction H_AEmpty; auto.
        3: contradiction H_AEmpty; auto.

        + unfold opAGtB in AGtB.
          unfold getLengthInSequenceB in AGtB.
          unfold SquashIterationDefinition at 1 in AGtB.
          unfold SquashIterationDefinition at 3 in AGtB.
          rewrite Nat.eqb_eq in H_normA.
          rewrite seqALengthFromNorm in AGtB.
          rewrite H_normA in AGtB.
          rewrite Tauto.if_same in AGtB.
          unfold fst in AGtB.
          replace (0=?0) with true in AGtB.
          rewrite H_sideA in AGtB.
          discriminate AGtB.
        + auto.
  }
  
  rewrite H_B in H_AEmptyBool.
  destruct A; 
    try destruct entries0; 
    unfold computeResultingOperation; 
    simpl; 
    simpl in H_AEmptyBool;
    rewrite H_AEmptyBool;
    auto.
  
- apply ASplit_lenALelenB in AGtB as H_AleB.
  destruct B eqn:H_B; unfold isInsert in H; try discriminate H.
  destruct entries.
  set (lenA:=⌈A⌉ₐ).
  fold lenA in H_AleB.
  simpl in H_AleB.
  assert(lenA = 0) as H_lenAeq0. { lia. }
  rewrite H_lenAeq0.
  rewrite splitOperationWith0Empty.

  unfold opAGtB in AGtB.
  fold lenA in AGtB. rewrite H_lenAeq0 in AGtB.
  set (sideA:=⌊A⌋ₐ).
  fold sideA in AGtB.
  unfold getLengthInSequenceB in AGtB.
  simpl in AGtB.
  destruct sideA eqn:H_sideA; destruct side0 eqn:H_side0; try discriminate AGtB.
  unfold smallerSide.
  rewrite Tauto.if_same.
  + unfold opLength.
    destruct (Datatypes.length entries =? 0) eqn:H_lenEntrisEq0.
    * unfold getLengthInSequenceA at 1.
      unfold SquashIterationDefinition at 5.
      unfold isLeft.
      unfold snd at 3.
      unfold andb.
      unfold splitOperation.
      unfold SquashIterationDefinition at 2.
      unfold SplitHelper.
      assert (0 <? Datatypes.length entries = false) as H_lenEntrisNGt0. {
        rewrite Nat.ltb_nlt. 
        rewrite Nat.eqb_eq in H_lenEntrisEq0.
        lia.
      }
      rewrite H_lenEntrisNGt0.
      unfold snd at 1.
      unfold Bool.eqb.
      unfold sideA in H_sideA.
      rewrite sidesEqual in H_sideA.
      rewrite H_sideA.
      reflexivity.
    * unfold andb.
      rewrite splitOperationWith0Unchanged.
      2: {
        unfold opLength.
        left.
        assert (Datatypes.length entries > 0). {
          rewrite Nat.eqb_neq in H_lenEntrisEq0.
          lia.
        }
        assumption.
      }
      unfold sideA in H_sideA.
      rewrite sidesEqual in H_sideA.
      rewrite H_sideA.
      auto.
  + change (⌊Insert> entries⌋ₐ) with right.
    unfold isLeft.
    unfold andb.
    rewrite Tauto.if_same.
    rewrite splitOperationWith0Unchanged.
    2: {
      unfold opLength.
      destruct (0 <? Datatypes.length entries) eqn:H_lenEntries.
      - rewrite Nat.ltb_lt in H_lenEntries. auto.
      - right.
        split.
        rewrite Nat.ltb_nlt in H_lenEntries. lia.
        unfold getLengthInSequenceB. unfold SquashIterationDefinition.
        auto.
    }
    unfold Bool.eqb.
    rewrite Tauto.if_same.
    unfold smallerSide.
    unfold sideA in H_sideA.
    rewrite sidesEqual in H_sideA.
    rewrite H_sideA.
    auto.
  + unfold opLength.
    destruct (Datatypes.length entries =? 0) eqn:H_lenEntrisEq0.
    * unfold getLengthInSequenceA at 1.
      unfold SquashIterationDefinition at 5.
      unfold isLeft.
      unfold snd at 3.
      unfold andb.
      unfold splitOperation.
      unfold SquashIterationDefinition at 2.
      unfold SplitHelper.
      assert (0 <? Datatypes.length entries = false) as H_lenEntrisNGt0. {
        rewrite Nat.ltb_nlt. 
        rewrite Nat.eqb_eq in H_lenEntrisEq0.
        lia.
      }
      rewrite H_lenEntrisNGt0.
      unfold snd at 1.
      unfold smallerSide.
      unfold Bool.eqb.
      unfold sideA in H_sideA.
      rewrite sidesEqual in H_sideA.
      rewrite H_sideA.
      reflexivity.
    * unfold andb.
      rewrite splitOperationWith0Unchanged.
      2: {
        unfold opLength.
        left.
        assert (Datatypes.length entries > 0). {
          rewrite Nat.eqb_neq in H_lenEntrisEq0.
          lia.
        }
        assumption.
      }
      unfold smallerSide.
      rewrite Tauto.if_same.
      unfold sideA in H_sideA.
      rewrite sidesEqual in H_sideA.
      rewrite H_sideA.
      reflexivity.
Qed.

Lemma AGtBImpliesNotEmptyAndSameSide: ∀ (A B:Operation), (A ≫ B) = true → (opAEmptyAndSameSide SquashIterationDefinition A B) = false.
intros.
rename H into H_AGtB.
unfold opAEmptyAndSameSide.
unfold opAGtB in H_AGtB.
destruct (‖A‖ =? 0) eqn:H_NAeq0.
- destruct(⌈B⌉ᵦ =? ⌈A⌉ₐ) eqn:H_BeqA.
  + destruct (⌊A⌋ₐ) eqn:H_sideA; try discriminate H_AGtB.
    destruct (⌊B⌋ᵦ) eqn:H_sideB; try discriminate H_AGtB.
    unfold isLeft.
    auto.
  + rewrite Nat.eqb_eq in H_NAeq0.
    replace (⌈A⌉ₐ) with 0 in H_AGtB. 2: {
      rewrite seqALengthFromNorm.
      rewrite H_NAeq0.
      rewrite Tauto.if_same.
      reflexivity.
    }
    rewrite Nat.ltb_lt in H_AGtB.
    lia.
- auto.
Qed.

Lemma getNextOperationCombinationLengthCSmaller: (CombinedOp ≫ CHead) = true → 
    (∃ (remABOp remAOp remBOp : Operation), (
      remainderAB = [remABOp]) ∧ 
      [remAOp] = AHeadSplit ∧ 
      (*((opAEmptyAndSameSide SquashIterationDefinition AHead BHead) = true → [] = BHeadSplit) ∧ 
      ((opAEmptyAndSameSide SquashIterationDefinition AHead BHead) = false → *)[remBOp] = BHeadSplit ∧ 
      (remABOp, remainderA, remainderB) = (getNextOperation SquashIterationDefinition remAOp remBOp)).
intros.
assert(splitOpC = true) as H_splitOpC. rewrite <-H. auto.
Opaque computeResultingOperation. Opaque splitOperation.
cbv delta [AHeadSplit BHeadSplit splitOp]. cbv beta. fold splitOpC. rewrite H_splitOpC. auto.
simpl. 

specialize splitOperationRemainder with (A:=AHead) (B:=CHead) as H_AHead.
specialize splitOperationRemainder with (A:=BHead) (B:=CHead) as H_BHead. 
specialize splitOperationRemainder with (A:=CombinedOp) (B:=CHead) as H_CHead. 

destruct ((isInsert BHead)) eqn:H_isInsertB.
- specialize getNextOperationInsert with (A:=AHead) (B:=BHead) as H_NextOp.
  set (nextOp:=getNextOperation SquashIterationDefinition AHead BHead).
  forward H_NextOp; only 1: assumption.
  unfold remainderAB.
  unfold remainderA.
  unfold remainderB.
  unfold OpResult2.
  cbv delta [getNextOperation].
  cbv zeta.
  cbv beta.
  rewrite H.
  set (x:=snd (fst (CombinedOp [≺ᵦCHead] ⊕ CHead ⊖ true, CombinedOp [≫ᵦCHead], []))).
  fold lengthC in x.
  fold sideC in x.
  simpl in x.
  unfold x.

  unfold CombinedOp.
  unfold OpResult1.
  rewrite H_NextOp.

  unfold CombinedOp in H.
  unfold OpResult1 in H.
  rewrite H_NextOp in H.
  Opaque getNextOperation.
  destruct (AHead ≫ BHead) eqn:AGtB.
  + simpl in H. 
    apply AGtBImpliesNotEmptyAndSameSide with (A:=AHead) (B:=BHead) in AGtB as H_ANotEmptyAndSameSideFalse.
    change (fst (fst (BHead, if (‖AHead‖ =? 0) && negb (isLeft (⌊BHead⌋ₐ)) then [] else [AHead], []))) with BHead. 
    forward H_BHead; auto.
    destruct H_BHead as [remABOp H_BHead].
    exists remABOp. rewrite <-H_BHead.
    exists AHead. exists remABOp. rewrite <-H_BHead.
    split. auto.
    split. auto.
    split. auto.
    rewrite H_ANotEmptyAndSameSideFalse.
    intros. (*discriminate H0.*)
    
    assert (AHead ≫ remABOp = true) as H_AheadGtremABOp. {
      specialize splitOperationLengthR2 with (A:=BHead) (y:=lengthC) (s:=sideC) as H_splitLenOp.
      unfold lengthC in H_splitLenOp. unfold sideC in H_splitLenOp.
      rewrite H_BHead in H_splitLenOp.
      unfold getOpFromArray in H_splitLenOp.
      forward H_splitLenOp. discriminate.
      cbn [hd] in H_splitLenOp.
      unfold opAGtB.
      unfold opAGtB in AGtB.
      rewrite seqBLengthFromNorm in AGtB.
      rewrite seqBLengthFromNorm.
      rewrite H_isInsertB in AGtB.
      specialize splitOpRemainsInsert with (A:=BHead) (C:=CHead) as H_remOpIsInsert.
      rewrite H_BHead in H_remOpIsInsert.
      cbn [getOpFromArray hd] in H_remOpIsInsert.
      forward H_remOpIsInsert. discriminate.
      rewrite H_remOpIsInsert.
      rewrite H_isInsertB.
      destruct(0 =? ⌈AHead⌉ₐ) eqn:H_AheadLength.
      - destruct (⌊AHead⌋ₐ) eqn:H_sideA; destruct (⌊BHead⌋ᵦ) eqn:H_sideB; try discriminate AGtB.
        (*Transparent splitOperation.*)
        (*Transparent SplitHelper.*)
        all: cbn [splitOperation SquashIterationDefinition SplitHelper] in H_BHead;
        destruct BHead eqn:H_BHeadSplit; destruct side0; try discriminate H_sideB;
        unfold SplitHelper in H_BHead;
        fold lengthC in H_BHead;
        fold sideC in H_BHead.
        2-5: destruct entries.
        1: destruct(lengthC <? amount).
        3-5: destruct (lengthC <? length entries) eqn:H_lengthC.
        all: try discriminate H_BHead.
        all: simpl in H_BHead; destruct (⌊remABOp⌋ᵦ) eqn:H_sideRemABOP; auto.
        all: cbv in H_sideB; try discriminate H_sideB.
        * destruct remABOp; try discriminate H_BHead.
            destruct side0 eqn:H_side0; try discriminate H_BHead.
            destruct entries0.
            cbv in H_sideRemABOP.
            discriminate H_sideRemABOP.
     - auto.
    }
    rewrite H_AheadGtremABOp.
    change remABOp with (getOpFromArray [remABOp]).
    rewrite <-H_BHead.
    change (snd (fst (BHead, if opAEmptyAndSameSide SquashIterationDefinition AHead BHead then [AHead] else [], []))) with 
           (if opAEmptyAndSameSide SquashIterationDefinition AHead BHead then [] else [AHead]).
    (*set (Y:=(snd (BHead, if (opAEmptyAndSameSide SquashIterationDefinition AHead BHead) then [] else [AHead], []))).
    unfold snd in Y.
    unfold Y.*)
    cbn -[getLengthInSequenceA getLengthInSequenceB].

    rewrite combineWithInsertIsInsert.
    2: {
      rewrite splitOpRemainsInsert.
      assumption.
      auto.
      rewrite H_BHead.
      discriminate.
    }

    replace (⌈↩BHead [≫ᵦCHead]⌉ᵦ) with 0.
    2: {
      rewrite seqBLengthFromNorm.
      rewrite splitOpRemainsInsert.
      rewrite H_isInsertB.
      auto.
      rewrite H_BHead.
      discriminate.
    }

    (*rewrite H_ANotEmptyAndSameSideFalse.*)

    destruct(‖AHead‖ =? 0) eqn:H_AHeadNormEq0.
    * apply ASplit_lenAGelenB in AGtB as H_AGeB.
      apply AGtB_lenAGelenB in H as H_BGeC.
      assert(⌈AHead⌉ₐ = 0). { 
        rewrite seqALengthFromNorm.
        rewrite Nat.eqb_eq in H_AHeadNormEq0.
        rewrite H_AHeadNormEq0. 
        rewrite Tauto.if_same. 
        auto. 
      }
      assert(⌈BHead⌉ᵦ = 0). { lia. }

      assert (⌊AHead⌋ᵦ = right) as H_AHeadSideRight. {
        unfold opAGtB in AGtB.
        
        rewrite H0 in AGtB.
        replace (⌈BHead⌉ᵦ) with 0 in AGtB.
        replace (0 =? 0) with true in AGtB.
        2: {
          symmetry.
          rewrite Nat.eqb_eq.
          auto.
        }
        rewrite <-sidesEqual.
        destruct (⌊AHead⌋ₐ); try discriminate AGtB.
        auto.
      }
      (* split. *)
      auto.

      rewrite Nat.eqb_eq in H_AHeadNormEq0.
      destruct( ⌊BHead⌋ₐ ) eqn:H_BHeadSide.
      **  unfold isLeft.
          unfold negb.
          unfold andb.

          replace (⌊↩BHead [≫ᵦCHead]⌋ᵦ) with left.
          2: {
            rewrite <-sidesEqual.
            rewrite sideRemainsUnchanged.
            rewrite H_BHeadSide.
            auto.
            rewrite H_BHead.
            discriminate.
          }
          rewrite splitOperationWith0Unchanged.
          2: {
            right.
            split. assumption.
            split. assumption.
            auto.
          }
          auto.
      **  unfold opAEmptyAndSameSide in H_ANotEmptyAndSameSideFalse.
          rewrite H_AHeadNormEq0 in H_ANotEmptyAndSameSideFalse.
          rewrite sidesEqual in H_ANotEmptyAndSameSideFalse.
          rewrite H_AHeadSideRight in H_ANotEmptyAndSameSideFalse.
          rewrite <-sidesEqual in H_ANotEmptyAndSameSideFalse.
          rewrite H_BHeadSide in H_ANotEmptyAndSameSideFalse.
          cbv in H_ANotEmptyAndSameSideFalse.
          discriminate H_ANotEmptyAndSameSideFalse.
    
    * unfold andb.
      rewrite splitOperationWith0Unchanged.
      2: {
        rewrite Nat.eqb_neq in H_AHeadNormEq0.
        lia.
  	  }
      auto.
  + cbn -[getLengthInSequenceB] in H.
    apply ASplit_lenALelenB in AGtB as H_AltB.
    rewrite seqBLengthFromNorm in H_AltB.
    rewrite H_isInsertB in H_AltB.
    cbn [fst].
    
    apply AGtB_lenAGelenB in H as H_lenCHead.
    assert((⌈AHead ⊕ (Insert (Seq []) (⌊AHead⌋ᵦ)) ⊖ false⌉ₐ) = 0) as H_comLenEq0. {
      destruct AHead.
      Transparent computeResultingOperation.
      all: unfold computeResultingOperation; unfold SquashIterationDefinition at 2.
      Opaque computeResultingOperation.
      1-2: cbv; auto.
      destruct entries.
      lia.
    }
    rewrite H_comLenEq0 in H_lenCHead.
    assert(lengthC = 0) as H_lengthCeq0. { unfold lengthC. lia. }
    rewrite H_lengthCeq0.
    assert (sideC = left ∧ ⌊AHead ⊕ (Insert (Seq []) (⌊AHead⌋ᵦ)) ⊖ false⌋ₐ = right) as H_Sides. {
      apply destructAGreaterB in H as H_CHeadEq0.
      rewrite H_comLenEq0 in H_CHeadEq0.
      fold lengthC in H_CHeadEq0.
      rewrite H_lengthCeq0 in H_CHeadEq0.
      destruct H_CHeadEq0 as [H_CHeadEq0|H_CHeadEq0]. 
      - rewrite Nat.ltb_lt in H_CHeadEq0.
        contradict H_CHeadEq0. lia.
      - fold sideC in H_CHeadEq0.
        destruct H_CHeadEq0 as [_ [H_CHeadEq1 H_CHeadEq0]].
        split. assumption.
        assumption.
    }
    destruct H_Sides as [H_sideC H_sidesCombined].
    rewrite H_sideC.
    rewrite splitOperationWith0Unchanged.
    2: {
      rewrite sidesEqual in H_sidesCombined.
      rewrite H_sidesCombined.
      destruct (0 <? ‖AHead ⊕ Insert (Seq []) (⌊AHead⌋ᵦ) ⊖ false‖) eqn:H_0ltN.
      - rewrite Nat.ltb_lt in H_0ltN.
        auto.
      - rewrite Nat.ltb_nlt in H_0ltN.
        right.
        split.
        lia.
        auto.
    }

      assert (BHead [≫≫0; left] = if ((‖BHead‖ =? 0) && (isLeft (⌊BHead⌋ᵦ))) then [] else [BHead]) as H_BHeadReplacement. {
        destruct BHead eqn:H_BHeadFull; unfold isInsert in H_isInsertB; try discriminate H_isInsertB.
        destruct entries.
        Transparent splitOperation.
        unfold splitOperation.
        unfold SquashIterationDefinition at 1.
        unfold SplitHelper.
        Opaque splitOperation.
        destruct (‖BHead‖ =? 0) eqn:H_normBHead.
        - unfold opLength in H_normBHead.
          rewrite H_BHeadFull in H_normBHead.
          replace (0 <? Datatypes.length entries) with false.
          2: {
            symmetry.
            rewrite Nat.ltb_nlt.
            rewrite Nat.eqb_eq in H_normBHead.
            lia.
          }
          unfold opLength.
          rewrite H_normBHead.
          destruct side0 eqn:H_side0.
          + cbv; auto.
          + unfold isLeft.
            unfold getLengthInSequenceB.
            unfold SquashIterationDefinition at 1.
            rewrite Nat.eqb_eq in H_normBHead.
            rewrite H_normBHead.
            rewrite skipn_O.
            simpl.
            auto.
        - unfold opLength in H_normBHead.
          rewrite H_BHeadFull in H_normBHead.
          replace (0 <? Datatypes.length entries) with true.
          2: {
            symmetry.
            rewrite Nat.ltb_lt.
            rewrite Nat.eqb_neq in H_normBHead.
            lia.
          }
          unfold opLength.
          rewrite H_normBHead.
          rewrite skipn_O.
          auto.
      }
      rewrite H_BHeadReplacement.

    exists (AHead ⊕ (Insert (Seq []) (⌊AHead⌋ᵦ))  ⊖ false).
    exists (AHead).

    assert (⌊AHead⌋ₐ = right) as H_sideA. {
      destruct AHead; 
      try destruct entries;
      cbn [computeResultingOperation] in H_sidesCombined;
      assumption.
    }
    assert((‖BHead‖ =? 0) && isLeft (⌊BHead⌋ᵦ) = false) as H_BHeadNot0AndLeft. {
      unfold opAGtB in AGtB.
      replace (⌈AHead⌉ₐ) with 0 in AGtB; only 2:lia.
      destruct (‖BHead‖ =? 0) eqn:H_BHeadLength.
      - rewrite seqBLengthFromNorm in AGtB.
        rewrite H_isInsertB in AGtB.
        rewrite H_sideA in AGtB.
        cbn -[getLengthInSequenceB] in AGtB.
        destruct (AGtB); try discriminate AGtB; auto.
      - auto.
    }
    rewrite H_BHeadNot0AndLeft.

    exists (BHead).
    repeat split; auto.

- 
specialize splitByLargerOp with (A:=AHead) (B:=BHead) (C:=CHead).
fold OpResult1. fold CombinedOp. fold splitOpC. rewrite H_isInsertB. intros. forward H0; auto.

give_up.
destruct H0 as [H_ASmaller H_BSmaller].
forward H_AHead. auto. destruct H_AHead as [remASplit H_remA]. fold lengthC in H_remA. fold sideC in H_remA. rewrite H_remA.
forward H_BHead. auto. destruct H_BHead as [remB H_remB]. fold lengthC in H_remB. fold sideC in H_remB. rewrite H_remB.

assert (∃ remABOp : Operation,  remainderAB = [remABOp]). {
  cbv delta [remainderAB OpResult2 getNextOperation]. cbv beta. fold splitOpC. rewrite H_splitOpC.
  cbv zeta. hnf. fold lengthC. fold sideC. 
  Opaque computeResultingOperation. Opaque splitOperation.
  simpl. specialize splitOperationRemainder with (A:=CombinedOp) (B:=CHead) as H2. 
  fold lengthC in H2. fold sideC in H2. 
  apply H2. auto.
}

destruct H0.
rewrite H0.
exists x. 

set (remA := if (isInsert BHead) then AHead else remASplit).
exists remA. exists remB.
split. 

(* Proof remainderAB = [remABOp] *)
auto.

split.

(* Proof [remAOp] = AHeadSplit *)
{ 
  unfold remA.
  rewrite H_isInsertB.
  auto.
}

(* Proof [remBOp] = BHeadSplit *)
split. auto.

(* Proof (remABOp, remainderA, remainderB) = (getNextOperation SquashIterationDefinition remAOp remBOp) *)
cbv delta [remainderAB OpResult2 getNextOperation]. cbv beta. fold splitOpC. 

set (splitOpARem := opAGtB SquashIterationDefinition remA remB).
set (splitOpA := opAGtB SquashIterationDefinition AHead BHead).

  assert(splitOpARem = splitOpA) as H_spOAREMeqspOA. 
  unfold splitOpARem.
  unfold splitOpA.
  rewrite <-resolveNonEmptyArray with (x:=remA) (y:=[remA]); auto. unfold remA. rewrite H_isInsertB.  rewrite <-H_remA.
  rewrite <-resolveNonEmptyArray with (x:=remB) (y:=[remB]); auto. rewrite <-H_remB.
  unfold lengthC. unfold sideC.

  apply splitLengthPreservedUnderCut with (A:=AHead) (B:=BHead) (C:=CHead); auto.


  Opaque getLengthInSequenceA. Opaque getLengthInSequenceB.
  simpl.

  unfold remainderA.
  unfold remainderB.
  cbv delta [OpResult1 getNextOperation]. cbv beta. simpl.
  fold splitOpA.
  (*rewrite <-H1.*)

  case_eq (splitOpARem).
  (* AHead is being split *)
  intros H_SplitOpARemTrue.

  rewrite <-resolveNonEmptyArray with (x:=remA) (y:=[remA]); auto.
  rewrite <-resolveNonEmptyArray with (x:=remB) (y:=[remB]); auto.
  rewrite <-H_spOAREMeqspOA.
  rewrite H_SplitOpARemTrue.
  unfold remA.
  rewrite H_isInsertB.
  rewrite <-H_remA. rewrite <-H_remB. unfold lengthC. unfold sideC.

  f_equal.
  f_equal.

  rewrite <-resolveNonEmptyArray with (x:=x) (y:=remainderAB); auto.
  unfold remainderAB.
  unfold OpResult2.
  Transparent getNextOperation.
  unfold getNextOperation.
  fold splitOpC. rewrite H_splitOpC.
  simpl.
  unfold CombinedOp. unfold OpResult1. unfold getNextOperation.
  fold splitOpA.
  rewrite <-H_spOAREMeqspOA. rewrite H_SplitOpARemTrue.
  simpl.

  apply swapCombineWithSplitOfA; auto.
  apply swapSplitRemainderWithShorterSplitBLen; auto.

  (* BHead is being split *)
  intros H_SplitOpARemTrue.

  rewrite <-resolveNonEmptyArray with (x:=remA) (y:=[remA]); auto.
  rewrite <-resolveNonEmptyArray with (x:=remB) (y:=[remB]); auto.
  unfold remA.
  rewrite H_isInsertB.
  rewrite <-H_remA. rewrite <-H_remB. unfold lengthC. unfold sideC.

  f_equal.
  f_equal.

  rewrite <-resolveNonEmptyArray with (x:=x) (y:=remainderAB); auto.
  unfold remainderAB.
  unfold OpResult2.
  unfold getNextOperation.
  fold splitOpC. rewrite H_splitOpC.
  simpl.
  unfold CombinedOp. unfold OpResult1. unfold getNextOperation.
  fold splitOpA. rewrite <-H_spOAREMeqspOA. rewrite H_SplitOpARemTrue.
  simpl.

  rewrite swapCombineWithSplitOfB; auto.
  fold splitOpA. rewrite <-H_spOAREMeqspOA. rewrite H_SplitOpARemTrue. auto.

  fold splitOpA. rewrite <-H_spOAREMeqspOA. rewrite H_SplitOpARemTrue.

  rewrite swapSplitRemainderWithShorterSplitALen with (C:=CHead); auto.
Admitted.

Lemma getNextOperationCombinationLengthCBigger: (splitOpC = false ) → 
     (remainderAB = [] ∧ 
     remainderA = AHeadSplit ∧
     remainderB = BHeadSplit).
intros.
split. {
 unfold remainderAB. unfold OpResult2. cbv delta [getNextOperation]. cbv beta. fold splitOpC. rewrite H. simpl. reflexivity.
}
split. {
 unfold AHeadSplit. rewrite H. reflexivity.
}
 unfold BHeadSplit. rewrite H. reflexivity.
Qed.

Lemma moveOperationIntoSquash: (OList (AHeadSplit++ATail) ○ OList (BHeadSplit++BTail) = OList (remainderAB ++ getOListEntries (OList (remainderA ++ ATail) ○ OList (remainderB ++ BTail)))) ∧ (remainderC=CHeadSplit).
  split.

  (* assert (lengthC < lengthOp ∨ lengthC >= lengthOp) as LenEq. lia. *)
  case_eq splitOpC.  intros H_splitOpC.

  (* Case splitOpC = true *)
  destruct (opAEqB SquashIterationDefinition CombinedOp CHead) eqn:H_ABSameSize.
  assert(⌈CombinedOp⌉ₐ = ⌈CHead⌉ᵦ ∧ ⌊CombinedOp⌋ₐ =⌊CHead⌋ᵦ).
  unfold opAEqB in H_ABSameSize.
  split.
  destruct (⌈CHead⌉ᵦ =? ⌈CombinedOp⌉ₐ) eqn:lenAeqlenB; try discriminate H_ABSameSize; try apply beq_nat_true in lenAeqlenB; auto. 
  destruct (⌈CHead⌉ᵦ =? ⌈CombinedOp⌉ₐ) eqn:lenAeqlenB; destruct(⌊CombinedOp⌋ₐ) eqn:H_Aside; destruct(⌊CHead⌋ᵦ) eqn:H_Bside; try discriminate H_ABSameSize; try apply beq_nat_true in lenAeqlenB; auto. 
  
  destruct H.
  assert(AHeadSplit = []). unfold AHeadSplit. rewrite H_splitOpC. unfold splitOp. give_up.
  assert(BHeadSplit = []). unfold BHeadSplit. rewrite H_splitOpC. unfold splitOp. give_up.
  assert(remainderA = []). give_up.
  assert(remainderB = []). give_up.
  assert(remainderAB = []). give_up.
  rewrite H1. rewrite H2. rewrite H3. rewrite H4. rewrite H5. auto.

  assert(CombinedOp ≫ CHead = true) as H_COpEqCH. give_up.
  specialize getNextOperationCombinationLengthCSmaller as H. 
  forward H; auto.
  destruct H as [remABOp [remAOp [remBOp [H_remainderAB [H_AHeadSplit [H_BHeadSplit H_Remainders]]]]]].

  specialize extractFirstSquashOp with (A:=AHeadSplit++ATail) (B:=BHeadSplit++BTail).

  resolveLet remainderABOp.
  intros H_extractFirstOp.

  
  forward H_extractFirstOp. {
    split.
    - rewrite <-H_AHeadSplit. specialize nil_cons with (x:=remAOp) (l:=ATail). auto.
    - rewrite <-H_BHeadSplit. specialize nil_cons with (x:=remBOp) (l:=BTail). auto.
  }
  rewrite H_extractFirstOp.
  Opaque getNextOperation.
  Opaque squash.
  simpl.

  assert (remainderAB = [(fst (fst remainderABOp))]) as H_RAB. unfold remainderABOp. rewrite <-H_AHeadSplit. rewrite <-H_BHeadSplit. simpl. rewrite <-H_Remainders. simpl. rewrite <-H_remainderAB. auto.
  assert (remainderA = (snd (fst remainderABOp))) as H_RA. unfold remainderABOp. rewrite <-H_AHeadSplit. rewrite <-H_BHeadSplit. simpl. rewrite <-H_Remainders. simpl. auto.
  assert (remainderB = (snd remainderABOp)) as H_RB. unfold remainderABOp. rewrite <-H_AHeadSplit. rewrite <-H_BHeadSplit. simpl. rewrite <-H_Remainders. simpl.  auto.

  rewrite H_RAB. 
  rewrite H_RA. 
  rewrite H_RB.
  fold combinedOp.
  fold remainderA0. 
  fold remainderB0.
  simpl. rewrite <-H_AHeadSplit. rewrite <-H_BHeadSplit. simpl.
  intros.

  reflexivity.

  (* Case splitOpC = false *)
  intros H_splitOpC.
  specialize getNextOperationCombinationLengthCBigger as H. 
  forward H. auto.
  destruct H as [HremAB [HremA HremB]].
  rewrite HremAB.
  rewrite HremA.
  rewrite HremB.
  simpl.
  unfold getOListEntries. destruct (OList (AHeadSplit ++ ATail) ○ OList (BHeadSplit ++ BTail)). auto.
  auto. 
  Admitted.

Let SwappedOpResult2 := (getNextOperation SquashIterationDefinition CHead CombinedOp).
Lemma reverseCombine1: (snd(fst(SwappedOpResult2))) = (snd(OpResult2)).
Admitted.

Lemma reverseCombine2: (snd(SwappedOpResult2)) = (snd(fst(OpResult2))).
Admitted.

Let OpResultBC :=  (getNextOperation SquashIterationDefinition BHead CHead).
Let OpResultA_BC := (getNextOperation SquashIterationDefinition AHead (fst (fst OpResultBC))).
Lemma reverseCombine3: (fst( (fst OpResultA_BC)) = (fst(fst(OpResult2)))).
Admitted.

Lemma lengthOfSplitHeads: (Datatypes.length AHeadSplit) + (Datatypes.length BHeadSplit) + (Datatypes.length CHeadSplit) < 3.
Admitted.

End SwapProof.

Transparent length.
Transparent splitOperation.

Eval compute in (MyFun (Skip> 3) (Insert> [<$0,0>; <$0,0>;<$0,0>]) (Skip< 3)).
Eval compute in (MyFun3 (Skip> 3) (Insert> [<$0,0>; <$0,0>;<$0,0>]) (Skip< 3)).
Eval compute in (MyFun3 (Skip> 0) (Insert< [<$0, 0>; <$1, 1>; <$2, 2>]) (Skip< 0)).
Eval compute in (MyFun3 (Remove> [<$0, 0>; <$1, 1>; <$2, 2>]) 
                         (Insert> [<$0, 0>; <$1, 1>; <$2, 2>])
                         (Skip< 0)).

Eval compute in (MyFun3 (Skip< 3) 
                         (Insert> [])
                         (Skip< 0)).

Section HeadSplitSwapLemmas.
  Variables AHead BHead CHead : Operation.
  Lemma AHeadSplitSwap: (AHeadSplit AHead BHead CHead) = (CHeadSplit BHead CHead AHead). Admitted.
  Lemma BHeadSplitSwap: (BHeadSplit AHead BHead CHead) = (AHeadSplit BHead CHead AHead). Admitted.
  Lemma CHeadSplitSwap: (CHeadSplit AHead BHead CHead) = (BHeadSplit BHead CHead AHead). Admitted.

End HeadSplitSwapLemmas.

Lemma listEmptyOrNot: ∀ (A: operationList), A = OList [] ∨ A <> OList [].
destruct A. destruct entries. left. reflexivity. specialize nil_cons with (x:=o) (l:=entries). right. intros contra. assert( (o :: entries) = []). injection contra. trivial.  contradict H. rewrite H0. reflexivity.
Qed.

Theorem squashAssociative: ∀ (A B C :operationList), (A ○ B) ○ C = A ○ (B ○ C).
intro A. intro B. intro C.
Opaque squash.
set (Y := (A,B,C)).
assert (A=(fst(fst Y))). auto.
assert (B=(snd(fst Y))). auto.
assert (C=(snd Y)). auto.
rewrite H. rewrite H0. rewrite H1. clear H. clear H0. clear H1.

set (listLen := (fun X : (operationList * operationList * operationList) => let '(A0,B0,C0) := X in ((getOListLength A0) ) + (getOListLength B0) + (getOListLength C0))).

(* Perform induction with regar to the length A + B + C *)
apply induction_ltof1 with (f:=@listLen) (P:=(fun X : (operationList * operationList * operationList) => (((fst (fst X)) ○ (snd (fst X))) ○ (snd X)) = (fst (fst X)) ○ ((snd (fst X)) ○ (snd X)))). unfold ltof. intros. rename H into IH.
clear Y. clear A. clear B. clear C.
set (A := (fst (fst x))).
set (B := (snd (fst x))).
set (C := (snd x)). 

(* Handle cases where one of the inputs is an empty list *)
assert(A = (fst(fst x))). auto. destruct A as [entriesA]. destruct entriesA as [|AHead ATail]. repeat rewrite emptyOListNop2. reflexivity. rename H into H_AeqAHT.
assert(B = (snd (fst x))). auto. destruct B as [entriesB]. destruct entriesB as [|BHead BTail]. rewrite emptyOListNop. rewrite emptyOListNop2. reflexivity. rename H into H_BeqBHT.
assert(C = (snd x)). auto. destruct C as [entriesC]. destruct entriesC as [|CHead CTail]. repeat rewrite emptyOListNop. reflexivity. rename H into H_CeqCHT.

set (A := (fst (fst x))).
set (B := (snd (fst x))).
set (C := (snd x)). 

(* Simplify left side *)
Opaque getNextOperation.
Opaque squash.
specialize extractFirstSquashOp with (A:=AHead::ATail) (B:=BHead::BTail). simpl.
resolveLet firstOpL1. intros extractFirstSquashOp1.
rewrite extractFirstSquashOp1. simpl.

specialize extractFirstSquashOp with (A:=(combinedOp :: getOListEntries (OList (remainderA ++ ATail) ○ OList (remainderB ++ BTail)))) (B:=CHead :: CTail). simpl.


resolveLet firstOpL2. intros extractFirstSquashOp2.
rewrite extractFirstSquashOp2. simpl.
rename remainderA0 into remainderAB. rename remainderB0 into remainderC.

Opaque AHeadSplit.
Opaque BHeadSplit.
Opaque CHeadSplit.

specialize moveOperationIntoSquash with (AHead := AHead) (BHead := BHead) (CHead := CHead) (ATail := ATail) (BTail := BTail) as H_Swap.
fold firstOpL1 in H_Swap.
fold combinedOp in H_Swap.
fold firstOpL2 in H_Swap.
fold remainderAB in H_Swap.
fold remainderA in H_Swap.
fold remainderB in H_Swap.
fold remainderC in H_Swap.

destruct H_Swap as [H_SwapAB H_SwapC]. auto.
rewrite <-H_SwapAB. rewrite H_SwapC. clear H_SwapAB. clear H_SwapC.


(* Apply induction hypothesis to swap operations in remainder *)
set (Y0 := (OList ((AHeadSplit AHead BHead CHead) ++ ATail))).
set (Y1 := (OList ((BHeadSplit AHead BHead CHead) ++ BTail))).
set (Y2 := (OList ((CHeadSplit AHead BHead CHead) ++ CTail))).
set (Y:=(Y0,Y1,Y2)).
assert (Y0=(fst (fst Y))) as AY0. auto. rewrite AY0.
assert (Y1=(snd (fst Y))) as AY1. auto. rewrite AY1.
assert (Y2=(snd Y)) as AY2. auto. rewrite AY2.

rewrite IH with (y:=Y).


(* Simplify right side *)
specialize extractFirstSquashOp with (A:=BHead::BTail) (B:=CHead::CTail). simpl.
resolveLet firstOpR1. intros extractFirstSquashOp3. rewrite extractFirstSquashOp3. rename remainderA0 into remainderB_R. rename remainderB0 into remainderC_R.
specialize extractFirstSquashOp with (A:=AHead::ATail) (B:=combinedOp1 :: getOListEntries (OList (remainderB_R ++ BTail) ○ OList (remainderC_R ++ CTail))). simpl.
resolveLet firstOpR2. intros extractFirstSquashOp4. rewrite extractFirstSquashOp4. rename remainderA0 into remainderA_R. rename remainderB0 into remainderBC_R. simpl. 
subst Y0; subst Y1; subst Y2; subst Y.

specialize moveOperationIntoSquash with (AHead := BHead) (BHead := CHead) (CHead := AHead) (ATail := BTail) (BTail := CTail) as H_Swap_R.
rewrite <-reverseCombine1 in H_Swap_R; auto.
rewrite <-reverseCombine2 in H_Swap_R; auto.

fold firstOpR1 in H_Swap_R.
fold combinedOp1 in H_Swap_R.
fold firstOpR2 in H_Swap_R.
fold remainderBC_R in H_Swap_R.
fold remainderA_R in H_Swap_R.
fold remainderB_R in H_Swap_R.
fold remainderC_R in H_Swap_R.

destruct H_Swap_R as [H_SwapBC H_SwapA]. auto.
rewrite <-H_SwapBC. rewrite H_SwapA. clear H_SwapBC H_SwapA.
rewrite AHeadSplitSwap with (AHead:=AHead) (BHead:=BHead) (CHead:=CHead).
rewrite BHeadSplitSwap with (AHead:=AHead) (BHead:=BHead) (CHead:=CHead).
rewrite CHeadSplitSwap with (AHead:=AHead) (BHead:=BHead) (CHead:=CHead).

do 2 f_equal.
specialize reverseCombine3 with (AHead:=AHead) (BHead:=BHead) (CHead:=CHead) as H_op; auto.
unfold combinedOp0. unfold combinedOp2. unfold firstOpL2. unfold firstOpR2. unfold combinedOp. unfold firstOpL1.
rewrite <-H_op; auto.

split. 
- specialize nil_cons with (x:=AHead) (l:=ATail). auto.
- specialize nil_cons with (x:=combinedOp1). auto.
- split. specialize nil_cons with (x:=BHead). auto.
specialize nil_cons with (x:=CHead). auto.
- (* Induction condition listLen Y < listLen X *)
  unfold Y. unfold Y0. unfold Y1. unfold Y2. unfold listLen. 
  resolveLet x1. 
  unfold A0. unfold B0.  unfold C0. unfold x1. fold A. fold B. fold C.  unfold getOListLength.

  repeat rewrite app_length.

  specialize lengthOfSplitHeads with (AHead:=AHead) (BHead:=BHead) (CHead:=CHead).
  intros.
  do 3 forward H; auto. 
  unfold A. rewrite <-H_AeqAHT.
  unfold B. rewrite <-H_BeqBHT.
  unfold C. rewrite <-H_CeqCHT.
  repeat rewrite concat_length.

  lia.

- split. specialize nil_cons with (x:=combinedOp). auto.
  specialize nil_cons with (x:=CHead). auto.
- split.
  specialize nil_cons with (x:=AHead). auto.
  specialize nil_cons with (x:=BHead). auto.
Qed.

(*
A⁻¹ ○ ∅ = A

A⁻¹ ○ A = ∅

A ○ (B ○ C) = (A ○ B) ○ C

A ↷ (B ○ C) = (A ↷ B) ↷ C

(A ↷ ∅) = A
([] ↷ A) = ∅
(A ○ B) ↷ C = (A ↷ C) ○ (B ↷ (A⁻¹ ○ C ○ (A ↷ B) ))

∀ ∃

*)