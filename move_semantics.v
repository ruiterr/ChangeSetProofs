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

  Definition splitOpAFun := if len2 =? len1 then match s1 with |right => true | left => false end else len2 <? len1.
  Definition opAGtB := if len2 =? len1 then match s1,s2 with |right,left => true | _,_ => false end else len2 <? len1.
  Definition opAEqB := if len2 =? len1 then match s1,s2 with |right,right => true |left,left=>true |_,_=>false end else false.


  Let splitOpA := splitOpAFun.

  Definition getNextOperation : (Operation * (list Operation) * (list Operation)) := 

    let splitOp     := if splitOpA then o1 else o2 in
    let splitLength := if splitOpA then len2 else len1 in
    let splitSide   := if splitOpA then s2 else s1 in

    let splitOp := (iterDef.(splitOperation) splitOp splitLength splitSide) in
    let opA :=  if splitOpA then (fst splitOp) else o1 in
    let opB :=  if splitOpA then o2 else (fst splitOp) in
    let remA := if splitOpA then (snd splitOp) else [] in
    let remB := if splitOpA then [] else (snd splitOp) in

    let resultingOp := iterDef.(computeResultingOperation) opA opB in

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
        (*let SAInfo := iterDef.(getLengthInSequenceA) o1 in
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
        let seqB := if splitOpA then t2 else (snd splitOp) ++ t2 in*)
        (*let '(resultingOp, remA, remB) := (getNextOperation iterDef o1 o2) in*)
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
Notation "x ≻  y" := (splitOpAFun SquashIterationDefinition x y) (at level 65, no associativity).

Notation "x ⊕ y" := (computeResultingOperation SquashIterationDefinition x y) (at level 65, right associativity).
Notation "x [≺ₐ y ]" := (fst (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceA SquashIterationDefinition y)) (snd (getLengthInSequenceA SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≻ₐ y ]" := (snd (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceA SquashIterationDefinition y)) (snd (getLengthInSequenceA SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≺ᵦ y ]" := (fst (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceB SquashIterationDefinition y)) (snd (getLengthInSequenceB SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≻ᵦ y ]" := (snd (splitOperation SquashIterationDefinition x (fst (getLengthInSequenceB SquashIterationDefinition y)) (snd (getLengthInSequenceB SquashIterationDefinition y)))) (at level 40, no associativity).
Notation "x [≺≺ y ; z ]" := (fst (splitOperation SquashIterationDefinition x y z)) (at level 40, no associativity).
Notation "x [≻≻ y ; z ]" := (snd (splitOperation SquashIterationDefinition x y z)) (at level 40, no associativity).
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


Lemma swapCombineWithSplitOfA: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → ↩( A[≺ᵦB] ⊕ B)[≻ᵦC] = (↩A[≻ᵦC])[≺ᵦ↩B[≻ᵦC]] ⊕ ↩B[≻ᵦC].
Admitted.

Lemma swapCombineWithSplitOfB: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → ↩(A ⊕ B[≺ₐA])[≻ᵦC] = ↩A[≻ᵦC] ⊕ (↩B[≻ᵦC])[≺ₐ↩A[≻ᵦC]].
Admitted.

Lemma swapSplitRemainderWithShorterSplitALen: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → A[≻ₐB] = (↩A[≻ᵦC])[≻ₐ↩B[≻ᵦC]].
Admitted.

Lemma swapSplitRemainderWithShorterSplitBLen: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → A[≻ᵦB] = (↩A[≻ᵦC])[≻ᵦ↩B[≻ᵦC]].
Admitted.


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

Lemma splitOperationLengthR2: ∀(A:Operation) (s : side) (y:nat), y < ‖A‖ → ‖↩A[≻≻ y ; s] ‖ = ‖A‖ - y.
intros.
unfold splitOperation. simpl.
destruct A eqn:H_A; destruct s; try destruct side0.
all: unfold SplitHelper.
all: unfold opLength in H.
all: try destruct entries.
all: apply Nat.ltb_lt in H.
all: rewrite H.
all: unfold opLength.
all: simpl.
all: try rewrite skipn_length.
all: try lia.
Qed.

Lemma splitOperationWith0Unchanged: ∀(A:Operation) (s : side), (‖A‖ > 0 ∨ (‖A‖ = 0 ∧ ⌊A⌋ᵦ = right ∧ s = left)) → A[≻≻0 ; s] = [A].
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

Lemma splitOperationWith0RightEmpty: ∀(A:Operation) (s : side), ((‖A‖ = 0 ∧ ⌊A⌋ᵦ = right ∧ s = right)) → A[≻≻0 ; s] = [].
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

Lemma splitLengthInB: ∀(A C:Operation), (A≫C) = true -> ⌈↩A[≻ᵦC]⌉ᵦ = ⌈A⌉ᵦ - ⌈C⌉ᵦ.
intros.
apply destructAGreaterB in H.


destruct A eqn:H_destA. 
Opaque length.
Opaque plus.
Opaque minus.
Opaque leb.
Opaque getLengthInSequenceA.
Opaque getLengthInSequenceB.

all: cbv delta [splitOperation]; simpl; unfold SplitHelper. 
Transparent getLengthInSequenceA.
Opaque getLengthInSequenceB.
 - destruct H. (* A = Skip Operation *)
   + cbv delta [getLengthInSequenceA] in H. simpl in H. rewrite H. simpl.
     set (lenC:=⌈C⌉ᵦ).
     Transparent getLengthInSequenceB.
     simpl. reflexivity.
   + destruct H as [H_eqAmount [H_eqSideA H_eqSideB]].
     assert(⌈C⌉ᵦ <? amount = false). 
     apply Nat.ltb_ge.
     apply Nat.eqb_eq in H_eqAmount.
     set (lenC:=⌈C⌉ᵦ).
     fold lenC in H_eqAmount.
     cbv delta [getLengthInSequenceA] in H_eqAmount. simpl in H_eqAmount. rewrite H_eqAmount. lia.
     rewrite H.
     cbv delta [getLengthInSequenceA] in H_eqSideA. simpl in H_eqSideA.
     rewrite H_eqSideA.
     destruct (⌊C⌋ᵦ) eqn:H_sideC.
     * set (lenC:=⌈C⌉ᵦ). simpl.
       fold lenC in H_eqAmount.
       cbv delta [getLengthInSequenceA] in H_eqAmount. simpl in H_eqAmount. apply Nat.eqb_eq in H_eqAmount.
       lia.
     * discriminate H_eqSideB.

 Opaque getLengthInSequenceB.
 - destruct H. (* A = Insert Operation *)
   + destruct entries eqn:H_entries.
     cbv delta [getLengthInSequenceA] in H. simpl in H.  rewrite H. simpl.
     set (lenC:=⌈C⌉ᵦ).
     Transparent getLengthInSequenceB.
     simpl. give_up.
   + destruct entries eqn:H_entries.
     destruct H as [H_eqAmount [H_eqSideA H_eqSideB]].
     assert(⌈C⌉ᵦ <? (length entries0) = false). 
     apply Nat.ltb_ge.
     apply Nat.eqb_eq in H_eqAmount.
     set (lenC:=⌈C⌉ᵦ).
     fold lenC in H_eqAmount.
     cbv delta [getLengthInSequenceA] in H_eqAmount. simpl in H_eqAmount. rewrite H_eqAmount. lia.
     rewrite H.
     cbv delta [getLengthInSequenceA] in H_eqSideA. simpl in H_eqSideA.
     rewrite H_eqSideA.
     destruct (⌊C⌋ᵦ) eqn:H_sideC.
     * set (lenC:=⌈C⌉ᵦ). simpl.
       fold lenC in H_eqAmount.
       cbv delta [getLengthInSequenceA] in H_eqAmount. simpl in H_eqAmount. apply Nat.eqb_eq in H_eqAmount.
       give_up.
     * discriminate H_eqSideB.

 Opaque getLengthInSequenceB.
 - destruct H. (* A = Remove Operation *)
   + destruct entries eqn:H_entries.
     cbv delta [getLengthInSequenceA] in H. simpl in H. 
     apply Nat.ltb_lt in H.
     apply Nat.nlt_0_r in H.
     contradiction.
   + destruct entries eqn:H_entries.
     destruct H as [H_eqAmount [H_eqSideA H_eqSideB]].
     apply Nat.eqb_eq in H_eqAmount.
     set (lenC:=⌈C⌉ᵦ).
     fold lenC in H_eqAmount.
     cbv delta [getLengthInSequenceA] in H_eqAmount. simpl in H_eqAmount. rewrite H_eqAmount. 
     destruct (0 <? Datatypes.length entries0) eqn:H_numEntriesGt0.
     * cbv delta [getLengthInSequenceB].
       simpl. lia.
     * cbv in H_eqSideA.
       rewrite H_eqSideA.
       rewrite H_eqSideB.
       cbv delta [getLengthInSequenceB]. 
       simpl.
       assert( (Datatypes.length entries0) = 0).
       apply Nat.ltb_ge in H_numEntriesGt0.
       lia.
       unfold skipn.
       rewrite H. lia.
Admitted.

Lemma splitLengthInA: ∀(A C:Operation), (A≫C) = true -> ⌈↩A [≻ᵦC]⌉ₐ = ⌈A⌉ₐ - ⌈C⌉ᵦ.
Admitted.

Definition MyFun (A B C: Operation) := ((A≫C), (B≫C), ⌈↩B[≻ᵦC]⌉ᵦ, (⌈↩A[≻ᵦC]⌉ₐ), ⌈B⌉ᵦ,  ⌈A⌉ₐ).
Definition MyFun2 (A B C: Operation) := ((↩A[≻ᵦC] ≻ ↩B[≻ᵦC]), (A ≻ B)).
Transparent getLengthInSequenceB.
Transparent length.
Transparent leb.
Transparent minus.
Eval compute in (MyFun2 (Skip< 5) (Insert> [<$0,0>; <$0,0>;<$0,0>;<$0,0>;<$0,0>]) (Skip< 3)).

Lemma splitOpRemainsInsert: ∀ (A C: Operation), A[≻ᵦC] ≠ [] ∧ (isInsert A) = true → (isInsert(↩A[≻ᵦC]) = true).
Admitted.

Definition notLargerLengthInsert (A C:Operation) := (isInsert A) = false ∨ (⌈C⌉ᵦ < ⌈A⌉ₐ).


Lemma splitOperationRemainder: ∀ A B : Operation, A ≫ B = true → ∃ C : Operation, A[≻ᵦB] = [C].
Admitted.

Lemma seqLengthPreservedUnderCut: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ 
                                                      (isInsert B) = false → ⌈↩B[≻ᵦC]⌉ᵦ ?= (⌈↩A[≻ᵦC]⌉ₐ) = (⌈B⌉ᵦ ?= ⌈A⌉ₐ).
intros.
destruct H as [H_AgtC [H_BgtC H_notLargerLengthInsert]].
apply destructAGreaterB in H_AgtC as H_AgtC2.
apply destructAGreaterB in H_BgtC as H_BgtC2.

destruct (isInsert B) eqn:H_BisInsert.

Transparent SplitHelper.
Opaque length.
Opaque splitOperation.
- assert(⌈↩B[≻ᵦC]⌉ᵦ = 0) as H_B1eq0. {
    cbv in H_BisInsert.
    set (lenC := ⌈C⌉ᵦ).
    set (sideC := ⌊C⌋ᵦ).
    destruct B eqn:H_eqB; try discriminate H_BisInsert.
    simpl. destruct entries.
    specialize splitOpRemainsInsert with (A:=B) (C:=C) as H_CisInsert. forward H_CisInsert. { 
      split.
      specialize splitOperationRemainder with (A:=B) (B:=C) as H. forward H; auto. rewrite H_eqB. auto. destruct H. rewrite H. discriminate.
      rewrite H_eqB. simpl. auto.
    }
    destruct (↩B[≻ᵦC]) eqn:H_eqC; try discriminate H_CisInsert.
    rewrite  H_eqB in H_eqC.
    unfold lenC. unfold sideC.
    rewrite H_eqC. destruct entries0. simpl. auto.
  }

  rewrite H_B1eq0.

  assert(⌈B⌉ᵦ = 0) as H_B1eq0_2. give_up.
  rewrite H_B1eq0_2.

  rewrite splitLengthInA; auto.

  destruct H_AgtC2.
  + assert(0 < ⌈A⌉ₐ - ⌈C⌉ᵦ). {
      rewrite Nat.ltb_lt in H.
      lia.
    }
    
    Search( _< _ ).
    
    specialize nat_compare_lt with (n:=0) (m:=⌈A⌉ₐ-⌈C⌉ᵦ) as H_lt.
    destruct H_lt.
    rewrite H1.
    assert(⌈A⌉ₐ > 0). {
     rewrite Nat.ltb_lt in H. lia. 
    }
    specialize nat_compare_lt with (n:=0) (m:=⌈A⌉ₐ) as H_Alt.
    destruct H_Alt.
    rewrite <-H4; auto. lia.
  + destruct H as [H_eqLen [H_sideA H_sideC]].
    assert(⌈A⌉ₐ - ⌈C⌉ᵦ = 0) as H_ACeq0. { rewrite Nat.eqb_eq in H_eqLen. lia. }
    rewrite H_ACeq0.
    unfold notLargerLengthInsert in H_notLargerLengthInsert.
    destruct H_notLargerLengthInsert. (*rewrite H_BisInsert in H. discriminate H.
    assert(⌈C⌉ᵦ = 0). { 
      rewrite seqBLengthFromNorm in H_B1eq0.
      assert( isInsert (↩B [≻ᵦC]) = true
      (*specialize splitOpRemainsInsert*)
      assert((isInsert (↩B [≻ᵦC])
      assert(⌈C⌉ᵦ = ⌈B⌉ᵦ). {
        rewrite splitOperationLengthR2 in H_B1eq0.
      destruct H_BgtC2. rewrite Nat.ltb_lt in H. 
    lia.

  simpl.
    rewrite H_eqB. simpl. auto. 
  destruct . 
  unfold SplitHelper. destruct C; try destruct entries0; try destruct side; try destruct side0; simpl; cbv. 
rewrite splitLengthInB; auto.
rewrite splitLengthInA; auto.*)

(*destruct H_AgtC; destruct H_BgtC.
destruct A eqn:H_destA; destruct B eqn:H_destB; destruct C eqn:H_destC.
Transparent getLengthInSequenceA.
Transparent getLengthInSequenceB.

all: unfold getLengthInSequenceA in H.
all: unfold getLengthInSequenceB in H.
all: simpl in H.
all:unfold getLengthInSequenceA in H0.
all: unfold getLengthInSequenceB in H0.
all: simpl in H0.

simpl; unfold SplitHelper; try rewrite H; try rewrite H0; simpl. give_up.
destruct entries as [entriesList] eqn:H_eqEntries. 
simpl in H. simpl in H0.
all: try destruct entries as [entriesList] eqn:H_eqEntries. 
all: try destruct entries0 as [entriesList0] eqn:H_eqEntries0. 
all: simpl in H.
all: simpl in H0.

(* Opaque splitOperation. *)
Opaque length.
all: simpl; unfold SplitHelper; try rewrite H; try rewrite H0; simpl.
give_up. give_up. give_up. give_up.*)


Admitted.


Lemma seqLengthPreservedUnderCutEQ: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ (isInsert B) = false → ⌈↩B [≻ᵦC]⌉ᵦ =? (⌈↩A [≻ᵦC]⌉ₐ) = (⌈B⌉ᵦ =? ⌈A⌉ₐ).
Admitted.

Lemma seqLengthPreservedUnderCutLT: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true ∧ (isInsert B) = false → ⌈↩B [≻ᵦC]⌉ᵦ <? (⌈↩A [≻ᵦC]⌉ₐ) = (⌈B⌉ᵦ <? ⌈A⌉ₐ).
Admitted.

Lemma sideRemainsUnchanged: ∀(A C:Operation), A[≻ᵦC]<>[] → ⌊↩A[≻ᵦC]⌋ₐ = ⌊A⌋ₐ.
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

Lemma splitLengthPreservedUnderCut: ∀(A B C:Operation), (A≫C) = true ∧ (B≫C) = true → (↩A[≻ᵦC] ≻ ↩B[≻ᵦC]) = (A ≻ B).
intros.
cbv delta [splitOpAFun]. cbv beta. cbv zeta.

destruct H.
specialize splitOperationRemainder with (A:=A) (B:=C) as HBC_exists. forward HBC_exists; auto.
destruct HBC_exists.
assert(A [≻ᵦC] <> []) as H_HC_notEmptySet. rewrite H1. intuition. discriminate H2.
destruct(⌊↩A [≻ᵦC]⌋ₐ) eqn:side_AC; destruct(⌊A⌋ₐ) eqn:side_A. all:auto.
specialize seqLengthPreservedUnderCutEQ with (A:=A) (B:=B) (C:=C). intros. forward H2; auto. give_up.
all: rewrite seqLengthPreservedUnderCutEQ ; auto.

all: destruct(⌈B⌉ᵦ =? ⌈A⌉ₐ) eqn:H3. 
all: auto; specialize sideRemainsUnchanged with (A:=A) (C:=C) as H_Side; rewrite H_Side in side_AC; try rewrite side_A in side_AC; try discriminate.

all: try rewrite seqLengthPreservedUnderCutLT ; auto.
all: assumption.
Qed.


(*Opaque length.
destruct A. destruct B. destruct C. {
 destruct side0; destruct side1; destruct side2 eqn:H_s2. 

all: (
  cbv delta [splitOpAFun getLengthInSequenceA getLengthInSequenceB SplitHelper]; cbv beta; simpl;  intros; unfold SplitHelper; destruct H;
  destruct(amount1=?amount); try discriminate H;
  destruct(amount1=?amount0); try discriminate H0;
  try rewrite H; try rewrite H0; simpl 
).

all: destruct(amount1<?amount0). all:destruct(amount1 <? amount). all:simpl.

all: destruct (amount0 - amount1 =? amount - amount1) eqn:H1.
all: try apply beq_nat_true  in H1.
all: try apply Nat.ltb_lt in H.
all: try apply Nat.ltb_lt in H0.
assert(amount0 = amount).
rewrite <-Nat.add_cancel_l with (p:=amount1) in H1.
rewrite le_plus_minus_r in H1.
rewrite le_plus_minus_r in H1; auto. lia. lia. 
rewrite <-beq_nat_true_iff in H2.
rewrite H2. auto.

assert(amount0 <> amount). give_up.
rewrite <-beq_nat_false_iff in H2.
rewrite H2. auto. give_up.


cbv delta [splitOpAFun getLengthInSequenceA getLengthInSequenceB SplitHelper]. cbv beta. simpl.  intros. unfold SplitHelper. destruct H. 
destruct(amount1=?amount); try discriminate H.
destruct(amount1=?amount0); try discriminate H0.
rewrite H. rewrite H0. simpl. 
destruct (amount0 - amount1 =? amount - amount1) eqn:H1.
apply beq_nat_true  in H1.
apply Nat.ltb_lt in H.
apply Nat.ltb_lt in H0.
assert(amount0 = amount).
rewrite <-Nat.add_cancel_l with (p:=amount1) in H1.
rewrite le_plus_minus_r in H1.
rewrite le_plus_minus_r in H1; auto. lia. lia. 
rewrite <-beq_nat_true_iff in H2.
rewrite H2. auto.

assert(amount0 <> amount). give_up.
rewrite <-beq_nat_false_iff in H2.
rewrite H2. auto. give_up.

Admitted.*)


(* Lemma splitLengthTransitivity: ∀(A B C:Operation), (A≫B) = true ∧ (B≫C) = true → (A≫C) = true.
intros. destruct H as [H_AgtC H_BgtC].
(* unfold splitOpAFun in H_AgtC. *)
apply destructAGreaterB in H_AgtC.
apply destructAGreaterB in H_BgtC.

unfold splitOpAFun.

destruct H_AgtC.
destruct H_BgtC.

rewrite Nat.ltb_lt in H.
rewrite Nat.ltb_lt in H0.
assert(⌈B⌉ᵦ < ⌈A⌉ₐ ∧ ⌈C⌉ᵦ < ⌈B⌉ₐ → ⌈C⌉ᵦ < ⌈A⌉ₐ).
Opaque length.

destruct B.  
  - destruct A; 
         intros; destruct H1; 
         apply lt_trans with (n:=⌈C⌉ᵦ) (m:=⌈Skip amount side0⌉ᵦ); auto. 
  - destruct A. destruct C. cbv. simpl. destruct entries eqn:H_eqEntries. intros. destruct H1. cbv in H0. cbv in H0. lia.
         intros. destruct H1. assert(⌈Skip amount side1⌉ₐ = ⌈Skip amount side1⌉ᵦ). cbv. reflexivity. 
         assert(⌈Insert entries side0⌉ᵦ = 0). cbv. 
         apply lt_trans with (n:=⌈C⌉ᵦ) (m:=⌈Insert entries side0⌉ᵦ) (p:=⌈Skip amount side1⌉ₐ); auto. assumption. 
  - destruct A;
         intros; destruct H1; 
         apply lt_trans with (n:=⌈C⌉ᵦ) (m:=⌈Insert entries side0⌉ₐ); auto. 


     
 unfold getLengthInSequenceA. unfold getLengthInSequenceB. simpl. lia.

assert(⌈C⌉ᵦ =? ⌈A⌉ₐ = false). 
specialize lt_trans with (n:=⌈C⌉ᵦ) (m:=⌈B⌉ᵦ) (p:=⌈A⌉ₐ) as H_CltA. forward H_CltA. 
assert(⌈C⌉ᵦ < ⌈A⌉ₐ). lia. 
assert(⌈C⌉ᵦ <> ⌈A⌉ₐ). lia. 
destruct (⌈C⌉ᵦ =? ⌈A⌉ₐ) eqn:X. 
 apply beq_nat_true in X. intuition. 
 reflexivity.

rewrite H1.


lia.

Admitted.*)


Section SplitOpByLarger.
  Variable A B C : Operation.
  Let combinedOp := (fst (fst (getNextOperation SquashIterationDefinition A B))).
  Lemma splitByLargerOp: combinedOp ≫ C = true → A ≫ C = true ∧ B ≫ C = true.
  Admitted.

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
Let splitOpC := splitOpAFun SquashIterationDefinition CombinedOp CHead.
 
Definition AHeadSplit := if splitOpC then if (isInsert BHead) then [AHead] else splitOp AHead else remainderA.
Definition BHeadSplit := if splitOpC then splitOp BHead else remainderB.
Definition CHeadSplit := remainderC.

Definition MyFun3 := (AHeadSplit, BHeadSplit, CombinedOp, remainderA, remainderB, remainderAB, getNextOperation SquashIterationDefinition (↩AHeadSplit) (↩BHeadSplit)).

(*Lemma getNextOperationCombinationLengthCSmallerRemAB: (splitOpC = true) → (∃ (remABOp:Operation), (remainderAB = [remABOp])).
intros.
cbv delta [remainderAB OpResult2 getNextOperation]. cbv beta. fold splitOpC. rewrite H.
cbv zeta. hnf. fold lengthC. fold sideC. 
Opaque computeResultingOperation. Opaque splitOperation.
simpl. specialize splitOperationRemainder with (A:=CombinedOp) (B:=CHead) as H2. 
fold lengthC in H2. fold sideC in H2. 
apply H2. auto.
Qed.

Lemma getNextOperationCombinationLengthCSmallerRemA: (splitOpC = true) → (∃ (remAOp:Operation), ([remAOp] = AHeadSplit)).
intros.
cbv delta [AHeadSplit splitOp]. cbv beta. fold splitOpC. rewrite H. auto.
simpl. specialize splitOperationRemainder with (A:=AHead) (B:=CHead) as H2. 
specialize splitByLargerOp with (A:=AHead) (B:=BHead) (C:=CHead) as H_SplitLarger.
fold OpResult1 in H_SplitLarger. fold CombinedOp in H_SplitLarger. fold splitOpC in H_SplitLarger. 
forward H_SplitLarger; auto. destruct H_SplitLarger. forward H2;auto. destruct H2.  unfold lengthC. 
unfold sideC. rewrite H2. exists x. auto.
Qed.

Lemma getNextOperationCombinationLengthCSmallerRemB: (splitOpC = true) → (∃ (remBOp:Operation), ([remBOp] = BHeadSplit)).
intros.
cbv delta [BHeadSplit splitOp]. cbv beta. fold splitOpC. rewrite H. auto.
simpl. specialize splitOperationRemainder with (A:=BHead) (B:=CHead) as H2. 
specialize splitByLargerOp with (A:=AHead) (B:=BHead) (C:=CHead).
fold OpResult1. fold CombinedOp. fold splitOpC. rewrite H. intros. destruct H0. auto. 
forward H2. auto. destruct H2. fold lengthC in H2. fold sideC in H2. rewrite H2. 
exists x. auto.
Qed.*)

Transparent length.
Transparent splitOperation.
Eval compute in ((Skip 0 right)[≻≻ 0 ; left ]).

Lemma getNextOperationCombinationLengthCSmaller: (CombinedOp ≫ CHead) = true → 
    (∃ (remABOp remAOp remBOp : Operation), (
      remainderAB = [remABOp]) ∧ 
      [remAOp] = AHeadSplit ∧ 
      [remBOp] = BHeadSplit ∧ 
      (remABOp, remainderA, remainderB) = (getNextOperation SquashIterationDefinition remAOp remBOp)).
intros.
assert(splitOpC = true) as H_splitOpC. give_up.
Opaque computeResultingOperation. Opaque splitOperation.
cbv delta [AHeadSplit BHeadSplit splitOp]. cbv beta. fold splitOpC. rewrite H_splitOpC. auto.
simpl. 

specialize splitOperationRemainder with (A:=AHead) (B:=CHead) as H_AHead.
specialize splitOperationRemainder with (A:=BHead) (B:=CHead) as H_BHead. 
specialize splitOperationRemainder with (A:=CombinedOp) (B:=CHead) as H_CHead. 

specialize splitByLargerOp with (A:=AHead) (B:=BHead) (C:=CHead).

Print OpResult1.
fold OpResult1. fold CombinedOp. fold splitOpC. rewrite H. intros. destruct H0 as [H_ASmaller H_BSmaller]. auto. 
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
 destruct (isInsert BHead) eqn:H_BHeadIsInsert. cbv in H_BHeadIsInsert.
 - destruct BHead eqn:H_BHead; try discriminate H_BHeadIsInsert.
   destruct entries. unfold remA. simpl. auto.
 - destruct BHead eqn:H_BHead; try discriminate H_BHeadIsInsert.
   all: simpl; unfold remA; auto.
}


(* Proof [remBOp] = BHeadSplit *)
split. auto.

(* Proof (remABOp, remainderA, remainderB) = (getNextOperation SquashIterationDefinition remAOp remBOp) *)
cbv delta [remainderAB OpResult2 getNextOperation]. cbv beta. fold splitOpC. 

set (splitOpARem := splitOpAFun SquashIterationDefinition remA remB).
set (splitOpA := splitOpAFun SquashIterationDefinition AHead BHead).

{
  destruct (isInsert BHead) eqn:H_BHeadIsInsert. cbv in H_BHeadIsInsert.
  - destruct BHead eqn:H_BHead; try discriminate H_BHeadIsInsert.
    assert(⌈remB⌉ᵦ = 0) as H_remBLength0. {
      rewrite seqBLengthFromNorm. unfold isInsert. 
      specialize splitOpRemainsInsert with (A:=BHead) (C:=CHead) as H_remBIsInsert.
      forward H_remBIsInsert. {
        split. 
        - fold lengthC. fold sideC. rewrite H_BHead. rewrite ->H_remB. discriminate.
        - unfold isInsert. rewrite H_BHead. auto.
      }
      rewrite H_BHead in H_remBIsInsert.
      fold lengthC in H_remBIsInsert. fold sideC in H_remBIsInsert.
      rewrite ->H_remB in H_remBIsInsert. simpl in H_remBIsInsert.
      
      destruct remB; cbv in  H_remBIsInsert; try discriminate H_remBIsInsert.
      auto.
    }

    cbv zeta.
    rewrite H_remBLength0.
    unfold splitOpAFun in splitOpARem.
    destruct (⌈remB⌉ᵦ =? ⌈remA⌉ₐ) eqn:H_remBGtRemA.
    + apply Nat.eqb_eq in H_remBGtRemA as H_remBGtRemAnonBool.
      rewrite <-H_remBGtRemAnonBool.
      rewrite H_remBLength0.
      assert(⌈AHead⌉ₐ = 0) as H_AHeadLength. {
        unfold remA in H_remBGtRemAnonBool.
        rewrite H_remBLength0 in H_remBGtRemAnonBool.
        auto.
      }

      destruct (⌊remA⌋ₐ) eqn:H_remASide.
      *  (*unfold splitOpARem;
        unfold remainderA; unfold remainderB; unfold OpResult1.
        all: destruct entries.
        all: change remB with (↩[remB]); rewrite <-H_remB.
        all: unfold remA.
        all: change x with (↩[x]); rewrite <-H0; unfold remainderAB; unfold OpResult2.
        all: unfold remA.

        Opaque getLengthInSequenceA.
        Opaque getLengthInSequenceB. 
        Opaque computeResultingOperation. 
        all: unfold getNextOperation.
        all: destruct (AHead ≻ Insert (Seq entries) side0).
        all: simpl.
        all: fold splitOpC; rewrite H_splitOpC.
        all: rewrite H_remB.
        destruct AHead eqn:H_AHead.*)

        unfold remA in H_remASide.
        (*rewrite H_amount.
        simpl in H_remASide.
        rewrite H_remASide.
        assert (⌈Insert (Seq entries) side0⌉ᵦ= 0). {
          Transparent getLengthInSequenceB.
          unfold getLengthInSequenceB.
          cbv. auto.
        }
        rewrite H1.*)
        unfold opAGtB in H_ASmaller.
        rewrite H_remASide in H_ASmaller.
        rewrite H_AHeadLength in H_ASmaller.
        assert (⌈CHead⌉ᵦ <? 0 = false) as H_CHeadNLt0. {
          rewrite Nat.ltb_ge.
          lia.
        }
        rewrite H_CHeadNLt0 in H_ASmaller.
        rewrite Tauto.if_same in H_ASmaller.
        discriminate H_ASmaller.
      * unfold splitOpARem;
        unfold remainderA; unfold remainderB; unfold OpResult1.
        destruct entries.
        change remB with (↩[remB]); rewrite <-H_remB.
        unfold remA.
        change x with (↩[x]); rewrite <-H0; unfold remainderAB; unfold OpResult2.
        unfold remA.

        Opaque getLengthInSequenceA.
        Opaque getLengthInSequenceB. 
        Opaque computeResultingOperation. 
        unfold getNextOperation.
        assert(AHead ≻ Insert (Seq entries) side0 = true) as H_AHeadGtBHead. {
          unfold splitOpAFun.
          rewrite seqBLengthFromNorm. simpl.
          rewrite H_AHeadLength.
          unfold remA in H_remASide.
          rewrite H_remASide.
          reflexivity.
        }
        rewrite H_AHeadGtBHead.
        assert(CombinedOp ≻ CHead = true) as H_CombinedOpGtCHead. { give_up. }
        rewrite H_CombinedOpGtCHead.
        simpl.

        assert(lengthC = 0 ∧ sideC = left) as H_CProperties. {
          unfold opAGtB in H_ASmaller.
          rewrite H_AHeadLength in H_ASmaller.
          unfold remA in H_remASide.
          rewrite H_remASide in H_ASmaller.
          destruct (⌈CHead⌉ᵦ =? 0) eqn:H_CHeadLength; destruct (⌊CHead⌋ᵦ) eqn:H_CHeadSide; try discriminate H_ASmaller.
          unfold lengthC. unfold sideC. 
          rewrite Nat.eqb_eq in H_CHeadLength.
          rewrite H_CHeadLength.
          auto.
        }
        destruct H_CProperties as [H_LengthC H_SideC].
        unfold lengthC. unfold sideC.
        rewrite <-sidesEqual with (A:=↩Insert (Seq entries) side0 [≻ᵦCHead]).
        rewrite sideRemainsUnchanged with (A:=Insert (Seq entries) side0) (C:=CHead).
        fold lengthC. fold sideC.
        rewrite H_LengthC. rewrite H_SideC.

        assert(⌈ Insert (Seq entries) side0⌉ᵦ = 0) as H_InsertLength. { rewrite seqBLengthFromNorm. simpl. auto. }
        rewrite H_InsertLength.
        assert(⌊Insert (Seq entries) side0⌋ᵦ = side0) as H_InsertSide. { 
          Transparent getLengthInSequenceB. 
          unfold getLengthInSequenceB. 
          simpl. 
          auto. 
          Opaque getLengthInSequenceB.
        }
        rewrite H_InsertSide.
        
        change (⌊Insert (Seq entries) side0⌋ₐ) with side0.
        rewrite splitOperationWith0Unchanged. simpl.
        rewrite splitOperationWith0Unchanged with (A:=Insert (Seq entries) side0). simpl.
        unfold CombinedOp.
        unfold OpResult1.
        simpl. rewrite H_AHeadGtBHead.
        simpl. rewrite H_InsertLength. rewrite H_InsertSide.
        reflexivity.
        specialize destructAGreaterB with (A:=Insert (Seq entries) side0) (B:=CHead) as H_BGtC.
        forward H_BGtC. apply H_BSmaller.
        { 
          destruct H_BGtC. 
          - fold lengthC in H1.
            rewrite H_LengthC in H1.
            rewrite seqALengthFromNorm in H1. simpl in H1.
            rewrite Nat.ltb_lt in H1.
            simpl. lia. 
          - right. 
            intuition.
            fold lengthC in H2.
            rewrite H_LengthC in H2.
            rewrite seqALengthFromNorm in H2. unfold isRemove in H2.
            rewrite Nat.eqb_eq in H2.
            auto.
        }

        { 
          unfold splitOpAFun in H_CombinedOpGtCHead.
          fold lengthC in H_CombinedOpGtCHead. fold sideC in H_CombinedOpGtCHead.
          rewrite H_LengthC in H_CombinedOpGtCHead. 
          {
            destruct (0 <? ‖CombinedOp‖) eqn:H_comGt0. 
            - rewrite Nat.ltb_lt in H_comGt0. lia.
            - right; split.
              rewrite Nat.ltb_nlt in H_comGt0.
              lia.
              split; auto.
              assert (0 =? ⌈CombinedOp⌉ₐ = true) as H_CombinedOpAEq0. {
                rewrite seqALengthFromNorm.
                destruct(isRemove CombinedOp); auto.
                rewrite Nat.eqb_eq. rewrite Nat.ltb_nlt in H_comGt0.
                lia.
              }
              rewrite H_CombinedOpAEq0 in H_CombinedOpGtCHead.
              destruct (⌊CombinedOp⌋ₐ) eqn:H_CombonedOpA in  H_CombinedOpGtCHead; try discriminate H_CombinedOpGtCHead.
              rewrite <-sidesEqual.
              assumption.
          }
        }
        fold lengthC; fold sideC.
        rewrite H_remB.
        discriminate.
        Transparent getLengthInSequenceB.
        Transparent getLengthInSequenceA.
        Transparent computeResultingOperation. 

    + assert(⌈remB⌉ᵦ < ⌈remA⌉ₐ). {
        apply Nat.eqb_neq in H_remBGtRemA.
        rewrite H_remBLength0.
        lia.
      }
      rewrite <-Nat.ltb_lt in H1.
      subst splitOpARem.
      rewrite H1.
      unfold remainderA. 
      unfold remainderB. 
      unfold OpResult1.
      unfold getNextOperation.
      fold splitOpA.
      unfold splitOpAFun in splitOpA.
      set (lenBHead := ⌈Insert entries side0⌉ᵦ).
      assert(lenBHead = ⌈Insert entries side0⌉ᵦ) as H_lenBHead; auto. 
      fold lenBHead in splitOpA.
      (* rewrite seqBLengthFromNorm with (A:=(Insert entries side0)) in lenBHead.*)
      unfold getLengthInSequenceB in lenBHead. cbv in lenBHead.
      destruct entries eqn:H_eqEntries.
      unfold lenBHead in splitOpA.
      destruct (0 =? ⌈AHead⌉ₐ) eqn:lenAHead.
      * simpl.

        assert(lengthC = 0) as H_length0. { 
          specialize destructAGreaterB with (A:=AHead) (B:=CHead) as H_SkipGreaterCHead.
          forward H_SkipGreaterCHead. auto.
          destruct H_SkipGreaterCHead.
          rewrite Nat.ltb_lt in H2.
          rewrite Nat.eqb_eq in lenAHead.
          rewrite <-lenAHead in H2.
          fold lengthC in H2.
          lia.

          destruct H2.
          rewrite Nat.eqb_eq in H2.
          rewrite Nat.eqb_eq in lenAHead.
          rewrite <-lenAHead in H2.
          fold lengthC in H2.
          assumption.
        }

        change remB with (↩[remB]) in H_remBGtRemA.
        rewrite <-H_remB in H_remBGtRemA.
        rewrite H_length0 in H_remBGtRemA.
        rewrite seqBLengthFromNorm in H_remBGtRemA.
        rewrite <-H_length0 in H_remBGtRemA.
        unfold lengthC in H_remBGtRemA.
        unfold sideC in H_remBGtRemA.

        rewrite splitOpRemainsInsert in H_remBGtRemA; 
          only 2:split; 
          only 2: ( 
            fold lengthC; fold sideC; rewrite H_remB; discriminate
          ); 
          only 2: (unfold isInsert; auto).

        fold lengthC in H_remBGtRemA.
        rewrite H_length0 in H_remBGtRemA.
        unfold remA in H_remBGtRemA.
        rewrite Nat.eqb_eq in lenAHead.
        rewrite <-lenAHead in H_remBGtRemA. 
        simpl in H_remBGtRemA.
        discriminate H_remBGtRemA.

      * rewrite Nat.eqb_neq in lenAHead.
        assert( (0 <? ⌈AHead⌉ₐ) = true). {rewrite Nat.ltb_lt. lia. }
        subst splitOpA.
        Opaque getLengthInSequenceA.
        Opaque getLengthInSequenceB.
        rewrite H2. fold lengthC. simpl. subst lenBHead. subst remA. 
        specialize sideRemainsUnchanged with (A:=BHead) (C:=CHead) as H_remBSide.
        fold lengthC in H_remBSide. fold sideC in H_remBSide. rewrite H_BHead in H_remBSide.
        forward H_remBSide. rewrite H_remB. discriminate.
        rewrite H_remB in H_remBSide. unfold getOpFromArray in H_remBSide. simpl in H_remBSide.
        Transparent getLengthInSequenceA.
        unfold getLengthInSequenceA at 2 in H_remBSide. 
        Opaque getLengthInSequenceA.
        simpl in H_remBSide.
        Transparent getLengthInSequenceA.
        Transparent getLengthInSequenceB.
        assert(⌊remB⌋ᵦ = ⌊remB⌋ₐ). { cbv. destruct remB; try destruct entries1; simpl; auto. }
        rewrite H3.
        rewrite H_remBSide.
        assert(⌊Insert (Seq entries0) side0⌋ᵦ = side0). { cbv. auto. }
        rewrite H4.
        assert (x = ↩remainderAB). { rewrite H0. simpl. auto. }
        rewrite H5.
        assert (↩remainderAB = AHead [≺≺0; side0] ⊕ remB). {
          Opaque computeResultingOperation.
          Opaque splitOperation.
          Opaque SquashIterationDefinition.
          Opaque Nat.eqb.
          Opaque Nat.ltb.
          set (rhs:= AHead [≺≺0; side0] ⊕ remB).
          cbv delta [getOpFromArray remainderAB OpResult2 getNextOperation CombinedOp]. simpl.
          assert(AHead ≻ Insert (Seq entries0) side0 = true) as H_AheadGtBHead. {
           cbv delta [splitOpAFun]. cbv beta. cbv zeta.  
           cbv delta [getLengthInSequenceB]. unfold SquashIterationDefinition at 1. simpl.
           specialize Nat.eqb_neq with (x:=0) (y:=⌈AHead⌉ₐ) as H_AHeadNeq0.
           destruct H_AHeadNeq0 as [_ H_AHeadNeq0].
           forward H_AHeadNeq0;auto. rewrite H_AHeadNeq0.
           unfold SquashIterationDefinition at 1. simpl. rewrite H2. 
           reflexivity.
          }
          rewrite H_AheadGtBHead.
          assert(CombinedOp = AHead [≺ᵦInsert (Seq entries0) side0] ⊕ Insert (Seq entries0) side0). {
            unfold CombinedOp.
            unfold OpResult1.
            unfold getNextOperation.
            rewrite H_AheadGtBHead. simpl.
            reflexivity.
          }
          

          rewrite <-H6.
          fold splitOpC.
          rewrite H_splitOpC.
          rewrite H6.
          fold lengthC. fold sideC.
          rewrite seqBLengthFromNorm. unfold isInsert.
          unfold rhs.
          assert(AHead [≺≺0; ⌊Insert (Seq entries0) side0⌋ᵦ] ⊕ (Insert (Seq entries0) side0) = (Insert (Seq entries0) side0)) as H_RemoveSplitLeft. {
            Transparent computeResultingOperation.
            Transparent SquashIterationDefinition.
            Transparent splitOperation.
            Transparent SplitHelper.
            unfold computeResultingOperation at 1.
            simpl.
            destruct AHead eqn:H_AHead; try destruct entries0; try destruct entries1.
            all: destruct side1; unfold SplitHelper; simpl.
            all: try assert(0 < amount) as H_amountGt0; simpl in lenAHead; try lia.
            all: try rewrite <-Nat.ltb_lt in H_amountGt0; try rewrite H_amountGt0; simpl; auto.
            assert (0 <? Datatypes.length entries0 = true) as H_entriesGt0; try rewrite Nat.ltb_lt; try lia.
            rewrite H_entriesGt0; simpl; auto.
            assert (0 <? Datatypes.length entries0 = true) as H_entriesGt0; try rewrite Nat.ltb_lt; try lia.
            rewrite H_entriesGt0; simpl; auto.
            assert (0 <? Datatypes.length entries1 = true) as H_entriesGt0; try rewrite Nat.ltb_lt; try lia.
            rewrite H_entriesGt0; simpl; auto.
            assert (0 <? Datatypes.length entries1 = true) as H_entriesGt0; try rewrite Nat.ltb_lt; try lia.
            rewrite H_entriesGt0; simpl; auto.
         }
         rewrite H_RemoveSplitLeft.
         change remB with (↩[remB]).
         rewrite <-H_remB.
         assert(AHead [≺≺0; side0] ⊕ ↩Insert (Seq entries0) side0 [≻≻lengthC; sideC] = ↩(Insert (Seq entries0) side0 [≻≻lengthC; sideC])). {

            Transparent computeResultingOperation.
            Transparent SquashIterationDefinition.
            Transparent splitOperation.
            all: destruct AHead eqn:H_AHead; try destruct entries0; try destruct entries1; try destruct side0; try destruct side1.
            Transparent SplitHelper.
            Transparent length.
            Transparent Nat.eqb.
            Transparent Nat.ltb.
            all: unfold splitOperation; simpl; unfold SplitHelper; simpl. 
            (*all: try assert(0 < amount) as H_amountGt0; simpl in lenAHead; try lia. *)
            all: simpl in lenAHead.
            assert(0 < amount) as H_param; only 1: lia.
            all: try (assert(0 < amount) as H_param; only 1: lia) +
                     (assert(0 < Datatypes.length entries0) as H_param; only 1: lia) + 
                     (assert(0 < Datatypes.length entries1) as H_param; only 1: lia).
            all: try rewrite <-Nat.ltb_lt in H_param; try rewrite H_param; simpl; auto.

            all: try assert( lengthC <? 0 = false) as H_lengthCnlt0; try rewrite Nat.ltb_nlt; try lia.
            all: try rewrite H_lengthCnlt0.
            all: case_eq(sideC); try (
              intros; simpl; auto;
              unfold opAGtB in H_BSmaller;
              fold lengthC in H_BSmaller; fold sideC in H_BSmaller;
              rewrite H7 in H_BSmaller;
              unfold getLengthInSequenceA in H_BSmaller;
              simpl in H_BSmaller;
              exfalso;
              destruct(lengthC =? 0); discriminate H_BSmaller
            ).

            all: intros; simpl; auto.
            
            Opaque getLengthInSequenceB.
            all: try solve [(
              assert( lengthC <? (S (Datatypes.length entries0)) = true) as H_lengthCltEntries; only 1:  (
                unfold opAGtB in H_BSmaller;
                fold lengthC in H_BSmaller;
                unfold getLengthInSequenceA in H_BSmaller;
                simpl in H_BSmaller;
                destruct (lengthC =? S (Datatypes.length entries0)); try discriminate H_BSmaller;
                auto
              );
              rewrite H_lengthCltEntries; simpl; auto
            ) 
            ].
            all: try destruct (lengthC <? (S (Datatypes.length entries0))) eqn:H_lenCDL; simpl; auto.

            (* TODO: Why doesn all not work here? *)
            (
              unfold opAGtB in H_BSmaller;
              unfold getLengthInSequenceA in H_BSmaller; simpl in H_BSmaller;
              fold lengthC in H_BSmaller;

              case_eq (lengthC =? S (Datatypes.length entries0)); only 1: (
                intro H_Test;
                rewrite H_Test in H_BSmaller;
                fold sideC in H_BSmaller;
                rewrite H7 in H_BSmaller; 
                discriminate H_BSmaller
              );
              intro H_Test;
              rewrite H_Test in H_BSmaller;
              rewrite H_lenCDL in H_BSmaller;
              discriminate H_BSmaller
            ).

            (
              unfold opAGtB in H_BSmaller;
              unfold getLengthInSequenceA in H_BSmaller; simpl in H_BSmaller;
              fold lengthC in H_BSmaller;

              case_eq (lengthC =? S (Datatypes.length entries0)); only 1: (
                intro H_Test;
                rewrite H_Test in H_BSmaller;
                fold sideC in H_BSmaller;
                rewrite H7 in H_BSmaller; 
                discriminate H_BSmaller
              );
              intro H_Test;
              rewrite H_Test in H_BSmaller;
              rewrite H_lenCDL in H_BSmaller;
              discriminate H_BSmaller
            ).

            (
              unfold opAGtB in H_BSmaller;
              unfold getLengthInSequenceA in H_BSmaller; simpl in H_BSmaller;
              fold lengthC in H_BSmaller;

              case_eq (lengthC =? S (Datatypes.length entries0)); only 1: (
                intro H_Test;
                rewrite H_Test in H_BSmaller;
                fold sideC in H_BSmaller;
                rewrite H7 in H_BSmaller; 
                discriminate H_BSmaller
              );
              intro H_Test;
              rewrite H_Test in H_BSmaller;
              rewrite H_lenCDL in H_BSmaller;
              discriminate H_BSmaller
            ).

            (
              unfold opAGtB in H_BSmaller;
              unfold getLengthInSequenceA in H_BSmaller; simpl in H_BSmaller;
              fold lengthC in H_BSmaller;

              case_eq (lengthC =? S (Datatypes.length entries0)); only 1: (
                intro H_Test;
                rewrite H_Test in H_BSmaller;
                fold sideC in H_BSmaller;
                rewrite H7 in H_BSmaller; 
                discriminate H_BSmaller
              );
              intro H_Test;
              rewrite H_Test in H_BSmaller;
              rewrite H_lenCDL in H_BSmaller;
              discriminate H_BSmaller
            ).
          }
          rewrite H7. auto.
        }
        rewrite H6; auto.
     

        Transparent getLengthInSequenceA.
        Transparent getLengthInSequenceB.
        Opaque computeResultingOperation.
        Opaque splitOperation.
        Transparent SquashIterationDefinition.
        Transparent Nat.eqb.
        Transparent Nat.ltb.

  - assert(splitOpARem = splitOpA) as H_spOAREMeqspOA. 
    unfold splitOpARem.
    unfold splitOpA.
    rewrite <-resolveNonEmptyArray with (x:=remA) (y:=[remA]); auto. unfold remA. rewrite <-H_remA.
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
  }
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

Definition A := [(Skip> 0)]).
Definition B := [Insert< [<$0, 0>; <$1, 1>; <$2, 2>]]).
Definition C := (OList [Skip< 0].

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