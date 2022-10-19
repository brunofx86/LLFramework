(** * Tactics for the focused system

In order to use FLL, this module must be imported. It defines useful
tactics for forward and backward (inversion) reasoning. Some useful
notations are also introduced.

As a general rule, tactics for the system without measures are names
with an apostrophe. For instance, [solveLL] for the system [seqN] and
[solveLL'] for the system [seq].
 *)
Require Export LL.Misc.Utils.
Require Export LL.SL.FLL.StructuralRules.
Require Import LL.Misc.Permutations.
Require Export LL.SL.FLL.PreTactics.
(* Require Export LL.SL.Focused.FLLAuxiliarResults. *)

Set Implicit Arguments.

Global Hint Constructors isFormula Remove seqN IsPositiveAtom : core .


Ltac llExact H :=
  let G:= type of H in
  match G with
  | (seqN _ ?x ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- seqN _ ?y ?Gamma' ?Delta' ?X ] =>
      assert( x <= y) by lia;
      eapply @HeightGeqEx with (n:=x) (CC':=Gamma) (LC':=Delta);
      [try perm | try perm | auto | lia ]

    end 
  end;auto.


Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (seq _ ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- seq _ ?Gamma' ?Delta' ?X ] =>
      apply @exchangeCC with (CC:= Gamma);auto; try perm;
      apply @exchangeLC with (LC:= Delta);auto;try perm
    end
  end;auto.

Ltac LLExact H := 
  match (type of H) with
  | seq _ _ _ _  =>  llExact' H
  | seqN _ _ _ _ _ => llExact H
  end.
  
 (* Hypothesis with a higher proof than the one needed *)
Ltac HProof :=
auto; try
  match goal with
 | [ H : seqN _ ?y ?G ?M ?X |- seqN _ ?x ?G ?M ?X ] =>
    assert( y <= x) by lia;
    eapply @HeightGeq  with (m:=x) in H;auto
 | [ H : seqN _ ?y ?G ?M ?X |- seqN _ ?x ?G' ?M' ?X ] =>
    LLExact H
 | [ H : seq _ ?y ?G ?M ?X |- seq _ ?G' ?M' ?X ] =>
    LLExact H
 | [ H : seqN _ ?n ?G ?M ?X |-  seq _ ?G ?M ?X ] =>
    eapply seqNtoSeq in H;exact H
 | [ H : seqN _ ?n ?G ?M ?X |-  seq _ ?G' ?M' ?X ] =>
    eapply seqNtoSeq in H; LLExact H  
  end.

Ltac solveLinearLogic :=
solveLL;try solve [HProof];
try
  match goal with
  | [H: seqN _ ?n ?B ?L (DW ?F) |- seqN _ ?m ?B ?L (DW (?F ⊕ ?G))] =>
      FLLleft; HProof
  | [H: seqN _ ?n ?B ?L (DW ?G) |- seqN _ ?m ?B ?L (DW (?F ⊕ ?G))] =>
      FLLright; HProof 
  | [H: seqN _ ?n ?B ?L (DW ?F) |- seq _ ?B ?L (DW (?F ⊕ ?G))] =>
      FLLleft; HProof
  | [H: seqN _ ?n ?B ?L (DW ?G) |- seq _ ?B ?L (DW (?F ⊕ ?G))] =>
      FLLright; HProof 
  | [H: seq _ ?B ?L (DW ?F) |- seq _ ?B ?L (DW (?F ⊕ ?G))] =>
      FLLleft
  | [H: seq _ ?B ?L (DW ?G) |- seq _ ?B ?L (DW (?F ⊕ ?G))] =>
      FLLright       
 end; try solveLL.

Ltac LLPermH H LI :=
  match goal with
  | [ H : seqN _ _ _ _ _ |- _] =>
          first[ apply exchangeLCN with (LC' := LI) in H ;[|perm]
               | apply exchangeCCN with (CC' := LI) in H ;[|perm]]
  | [ H : seq _ _ _ _ |- _] =>
          first[ apply exchangeLC with (LC' := LI) in H ;[|perm]
               | apply exchangeCC with (CC' := LI) in H ;[|perm]]
   end.


Ltac LLrew1 H1 H2 :=
 let G1:= type of H1 in
  match G1 with
  | Permutation ?A ?B => 
       let G2:= type of H2 in
         match G2 with
         | seq _ ?A _ _  =>
           eapply exchangeCC in H2; [| exact H1]
         | seq _ ?B _ _  =>
           eapply exchangeCC in H2; [| symmetry in H1; exact H1]
         | seq _  _ ?A _  =>
           eapply exchangeLC in H2; [| exact H1]
         | seq _ _ ?B _  =>
           eapply exchangeLC in H2; [| symmetry in H1; exact H1]
         
         | seqN _ _ ?A _ _  =>
           eapply exchangeCCN in H2; [| exact H1]
         | seqN _ _ ?B _ _  =>
           eapply exchangeCCN in H2; [| symmetry in H1; exact H1]
         | seqN _ _ _ ?A _  =>
           eapply exchangeLCN in H2; [| exact H1]
         | seqN _ _ _ ?B _  =>
           eapply exchangeLCN in H2; [| symmetry in H1; exact H1]
         
         | _ => idtac H2 "must to be a LL sequent"    
     end 
  | _ => idtac H1 "must to be a permutation"    
 end.

Ltac LLrew2 H :=
 let G:= type of H in
  match G with
  | Permutation ?A ?B => 
         match goal with
         | [ |- seq  _?A _ _]  =>
           eapply (exchangeCC H)
         | [ |- seq _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCC H);
           symmetry in H
         | [ |- seq _ _ ?A _ ] =>
           eapply (exchangeLC H)
         | [ |- seq _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLC H);
           symmetry in H
          | [ |- seqN _ _ ?A _ _]  =>
           eapply (exchangeCCN H)
         | [ |- seqN _ _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCCN H);
           symmetry in H
         | [ |- seqN _ _ _?A _ ] =>
           eapply (exchangeLCN H)
         | [ |- seqN _ _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLCN H);
           symmetry in H
         | _ => idtac "This goal is not compatible with " H    
     end 
  | _ => idtac H "must to be a permutation"    
 end.

 Tactic Notation "LLrewrite" constr(H) := LLrew2 H. 
 Tactic Notation "LLrewrite" constr(H1) "in" constr(H2) := LLrew1 H1 H2.

  
Ltac LLPerm LI :=
  match goal with
  | [ |- seqN _ _ _ _ _ ] =>
          first[ apply exchangeLCN with (LC := LI);[perm|]
               | apply exchangeCCN with (CC := LI);[perm|]]
  | [ |- seq _ _ _ _] =>
          first[ apply exchangeLC with (LC := LI);[perm|]
               | apply exchangeCC with (CC := LI);[perm|]]
     
end.


Ltac LLSwap :=
  match goal with
  | [ |-seqN _ _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-seqN _ _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  | [ |-seq  _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-seq  _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  end.

(** This tactic must be used to reason by inversion on hypotheses
  containing FLL sequents. Must of the "irrelevant" cases (as, e.g.,
  assuming that focused can be lost on a positive formula) are
  discarded. *)
  
Ltac invTriStep H :=
  repeat autounfold in H; simpl in H;
  let F := type of H in
  match F with
  |  seqN _ _ _ _ (DW ?S) =>
   match S with
      | Bot => inversion H
      | One => inversion H;subst;clearPolarity;solvePolarity
      | Zero  => inversion H;subst;clearPolarity;solvePolarity
      | Top => inversion H;subst;clearPolarity;solvePolarity
      | atom _  => inversion H;subst;clearPolarity;solvePolarity
      | perp _  => inversion H;subst;clearPolarity;solvePolarity
      | AOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | AAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | Bang _ => inversion H;subst;clearPolarity;solvePolarity
      | Quest _ => inversion H;subst;clearPolarity;solvePolarity
      | Some _ => inversion H;subst;clearPolarity;solvePolarity
      | All _ => inversion H;subst;clearPolarity;solvePolarity     
      end
  | seqN _ _ _ _ (UP (?S::_)) =>
   match S with
      | Bot => inversion H;subst;clearPolarity;solvePolarity
      | One => inversion H;subst;clearPolarity;solvePolarity
      | Zero  => inversion H;subst;clearPolarity;solvePolarity
      | Top => inversion H;subst;clearPolarity;solvePolarity
      | atom _  => inversion H;subst;clearPolarity;solvePolarity
      | perp _  => inversion H;subst;clearPolarity;solvePolarity
      | AOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | AAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | Bang _ => inversion H;subst;clearPolarity;solvePolarity
      | Quest _ => inversion H;subst;clearPolarity;solvePolarity
      | Some _ => inversion H;subst;clearPolarity;solvePolarity
      | All _ => inversion H;subst;clearPolarity;solvePolarity     
      end      
end.

Ltac invTriStep' H :=
  repeat autounfold in H; simpl in H;
  let F := type of H in
  match F with
  |  seq _ _ _ (DW ?S) =>
   match S with
      | Bot => inversion H;subst;clearPolarity;solvePolarity
      | One => inversion H;subst;clearPolarity;solvePolarity
      | Zero  => inversion H;subst;clearPolarity;solvePolarity
      | Top => inversion H;subst;clearPolarity;solvePolarity
      | atom _  => inversion H;subst;clearPolarity;solvePolarity
      | perp _  => inversion H;subst;clearPolarity;solvePolarity
      | AOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | AAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | Bang _ => inversion H;subst;clearPolarity;solvePolarity
      | Quest _ => inversion H;subst;clearPolarity;solvePolarity
      | Some _ => inversion H;subst;clearPolarity;solvePolarity
      | All _ => inversion H;subst;clearPolarity;solvePolarity     
      end
  | seq _ _ _ (UP (?S::_)) =>
   match S with
      | Bot => inversion H;subst;clearPolarity;solvePolarity
      | One => inversion H;subst;clearPolarity;solvePolarity
      | Zero  => inversion H;subst;clearPolarity;solvePolarity
      | Top => inversion H;subst;clearPolarity;solvePolarity
      | atom _  => inversion H;subst;clearPolarity;solvePolarity
      | perp _  => inversion H;subst;clearPolarity;solvePolarity
      | AOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MOr _ _ => inversion H;subst;clearPolarity;solvePolarity
      | MAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | AAnd _ _  => inversion H;subst;clearPolarity;solvePolarity
      | Bang _ => inversion H;subst;clearPolarity;solvePolarity
      | Quest _ => inversion H;subst;clearPolarity;solvePolarity
      | Some _ => inversion H;subst;clearPolarity;solvePolarity
      | All _ => inversion H;subst;clearPolarity;solvePolarity     
      end      
end.
  
Ltac invTri H := invTriStep H ; clear H.
Ltac invTri' H := invTriStep' H ; clear H.

(* Applies, possibly several times, inversion (invTri) on the 
    hypothesis containing focused sequents. It stops when the negative 
    phase ends ([Gamma ; Delta ; > []])
 *)
Ltac InvTriAll :=
  repeat
    match goal with
    | [H : seqN _ _ _ _ (DW _) |- _ ] => invTri H
    | [H : seqN _ _ _ _ (UP (?C :: _)) |- _ ] => invTri H
    end.

Ltac InvTriAll' :=
  repeat
    match goal with
    | [H : seq _ _ _ (DW _) |- _ ] => invTri' H
    | [H : seq _ _  _ (UP (?C :: _)) |- _ ] => invTri' H
    end.
