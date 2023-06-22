(** * Tactics for the focused system

In order to use FLL, this module must be imported. It defines useful
tactics for forward and backward (inversion) reasoning. Some useful
notations are also introduced.

As a general rule, tactics for the system without measures are names
with an apostrophe. For instance, [solveLL] for the system [seqN] and
[solveLL'] for the system [seq].
 *)
Require Export LL.Misc.Utils.
Require Export LL.Framework.SL.FLL.StructuralRules.
Require Import LL.Misc.Permutations.
Require Export LL.Framework.SL.FLL.PreTactics.
(* Require Export LL.SL.Focused.FLLAuxiliarResults. *)

Set Implicit Arguments.

Global Hint Constructors isFormula Remove FLLN posAtom : core .


Ltac llExact H :=
  let G:= type of H in
  match G with
  | (FLLN _ ?x ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- FLLN _ ?y ?Gamma' ?Delta' ?X ] =>
      assert( x <= y) by lia;
      eapply @heightGeqFLLNEx with (n:=x) (CC':=Gamma) (LC':=Delta);
      [try perm | try perm | auto | lia ]

    end 
  end;auto.


Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (FLLS _ ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- FLLS _ ?Gamma' ?Delta' ?X ] =>
      apply @exchangeCC with (CC:= Gamma);auto; try perm;
      apply @exchangeLC with (LC:= Delta);auto;try perm
    end
  end;auto.

Ltac LLExact H := 
  match (type of H) with
  | FLLS _ _ _ _  =>  llExact' H
  | FLLN _ _ _ _ _ => llExact H
  end.
  
 (* Hypothesis with a higher proof than the one needed *)
Ltac HProof :=
auto; try
  match goal with
 | [ H : FLLN _ ?y ?G ?M ?X |- FLLN _ ?x ?G ?M ?X ] =>
    assert( y <= x) by lia;
    eapply @heightGeqFLLN  with (m:=x) in H;auto
 | [ H : FLLN _ ?y ?G ?M ?X |- FLLN _ ?x ?G' ?M' ?X ] =>
    LLExact H
 | [ H : FLLS _ ?y ?G ?M ?X |- FLLS _ ?G' ?M' ?X ] =>
    LLExact H
 | [ H : FLLN _ ?n ?G ?M ?X |-  FLLS _ ?G ?M ?X ] =>
    eapply FLLNtoFLLS in H;exact H
 | [ H : FLLN _ ?n ?G ?M ?X |-  FLLS _ ?G' ?M' ?X ] =>
    eapply FLLNtoFLLS in H; LLExact H  
  end.

Ltac solveLinearLogic :=
solveLL;try solve [HProof];
try
  match goal with
  | [H: FLLN _ ?n ?B ?L (DW ?F) |- FLLN _ ?m ?B ?L (DW (?F ⊕ ?G))] =>
      LLleft; HProof
  | [H: FLLN _ ?n ?B ?L (DW ?G) |- FLLN _ ?m ?B ?L (DW (?F ⊕ ?G))] =>
      LLright; HProof 
  | [H: FLLN _ ?n ?B ?L (DW ?F) |- FLLS _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLleft; HProof
  | [H: FLLN _ ?n ?B ?L (DW ?G) |- FLLS _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLright; HProof 
  | [H: FLLS _ ?B ?L (DW ?F) |- FLLS _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLleft
  | [H: FLLS _ ?B ?L (DW ?G) |- FLLS _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLright       
 end; try solveLL.

Ltac LLPermH H LI :=
  match goal with
  | [ H : FLLN _ _ _ _ _ |- _] =>
          first[ apply exchangeLCN with (LC' := LI) in H ;[|perm]
               | apply exchangeCCN with (CC' := LI) in H ;[|perm]]
  | [ H : FLLS _ _ _ _ |- _] =>
          first[ apply exchangeLC with (LC' := LI) in H ;[|perm]
               | apply exchangeCC with (CC' := LI) in H ;[|perm]]
   end.


Ltac LLrew1 H1 H2 :=
 let G1:= type of H1 in
  match G1 with
  | Permutation ?A ?B => 
       let G2:= type of H2 in
         match G2 with
         | FLLS _ ?A _ _  =>
           eapply exchangeCC in H2; [| exact H1]
         | FLLS _ ?B _ _  =>
           eapply exchangeCC in H2; [| symmetry in H1; exact H1]
         | FLLS _  _ ?A _  =>
           eapply exchangeLC in H2; [| exact H1]
         | FLLS _ _ ?B _  =>
           eapply exchangeLC in H2; [| symmetry in H1; exact H1]
         
         | FLLN _ _ ?A _ _  =>
           eapply exchangeCCN in H2; [| exact H1]
         | FLLN _ _ ?B _ _  =>
           eapply exchangeCCN in H2; [| symmetry in H1; exact H1]
         | FLLN _ _ _ ?A _  =>
           eapply exchangeLCN in H2; [| exact H1]
         | FLLN _ _ _ ?B _  =>
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
         | [ |- FLLS  _?A _ _]  =>
           eapply (exchangeCC H)
         | [ |- FLLS _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCC H);
           symmetry in H
         | [ |- FLLS _ _ ?A _ ] =>
           eapply (exchangeLC H)
         | [ |- FLLS _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLC H);
           symmetry in H
          | [ |- FLLN _ _ ?A _ _]  =>
           eapply (exchangeCCN H)
         | [ |- FLLN _ _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCCN H);
           symmetry in H
         | [ |- FLLN _ _ _?A _ ] =>
           eapply (exchangeLCN H)
         | [ |- FLLN _ _ _ ?B _]  =>
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
  | [ |- FLLN _ _ _ _ _ ] =>
          first[ apply exchangeLCN with (LC := LI);[perm|]
               | apply exchangeCCN with (CC := LI);[perm|]]
  | [ |- FLLS _ _ _ _] =>
          first[ apply exchangeLC with (LC := LI);[perm|]
               | apply exchangeCC with (CC := LI);[perm|]]
     
end.


Ltac LLSwap :=
  match goal with
  | [ |-FLLN _ _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-FLLN _ _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  | [ |-FLLS  _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-FLLS  _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  end.

(** This tactic must be used to reason by inversion on hypotheses
  containing FLL sequents. Must of the "irrelevant" cases (as, e.g.,
  assuming that focused can be lost on a positive formula) are
  discarded. *)
  
Ltac invTriStep H :=
  repeat autounfold in H; simpl in H;
  let F := type of H in
  match F with
  |  FLLN _ _ _ _ (DW ?S) =>
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
  | FLLN _ _ _ _ (UP (?S::_)) =>
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
  |  FLLS _ _ _ (DW ?S) =>
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
  | FLLS _ _ _ (UP (?S::_)) =>
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
    | [H : FLLN _ _ _ _ (DW _) |- _ ] => invTri H
    | [H : FLLN _ _ _ _ (UP (?C :: _)) |- _ ] => invTri H
    end.

Ltac InvTriAll' :=
  repeat
    match goal with
    | [H : FLLS _ _ _ (DW _) |- _ ] => invTri' H
    | [H : FLLS _ _  _ (UP (?C :: _)) |- _ ] => invTri' H
    end.
