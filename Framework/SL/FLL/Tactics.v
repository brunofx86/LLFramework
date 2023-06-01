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

Global Hint Constructors isFormula Remove flln posAtom : core .


Ltac llExact H :=
  let G:= type of H in
  match G with
  | (flln _ ?x ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- flln _ ?y ?Gamma' ?Delta' ?X ] =>
      assert( x <= y) by lia;
      eapply @heightGeqFLLNEx with (n:=x) (CC':=Gamma) (LC':=Delta);
      [try perm | try perm | auto | lia ]

    end 
  end;auto.


Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (flls _ ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- flls _ ?Gamma' ?Delta' ?X ] =>
      apply @exchangeCC with (CC:= Gamma);auto; try perm;
      apply @exchangeLC with (LC:= Delta);auto;try perm
    end
  end;auto.

Ltac LLExact H := 
  match (type of H) with
  | flls _ _ _ _  =>  llExact' H
  | flln _ _ _ _ _ => llExact H
  end.
  
 (* Hypothesis with a higher proof than the one needed *)
Ltac HProof :=
auto; try
  match goal with
 | [ H : flln _ ?y ?G ?M ?X |- flln _ ?x ?G ?M ?X ] =>
    assert( y <= x) by lia;
    eapply @heightGeqFLLN  with (m:=x) in H;auto
 | [ H : flln _ ?y ?G ?M ?X |- flln _ ?x ?G' ?M' ?X ] =>
    LLExact H
 | [ H : flls _ ?y ?G ?M ?X |- flls _ ?G' ?M' ?X ] =>
    LLExact H
 | [ H : flln _ ?n ?G ?M ?X |-  flls _ ?G ?M ?X ] =>
    eapply FLLNtoFLLS in H;exact H
 | [ H : flln _ ?n ?G ?M ?X |-  flls _ ?G' ?M' ?X ] =>
    eapply FLLNtoFLLS in H; LLExact H  
  end.

Ltac solveLinearLogic :=
solveLL;try solve [HProof];
try
  match goal with
  | [H: flln _ ?n ?B ?L (DW ?F) |- flln _ ?m ?B ?L (DW (?F ⊕ ?G))] =>
      LLleft; HProof
  | [H: flln _ ?n ?B ?L (DW ?G) |- flln _ ?m ?B ?L (DW (?F ⊕ ?G))] =>
      LLright; HProof 
  | [H: flln _ ?n ?B ?L (DW ?F) |- flls _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLleft; HProof
  | [H: flln _ ?n ?B ?L (DW ?G) |- flls _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLright; HProof 
  | [H: flls _ ?B ?L (DW ?F) |- flls _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLleft
  | [H: flls _ ?B ?L (DW ?G) |- flls _ ?B ?L (DW (?F ⊕ ?G))] =>
      LLright       
 end; try solveLL.

Ltac LLPermH H LI :=
  match goal with
  | [ H : flln _ _ _ _ _ |- _] =>
          first[ apply exchangeLCN with (LC' := LI) in H ;[|perm]
               | apply exchangeCCN with (CC' := LI) in H ;[|perm]]
  | [ H : flls _ _ _ _ |- _] =>
          first[ apply exchangeLC with (LC' := LI) in H ;[|perm]
               | apply exchangeCC with (CC' := LI) in H ;[|perm]]
   end.


Ltac LLrew1 H1 H2 :=
 let G1:= type of H1 in
  match G1 with
  | Permutation ?A ?B => 
       let G2:= type of H2 in
         match G2 with
         | flls _ ?A _ _  =>
           eapply exchangeCC in H2; [| exact H1]
         | flls _ ?B _ _  =>
           eapply exchangeCC in H2; [| symmetry in H1; exact H1]
         | flls _  _ ?A _  =>
           eapply exchangeLC in H2; [| exact H1]
         | flls _ _ ?B _  =>
           eapply exchangeLC in H2; [| symmetry in H1; exact H1]
         
         | flln _ _ ?A _ _  =>
           eapply exchangeCCN in H2; [| exact H1]
         | flln _ _ ?B _ _  =>
           eapply exchangeCCN in H2; [| symmetry in H1; exact H1]
         | flln _ _ _ ?A _  =>
           eapply exchangeLCN in H2; [| exact H1]
         | flln _ _ _ ?B _  =>
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
         | [ |- flls  _?A _ _]  =>
           eapply (exchangeCC H)
         | [ |- flls _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCC H);
           symmetry in H
         | [ |- flls _ _ ?A _ ] =>
           eapply (exchangeLC H)
         | [ |- flls _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLC H);
           symmetry in H
          | [ |- flln _ _ ?A _ _]  =>
           eapply (exchangeCCN H)
         | [ |- flln _ _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCCN H);
           symmetry in H
         | [ |- flln _ _ _?A _ ] =>
           eapply (exchangeLCN H)
         | [ |- flln _ _ _ ?B _]  =>
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
  | [ |- flln _ _ _ _ _ ] =>
          first[ apply exchangeLCN with (LC := LI);[perm|]
               | apply exchangeCCN with (CC := LI);[perm|]]
  | [ |- flls _ _ _ _] =>
          first[ apply exchangeLC with (LC := LI);[perm|]
               | apply exchangeCC with (CC := LI);[perm|]]
     
end.


Ltac LLSwap :=
  match goal with
  | [ |-flln _ _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-flln _ _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  | [ |-flls  _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-flls  _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  end.

(** This tactic must be used to reason by inversion on hypotheses
  containing FLL sequents. Must of the "irrelevant" cases (as, e.g.,
  assuming that focused can be lost on a positive formula) are
  discarded. *)
  
Ltac invTriStep H :=
  repeat autounfold in H; simpl in H;
  let F := type of H in
  match F with
  |  flln _ _ _ _ (DW ?S) =>
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
  | flln _ _ _ _ (UP (?S::_)) =>
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
  |  flls _ _ _ (DW ?S) =>
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
  | flls _ _ _ (UP (?S::_)) =>
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
    | [H : flln _ _ _ _ (DW _) |- _ ] => invTri H
    | [H : flln _ _ _ _ (UP (?C :: _)) |- _ ] => invTri H
    end.

Ltac InvTriAll' :=
  repeat
    match goal with
    | [H : flls _ _ _ (DW _) |- _ ] => invTri' H
    | [H : flls _ _  _ (UP (?C :: _)) |- _ ] => invTri' H
    end.
