(** * Tactics for the focused system

In order to use MMLL, this module must be imported. It defines useful
tactics for forward and backward (inversion) reasoning. Some useful
notations are also introduced.

As a general rule, tactics for the system without measures are names
with an apostrophe. For instance, [solveLL] for the system [MLLN] and
[solveLL'] for the system [MLLS].
 *)

Require Export LL.Framework.SL.MMLL.StructuralRules.
Require Export LL.Framework.SL.MMLL.PreTactics.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Section FLL. *)

Ltac contraction_set M := 
 eapply @contractionSet with (L:=M);intros;
    match goal with
    | [H: In ?F ?X |- In ?F ?Y] =>
      try apply in_or_app;intuition
    end.

(** Finishes the proof if H is a MLLSuent that only needs some exchanges to be
equal to the goal *) 
Ltac llExact H :=
  let G:= type of H in
  match G with
  | (MLLN ?T ?x ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- MLLN ?T ?y ?Gamma' ?Delta' ?X ] =>
      assert( x <= y) by lia;
      eapply @HeightGeqEx with (n:=x) (CC':=Gamma) (LC':=Delta);
      [try perm | try perm | auto | lia ]

    end 
  end;auto.


Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (MLLS ?T ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- MLLS ?T ?Gamma' ?Delta' ?X ] =>
      apply @exchangeCC with (CC:= Gamma);auto; try perm;
      apply @exchangeLC with (LC:= Delta);auto;try perm
    end
  end;auto.

Ltac LLExact H := 
  match (type of H) with
  | MLLS _ _ _ _  =>  llExact' H
  | MLLN _ _ _ _ _ => llExact H
  end.
  
 (* Hypothesis with a higher proof than the one needed *)
Ltac HProof :=
auto; try
  match goal with
 | [ H : MLLN ?th ?y ?G ?M ?X |- MLLN ?th ?x ?G ?M ?X ] =>
    assert( y <= x) by lia;
    eapply @HeightGeq  with (m:=x) in H;auto
 | [ H : MLLN ?th ?y ?G ?M ?X |- MLLN ?th ?x ?G' ?M' ?X ] =>
    LLExact H
 | [ H : MLLS ?th ?y ?G ?M ?X |- MLLS ?th ?G' ?M' ?X ] =>
    LLExact H
 | [ H : MLLN _ ?n ?G ?M ?X |-  MLLS _ ?G ?M ?X ] =>
    eapply MLLNtoSeq in H;exact H
 | [ H : MLLN _ ?n ?G ?M ?X |-  MLLS _ ?G' ?M' ?X ] =>
    eapply MLLNtoSeq in H; LLExact H

 | [ H : tri_bangK4 _ ?n ?B ?i ?D ?M (UP ?L) |- tri_bangK4' _ ?B ?i ?D ?M (UP ?L)  ] =>
    eapply MLLNtoSeq_mutual in H;[exact H;firstorder]    
  end.

Ltac solveLinearLogic :=
solveLL;try solve [HProof];
try
  match goal with
  | [H: MLLN _ ?n ?B ?L (DW ?F) |- MLLN _ ?m ?B ?L (DW (AOr ?F ?G))] =>
      LLleft; HProof
  | [H: MLLN _ ?n ?B ?L (DW ?G) |- MLLN _ ?m ?B ?L (DW (AOr ?F ?G))] =>
      LLright; HProof 
  | [H: MLLN _ ?n ?B ?L (DW ?F) |- MLLS _ ?B ?L (DW (AOr ?F ?G))] =>
      LLleft; HProof
  | [H: MLLN _ ?n ?B ?L (DW ?G) |- MLLS _ ?B ?L (DW (AOr ?F ?G))] =>
      LLright; HProof 
  | [H: MLLS _ ?B ?L (DW ?F) |- MLLS _ ?B ?L (DW (AOr ?F ?G))] =>
      LLleft
  | [H: MLLS _ ?B ?L (DW ?G) |- MLLS _ ?B ?L (DW (AOr ?F ?G))] =>
      LLright       
 end; try solveF.


(** This tactic must be used to reason by inversion on hypotheses
  containing FLL MLLSuents. Must of the "irrelevant" cases (as, e.g.,
  assuming that focused can be lost on a positive formula) are
  discarded. *)
Ltac invTriStep H :=
  repeat autounfold in H;
  simpl in H;
  let F := type of H in
  let H' := fresh "H" in
  match F with
  | MLLN _ _  _ _ (UP []) => inversion H;subst;solveF (* decision rules *)
  | MLLN _ _  _ _ (UP ((One ):: _)) => inversion H;subst (* Store *)
  | MLLN _ _  _ _ (UP ((Zero ):: _)) => inversion H;subst (* Store *)
  | MLLN _ _  _ _ (UP ((Bot ):: _)) => inversion H;[subst | solveF] (* Bot *)
  | MLLN _ _  _ _ (UP ((atom _ ):: _)) => inversion H;subst (* Store *)
  | MLLN _ _  _ _ (UP ((perp _ ):: _)) => inversion H;subst (* Store *)
  | MLLN _ _  _ _ (UP ((AAnd _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with  *)
  | MLLN _ _  _ _ (UP ((MOr _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with /release *)
  | MLLN _ _  _ _ (UP ((AOr _ _) :: _)) => inversion H;subst (* store *)
  | MLLN _ _  _ _ (UP ((MAnd _ _) :: _)) => inversion H;subst (* store *)
  | MLLN _ _  _ _ (UP ((Bang _ _) :: _)) => inversion H;subst (* store *)
  | MLLN _ _  _ _ (UP ((Quest _ _):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* quest *)
  | MLLN _ _  _ _ (UP ((All _):: _) ) => inversion H;subst; [solveF | idtac] (* forall /release *)
  | MLLN _ _  _ _ (UP ((Some _):: _) ) => inversion H;subst (* store *)
  | MLLN _ _  _ _ (UP ((Top):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* top *)
  | MLLN _ _  _ _ (DW (MAnd _ _)) => inversion H;subst;[idtac | solveF] (* tensor --2nd branch contradictory/release*)
  | MLLN _ _  _ _ (DW (AOr _ _)) => inversion H;subst;[idtac | idtac | solveF]  (* oplus --2nd branch contradictory *)
  | MLLN _ _  _ _ (DW (Bang _ _)) => inversion H;subst;[idtac | solveF]  (* --2nd branch contradictory *)
  | MLLN _ _  _ _ (DW  (perp _)) => apply FocusAtomN in H as H';inversion H';solveF (* [solveF | intro; apply True]*)  (* focus on an atom*)
  | MLLN _ _  _ _ (DW  (atom _ )) => inversion H;subst (* release *)
  | MLLN _ _  _ _ (DW  (Top)) => inversion H;subst (* top *)
  | MLLN _ _  _ _ (DW  (Bot)) => inversion H;subst (* bot *)
  | MLLN _ _  _ _ (DW  (Quest _ _)) => inversion H;subst (* quest *)
  | MLLN _ _  _ _ (DW  (MOr _ _)) => inversion H;subst 
  | MLLN _ _  _ _ (DW  (AAnd _ _)) => inversion H;subst (* with /release *)
  | MLLN _ _  _ _ (DW  (All _) ) => inversion H;subst (* forall /release *)
  | MLLN _ _  _ _ (DW (Some _) ) => inversion H;subst; [solveF | ] (* exists *)
  | MLLN _ _  _ _ (DW (Zero) ) => inversion H;solveF 
  end.

Ltac invTri H := invTriStep H ; clear H.

(** Version without measures *)
Ltac invTri' H :=
  repeat autounfold in H;
  simpl in H;
  let F := type of H in
  let H' := fresh "H" in
  match F with
  | MLLS _  _ _ (UP []) => inversion H;subst;solveF (* decision rules *)
  | MLLS _  _ _ (UP ((One ):: _)) => inversion H;subst (* Store *)
  | MLLS _  _ _ (UP ((Zero ):: _)) => inversion H;subst (* Store *)
  | MLLS _  _ _ (UP ((Bot ):: _)) => inversion H;[subst | solveF] (* Bot *)
  | MLLS _  _ _ (UP ((Top):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* top *)
  | MLLS _  _ _ (UP ((atom _ ):: _)) => inversion H;subst (* Store *)
  | MLLS _  _ _ (UP ((perp _ ):: _)) => inversion H;subst (* Store *)
  | MLLS _  _ _ (UP ((AAnd _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with  *)
  | MLLS _  _ _ (UP ((MOr _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with /release *)
  | MLLS _  _ _ (UP ((AOr _ _) :: _)) => inversion H;subst (* store *)
  | MLLS _  _ _ (UP ((MAnd _ _) :: _)) => inversion H;subst (* store *)
  | MLLS _  _ _ (UP ((Bang _ _) :: _)) => inversion H;subst (* store *)
  | MLLS _  _ _ (UP ((Quest _ _):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* quest *)
  | MLLS _  _ _ (UP ((All _):: _) ) => inversion H;subst; [solveF | idtac] (* forall /release *)
  | MLLS _  _ _ (UP ((Some _):: _) ) => inversion H;subst (* store *)
  | MLLS _  _ _ (DW (MAnd _ _)) => inversion H;subst;[idtac | solveF] (* tensor --2nd branch contradictory/release*)
  | MLLS _  _ _ (DW (AOr _ _)) => inversion H;subst;[idtac | idtac |  solveF] (* oplus --2nd branch contradictory/release*)
  | MLLS _  _ _ (DW (Bang _ _)) => inversion H;subst;[idtac | solveF] (* 2nd branch contradictory/release*)
(*  | MLLS _  _ _ (DW  (perp _)) => apply FocusAtom in H as H'; inversion H'; solveF  *)  (* focus on an atom*)
  | MLLS _  _ _ (DW  (atom _ )) => inversion H;subst (* release *)
  | MLLS _  _ _ (DW  (Top)) => inversion H;subst (* top *)
  | MLLS _  _ _ (DW  (Bot)) => inversion H;subst (* bot *)
  | MLLS _  _ _ (DW  (Quest _ _)) => inversion H;subst (* quest *)
  | MLLS _  _ _ (DW  (MOr _ _)) => inversion H;subst 
  | MLLS _  _ _ (DW  (AAnd _ _)) => inversion H;subst (* with /release *)
  | MLLS _  _ _ (DW  (All _) ) => inversion H;subst (* forall /release *)
  | MLLS _  _ _ (DW (Some _) ) => inversion H;subst; [solveF | ] (* exists *)
  | MLLS _  _ _ (DW (Zero ) ) => inversion H;solveF
  end;
  clear H.

Ltac FLLInversion H :=
  match (type of H) with
  | MLLS _ _ _ _  =>  invTri' ; clear H
  | MLLN _ _ _ _ _ => invTriStep H ; clear H
end.

    

(* Applies, possibly several times, inversion (invTri) on the 
    hypothesis containing focused MLLSuents. It stops when the negative 
    phase ends ([Gamma ; Delta ; > []])
 *)

Ltac FLLInversionAll :=
  repeat
    match goal with
    | [H : MLLN _ _ _ _ (DW _) |- _ ] => invTri H
    | [H : MLLN _ _ _ _ (UP (?C :: _)) |- _ ] => invTri H
    | [H : MLLS _ _ _ (DW _) |- _ ] => invTri' H
    | [H : MLLS _ _ _ (UP (?C :: _)) |- _ ] => invTri' H
    end.
  

(* Check if the permutation P applies to the MLLSuent in H and rewrites it *)
Ltac LLPermH H LI :=
  match goal with
  | [ H : MLLN _ _ _ _ _ |- _] =>
          first[ apply exchangeLCN with (LC' := LI) in H ;[|sauto]
               | apply exchangeCCN with (CC' := LI) in H ;[|sauto]]
  | [ H : MLLS _ _ _ _ |- _] =>
          first[ apply exchangeLC with (LC' := LI) in H ;[|sauto]
               | apply exchangeCC with (CC' := LI) in H ;[|sauto]]
  | [ H : tri_bangK4 _ _ _ _ _ _ _ |- _] =>
          first[ apply exchangeCCNK4 with (CC' := LI) in H ;[|sauto]
               | apply exchangeCCNKK4 with (CC' := LI) in H ;[|sauto]]
  | [ H : tri_bangK4' _ _ _ _ _ _ |- _] =>
          first[ apply exchangeCCK4 with (CC' := LI) in H ;[|sauto]
               | apply exchangeCCKK4 with (CC' := LI) in H ;[|sauto]]
  end.


Ltac LLrew1 H1 H2 :=
 let G1:= type of H1 in
  match G1 with
  | Permutation ?A ?B => 
       let G2:= type of H2 in
         match G2 with
         | MLLS _ ?A _ _  =>
           eapply exchangeCC in H2; [| exact H1]
         | MLLS _ ?B _ _  =>
           eapply exchangeCC in H2; [| symmetry in H1; exact H1]
         | MLLS _ _ ?A _  =>
           eapply exchangeLC in H2; [| exact H1]
         | MLLS _ _ ?B _  =>
           eapply exchangeLC in H2; [| symmetry in H1; exact H1]
         
         | MLLN _ _ ?A _ _  =>
           eapply exchangeCCN in H2; [| exact H1]
         | MLLN _ _ ?B _ _  =>
           eapply exchangeCCN in H2; [| symmetry in H1; exact H1]
         | MLLN _ _ _ ?A _  =>
           eapply exchangeLCN in H2; [| exact H1]
         | MLLN _ _ _ ?B _  =>
           eapply exchangeLCN in H2; [| symmetry in H1; exact H1]
         
         | _ => idtac H2 "must to be a LL MLLSuent"    
     end 
  | _ => idtac H1 "must to be a permutation"    
 end.

Ltac LLrew2 H :=
 let G:= type of H in
  match G with
  | Permutation ?A ?B => 
         match goal with
         | [ |- MLLS _ ?A _ _]  =>
           eapply (exchangeCC H)
         | [ |- MLLS _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCC H);
           symmetry in H
         | [ |- MLLS _ _ ?A _ ] =>
           eapply (exchangeLC H)
         | [ |- MLLS _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLC H);
           symmetry in H
          | [ |- MLLN _ _ ?A _ _]  =>
           eapply (exchangeCCN H)
         | [ |- MLLN _ _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCCN H);
           symmetry in H
         | [ |- MLLN _ _ _ ?A _ ] =>
           eapply (exchangeLCN H)
         | [ |- MLLN _ _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLCN H);
           symmetry in H
         | _ => idtac "This goal is not compatible with " H    
     end 
  | _ => idtac H "must to be a permutation"    
 end.

 Tactic Notation "LLrewrite" constr(H) := LLrew2 H. 
 Tactic Notation "LLrewrite" constr(H1) "in" constr(H2) := LLrew1 H1 H2.

 Tactic Notation "LLSplit" :=  
     match goal with
      | [ |- MLLS _ ?B _ _]  => LLrewrite (symmetry (cxtDestruct B))
      | [ |- MLLN _ _ ?B _ _]  => LLrewrite (symmetry (cxtDestruct B))
     end.
     
  Tactic Notation "LLSplit" "in" constr(H)  :=  
     match type of H with
      | MLLS _ ?B _ _  => LLrewrite (cxtDestruct B) in H
      | MLLN _ _ ?B _ _  => LLrewrite (cxtDestruct B) in H
     end.    
        
  
Ltac LLPerm LI :=
  match goal with
  | [ |- MLLN _ _ _ _ _ ] =>
          first[ apply exchangeLCN with (LC := LI);[sauto|]
               | apply exchangeCCN with (CC := LI);[sauto|]]
  | [ |- MLLS _ _ _ _ ] =>
          first[ apply exchangeLC with (LC := LI);[sauto|]
               | apply exchangeCC with (CC := LI);[sauto|]]
  | [ |- tri_bangK4 _ _ _ _ _ _ _ ] =>
          first[ apply exchangeCCNK4 with (CC := LI);[sauto|]
               | apply exchangeCCNKK4 with (CC := LI);[perm|]]
  | [ |- tri_bangK4' _ _ _ _ _ _ ] =>
          first[ apply exchangeCCK4 with (CC := LI);[sauto|]
               | apply exchangeCCKK4 with (CC := LI);[sauto|]]
end.
  
(** This version of [LLPerm] first simplifies the parameter LI *)
Ltac sLLPermH H LI :=
  let LI' := (eval cbn in LI ) in
  let LI'' := constr:(LI') in
  LLPermH H LI''.

Ltac sLLPerm LI :=
  let LI' := (eval cbn in LI ) in
  let LI'' := constr:(LI') in
  LLPerm LI''.
(** "rewrite perm_swap in H" would be enough for exchanging the first 2
elements of a list. However, such rewrite is quite slow (probably for
Coq's search mechanism in Class Instances). This tactic implement the
same step without using rewriting *)
Ltac LLSwapH H :=
        let Hs := type of H in 
        match Hs with
        |  (MLLN _ _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCCN with (CC':= (G :: F :: L)) in H;[|perm]
        |  (MLLS  _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCC with (CC':= (G :: F :: L)) in H;[|perm]
        end.

Ltac LLSwap :=
  match goal with
  | [ |-MLLN _ _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-MLLN _ _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  | [ |-MLLS  _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-MLLS  _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  end.

Ltac finishExponential :=  match goal with
  | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: m4 ?a = true, H3: u ?a = true |- _ ] => 
       let a := fresh "CK4" in
       let c := fresh "CN" in
        apply InvSubExpPhaseUK4 in H; 
        [ destruct H as [a H];
          destruct H as [c H];CleanContext | auto | auto | try solve[auto | intro;subst;solveSubExp] ]           

    | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: u ?a = true |- _ ] => 
     let a := fresh "CK4" in
     let b := fresh "CK" in
     let c := fresh "CN" in
        apply InvSubExpPhaseU in H; 
        [ destruct H as [a H];
          destruct H as [b H];
          destruct H as [c H];CleanContext | auto | try solve[auto | intro;subst;solveSubExp] ]; idtac H2    

   
    | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: m4 ?a = true |- _ ] => 
       let a := fresh "CK4" in
       let c := fresh "CN" in
        apply InvSubExpPhaseK4 in H; 
        [ destruct H as [a H];
          destruct H as [c H];CleanContext | auto | try solve[auto | intro;subst;solveSubExp] ]           
   
 | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: UNoDSigMMLL |- _ ] => 
     let a := fresh "CK4" in
     let b := fresh "CK" in
     let c := fresh "CN" in
        apply InvSubExpPhaseU in H; 
        [ destruct H as [a H];
          destruct H as [b H];
          destruct H as [c H];CleanContext | auto | try solve[auto | intro;subst;solveSubExp] ]; idtac H2    

 | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L) |- _ ] => 
     let a := fresh "CK4" in
     let b := fresh "CK" in
     let c := fresh "CN" in
        apply InvSubExpPhase in H;
        [ destruct H as [a H];
         destruct H as [b H];
         destruct H as [c H];CleanContext |  try solve[auto | intro;subst;solveSubExp] ]
    end.

  Ltac LLSwapL H :=
        let Hs := type of H in 
        match Hs with
        |  (MLLN _ _ _ (?F :: ?G :: ?L) _) =>
           apply exchangeLCN with (LC':= (G :: F :: L)) in H;[|perm]
        |  (MLLS  _ _ (?F :: ?G :: ?L) _) =>
           apply exchangeLC with (LC':= (G :: F :: L)) in H;[|perm]
        end.

  Ltac LLSwapC H :=
        let Hs := type of H in 
        match Hs with
        |  (MLLN _ _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCCN with (CC':= (G :: F :: L)) in H;[|perm]
        |  (MLLS  _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCC with (CC':= (G :: F :: L)) in H;[|perm]
        end.

