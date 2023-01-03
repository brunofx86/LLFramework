(** * Definitions for the OL Cut-Elimination Theorem  *)

(** This file contains some useful definitions and tactics for the
proof of the cut-elimination theorem of Object Logics *)


Require Import LL.OL.Requirement1.

Set Implicit Arguments. 

Section Bipoles.
Context `{OLR: OORules}.

Variable theory : oo -> Prop.
Variable Gamma : list oo. (* classical context *)
Variable Delta : list oo. (* linear context *)

Definition GenericBiPoleFailI
  F (Rule:  oo) : Prop :=
  forall n, seqN theory n Gamma (atom (up F)::Delta) ( DW Rule) -> False .

Definition GenericBiPoleAxiomI
  (F connective: uexp) 
  (Rule:  oo)
  (RBody: oo) : Prop :=
  forall n,
  seqN theory n Gamma (atom (up F)::Delta) ( DW Rule) ->
  isOLFormula connective ->
    ( (* case the atom is taken from the linear context *)
      (exists D1,
       Permutation Delta ( atom (down connective ) :: LEncode D1) /\
       seq theory  Gamma (atom (up F)::LEncode D1) (DW RBody) /\
       forall Delta1 Gamma1 (theory' : oo -> Prop),
       (theory'  (Rule)) ->
       seq theory' Gamma1  ( atom (down ((connective)) ) :: Delta1) (UP []))
     \/
    ( (* case the atom is taken from the classical context *)
       In (atom ( down connective )) Gamma /\
       seqN theory 0  Gamma (atom (up F)::Delta) (UP [RBody] ) /\  
       forall Delta1 Gamma1 (theory' : oo -> Prop),
       (theory'  Rule) ->
       In ( atom (down (connective) )) Gamma1 ->
       seq theory' Gamma1 Delta1 (UP []))).

Definition GenericBiPole1PI
  (F connective: uexp) 
  (Rule RBody:  oo)  : Prop :=
  forall n,
  seqN theory n Gamma (atom (up F):: Delta) ( DW Rule) ->
  isOLFormula connective ->
  exists D1' n' n'',    
  isOLFormulaL D1' /\ 
    (
      ( exists D1,
        Permutation Delta (atom (down connective)::LEncode D1) /\ 
        seq theory  Gamma (atom (up F)::LEncode D1) ( DW RBody) /\
        seqN theory n' Gamma (atom (up F)::LEncode (D1 ++ D1')) ( UP [])  /\
        n'' > 0 /\
        n = plus n' n'' /\
        forall Delta1 Gamma1 (theory' : oo -> Prop),
        (theory'  (Rule)) ->
        seq theory' Gamma1 (Delta1 ++ LEncode D1') (UP []) -> 
         seq theory' Gamma1 ( (atom (down ((connective)) )) :: Delta1) (UP []))
     \/
      ( In (atom (down (connective))) Gamma /\
        seq theory  Gamma (atom (up F)::Delta) (DW RBody) /\
        seqN theory n' Gamma (atom (up F):: (Delta ++ LEncode D1')) ( UP [])  /\
        n'' > 0 /\
        n = plus n'  n'' /\
        (forall Delta1 Gamma1 (theory' : oo -> Prop),
          seq theory' Gamma1 (Delta1 ++ LEncode D1') (UP []) ->
          seq theory' Gamma1 Delta1 (DW RBody))) ).
   
Definition GenericBiPole2PMI
(F connective: uexp)
  (Rule RBody: oo): Prop :=
  forall n,
  seqN theory n Gamma (atom (up F)::Delta) ( DW Rule) ->
  isOLFormula connective ->
  exists D D1' D2' n' n'',
  isOLFormulaL D1' /\
  IsPositiveAtomFormulaL D2' /\
  ( 
    ( Permutation Delta (atom (down connective):: LEncode D) /\
       seq theory  Gamma (atom (up F)::LEncode D) (DW RBody) /\
       seqN theory n' Gamma (atom (up F)::LEncode (D ++ D1')) (UP []) /\
       seqN theory n' Gamma (D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       seq theory' Gamma1 (Delta ++ LEncode D1') (UP []) ->
       seq theory' Gamma1 (D2') (UP []) ->
       seq theory' Gamma1 (atom ((down (connective))) :: Delta) (UP []))
   \/
       ( In (atom (down (connective) )) Gamma  /\ 
          Permutation Delta (LEncode D) /\
          seq theory  Gamma (atom (up F):: Delta) (DW RBody) /\
          seqN theory n' Gamma (atom (up F):: LEncode (D++D1')) (UP []) /\
          seqN theory n' Gamma (D2') (UP []) /\
          n'' > 0 /\
          n = plus n' n'' /\
          forall Delta Gamma1 (theory' : oo -> Prop),
          seq theory' Gamma1 (Delta ++ LEncode D1') (UP []) ->
          seq theory' Gamma1 (D2') (UP []) ->
          seq theory' Gamma1 (Delta) (DW RBody))).

Definition GenericBiPole2PAI
  (F connective: uexp)
  (Rule RBody: oo)  : Prop :=
  forall n,
  seqN theory n Gamma (atom (up F)::Delta) (DW Rule) ->
  isOLFormula connective ->
  exists D12 D1' D2'  n' n'',
  isOLFormulaL D1' /\
  isOLFormulaL D2' /\
  ( 
     ( Permutation Delta (atom (down connective):: LEncode D12) /\
       seq theory  Gamma (atom (up F)::LEncode D12) (DW RBody) /\
       seqN theory n' Gamma (atom (up F):: LEncode (D12 ++ D1')) (UP []) /\
       seqN theory n' Gamma (atom (up F):: LEncode (D12 ++ D2')) (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       seq theory' Gamma1 (Delta12 ++ LEncode D1') (UP []) ->
       seq theory' Gamma1 (Delta12 ++ LEncode D2') (UP []) ->
       seq theory' Gamma1 (atom ((down (connective))) :: Delta12) (UP [])
     )
   \/
     ( In (atom (down (connective))) Gamma /\
       seq theory  Gamma  (atom (up F)::Delta) (DW RBody) /\
       seqN theory n' Gamma (atom (up F):: (Delta ++ LEncode D1')) (UP []) /\
       seqN theory n' Gamma (atom (up F)::(Delta ++ LEncode D2')) (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       seq theory' Gamma1 (Delta12 ++ LEncode D1') (UP []) ->
       seq theory' Gamma1 (Delta12 ++ LEncode D2') (UP []) ->
       seq theory' Gamma1 Delta12 (DW RBody))).

Definition GenericBiPole1P'
  (connective: uexp) 
  (Rule:  oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
  exists D1' n' n'',    
  IsPositiveAtomBFormulaL D1' /\ 
    (
      ( exists D1,
        Permutation Delta ((atom (predicate connective))::D1) /\ 
        seq theory  Gamma D1 ( DW RBody) /\
        seqN theory n' Gamma (D1 ++ D1') ( UP [])  /\
        n'' > 0 /\
        n = plus n' n'' /\
        forall Delta1 Gamma1 (theory' : oo -> Prop),
        theory'  Rule ->
        seq theory' Gamma1 (Delta1 ++ D1') (UP []) -> 
         seq theory' Gamma1 ( (atom (predicate ((connective)) )) :: Delta1) (UP []))
     \/
      ( In (atom (predicate (connective))) Gamma /\
        seq theory  Gamma Delta (DW RBody) /\
        seqN theory n' Gamma (Delta ++ D1') ( UP [])  /\
        n'' > 0 /\
        n = plus n'  n'' /\
        (forall Delta1 Gamma1 (theory' : oo -> Prop),
          seq theory' Gamma1 (Delta1 ++ D1') (UP []) ->
          seq theory' Gamma1 Delta1 (UP [RBody]))) ).

Definition GenericBiPole2PM'
  (connective: uexp)
  (Rule: oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
  exists D D1' D2'  n' n'',
  IsPositiveAtomBFormulaL D1' /\
  IsPositiveAtomBFormulaL D2' /\
  ( 
    ( Permutation Delta (atom ((predicate connective )) :: D) /\
       seq theory  Gamma D (DW RBody) /\
       seqN theory n' Gamma D1' (UP []) /\
       seqN theory n' Gamma (D ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       seq theory' Gamma1 D1' (UP []) ->
       seq theory' Gamma1 (Delta ++ D2') (UP []) ->
       seq theory' Gamma1 (atom ((predicate (connective))) :: Delta) (UP []))
   \/
       ( In (atom (predicate (connective) )) Gamma  /\
          seq theory  Gamma Delta (DW RBody) /\
          seqN theory n' Gamma ( D1') (UP []) /\
          seqN theory n' Gamma (Delta ++ D2') (UP []) /\
          n'' > 0 /\
          n = plus n' n'' /\
          forall Delta Gamma1 (theory' : oo -> Prop),
          seq theory' Gamma1 D1' (UP []) ->
          seq theory' Gamma1 (Delta ++ D2') (UP []) ->
          seq theory' Gamma1 (Delta) (UP [RBody]))).


Definition GenericBiPole2PA'
  (connective: uexp)
  (Rule: oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta (DW Rule) ->
  isOLFormula connective ->
  exists D12 D1' D2' n' n'',
  IsPositiveAtomBFormulaL D1' /\
  IsPositiveAtomBFormulaL D2' /\
  ( 
     ( Permutation Delta (atom ((predicate connective )) :: D12) /\
       seq theory  Gamma D12 (DW RBody) /\
       seqN theory n' Gamma (D12 ++ D1') (UP []) /\
       seqN theory n' Gamma (D12 ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       seq theory' Gamma1 (Delta12 ++ D1') (UP []) ->
       seq theory' Gamma1 (Delta12 ++ D2') (UP []) ->
       seq theory' Gamma1 ( atom ((predicate ( connective) )) :: Delta12) (UP [])
     )
   \/
     ( In (atom (predicate (connective))) Gamma /\
       seq theory  Gamma Delta (DW RBody) /\
       seqN theory n' Gamma (Delta ++ D1') (UP []) /\
       seqN theory n' Gamma (Delta ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       seq theory' Gamma1 (Delta12 ++ D1') (UP []) ->
       seq theory' Gamma1 (Delta12 ++ D2') (UP []) ->
       seq theory' Gamma1 Delta12 (UP [RBody]))).

Definition BiPoleC' (lab: cons) (s:Side) (t : BipoleEnumCte): Prop :=
  match (sideC s) with
  | (rule, body, pred) =>
    match t with
      | BCFail => GenericBiPoleFail theory Gamma Delta (rule lab)
      | BCAxiom => GenericBiPoleAxiom  theory Gamma Delta  (t_cons lab) (rule lab) ( (rulesC lab).(body) )  pred
      | BCOneP => GenericBiPole1P' (t_cons lab) (rule lab) ( (rulesC lab).(body) ) pred
    end
 end.

Definition BiPoleCI  F (lab: cons) (t : BipoleEnumCte): Prop :=
    match t with
      | BCFail => GenericBiPoleFailI F (makeLRuleC lab)
      | BCAxiom => GenericBiPoleAxiomI  F (t_cons lab) (makeLRuleC lab) ( (rulesC lab).(rc_lftBody) ) 
      | BCOneP => GenericBiPole1PI F (t_cons lab) (makeLRuleC lab) ( (rulesC lab).(rc_lftBody) ) 
 end.


Definition BiPoleU' (lab: ucon) (s:Side) (t : BipoleEnum): Prop :=
  match (sideUnary s) with
  | (rule, body, pred) =>
     match t with
     | BOneP => forall Fo1, GenericBiPole1P' (t_ucon lab Fo1) (rule lab Fo1) ( (rulesU lab).(body) Fo1) pred
     | BTwoPM => forall Fo1, GenericBiPole2PM' (t_ucon lab Fo1) (rule lab Fo1) ( (rulesU lab).(body) Fo1) pred
     | BTwoPA => forall Fo1, GenericBiPole2PA' (t_ucon lab Fo1) (rule lab Fo1) ( (rulesU lab).(body) Fo1) pred
     end
end.

Definition BiPoleUI F (lab: ucon)  (t : BipoleEnum) : Prop :=
     match t with
     | BOneP => forall Fo1, GenericBiPole1PI F (t_ucon lab Fo1)  (makeLRuleU lab Fo1) ( (rulesU lab).(ru_lftBody) Fo1) 
     | BTwoPM => forall Fo1, GenericBiPole2PMI F (t_ucon lab Fo1)  (makeLRuleU lab Fo1) ( (rulesU lab).(ru_lftBody) Fo1)
     | BTwoPA => forall Fo1, GenericBiPole2PAI F (t_ucon lab Fo1)  (makeLRuleU lab Fo1) ( (rulesU lab).(ru_lftBody) Fo1)
end. 
    

Definition BiPoleB' (lab: bcon) (s:Side) (t : BipoleEnum): Prop :=
  match (sideBinary s) with
  | (rule, body, pred) =>
    match t with
    | BOneP => forall Fo1 Go1, GenericBiPole1P' (t_bcon lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesB lab).(body) Fo1 Go1) pred
    | BTwoPM => forall Fo1 Go1, GenericBiPole2PM' (t_bcon lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesB lab).(body) Fo1 Go1) pred
    | BTwoPA => forall Fo1 Go1, GenericBiPole2PA' (t_bcon lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesB lab).(body) Fo1 Go1) pred
    end
end.

Definition BiPoleBI F (lab: bcon)  (t : BipoleEnum) : Prop :=
     match t with
     | BOneP => forall Fo1 Go1, GenericBiPole1PI  F (t_bcon lab Fo1 Go1)  (makeLRuleB lab Fo1 Go1) ( (rulesB lab).(rb_lftBody) Fo1 Go1) 
     | BTwoPM => forall Fo1 Go1, GenericBiPole2PMI F (t_bcon lab Fo1 Go1)  (makeLRuleB lab Fo1 Go1) ( (rulesB lab).(rb_lftBody) Fo1 Go1)
     | BTwoPA => forall Fo1 Go1, GenericBiPole2PAI  F (t_bcon lab Fo1 Go1)  (makeLRuleB lab Fo1 Go1) ( (rulesB lab).(rb_lftBody) Fo1 Go1)
end. 


Definition BiPoleQ' (lab: qcon) (s:Side) (t : BipoleEnum): Prop :=
  match (sideQuantifier s) with
  | (rule, body, pred) =>
    match t with
    | BOneP => forall FX, uniform FX /\ GenericBiPole1P' (t_qcon lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    | BTwoPM => forall FX, uniform FX /\ GenericBiPole2PM' (t_qcon lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    | BTwoPA => forall FX, uniform FX /\ GenericBiPole2PA' (t_qcon lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    end
end.

 
Definition BiPoleQI  F (lab: qcon) (t : BipoleEnum): Prop :=
    match t with
    | BOneP => forall FX, uniform FX /\ GenericBiPole1PI F (t_qcon lab FX)  (makeLRuleQ lab FX) ( (rulesQ lab).(rq_lftBody) FX)
    | BTwoPM => forall FX, uniform FX /\ GenericBiPole2PMI F (t_qcon lab FX)  (makeLRuleQ lab FX) ( (rulesQ lab).(rq_lftBody) FX)
    | BTwoPA => forall FX, uniform FX /\ GenericBiPole2PAI  F (t_qcon lab FX)  (makeLRuleQ lab FX) ( (rulesQ lab).(rq_lftBody) FX)  end.

End Bipoles.

        
  
Section wellFormedTheory.
Context `{OLR: OORules}.
  (** A well-formed theory consists of rules that are cut-coherent
    and each rule is either a one-premise or a two-premises rule that
    satisfy the predicates [BiPole] *)

Definition wellFormedC' :Prop :=
  forall Theory Gamma Delta (lab: cons) (s:Side),
  exists (t: BipoleEnumCte), BiPoleC' Theory Gamma Delta lab s t.

Definition wellFormedCI :Prop :=
  forall Theory Gamma Delta F (lab: cons),
  exists (t: BipoleEnumCte), BiPoleCI Theory Gamma Delta F lab t.
    
Definition wellFormedU': Prop :=
  forall Theory Gamma Delta (lab: ucon) (s:Side),
  BiPoleU' Theory Gamma Delta lab s BOneP.

Definition wellFormedUI: Prop :=
  forall Theory Gamma Delta F (lab: ucon) ,
  BiPoleUI Theory Gamma Delta F lab BOneP.

Definition wellFormedB': Prop :=
  forall Theory Gamma Delta (lab: bcon) (s:Side),
  exists (t : BipoleEnum),  BiPoleB' Theory Gamma Delta lab s t.

Definition wellFormedBI: Prop :=
  forall Theory Gamma Delta F (lab: bcon),
  exists (t : BipoleEnum),  BiPoleBI Theory Gamma (LEncode Delta) F lab t.
  

Definition wellFormedQ': Prop :=
  forall Theory Gamma Delta (lab: qcon) (s:Side),
  BiPoleQ' Theory Gamma Delta lab s BOneP.

Definition wellFormedQI: Prop :=
  forall Theory Gamma Delta F (lab: qcon),
  BiPoleQI Theory Gamma Delta F lab BOneP.


Definition wellFormedTheory'  : Prop :=
  wellFormedC' /\   
  wellFormedU' /\ 
  wellFormedB' /\ 
  wellFormedQ' .

Definition wellFormedTheoryI  : Prop :=
  wellFormedCI /\
  wellFormedUI /\ 
  wellFormedBI /\ 
  wellFormedQI .


End wellFormedTheory.

Global Hint Unfold BiPoleC' BiPoleU' BiPoleB' BiPoleQ' : core .
Global Hint Unfold BiPoleCI BiPoleUI BiPoleBI BiPoleQI : core .
Global Hint Unfold wellFormedC' wellFormedU' wellFormedB' wellFormedQ' wellFormedTheory': core .
Global Hint Unfold wellFormedCI wellFormedUI wellFormedBI wellFormedQI wellFormedTheoryI: core .
