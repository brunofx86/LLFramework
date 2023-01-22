(** * Definitions for the OL Cut-Elimination Theorem  *)

(** This file contains some useful definitions and tactics for the
proof of the cut-elimination theorem of Object Logics *)


Require Export LL.SL.FLL.Specifications.Bipoles.

Set Implicit Arguments. 


(** Building the inference rules (bipoles)  cut-coherence and well-formedness conditions *)
Section Bipoles.
Context `{OLR: OORules}.

Variable theory : oo -> Prop.
Variable Gamma : list oo. (* classical context *)
Variable Delta : list oo. (* linear context *)
    
   (** The following definition determines the possible shapes of
    derivation when a bipole is focused on. We consider four cases:
- [GenericBiPoleFail] when the sequent is not provable (e.g., this is
  useful when encoding the rule for falsity on the left (no rule)
- [GenericBiPoleAxiom] when the sequent must finish immediately (e..g,
  when the falsity-left rule is encoded
- [GenericBiPole1P] when the derivation must produce a unique premise
- [GenericBiPole2PM] when the bipole produces two premises and the
  context is split (multiplicative case )
- [GenericBiPole2PA] when the bipole produces two premises and the
  context is shared (additive case )
     *)
    
(** Case No Provable *)
Definition GenericBiPoleFail
  (Rule:  oo) : Prop :=
  forall n, flln theory n Gamma Delta ( DW Rule) -> False .

(** Case of 0 premise *)
Definition GenericBiPoleAxiom
  (connective: uexp) 
  (Rule:  oo)
  (RBody: oo) 
  (predicate: uexp -> atm) : Prop :=
  forall n,
  flln theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
    ( (* case the atom is taken from the linear context *)
      (exists D1,
       Permutation Delta ( atom (predicate connective ) :: D1) /\
       flls theory  Gamma D1 (DW RBody) /\
       forall Delta1 Gamma1 (theory' : oo -> Prop),
       (theory'  (Rule)) ->
       flls theory' Gamma1  ( atom (predicate ((connective)) ) :: Delta1) (UP []))
     \/
    ( (* case the atom is taken from the classical context *)
       In (atom ( predicate connective )) Gamma /\
       flln theory 0  Gamma Delta (UP [RBody] ) /\  
       forall Delta1 Gamma1 (theory' : oo -> Prop),
       (theory'  Rule) ->
       In ( atom (predicate (connective) )) Gamma1 ->
       flls theory' Gamma1 Delta1 (UP []))).

(** Case of 1 premise *)
Definition GenericBiPole1P
  (connective: uexp) 
  (Rule:  oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  flln theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
  exists D1' n' n'',    
  IsPositiveAtomFormulaL D1' /\ 
    (
      ( exists D1,
        Permutation Delta ((atom (predicate connective))::D1) /\ 
        flls theory  Gamma D1 ( DW RBody) /\
        flln theory n' Gamma (D1 ++ D1') ( UP [])  /\
        n'' > 0 /\
        n = plus n' n'' /\
        forall Delta1 Gamma1 (theory' : oo -> Prop),
        (theory'  (Rule)) ->
        flls theory' Gamma1 (Delta1 ++ D1') (UP []) -> 
         flls theory' Gamma1 ( (atom (predicate ((connective)) )) :: Delta1) (UP []))
     \/
      ( In (atom (predicate (connective))) Gamma /\
        flls theory  Gamma Delta (DW RBody) /\
        flln theory n' Gamma (Delta ++ D1') ( UP [])  /\
        n'' > 0 /\
        n = plus n'  n'' /\
        (forall Delta1 Gamma1 (theory' : oo -> Prop),
          flls theory' Gamma1 (Delta1 ++ D1') (UP []) ->
          flls theory' Gamma1 Delta1 (DW RBody))) ).
    
(** Case of 2 premises (multiplicative case) *)
Definition GenericBiPole2PM
  (connective: uexp)
  (Rule: oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  flln theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
  exists D1 D2 D1' D2'  n' n'',
  IsPositiveAtomFormulaL D1' /\
  IsPositiveAtomFormulaL D2' /\
  ( 
    ( Permutation Delta (atom ((predicate connective )) :: (D1 ++ D2)) /\
       flls theory  Gamma (D1 ++ D2) (DW RBody) /\
       flln theory n' Gamma (D1 ++ D1') (UP []) /\
       flln theory n' Gamma (D2 ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta1 Delta2 Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       flls theory' Gamma1 (Delta1 ++ D1') (UP []) ->
       flls theory' Gamma1 (Delta2 ++ D2') (UP []) ->
       flls theory' Gamma1 (atom ((predicate (connective))) :: Delta1 ++ Delta2) (UP []))
   \/
       ( In (atom (predicate (connective) )) Gamma  /\
          Permutation Delta (D1 ++ D2) /\
          flls theory  Gamma Delta (DW RBody) /\
          flln theory n' Gamma (D1 ++ D1') (UP []) /\
          flln theory n' Gamma (D2 ++ D2') (UP []) /\
          n'' > 0 /\
          n = plus n' n'' /\
          forall Delta1 Delta2 Gamma1 (theory' : oo -> Prop),
          flls theory' Gamma1 (Delta1 ++ D1') (UP []) ->
          flls theory' Gamma1 (Delta2 ++ D2') (UP []) ->
          flls theory' Gamma1 (Delta1 ++ Delta2) (DW RBody))).


(** Case of 2 premises (additive case) *)
Definition GenericBiPole2PA
  (connective: uexp)
  (Rule: oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  flln theory n Gamma Delta (DW Rule) ->
  isOLFormula connective ->
  exists D12 D1' D2' n' n'',
  IsPositiveAtomFormulaL D1' /\
  IsPositiveAtomFormulaL D2' /\
  ( 
     ( Permutation Delta (atom ((predicate connective )) :: D12) /\
       flls theory  Gamma D12 (DW RBody) /\
       flln theory n' Gamma (D12 ++ D1') (UP []) /\
       flln theory n' Gamma (D12 ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       flls theory' Gamma1 (Delta12 ++ D1') (UP []) ->
       flls theory' Gamma1 (Delta12 ++ D2') (UP []) ->
       flls theory' Gamma1 ( atom ((predicate ( connective) )) :: Delta12) (UP [])
     )
   \/
     ( In (atom (predicate (connective))) Gamma /\
       flls theory  Gamma Delta (DW RBody) /\
       flln theory n' Gamma (Delta ++ D1') (UP []) /\
       flln theory n' Gamma (Delta ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       flls theory' Gamma1 (Delta12 ++ D1') (UP []) ->
       flls theory' Gamma1 (Delta12 ++ D2') (UP []) ->
       flls theory' Gamma1 Delta12 (DW RBody))).

Inductive BipoleEnum :=  BOneP | BTwoPM | BTwoPA .
Inductive BipoleEnumCte :=  BCFail | BCAxiom | BCOneP .

Definition sideConstant (s:Side) :=
  match s with
  | Left => (makeLRuleC, rc_lftBody, down)
  | Right => (makeRRuleC, rc_rgtBody, up)
end.
    
Definition sideUnary (s:Side) :=
  match s with
  | Left => (makeLRuleU, ru_lftBody, down)
  | Right => (makeRRuleU, ru_rgtBody, up)
end.

Definition sideBinary (s:Side) :=
  match s with
  | Left => (makeLRuleB, rb_lftBody, down)
  | Right => (makeRRuleB, rb_rgtBody, up)
end.


Definition sideQuantifier (s:Side) :=
  match s with
  | Left => (makeLRuleQ, rq_lftBody, down)
  | Right => (makeRRuleQ, rq_rgtBody, up)
end.


Definition BiPoleC (lab: ccon) (s:Side) (t : BipoleEnumCte): Prop :=
  match (sideConstant s) with
  | (rule, body, pred) =>
    match t with
      | BCFail => GenericBiPoleFail (rule lab)
      | BCAxiom => GenericBiPoleAxiom  (t_ccon lab) (rule lab) ( (rulesC lab).(body) )  pred
      | BCOneP => GenericBiPole1P (t_ccon lab) (rule lab) ( (rulesC lab).(body) ) pred
    end
 end.

Definition BiPoleU (lab: ucon) (s:Side) (t : BipoleEnum): Prop :=
  match (sideUnary s) with
  | (rule, body, pred) =>
     match t with
     | BOneP => forall Fo1, GenericBiPole1P (t_ucon lab Fo1) (rule lab Fo1) ( (rulesU lab).(body) Fo1) pred
     | BTwoPM => forall Fo1, GenericBiPole2PM (t_ucon lab Fo1) (rule lab Fo1) ( (rulesU lab).(body) Fo1) pred
     | BTwoPA => forall Fo1, GenericBiPole2PA (t_ucon lab Fo1) (rule lab Fo1) ( (rulesU lab).(body) Fo1) pred
     end
end.

Definition BiPoleB (lab: bcon) (s:Side) (t : BipoleEnum): Prop :=
  match (sideBinary s) with
  | (rule, body, pred) =>
    match t with
    | BOneP => forall Fo1 Go1, GenericBiPole1P (t_bcon lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesB lab).(body) Fo1 Go1) pred
    | BTwoPM => forall Fo1 Go1, GenericBiPole2PM (t_bcon lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesB lab).(body) Fo1 Go1) pred
    | BTwoPA => forall Fo1 Go1, GenericBiPole2PA (t_bcon lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesB lab).(body) Fo1 Go1) pred
    end
end.

Definition BiPoleQ (lab: qcon) (s:Side) (t : BipoleEnum): Prop :=
  match (sideQuantifier s) with
  | (rule, body, pred) =>
    match t with
    | BOneP => forall FX, uniform FX /\ GenericBiPole1P (t_qcon lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    | BTwoPM => forall FX, uniform FX /\ GenericBiPole2PM (t_qcon lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    | BTwoPA => forall FX, uniform FX /\ GenericBiPole2PA (t_qcon lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    end
end.
End Bipoles.

Section wellFormedTheory.
Context `{OLR: OORules}.

Definition wellFormedC :Prop :=
  forall Theory Gamma Delta (lab: ccon) (s:Side),
  exists (t: BipoleEnumCte), BiPoleC Theory Gamma Delta lab s t.
    
Definition wellFormedU: Prop :=
  forall Theory Gamma Delta (lab: ucon) (s:Side),
  BiPoleU Theory Gamma Delta lab s BOneP.

Definition wellFormedB: Prop :=
  forall Theory Gamma Delta (lab: bcon) (s:Side),
  exists (t : BipoleEnum),  BiPoleB Theory Gamma Delta lab s t.

(* We assume that quantifiers are encoded with one premise bipoles *)
Definition wellFormedQ: Prop :=
  forall Theory Gamma Delta (lab: qcon) (s:Side),
  BiPoleQ Theory Gamma Delta lab s BOneP.

Definition wellFormedTheory  : Prop :=
  wellFormedC /\ wellFormedU /\ 
  wellFormedB /\ wellFormedQ.

End wellFormedTheory.


Global Hint Unfold BiPoleC BiPoleU BiPoleB BiPoleQ : core .
Global Hint Unfold wellFormedC wellFormedU wellFormedB wellFormedQ wellFormedTheory: core .
