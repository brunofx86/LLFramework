(** * Definitions for the OL Cut-Elimination Theorem  *)

(** This file contains some useful definitions and tactics for the
proof of the cut-elimination theorem of Object Logics *)


Require Export LL.Framework.OL.StructuralClauses.
Require Import Coq.Init.Nat.
Require Import LL.Framework.SL.Focused.CutElimination.
Import LL.Misc.Permutations.
Import Coq.Init.Datatypes.
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

 

(** ** Rules of the encoded proof system *)
Section OLInferenceRules.
Context `{OL: OLSyntax}.
  
Inductive Side := Left | Right .

(** Encoding of inference rules for units *)
Record ruleCte :={
  rc_rightBody : oo ; (* body of the right rule *)
  rc_leftBody : oo  (* body of the left rule *) } .

(** Encoding of inference rules for unary connectives *)
Record ruleUnary := {
  ru_rightBody : uexp -> oo; 
  ru_leftBody : uexp ->  oo }.
  
(** Encoding of inference rules for binary connectives *)
Record ruleBin := {
  rb_rightBody : uexp -> uexp -> oo; 
  rb_leftBody : uexp -> uexp -> oo }.

(** Encoding of inference rules for quantifiers *)
Record ruleQ := {
  rq_rightBody : (uexp -> uexp) -> oo;
  rq_leftBody :  (uexp -> uexp) -> oo }.
  
(** We assume an external definition mapping each
    connective/quantifier with a left and right rule *) 
Class OORules := {
  rulesCte : constants -> ruleCte ;
  rulesUnary : uconnectives -> ruleUnary;
  rulesBin : connectives -> ruleBin;
  rulesQ :   quantifiers -> ruleQ }.
  
End OLInferenceRules.

(** Building the inference rules (bipoles)  cut-coherence and well-formedness conditions *)
Section Bipoles.
Context `{OLR: OORules}.
  
(** Building the bipoles of the rules out of the user definitions  *)
Definition makeLRuleConstant (lab : constants) :=
    ( perp ( down  ( t_cons lab) )) ⊗ (rulesCte lab).(rc_leftBody) .

Definition makeRRuleConstant (lab : constants) :=
    ( perp ( up  ( t_cons lab))) ⊗ (rulesCte lab).(rc_rightBody) .

Definition makeLRuleUnary (lab : uconnectives) :=
    fun (F:uexp) => (perp ( down  ( t_ucon lab F)) ) ⊗ (rulesUnary lab).(ru_leftBody)  F .

Definition makeRRuleUnary (lab : uconnectives) :=
    fun (F:uexp) => (perp ( up  ( t_ucon lab F)) ) ⊗ (rulesUnary lab).(ru_rightBody)  F.
  
Definition makeLRuleBin (lab : connectives) :=
    fun (F G :uexp) => (perp ( down  ( t_bin lab F G)) ) ⊗ (rulesBin lab).(rb_leftBody)  F G.

Definition makeRRuleBin (lab : connectives) :=
    fun (F G :uexp) => (perp ( up  ( t_bin lab F G)) ) ⊗ (rulesBin lab).(rb_rightBody)  F G.

Definition makeLRuleQ (lab : quantifiers) :=
    fun FX => ( perp ( down  ( t_quant lab FX))) ⊗ (rulesQ lab).(rq_leftBody) FX.

Definition makeRRuleQ (lab : quantifiers) :=
    fun FX => ( perp ( up  ( t_quant lab FX))) ⊗ (rulesQ lab).(rq_rightBody) FX.
  
(** *** Bipoles *)

(** We give a general definition of the bipoles that may appear in the specification of object logics. Left and right introduction rules are considered as well as one/two premises rules. *)
  
Hint Unfold makeLRuleConstant makeRRuleConstant makeLRuleUnary makeRRuleUnary makeLRuleBin makeRRuleBin makeLRuleQ makeRRuleQ : core.

(** This is the FLL logical theory including the right and left rules for the connectives and the quantifiers *)

Inductive buildTheory  : oo ->  Prop :=
  | bcteR : forall C, isOLFormula (t_cons C) -> buildTheory (makeRRuleConstant C)
  | bcteL : forall C, isOLFormula (t_cons C) -> buildTheory (makeLRuleConstant C) 
  | buconnR : forall C F, isOLFormula ( t_ucon C F) -> buildTheory  (makeRRuleUnary C F)
  | buconnL : forall C F, isOLFormula ( t_ucon C F) -> buildTheory  (makeLRuleUnary C F)
  | bconnR : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (makeRRuleBin C F G)
  | bconnL : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (makeLRuleBin C F G)
  | bQconnR : forall C FX, isOLFormula  (t_quant C FX)  -> buildTheory  (makeRRuleQ C FX)
  | bQconnL : forall C FX, isOLFormula  (t_quant C FX)  -> buildTheory  (makeLRuleQ C FX) .

Section Bipoles.
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
  (connective: uexp) 
  (Rule:  oo)
  (predicate: uexp -> atm) : Prop :=
  forall n, seqN theory n Gamma Delta ( DW Rule) -> False .

(** Case of 0 premise *)
Definition GenericBiPoleAxiom
  (connective: uexp) 
  (Rule:  oo)
  (RBody: oo) 
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
    ( (* case the atom is taken from the linear context *)
      (exists D1,
       Permutation Delta ( atom (predicate connective ) :: D1) /\
       seq theory  Gamma D1 (DW RBody) /\
       forall Delta1 Gamma1 (theory' : oo -> Prop),
       (theory'  (Rule)) ->
       seq theory' Gamma1  ( atom (predicate ((connective)) ) :: Delta1) (UP []))
     \/
    ( (* case the atom is taken from the classical context *)
       In (atom ( predicate connective )) Gamma /\
       seqN theory 0  Gamma Delta (UP [RBody] ) /\  
       forall Delta1 Gamma1 (theory' : oo -> Prop),
       (theory'  Rule) ->
       In ( atom (predicate (connective) )) Gamma1 ->
       seq theory' Gamma1 Delta1 (UP []))).
 
(** Case of 1 premise *)
Definition GenericBiPole1P
  (connective: uexp) 
  (Rule:  oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
  exists D1' B1' n' n'',    
  posAtomFormulaL D1' /\ 
  posAtomFormulaL B1' /\
    (
      ( exists D1,
        Permutation Delta ((atom (predicate connective))::D1) /\ 
        seq theory  Gamma D1 ( DW RBody) /\
        seqN theory n' (Gamma ++ B1') (D1 ++ D1') ( UP [])  /\
        n'' > 0 /\
        n = plus n' n'' /\
        forall Delta1 Gamma1 (theory' : oo -> Prop),
        (theory'  (Rule)) ->
        seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (UP []) -> 
         seq theory' Gamma1 ( (atom (predicate ((connective)) )) :: Delta1) (UP []))
     \/
      ( In (atom (predicate (connective))) Gamma /\
        seq theory  Gamma Delta (DW RBody) /\
        seqN theory n' (Gamma ++ B1') (Delta ++ D1') ( UP [])  /\
        n'' > 0 /\
        n = plus n'  n'' /\
        (forall Delta1 Gamma1 (theory' : oo -> Prop),
          seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (UP []) ->
          seq theory' Gamma1 Delta1 (DW RBody))) ).
    
   
(** Case of 2 premises (multiplicative case) *)
Definition GenericBiPole2PM
  (connective: uexp)
  (Rule: oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta ( DW Rule) ->
  isOLFormula connective ->
  exists D1 D2 D1' D2' B1' B2'  n' n'',
  posAtomFormulaL D1' /\
  posAtomFormulaL D2' /\
  posAtomFormulaL B1' /\
  posAtomFormulaL B2' /\
  ( 
    ( Permutation Delta (atom ((predicate connective )) :: (D1 ++ D2)) /\
       seq theory  Gamma (D1 ++ D2) (DW RBody) /\
       seqN theory n' (Gamma ++ B1') (D1 ++ D1') (UP []) /\
       seqN theory n' (Gamma ++ B2') (D2 ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta1 Delta2 Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (UP []) ->
       seq theory' (Gamma1 ++ B2') (Delta2 ++ D2') (UP []) ->
       seq theory' Gamma1 (atom ((predicate (connective))) :: Delta1 ++ Delta2) (UP []))
   \/
       ( In (atom (predicate (connective) )) Gamma  /\
          Permutation Delta (D1 ++ D2) /\
          seq theory  Gamma (D1 ++ D2) (DW RBody) /\
          seqN theory n' (Gamma ++ B1') (D1 ++ D1') (UP []) /\
          seqN theory n' (Gamma ++ B2') (D2 ++ D2') (UP []) /\
          n'' > 0 /\
          n = plus n' n'' /\
          forall Delta1 Delta2 Gamma1 (theory' : oo -> Prop),
          seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (UP []) ->
          seq theory' (Gamma1 ++ B2') (Delta2 ++ D2') (UP []) ->
          seq theory' Gamma1 (Delta1 ++ Delta2) (DW RBody))).

(** Case of 2 premises (additive case) *)
Definition GenericBiPole2PA
  (connective: uexp)
  (Rule: oo)
  (RBody: oo)
  (predicate: uexp -> atm) : Prop :=
  forall n,
  seqN theory n Gamma Delta (DW Rule) ->
  isOLFormula connective ->
  exists D12 D1' D2' B1' B2'  n' n'',
  posAtomFormulaL D1' /\
  posAtomFormulaL D2' /\
  posAtomFormulaL B1' /\
  posAtomFormulaL B2' /\
  ( 
     ( Permutation Delta (atom ((predicate connective )) :: D12) /\
       seq theory  Gamma D12 (DW RBody) /\
       seqN theory n' (Gamma ++ B1') (D12 ++ D1') (UP []) /\
       seqN theory n' (Gamma ++ B2') (D12 ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       theory' Rule ->
       seq theory' (Gamma1 ++ B1') (Delta12 ++ D1') (UP []) ->
       seq theory' (Gamma1 ++ B2') (Delta12 ++ D2') (UP []) ->
       seq theory' Gamma1 ( atom ((predicate ( connective) )) :: Delta12) (UP [])
     )
   \/
     ( In (atom (predicate (connective))) Gamma /\
       Permutation Delta D12 /\
       seq theory  Gamma D12 (DW RBody) /\
       seqN theory n' (Gamma ++ B1') (D12 ++ D1') (UP []) /\
       seqN theory n' (Gamma ++ B2') (D12 ++ D2') (UP []) /\
       n'' > 0 /\
       n = plus n' n'' /\
       forall Delta12 Gamma1 (theory' : oo -> Prop),
       seq theory' (Gamma1 ++ B1') (Delta12 ++ D1') (UP []) ->
       seq theory' (Gamma1 ++ B2') (Delta12 ++ D2') (UP []) ->
       seq theory' Gamma1 Delta12 (DW RBody))).

Inductive BipoleEnum :=  BOneP | BTwoPM | BTwoPA .
Inductive BipoleEnumCte :=  BCFail | BCAxiom | BCOneP .

Definition sideConstant (s:Side) :=
  match s with
  | Left => (makeLRuleConstant,  rc_leftBody, down)
  | Right => (makeRRuleConstant, rc_rightBody, up)
end.
    
Definition sideUnary (s:Side) :=
  match s with
  | Left => (makeLRuleUnary,  ru_leftBody, down)
  | Right => (makeRRuleUnary, ru_rightBody, up)
end.

Definition sideBinary (s:Side) :=
  match s with
  | Left => (makeLRuleBin, rb_leftBody, down)
  | Right => (makeRRuleBin, rb_rightBody, up)
end.

Definition sideQuantifier (s:Side) :=
  match s with
  | Left => (makeLRuleQ, rq_leftBody, down)
  | Right => (makeRRuleQ, rq_rightBody, up)
end.

Definition BiPoleCte (lab: constants) (s:Side) (t : BipoleEnumCte): Prop :=
  match (sideConstant s) with
  | (rule, body, pred) =>
    match t with
      | BCFail => GenericBiPoleFail (t_cons lab) (rule lab)  pred
      | BCAxiom => GenericBiPoleAxiom  (t_cons lab) (rule lab) ( (rulesCte lab).(body) )  pred
      | BCOneP => GenericBiPole1P (t_cons lab) (rule lab) ( (rulesCte lab).(body) ) pred
    end
 end.
    
Definition BiPoleUnary (lab: uconnectives) (s:Side) (t : BipoleEnum): Prop :=
  match (sideUnary s) with
  | (rule, body, pred) =>
     match t with
     | BOneP => forall Fo1, GenericBiPole1P (t_ucon lab Fo1) (rule lab Fo1) ( (rulesUnary lab).(body) Fo1) pred
     | BTwoPM => forall Fo1, GenericBiPole2PM (t_ucon lab Fo1) (rule lab Fo1) ( (rulesUnary lab).(body) Fo1) pred
     | BTwoPA => forall Fo1, GenericBiPole2PA (t_ucon lab Fo1) (rule lab Fo1) ( (rulesUnary lab).(body) Fo1) pred
     end
end.
    
    
Definition BiPoleBinary (lab: connectives) (s:Side) (t : BipoleEnum): Prop :=
  match (sideBinary s) with
  | (rule, body, pred) =>
    match t with
    | BOneP => forall Fo1 Go1, GenericBiPole1P (t_bin lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesBin lab).(body) Fo1 Go1) pred
    | BTwoPM => forall Fo1 Go1, GenericBiPole2PM (t_bin lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesBin lab).(body) Fo1 Go1) pred
    | BTwoPA => forall Fo1 Go1, GenericBiPole2PA (t_bin lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesBin lab).(body) Fo1 Go1) pred
    end
end.


Definition BiPoleQuantifier (lab: quantifiers) (s:Side) (t : BipoleEnum): Prop :=
  match (sideQuantifier s) with
  | (rule, body, pred) =>
    match t with
    | BOneP => forall FX, uniform FX /\ GenericBiPole1P (t_quant lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    | BTwoPM => forall FX, uniform FX /\ GenericBiPole2PM (t_quant lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    | BTwoPA => forall FX, uniform FX /\ GenericBiPole2PA (t_quant lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
    end
end.
 
End Bipoles.

Hint Unfold BiPoleCte BiPoleUnary BiPoleBinary BiPoleQuantifier : core .
        
(** INIT and CUT rules *)
Definition RINIT (F:uexp) : oo := (perp (up  F) )  ⊗ (perp (down F) ) .
Definition RCUT  (F:uexp) : oo := (atom (up  F) )  ⊗ (atom (down F) ).

(*   (** Allowing contraction and weakening on the left side of the sequent *)
  Definition POS F := ((perp (down F)) ⊗ ? atom (down F)).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG F := ((perp (up F)) ⊗ ? atom (up F)).
 *) 
  
  Hint Unfold RINIT RCUT : core.

 (** The cut rule applied on object level terms of a given size  *)
  Inductive CutRuleN (n:nat) : oo -> Prop :=
  | ctn : forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN n (RCUT F). 
  Hint Constructors CutRuleN : core.

Lemma CuteRuleNBound : forall h n B L X ,  seqN (CutRuleN n) h B L X ->
                                             forall m, n<=m -> seq (CutRuleN m) B L X .
Proof with sauto;solveLL.
  induction h using strongind ; intros.
  inversion H ...
  inversion H0;solveLL;
  repeat match goal with
    | [ Hs : seqN (CutRuleN n) h ?B1 ?N1 ?X1 |- _] =>
      let Hs1 := fresh in
        assert (Hs1 : seq (CutRuleN m) B1 N1 X1) by
                   (eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveLL );clear Hs
             end...
  1-15:eauto.
  TFocus F...
  2:eauto.
  inversion H4...
  eapply ctn with (m:=m0)... 
Qed.

Lemma CuteRuleNBound' : forall n B L X ,
      seq (CutRuleN n)  B L X ->
      forall m, n<=m -> seq (CutRuleN m) B L X .
Proof with sauto.    
  intros.
  apply FLLNtoFLLS in H...
  apply CuteRuleNBound with (m:=m) in H...
Qed.

(** There are no (object logic) formulas of size 0 *)
Lemma CuteRuleN0 : forall F, ~ (CutRuleN 0 F).
Proof with solveLL.
  intros F Hn.
  inversion Hn...
  generalize (LengthFormula H H0); intro. lia.
Qed.
  
  
  (** CUT-Coherence bounded with the size of the cut *)

Definition CutCoherenceCte (R: ruleCte) :=
  R.(rc_rightBody) = dual (R.(rc_leftBody))  /\  
  seq EmptyTheory [] [] (UP [dual ( R.(rc_rightBody) ) ; dual (R.(rc_leftBody)  )]). 
  
Definition CutCoherenceUnary (R: ruleUnary) :=
  forall F n,  
    lengthUexp F n ->
    isOLFormula F ->
    seq (CutRuleN n) [] [] (UP [dual ( R.(ru_rightBody) F ) ; dual (R.(ru_leftBody) F )]).
  
Definition CutCoherenceBin (R: ruleBin) :=
  forall F G n m,  
    lengthUexp F n ->
    lengthUexp G m ->
    isOLFormula F -> 
    isOLFormula G->
    seq (CutRuleN (max n m)) [] [] (UP [dual ( R.(rb_rightBody) F G) ; dual (R.(rb_leftBody) F G)]).

  (** CUT-Coherence for quantifiers *)
Definition CutCoherenceQ (R: ruleQ) :=
  forall FX FX' n ,  
    uniform FX -> uniform FX' ->
    ext_eq FX FX' ->
    lengthUexp (FX (Var 0%nat))  n ->
    (forall t, proper t -> isOLFormula (FX t)) -> 
    seq (CutRuleN n) [] [] (UP [ dual(R.(rq_rightBody) FX) ; dual(R.(rq_leftBody) FX') ]) .

  
(** CUT-Coherence for the wholse Object logic *)
Definition CutCoherence  : Prop :=
  (forall (lab : constants), CutCoherenceCte (rulesCte lab)) /\ 
  (forall (lab : uconnectives), CutCoherenceUnary (rulesUnary lab)) /\
  (forall (lab : connectives), CutCoherenceBin (rulesBin lab)) /\
  (forall (lab : quantifiers), CutCoherenceQ (rulesQ lab)).
  

  (** A well-formed theory consists of rules that are cut-coherent
    and each rule is either a one-premise or a two-premises rule that
    satisfy the predicates [BiPole] *)

Definition wellFormedCte :Prop :=
  forall Theory Gamma Delta (lab: constants) (s:Side),
  exists (t: BipoleEnumCte), BiPoleCte Theory Gamma Delta lab s t.
    
Definition wellFormedUnary: Prop :=
  forall Theory Gamma Delta (lab: uconnectives) (s:Side),
  BiPoleUnary Theory Gamma Delta lab s BOneP.

Definition wellFormedBinary: Prop :=
  forall Theory Gamma Delta (lab: connectives) (s:Side),
  exists (t : BipoleEnum),  BiPoleBinary Theory Gamma Delta lab s t.

(* We assume that quantifiers are encoded with one premise bipoles *)
Definition wellFormedQuantifier: Prop :=
  forall Theory Gamma Delta (lab: quantifiers) (s:Side),
  BiPoleQuantifier Theory Gamma Delta lab s BOneP.

Definition wellFormedTheory  : Prop :=
  wellFormedCte /\   
  wellFormedUnary /\ 
  wellFormedBinary /\ 
  wellFormedQuantifier .
 
Definition wellTheory : Prop := CutCoherence  /\ wellFormedTheory.

Hint Unfold CutCoherenceBin CutCoherenceQ  CutCoherence wellFormedCte wellFormedUnary wellFormedBinary wellFormedQuantifier wellTheory  : core .
  
Record structrules := mk_srules {
  pos : bool ;
  neg : bool  }.

(** A theory with only with the object logic rules *)
Inductive OLTheory  P : oo -> Prop :=
  | ooth_rules : forall OO, buildTheory OO ->  OLTheory P OO
  | ooth_init : forall OO, isOLFormula OO -> OLTheory P (RINIT OO) 
  | ooth_strpos {f : pos P = true}: forall OO, isOLFormula OO -> OLTheory P (POS OO) 
  | ooth_strneg {f : neg P = true}: forall OO, isOLFormula OO -> OLTheory P (NEG OO) .
  
Definition PN := (mk_srules true true).
Definition PnN := (mk_srules true false).
Definition nPnN := (mk_srules false false).
  
  (** A theory including cuts of size [n] *)
Inductive OLTheoryCut P (n:nat) : oo -> Prop :=
  | oothc_theory : forall OO, buildTheory OO ->  OLTheoryCut P n OO
  | oothc_init : forall OO, isOLFormula OO -> OLTheoryCut P n (RINIT OO) 
  | oothc_cutn : forall OO, CutRuleN n OO -> OLTheoryCut P n OO
  | oothc_strpos {f : pos P = true}: forall OO, isOLFormula OO -> OLTheoryCut P n (POS OO) 
  | oothc_strneg {f : neg P = true}: forall OO,isOLFormula OO ->  OLTheoryCut P n (NEG OO) .
  
  
Hint Constructors  OLTheoryCut OLTheory   : core.

    
(** Some easy equivalences on the  above theories *)
Lemma OOTheryCut0 {P}: forall F, OLTheory P F <-> (OLTheoryCut P 0) F.
Proof.  
  intros.
  split;intro H ;inversion H;subst;auto.
  inversion H0.
  assert (m =  0%nat) by lia;subst.
  generalize (LengthFormula H1 H2);intro. lia.
Qed.

Lemma TheoryEmb1 {P}: forall n F  , OLTheory P F -> (OLTheoryCut P n) F.
Proof. 
  intros.
  inversion H;subst; solve[constructor;auto].
Qed.

Lemma TheoryEmb2 {P}: forall n F  , ((CutRuleN n) F) -> (OLTheoryCut P n) F.
Proof.  
  intros.
  inversion H;subst.
  apply oothc_cutn;auto.
Qed.  
  
End Bipoles.
