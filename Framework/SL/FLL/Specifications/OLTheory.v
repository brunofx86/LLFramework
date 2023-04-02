(** * Definitions for the OL Cut-Elimination Theorem  *)

(** This file contains some useful definitions and tactics for the
proof of the cut-elimination theorem of Object Logics *)

Require Import LL.Framework.OL.SyntaxResults.
Require Export LL.Framework.SL.FLL.Specifications.CutCoherence.
Set Implicit Arguments.

Section OLTheory.
Context `{OLR: OORules}.

Inductive buildTheory  : oo ->  Prop :=
  | bcteR : forall C, isOLFormula (t_ccon C) -> buildTheory (makeRRuleC C)
  | bcteL : forall C, isOLFormula (t_ccon C) -> buildTheory (makeLRuleC C) 
  | buconnR : forall C F, isOLFormula ( t_ucon C F) -> buildTheory  (makeRRuleU C F)
  | buconnL : forall C F, isOLFormula ( t_ucon C F) -> buildTheory  (makeLRuleU C F)
  | bconnR : forall C F G, isOLFormula ( t_bcon C F G) -> buildTheory  (makeRRuleB C F G)
  | bconnL : forall C F G, isOLFormula ( t_bcon C F G) -> buildTheory  (makeLRuleB C F G)
  | bQconnR : forall C FX, uniform FX -> isOLFormula  (t_qcon C FX)  -> buildTheory  (makeRRuleQ C FX)
  | bQconnL : forall C FX, uniform FX -> isOLFormula  (t_qcon C FX)  -> buildTheory  (makeLRuleQ C FX) .

Record structrules := {
  pos : Prop ;
  neg : Prop  }.

(** A theory with only with the object logic rules *)
Inductive OLTheory  P : oo -> Prop :=
  | ooth_rules : forall OO, buildTheory OO ->  OLTheory P OO
  | ooth_init : forall OO, isOLFormula OO -> OLTheory P (RINIT OO) 
  | ooth_strpos {f : pos P}: forall OO, isOLFormula OO -> OLTheory P (POS OO) 
  | ooth_strneg {f : neg P}: forall OO, isOLFormula OO -> OLTheory P (NEG OO) .
  
Definition PN := {| pos:= True ; neg:= True|}.
Definition PnN :=  {| pos:= True ; neg:= False |}.
Definition nPnN := {| pos:= False ; neg:= False|}.
  
  (** A theory including cuts of size [n] *)
Inductive OLTheoryCut P (n:nat) : oo -> Prop :=
  | oothc_theory : forall OO, OLTheory  P  OO ->  OLTheoryCut P n OO
  | oothc_cutn : forall OO, CutRuleN cutR1 n OO -> OLTheoryCut P n OO.

Inductive OLTheoryCutI P (n:nat) : oo -> Prop :=
  | oothc_theoryi : forall OO, OLTheory  P  OO ->  OLTheoryCutI P n OO
  | oothc_cutni : forall OO, CutRuleN cutR2 n OO -> OLTheoryCutI P n OO.

Hint Constructors  OLTheoryCut OLTheoryCutI OLTheory   : core.
    
(** Some easy equivalences on the  above theories *)
Lemma OOTheryCut0 {P}: forall F, OLTheory P F <-> (OLTheoryCut P 0) F.
Proof.  
  intros.
  split;intro H ;inversion H;subst;auto.
  inversion H0.
  all: assert (m =  0%nat) by lia;subst.
  generalize (LengthFormula H1 H2);intro. lia.
generalize (LengthFormula H1 H2);intro. lia.
Qed.

Lemma OOTheryCutI0 {P}: forall F, OLTheory P F <-> (OLTheoryCutI P 0) F.
Proof.  
  intros.
  split;intro H ;inversion H;subst;auto.
  inversion H0.
  all: assert (m =  0%nat) by lia;subst.
  generalize (LengthFormula H1 H2);intro. lia.
generalize (LengthFormula H1 H2);intro. lia.
Qed.

Lemma TheoryEmb1 {P}: forall n F  , OLTheory P F -> (OLTheoryCut P n) F /\ (OLTheoryCutI P n) F.
Proof. 
  intros. 
  split.
  inversion H;subst; solve[constructor;auto].
inversion H;subst; solve[constructor;auto].
Qed.


Lemma TheoryEmb2 {P}: forall n F  , ((CutRuleN cutR1 n) F) -> (OLTheoryCut P n) F.
Proof.  
  intros.
  inversion H;subst;sauto. 
Qed.  

Lemma TheoryEmb2' {P}: forall n F  , ((CutRuleN cutR2 n) F) -> (OLTheoryCutI P n) F.
Proof.  
  intros.
  inversion H;subst;sauto. 
Qed.  

Lemma TheoryEmb3 {P}: forall m n F , n<=m -> (OLTheoryCut P n) F -> (OLTheoryCut P m) F.
Proof with sauto. 
  intros.
  inversion H0;subst; try solve[constructor;auto].
  inversion H1...
  apply oothc_cutn;auto.
  apply ctn with (m:=m0);auto.
  lia.
  firstorder.
Qed.

Lemma TheoryEmb3' {P}: forall m n F , n<=m -> (OLTheoryCutI P n) F -> (OLTheoryCutI P m) F.
Proof with sauto. 
  intros.
  inversion H0;subst; try solve[constructor;auto].
  inversion H1... firstorder.
  apply oothc_cutni;auto.
  apply ctni with (m:=m0);auto.
lia.
Qed.

Lemma weakOLTheory n m B L X P: flln (OLTheory P) m B L X -> flls (OLTheoryCut P n) B L X.
Proof.
   intros.
   apply WeakTheory with (theory := OLTheory P). auto using TheoryEmb1.
   HProof.
Qed.



End OLTheory.

Global Hint Resolve weakOLTheory: core.
Global Hint Constructors  buildTheory OLTheoryCut OLTheoryCutI OLTheory : core.
