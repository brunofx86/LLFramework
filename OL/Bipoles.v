Require Export LL.OL.StructuralClauses.

Set Implicit Arguments. 

(** ** Rules of the encoded proof system *)
Section OLInferenceRules.
Context `{OL: OLSyntax}.
  
Inductive Side := Left | Right .

(** Encoding of inference rules for units *)
Record ruleC :={
  rc_rgtBody : oo ; (* body of the right rule *)
  rc_lftBody : oo  (* body of the left rule *) } .

(** Encoding of inference rules for unary connectives *)
Record ruleU := {
  ru_rgtBody : uexp -> oo; 
  ru_lftBody : uexp ->  oo }.
  
(** Encoding of inference rules for binary connectives *)
Record ruleB := {
  rb_rgtBody : uexp -> uexp -> oo; 
  rb_lftBody : uexp -> uexp -> oo }.

(** Encoding of inference rules for quantifiers *)
Record ruleQ := {
  rq_rgtBody : (uexp -> uexp) -> oo;
  rq_lftBody :  (uexp -> uexp) -> oo }.
  
(** We assume an external definition mapping each
    connective/quantifier with a left and right rule *) 
Class OORules := {
  rulesC : cons -> ruleC ;
  rulesU : ucon -> ruleU;
  rulesB : bcon -> ruleB;
  rulesQ : qcon -> ruleQ }.
  
End OLInferenceRules.

(** Building the inference rules (bipoles)  cut-coherence and well-formedness conditions *)
Section Bipoles.
Context `{OLR: OORules}.
  
(** Building the bipoles of the rules out of the user definitions  *)
Definition makeLRuleC c :=
    ( perp ( down  ( t_cons c) )) ⊗ (rulesC c).(rc_lftBody) .
   
Definition makeRRuleC c :=
    ( perp ( up  ( t_cons c))) ⊗ (rulesC c).(rc_rgtBody) .

Definition makeLRuleU uc :=
    fun (F:uexp) => (perp ( down  ( t_ucon uc F)) ) ⊗ (rulesU uc).(ru_lftBody)  F .

Definition makeRRuleU uc :=
    fun (F:uexp) => (perp ( up  ( t_ucon uc F)) ) ⊗ (rulesU uc).(ru_rgtBody)  F.
  
Definition makeLRuleB bc :=
    fun (F G :uexp) => (perp ( down  ( t_bcon bc F G)) ) ⊗ (rulesB bc).(rb_lftBody)  F G.

Definition makeRRuleB bc :=
    fun (F G :uexp) => (perp ( up  ( t_bcon bc F G)) ) ⊗ (rulesB bc).(rb_rgtBody)  F G.
    
Definition makeLRuleQ qc :=
    fun FX => ( perp ( down  ( t_qcon qc FX))) ⊗ (rulesQ qc).(rq_lftBody) FX.

Definition makeRRuleQ qc :=
    fun FX => ( perp ( up  ( t_qcon qc FX))) ⊗ (rulesQ qc).(rq_rgtBody) FX.


Definition sideC (s:Side) :=
  match s with
  | Left => (makeLRuleC,  rc_lftBody, down)
  | Right => (makeRRuleC, rc_rgtBody, up)
end.
    
Definition sideU (s:Side) :=
  match s with
  | Left => (makeLRuleU,  ru_lftBody, down)
  | Right => (makeRRuleU, ru_rgtBody, up)
end.

Definition sideB (s:Side) :=
  match s with
  | Left => (makeLRuleB, rb_lftBody, down)
  | Right => (makeRRuleB, rb_rgtBody, up)
end.


Definition sideQ (s:Side) :=
  match s with
  | Left => (makeLRuleQ, rq_lftBody, down)
  | Right => (makeRRuleQ, rq_rgtBody, up)
end.

End Bipoles.   
(** *** Bipoles *)

(** We give a general definition of the bipoles that may appear in the specification of object logics. Left and right introduction rules are considered as well as one/two premises rules. *)
  
Global Hint Unfold makeLRuleC makeRRuleC makeLRuleU makeRRuleU makeLRuleB makeRRuleB makeLRuleQ makeRRuleQ : core.
