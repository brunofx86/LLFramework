Require Import LL.Framework.OL.SyntaxResults.
Require Export LL.Framework.SL.FLL.Specifications.Bipoles.

Section CutRule.
Context `{OL: OLSyntax}.

(** INIT and CUT rules *)
Definition RINIT (F:uexp) : oo := (perp (up  F) )  ⊗ (perp (down F) ) .
Definition RCUT  (F:uexp) : oo := (atom (up  F) )  ⊗ (atom (down F) ).
Definition RCUTI  (F:uexp) : oo := (Bang (atom (up  F)) )  ⊗ (atom (down F) ).

Hint Unfold RINIT RCUT  RCUTI: core.

Record cutrule := {
  cutC : Prop }.

 (** The cut rule applied on object level terms of a given size  *)
  Inductive CutRuleN P (n:nat) : oo -> Prop :=
  | ctn {f : cutC P}: forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN P n (RCUT F) 
  | ctni {f : ~ cutC P}: forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN P n (RCUTI F). 

  Hint Constructors CutRuleN : core.

Lemma CuteRuleNBound : forall h n B L X P ,  flln (CutRuleN P n) h B L X ->
                                             forall m, n<=m -> flls (CutRuleN P m) B L X .
Proof with sauto;solveLL.
  induction h using strongind ; intros.
  inversion H ...
  inversion H0;solveLL;
  repeat match goal with
    | [ Hs : flln (CutRuleN n) h ?B1 ?N1 ?X1 |- _] =>
      let Hs1 := fresh in
        assert (Hs1 : flls (CutRuleN P m) B1 N1 X1) by
                   (eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveLL );clear Hs
             end...
  1-15:eauto.
  LLPerm(F::B)... eauto.
  TFocus F...
  2:eauto.
  inversion H4...
  eapply ctn with (m:=m0)... 
  eapply ctni with (m:=m0)... 
Qed.

Lemma CuteRuleNBound' : forall n B L X P ,
      flls (CutRuleN P n)  B L X ->
      forall m, n<=m -> flls (CutRuleN P m) B L X .
Proof with sauto.    
  intros.
  apply seqtoSeqN in H...
  apply CuteRuleNBound with (m:=m) in H...
Qed.

(** There are no (object logic) formulas of size 0 *)
Lemma CuteRuleN0 : forall F P, ~ (CutRuleN P 0 F).
Proof with solveLL.
  intros F P Hn.
  inversion Hn...
  generalize (LengthFormula H H0); intro. 
  lia. 
  generalize (LengthFormula H H0); intro. 
  lia. 
Qed.

Definition cutR1 := {| cutC:= True |}.
Definition cutR2 := {| cutC:= False |}.

Lemma CutBaseL n F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR1 n) [] [⌈ F ⌉^;⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  TFocus (RCUT F).
  inversion H1.
  eapply ctn with (m:=n)... firstorder. 
  FLLsplit [⌈ F ⌉^]  [⌊ F ⌋^]  .
  all: solveLL.
Qed. 

Lemma CutBaseL' n F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR1 n) [] [⌊ F ⌋^;⌈ F ⌉^] (UP []).
Proof with sauto.
  intros.
  LLPerm [⌈ F ⌉^;⌊ F ⌋^].
  apply CutBaseL...
 Qed. 

Lemma CutBaseC n F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR1 n) [⌈ F ⌉^] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros...
  TFocus (RCUT F).
  inversion H1.
  eapply ctn with (m:=n)... firstorder. 
  FLLsplit (@nil oo) [⌊ F ⌋^].   
  all: solveLL.
Qed. 

Lemma CutBaseLMAX n m F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR1 (Nat.max n m)) [] [⌈ F ⌉^;⌊ F ⌋^] (UP []).
Proof with sauto.
  intros...
  eapply CuteRuleNBound' with (n:=n)...
  apply CutBaseL...
Qed. 

Lemma CutBaseLMAX' n m F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR1 (Nat.max n m)) [] [⌊ F ⌋^;⌈ F ⌉^] (UP []).
Proof with sauto.
  intros.
  LLPerm [⌈ F ⌉^;⌊ F ⌋^].
  apply CutBaseLMAX...
 Qed. 

Lemma CutBaseRMAX n m F:   
lengthUexp F m -> isOLFormula F ->
flls (CutRuleN cutR1 (Nat.max n m)) [] [⌈ F ⌉^;⌊ F ⌋^] (UP []).
Proof with sauto.
  intros...
  eapply CuteRuleNBound' with (n:=m)...
  apply CutBaseL...
Qed. 

Lemma CutBaseRMAX' n m F:   
lengthUexp F m -> isOLFormula F ->
flls (CutRuleN cutR1 (Nat.max n m)) [] [⌊ F ⌋^;⌈ F ⌉^] (UP []).
Proof with sauto.
  intros...
  LLPerm [⌈ F ⌉^;⌊ F ⌋^].
  apply CutBaseRMAX...
Qed. 

Lemma CutBaseCMAX n m F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR1 (Nat.max n m)) [⌈ F ⌉^] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros...
  eapply CuteRuleNBound' with (n:=n)...
  apply CutBaseC...

Qed. 

Lemma CutBaseCMAX' n m F:   
lengthUexp F m -> isOLFormula F ->
flls (CutRuleN cutR1 (Nat.max n m)) [⌈ F ⌉^] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros...
  eapply CuteRuleNBound' with (n:=m)...
  apply CutBaseC...

Qed. 

Lemma CutBaseI n m F:   
lengthUexp F n -> isOLFormula F ->
flls (CutRuleN cutR2 (Nat.max n m)) [⌈ F ⌉^] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  TFocus (RCUTI F).
  inversion H1.
  eapply ctni with (m:=n)...  
  FLLsplit (@nil oo) [⌊ F ⌋^].   
  all: solveLL.
Qed. 

Lemma CutBaseI' n m F:   
lengthUexp F m -> isOLFormula F ->
flls (CutRuleN cutR2 (Nat.max n m)) [⌈ F ⌉^] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  TFocus (RCUTI F).
  inversion H1.
  eapply ctni with (m:=m)...
  FLLsplit (@nil oo) [⌊ F ⌋^].   
  all: solveLL.
Qed. 

End CutRule.

Section CutCoherence. 
Context `{OLR: OORules}.
 
  (** CUT-Coherence bounded with the size of the cut *)

Definition CutCoherenceC (R: ruleC) :=
  R.(rc_rgtBody) = dual (R.(rc_lftBody))  /\  
  flls EmptyTheory [] [] (UP [dual ( R.(rc_rgtBody) ) ; dual (R.(rc_lftBody)  )]). 
  
Definition CutCoherenceU P (R: ruleU) :=
  forall F n,  
    lengthUexp F n ->
    isOLFormula F ->
    flls (CutRuleN P n) [] [] (UP [dual ( R.(ru_rgtBody) F ) ; dual (R.(ru_lftBody) F )]).
  
Definition CutCoherenceB P (R: ruleB) :=
  forall F G n m,  
    lengthUexp F n ->
    lengthUexp G m ->
    isOLFormula F -> 
    isOLFormula G->
    flls (CutRuleN P (Nat.max n m)) [] [] (UP [dual ( R.(rb_rgtBody) F G) ; dual (R.(rb_lftBody) F G)]).

  (** CUT-Coherence for quantifiers *)
Definition CutCoherenceQ P (R: ruleQ) :=
  forall FX FX' n ,  
    uniform FX -> uniform FX' ->
    ext_eq FX FX' ->
    lengthUexp (FX (Var 0%nat))  n ->
    (forall t, proper t -> isOLFormula (FX t)) -> 
    flls (CutRuleN P n) [] [] (UP [ dual(R.(rq_rgtBody) FX) ; dual(R.(rq_lftBody) FX') ]) .

  
(** CUT-Coherence for the wholse Object logic *)
Definition CutCoherence  P: Prop :=
  (forall (lab : ccon), CutCoherenceC (rulesC lab)) /\ 
  (forall (lab : ucon), CutCoherenceU P (rulesU lab)) /\
  (forall (lab : bcon), CutCoherenceB P (rulesB lab)) /\
  (forall (lab : qcon), CutCoherenceQ P (rulesQ lab)).

End CutCoherence.

Global Hint Resolve CutBaseL CutBaseL' CutBaseC CutBaseI CutBaseI': core. 

Global Hint Resolve CutBaseLMAX CutBaseLMAX'  : core. 
Global Hint Resolve CutBaseRMAX CutBaseRMAX' : core. 
Global Hint Resolve CutBaseCMAX CutBaseCMAX' : core. 
