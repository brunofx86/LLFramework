Require Import LL.Framework.OL.SyntaxResults.
Require Export LL.Framework.SL.MMLL.Specifications.Bipoles.

Section CutRule.
Context `{OL: OLSyntax}.
Context `{SI: SigMMLL}.

(** INIT and CUT rules *)
Definition RINIT (F:uexp) : oo := (perp (up  F) )  ⊗ (perp (down F) ) .
Definition RCUT  (F:uexp) : oo := (atom (up  F) )  ⊗ (atom (down F) ).
Definition RCUTI  a (F:uexp) : oo := (Bang a (atom (up  F)) )  ⊗ (atom (down F) ).

Hint Unfold RINIT RCUT  RCUTI: core.

Record cutrule := {
  cutC : Prop }.

 (** The cut rule applied on object level terms of a given size  *)
  Inductive CutRuleN P (n:nat) : oo -> Prop :=
  | ctn {f : cutC P}: forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN P n (RCUT F) 
  | ctni {f : ~ cutC P}: forall a  (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN P n (RCUTI a F). 

  Hint Constructors CutRuleN : core.

Lemma CuteRuleNBound : forall h n B L X P ,  MLLN (CutRuleN P n) h B L X ->
                                             forall m, n<=m -> MLLS (CutRuleN P m) B L X .
Proof with sauto;try solveLL.
  induction h using strongind ; intros.
  inversion H ...
  inversion H0;solveLL;
  repeat match goal with
    | [ Hs : MLLN (CutRuleN n) h ?B1 ?N1 ?X1 |- _] =>
      let Hs1 := fresh in
        assert (Hs1 : MLLS (CutRuleN P m) B1 N1 X1) by
                   (eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveLL );clear Hs
             end...
  1-15:eauto. 
  2-3:eauto.
  
  eapply tri_dec3' with  (F:=F). 
  2:eauto.
  inversion H3...
  eapply ctn with (m:=m0)... 
  eapply ctni with (m:=m0)...
  eauto.
  finishExponential.
  eapply tri_bang'... 
  eapply GenK4Rel' with (C4:=CK4) (CK:=CK) (CN:=CN)...
  eapply H. 2: exact H12. lia.
  auto.
  finishExponential.
  eapply tri_bangD' with (i:=i)... 
  eapply GenK4Rel' with (C4:=CK4) (CK:=CK) (CN:=CN)...
  intro... solveSignature1. 
  eapply H. 2: exact H12. lia.
  auto.
Qed.

Lemma CuteRuleNBound' : forall n B L X P ,
      MLLS (CutRuleN P n)  B L X ->
      forall m, n<=m -> MLLS (CutRuleN P m) B L X .
Proof with sauto.    
  intros.
   apply MLLStoSeqN in H...
  apply CuteRuleNBound with (m:=m) in H...
Qed.
 
(** There are no (object logic) formulas of size 0 *)
Lemma CuteRuleN0 : forall F P, ~ (CutRuleN P 0 F).
Proof with try solveLL.
  intros F P Hn.
  inversion Hn...
  generalize (LengthFormula H H0); intro. 
  lia. 
  generalize (LengthFormula H H0); intro. 
  lia. 
Qed.

Definition cutR1 := {| cutC:= True |}.
Definition cutR2 := {| cutC:= False |}.

Lemma CutBaseL n m F:   
lengthUexp F n -> isOLFormula F ->
MLLS (CutRuleN cutR1 (Nat.max n m)) [] [⌈ F ⌉^;⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  LLtheory (RCUT F).
  2: inversion H1.
  eapply ctn with (m:=n)... firstorder. 
  LLtensor [⌈ F ⌉^]  [⌊ F ⌋^]  .
  all: solveLL.
Qed. 

Lemma CutBaseL' n m F:   
lengthUexp F n -> isOLFormula F ->
MLLS (CutRuleN cutR1 (Nat.max n m)) [] [⌊ F ⌋^;⌈ F ⌉^] (UP []).
Proof with sauto.
  intros.
  LLPerm [⌈ F ⌉^;⌊ F ⌋^].
  apply CutBaseL...
 Qed. 

Lemma CutBaseR n m F:   
lengthUexp F m -> isOLFormula F ->
MLLS (CutRuleN cutR1 (Nat.max n m)) [] [⌈ F ⌉^;⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  LLtheory (RCUT F).
  2: inversion H1.
  eapply ctn with (m:=m)... firstorder. 
  LLtensor [⌈ F ⌉^]  [⌊ F ⌋^]  .
  all: solveLL.
Qed. 

Lemma CutBaseR' n m F:   
lengthUexp F m -> isOLFormula F ->
MLLS (CutRuleN cutR1 (Nat.max n m)) [] [⌊ F ⌋^;⌈ F ⌉^] (UP []).
Proof with sauto.
  intros...
  LLPerm [⌈ F ⌉^;⌊ F ⌋^].
  apply CutBaseR...
Qed. 

Lemma CutBaseC n m a F:   u a = true -> mt a  =  true ->
lengthUexp F n -> isOLFormula F ->
MLLS (CutRuleN cutR1 (Nat.max n m)) [(a,⌈ F ⌉^)] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  LLtheory (RCUT F).
  2: inversion H3.
  eapply ctn with (m:=n)... firstorder. 
  LLtensor (@nil oo) [⌊ F ⌋^].   
  all: try solveLL.
  LLfocus2 a (⌈ F ⌉^).
Qed. 

Lemma CutBaseC' n m a F:   
lengthUexp F m -> isOLFormula F -> u a = true -> mt a  =  true ->
MLLS (CutRuleN cutR1 (Nat.max n m)) [(a,⌈ F ⌉^)] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  LLtheory (RCUT F).
  2:inversion H3.
  eapply ctn with (m:=m)... firstorder. 
  LLtensor (@nil oo) [⌊ F ⌋^].   
  all: try solveLL.
  LLfocus2 a (⌈ F ⌉^).
Qed. 


(* Lemma CutBaseI n m a F:   
lengthUexp F n -> isOLFormula F -> u a = true -> mt a  =  true ->
MLLS (CutRuleN cutR2 (Nat.max n m)) [(a,⌈ F ⌉^)] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  LLtheory (RCUTI a F).
  2: inversion H3.
  eapply ctni with (m:=n)...  
  LLtensor (@nil oo) [⌊ F ⌋^].   
  all: try solveLL.
  LLfocus2 a (⌈ F ⌉^).
Qed. 

Lemma CutBaseI' n m F:   
lengthUexp F m -> isOLFormula F ->
MLLS (CutRuleN cutR2 (Nat.max n m)) [⌈ F ⌉^] [⌊ F ⌋^] (UP []).
Proof with sauto.
  intros... 
  LLtheory (RCUTI F).
  inversion H1.
  eapply ctni with (m:=m)...
  LLtensor (@nil oo) [⌊ F ⌋^].   
  all: solveLL.
Qed. 
 *)
End CutRule.

Section CutCoherence. 
Context `{OLR: OORules}.
 
  (** CUT-Coherence bounded with the size of the cut *)

Definition CutCoherenceCte (R: ruleC) :=
  R.(rc_rgtBody) = dual (R.(rc_lftBody))  /\  
  MLLS EmptyTheory [] [] (UP [dual ( R.(rc_rgtBody) ) ; dual (R.(rc_lftBody)  )]). 
  
Definition CutCoherenceUnary P (R: ruleU) :=
  forall F n,  
    lengthUexp F n ->
    isOLFormula F ->
    MLLS (CutRuleN P n) [] [] (UP [dual ( R.(ru_rgtBody) F ) ; dual (R.(ru_lftBody) F )]).
  
Definition CutCoherenceBin P (R: ruleB) :=
  forall F G n m,  
    lengthUexp F n ->
    lengthUexp G m ->
    isOLFormula F -> 
    isOLFormula G->
    MLLS (CutRuleN P (Nat.max n m)) [] [] (UP [dual ( R.(rb_rgtBody) F G) ; dual (R.(rb_lftBody) F G)]).

  (** CUT-Coherence for quantifiers *)
Definition CutCoherenceQ P (R: ruleQ) :=
  forall FX FX' n ,  
    uniform FX -> uniform FX' ->
    ext_eq FX FX' ->
    lengthUexp (FX (Var 0%nat))  n ->
    (forall t, proper t -> isOLFormula (FX t)) -> 
    MLLS (CutRuleN P n) [] [] (UP [ dual(R.(rq_rgtBody) FX) ; dual(R.(rq_lftBody) FX') ]) .

  
(** CUT-Coherence for the wholse Object logic *)
Definition CutCoherence  P: Prop :=
  (forall (lab : ccon), CutCoherenceCte (rulesC lab)) /\ 
  (forall (lab : ucon), CutCoherenceUnary P (rulesU lab)) /\
  (forall (lab : bcon), CutCoherenceBin P (rulesB lab)) /\
  (forall (lab : qcon), CutCoherenceQ P (rulesQ lab)).

End CutCoherence.