(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export LL.Misc.Hybrid.
Require Export LL.Framework.SL.FLL.Specifications.StructuralClauses. 
Require Export LL.Framework.SL.FLL.Specifications.Requirement2.
Require Export LL.Framework.SL.FLL.Specifications.OLTheory.


Require Import Coq.Init.Nat.
Require Import LL.Framework.OL.SyntaxResults.
Require Import LL.Framework.SL.FLL.CutElimination.
Import LL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(** ** Cut Elimination Procedure *)
Section CutElimination .
  Context `{OLR: OORules}.

  (** As a general hypothesis, we assume that the Object logic is cut-coherent *)
  Hypothesis LTWell1 : wellFormedTheory'.
(*   Hypothesis LTWell2: wellFormedTheoryI. *)
  Hypothesis LTCutCoherence: CutCoherence cutR2.
   
  Definition ctWellFormed := proj1 LTWell1.
  Definition unWellFormed := proj1 (proj2 LTWell1).
  Definition biWellFormed := proj1 (proj2 (proj2 LTWell1)).
  Definition quWellFormed := proj2 (proj2 (proj2 LTWell1)).

  Definition ctCutCo := proj1 LTCutCoherence.
  Definition unCutCo := proj1 (proj2 LTCutCoherence).
  Definition biCutCo := proj1 (proj2 (proj2 LTCutCoherence)).
  Definition quCutCo := proj2 (proj2 (proj2 LTCutCoherence)).
  
  (** Extracting the needed facts given that all the OL constants are well-defined *)
   Ltac wellConstant HSeq :=
    let HS := type of HSeq in
    match HS with
    | flln ?Rules ?n ?Gamma ?M (DW (?Side ?C)) =>
      let Side' :=
          match Side with 
          makeRRuleC => Right
           | makeLRuleC => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (ctWellFormed Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ];
          destruct bpEnum;[ apply LTWell' in HSeq; contradiction (* fail case *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell' (* axiom *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell'] (* one premise *)
    end.
    
   Ltac wellUnary HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (flln ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with 
          makeRRuleU => Right 
          | makeLRuleU => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize  (unWellFormed Rules Gamma M C Side' );
        intro LTWell';generalize (LTWell' _ _ HSeq);intro;clear LTWell'
    end.
 
  (** Extracting well-formed conditions for binary predicates *)
  Ltac wellBinary HSeq :=
    let HS := type of HSeq in
    match HS with
    | (flln ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F ?G))) =>
      let Side' :=
          match Side with makeRRuleB => Right | makeLRuleB => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (biWellFormed Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ]; 
        destruct bpEnum;generalize (LTWell' _ _ _ HSeq);intro;clear LTWell'
    end.

  Ltac wellQuantifier HSeq :=
    let HS := type of HSeq in
    match HS with
    | (flln ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with makeRRuleQ => Right | makeLRuleQ => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
         let HUniform := fresh "HUniform" in
        generalize  (quWellFormed Rules Gamma M C Side' F); intro LTWell';
      destruct LTWell' as [HUniform LTWell'];generalize (LTWell'  _ HSeq); intro; clear LTWell'
    end.

(** Inductive hypothesis in the theorem [OLCutElimStep]. This is
  useful to simplify the theorems below *)
  Definition OOCut n' h : Prop :=
    forall n h1 h2 FCut M N Gamma,
      h1 + h2 < h ->
          n' <= n ->
            isOLFormula FCut ->
            lengthUexp FCut n' ->
            IsPositiveAtomBFormulaL M ->
            isOLFormulaL Gamma ->
            isOLFormulaL N ->
            flln (OLTheory PnN) h1 (LEncode Gamma) (atom (up FCut)::LEncode N) (UP [] ) ->
            flln (OLTheory PnN) h2 (atom (down FCut)::LEncode Gamma) M (UP []) -> 
            flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
                  
 Ltac applyOOCut := 
  match goal with
  | [ H: OOCut _ _ |- 
         flln ?th ?x ?BX (?FF::?N) (UP []) -> 
         flln ?th ?y (?GG::?BX) ?M (UP [])-> 
         flls ?thc ?BX (?M++?N) (UP []) ] => eapply H; try OLSolve
  | _ => idtac end.
  
Ltac cutOL P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | flln ?th ?h1 ?B (atom (up ?FC) :: ?N) (UP []) => 
          match tP2 with 
          | flln ?th ?h2 (atom (down ?FC) :: ?B) ?M (UP []) =>  
           match goal with
           | [ H: OOCut ?n' _, Hn: ?n' <= ?n  |- _ ] =>   
                 assert(H': tP1 -> tP2 -> flls (OLTheoryCutI PnN (pred n)) B (M++ N) (UP []));applyOOCut
           end
           | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.
   
Ltac SubCases :=
repeat 
match goal with
  | H: Permutation (_::_) (_::_) |- _ => checkPermutationCases H
  | H: Permutation (_ ++ _) (_ :: _) |- _ => checkPermutationCases H
  | H: Permutation (_ :: _) (_ ++ _) |- _ => checkPermutationCases H
  | H:  (⌈ ?F ⌉) =  (⌈ ?G ⌉) |- _ => inversion H;sauto
  | H:  (⌊ ?F ⌋) =  (⌊ ?G ⌋) |- _ => inversion H;sauto      
end.

      
Ltac Cases H := destruct H;sauto;SubCases;
repeat
match goal with
| H: Permutation ?M (_::_) |- context[?M] => rewrite H
| H: Permutation (_++_) ?M  |- context[?M] => rewrite <- H
end
.
 
Ltac PermuteLeft :=    
  match goal with 
       |[ Hr: flln _ ?x ( (⌊ ?F ⌋)::?G) (?X1 ++ _) (UP []),  
       Hr': flln _ ?x ( (⌊ ?F ⌋)::?G)  (?X2 ++ _) (UP []),              
       Hl: flln ?th ?n ?G ((⌈ ?F ⌉) ::?N) (UP []) |- _] =>
   assert(Hl': flln th n G ((⌈ F ⌉) :: N) (UP []) ) by auto; 
   try rewrite <- app_comm_cons in Hr, Hr' 
 (*   |[ Hr: flln _ ?x (?G ++ ?Y1) (?X ++ _) (UP []),   
        Hr': flln _ ?x (?G ++ ?Y2) (?X ++ _) (UP []),             
       Hl: flln ?th ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []),
       Hp: Permutation ( (⌊ ?F ⌋) :: _) ?X |- _] =>
   assert(Hl': flln th n G ( (⌈ F ⌉) :: N) (UP [])) by auto; 
   apply weakeningGenN_rev with (CC':= Y1) in Hl;
   apply weakeningGenN_rev with (CC':= Y2) in Hl';
   rewrite <- Hp in Hr, Hr';
    rewrite <- app_comm_cons in Hr, Hr'    
  *)
  (*     |[ Hr: flln _ ?x (( (⌊ ?F ⌋)::?G) ++ ?Y) (?X ++ _) (UP []),               
       Hl: flln _ ?n ?G ((⌈ ?F ⌉) :: LEncode ?N) (UP []) |- _] =>
       apply weakeningGenN_rev with (CC':= Y) in Hl;
       rewrite <- app_comm_cons in Hr,Hl
  *)
  |[ Hr: flln _ ?x ((⌊ ?F ⌋::?G)) (?X ++ _) (UP []),               
       Hl: flln _ ?n ?G ( (⌈ ?F ⌉) ::?N) (UP []) |- _] =>
       rewrite <- app_comm_cons in Hr       

       end.
 
(** Unary Right is not principal on the left branch *)    
Lemma UnaryRightNotPrincipalL n n' n0 n1 C FCut F Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_ucon C F) ->
IsPositiveAtomBFormulaL M ->
isOLFormulaL Gamma ->
isOLFormulaL N ->
buildTheory (makeRRuleU C F) ->
flln (OLTheory PnN) (S n0) (LEncode Gamma) ((⌈ FCut ⌉) ::  LEncode N) (UP []) ->
flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M
     (DW (makeRRuleU C F)) ->
flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros Hn Hc Hl HFCut HF HM HGamma HN.
  intros Hth Hseq1 Hseq2.
  wellUnary Hseq2.
  * Cases H.
     - cutOL Hseq1 H1. 
        OLSolve.
        rewrite <- app_comm_cons.
        apply H7...
        rewrite Permutation_assoc_comm...
     - inversion H1...
        apply NoUinL in H...  
 Qed.

(** Unary Left is not principal on the left branch *) 
Lemma UnaryLeftNotPrincipalL n n' n0 n1 C FCut F Gamma M N: 
FCut <> t_ucon C F ->
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_ucon C F) ->
IsPositiveAtomBFormulaL M ->
isOLFormulaL Gamma ->
isOLFormulaL N ->
buildTheory (makeLRuleU C F) ->
flln (OLTheory PnN) (S n0) (LEncode Gamma) ((⌈ FCut ⌉) :: LEncode N) (UP []) ->
flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M
     (DW (makeLRuleU C F)) ->
flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros Hd Hn Hc Hl HFCut HF HM HGamma HN.
  intros Hth Hseq1 Hseq2.
  wellUnary Hseq2.
  * Cases H.
     - cutOL Hseq1 H1. 
        OLSolve. 
        rewrite <- app_comm_cons.
        apply H7...
        rewrite Permutation_assoc_comm...
     - inversion H1...
        inversion H...
        cutOL Hseq1 H3. 
        assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleU C F))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1.
        apply H7...
        rewrite Permutation_assoc_comm...
Qed. 
  
Lemma OLCutHasPos n: hasPos (OLTheoryCutI PnN n).
Proof with sauto.
   intro.
   intros...  
   constructor. apply ooth_strpos... firstorder.
Qed.
   
 
 Lemma OLHasPos: hasPos (OLTheory PnN).
Proof with sauto.
   intro.
   intros... apply ooth_strpos... firstorder.
 Qed.
   
 #[local] Hint Resolve OLCutHasPos OLHasPos : core. 

Ltac clearNotFormulas :=
repeat
multimatch goal with
| [ H: _ |- IsPositiveAtomFormulaL _] => 
    let tH := type of H in 
    match tH with
     | Permutation _ _ => idtac
     | IsPositiveAtomFormula _ => idtac
     | IsPositiveAtomFormulaL _ => idtac
     | _ => clear H
    end 
end.


(** Binary Right is not principal on the left branch *) 
Lemma BinaryRightNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
IsPositiveAtomBFormulaL M ->
isOLFormulaL Gamma ->
isOLFormulaL N ->
buildTheory (makeRRuleB C F G) ->
flln (OLTheory PnN) (S n0) (LEncode Gamma) ( (⌈ FCut ⌉) :: LEncode N) (UP []) ->
flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M
     (DW (makeRRuleB C F G)) ->
flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros Hn Hc Hl HFCut HF HM HGamma HN.
  intros Hth Hseq1 Hseq2.
  wellBinary Hseq2.
  * Cases H.
     - cutOL Hseq1 H1. 
        OLSolve. 
        rewrite <- app_comm_cons.
        apply H7...
        rewrite Permutation_assoc_comm...
     -  inversion H1...
        apply NoUinL in H...
  * Cases H.
     - 
        cutOL Hseq1 H4. 
        cutOL Hseq1 H5. 
       rewrite H3 in HM. 
        inversion HM... OLSolve. 
        apply PosSetP... 
        apply H9...
        apply AbsorptionLSet'... 
        apply AbsorptionLSet'... 
     -  inversion H3...
        apply NoUinL in H...
  * Cases H.
     - PermuteLeft. 
        cutOL Hseq1 H4. 
        OLSolve.  
        cutOL Hl' H5. 
        OLSolve.
        rewrite <- app_comm_cons. 
        apply H9...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
     -  inversion H3...
        apply NoUinL in H...
Qed.

 (** Unary Left is not principal on the left branch *)  
Lemma BinaryLeftNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
FCut <> t_bcon C F G ->
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
IsPositiveAtomBFormulaL M ->
isOLFormulaL Gamma ->
isOLFormulaL N ->
buildTheory (makeLRuleB C F G) ->
flln (OLTheory PnN) (S n0)  (LEncode Gamma) ( (⌈ FCut ⌉) :: LEncode N) (UP []) ->
flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode  Gamma) M
     (DW (makeLRuleB C F G)) ->
flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros Hd Hn Hc Hl HFCut HF HM HGamma HN.
  intros Hth Hseq1 Hseq2.
  wellBinary Hseq2.
  * Cases H.
     - cutOL Hseq1 H1. 
        OLSolve. 
        rewrite <- app_comm_cons.
        apply H7...
        rewrite Permutation_assoc_comm...
     -  inversion H1...
        inversion H...
        cutOL Hseq1 H3.
               assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C F G))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1.
        apply H7...
        rewrite Permutation_assoc_comm...
  * Cases H.
     - cutOL Hseq1 H4. 
        cutOL Hseq1 H5. 
        rewrite H3 in HM. 
        inversion HM... 
        apply PosSetP... 
        apply H9...
        apply AbsorptionLSet'... 
        apply AbsorptionLSet'... 
     -  inversion H3...
        inversion H...
        cutOL Hseq1 H4.
        cutOL Hseq1 H5.
                apply PosSetP... 
           assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C F G))...
        LLPerm ([]++M).
         eapply InvTensorT'. exact mTh.
        solveLL. apply weakeningGen. LLfocus1.

        apply H9...
        apply AbsorptionLSet'... 
        apply AbsorptionLSet'... 
  * Cases H.
     - PermuteLeft. 
        cutOL Hseq1 H4. 
        OLSolve.  
        cutOL Hl' H5. 
        OLSolve. 
        apply H9...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
     -  inversion H3...
        inversion H...
        PermuteLeft. 
        cutOL Hseq1 H4.
        cutOL Hl' H5.
           assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C F G))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL.  LLfocus1.
      apply H9... 
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
Qed.
  
 (** Quantifier Right is not principal on the left branch *) 
 Lemma QuantifierRightNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_qcon C FX) ->
IsPositiveAtomBFormulaL M ->
isOLFormulaL Gamma ->
isOLFormulaL N ->
buildTheory (makeRRuleQ C FX) ->
flln (OLTheory PnN) (S n0) (LEncode Gamma) ( (⌈ FCut ⌉) ::LEncode N) (UP []) ->
flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M
     (DW (makeRRuleQ C FX)) ->
flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros Hn Hc Hl HFCut HF HM HGamma HN.
  intros Hth Hseq1 Hseq2.
  wellQuantifier Hseq2.
  * Cases H.
     - cutOL Hseq1 H1. 
        OLSolve.
        rewrite <- app_comm_cons.
        apply H7...
        rewrite Permutation_assoc_comm...
     - inversion H1...
        apply NoUinL in H...
Qed.

 (** Quantifier Left is not principal on the left branch *) 
 Lemma QuantifierLeftNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 FCut <> t_qcon C FX -> 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_qcon C FX) ->
IsPositiveAtomBFormulaL M ->
isOLFormulaL Gamma ->
isOLFormulaL N ->
buildTheory (makeLRuleQ C FX) ->
flln (OLTheory PnN) (S n0) (LEncode Gamma) ( (⌈ FCut ⌉) :: LEncode N) (UP []) ->
flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M
     (DW (makeLRuleQ C FX)) ->
flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros Hd Hn Hc Hl HFCut HF HM HGamma HN.
  intros Hth Hseq1 Hseq2.
  wellQuantifier Hseq2.
  * Cases H.
     - cutOL Hseq1 H1. 
        OLSolve. 
        rewrite <- app_comm_cons.
        apply H7...
        rewrite Permutation_assoc_comm...
     - inversion H1...
        inversion H...
        cutOL Hseq1 H3.
               assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleQ C FX))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1.
        apply H7...
        rewrite Permutation_assoc_comm...
Qed.
 
Ltac permuteUnary :=
match goal with
| [H: ?n' <= ?n,
   Hl: flln _ _ ?G (_::LEncode ?N) (UP []) ,
   Hr : flln _ _ (_ :: ?G) ?M (DW (makeRRuleU _ _))
  |-  flls _ ?G (?M ++ LEncode ?N) (UP []) ] =>
   refine (UnaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: flln _ _ ?G (_::LEncode ?N) (UP []) ,
   Hr : flln _ _ (_ :: ?G) ?M (DW (makeLRuleU _ _))
  |-  flls _ ?G (?M ++ LEncode ?N) (UP []) ] =>
refine (UnaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.     
 
       
 
Ltac permuteBinary :=
match goal with
| [H: ?n' <= ?n,
   Hl: flln _ _ ?G (_::LEncode ?N) (UP []) ,
   Hr : flln _ _ (_ :: ?G) ?M (DW (makeRRuleB _ _ _))
  |-  flls _ ?G (?M ++ LEncode ?N) (UP []) ] =>
   refine (BinaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: flln _ _ ?G (_::LEncode ?N) (UP []) ,
   Hr : flln _ _ (_ :: ?G) ?M (DW (makeLRuleB _ _ _))
  |-  flls _ ?G (?M ++ LEncode ?N) (UP []) ] =>
refine (BinaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
 
 Ltac permuteQuantifier :=
match goal with
| [H: ?n' <= ?n,
   Hl: flln _ _ ?G (_::LEncode ?N) (UP []) ,
   Hr : flln _ _ (_ :: ?G) ?M (DW (makeRRuleQ _ _))
  |-  flls _ ?G (?M ++ LEncode ?N) (UP []) ] =>
   refine (QuantifierRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: flln _ _ ?G (_::LEncode ?N) (UP []) ,
   Hr : flln _ _ (_ :: ?G) ?M (DW (makeLRuleQ _ _))
  |-  flls _ ?G (?M ++ LEncode ?N) (UP []) ] =>
refine (QuantifierLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
       
Ltac Cases' H := destruct H;sauto;SubCases.

 Lemma dualRev F G: F = dual G -> G = dual F.
 Proof with sauto.
 intros.
 rewrite H...
 rewrite <- ng_involutive...
 Qed.

   Hypothesis LTWell2: wellFormedTheoryI. 
Definition ctWellFormed2 := proj1 LTWell2.
  Definition unWellFormed2 := proj1 (proj2 LTWell2).
  Definition biWellFormed2 := proj1 (proj2 (proj2 LTWell2)).
  Definition quWellFormed2 := proj2 (proj2 (proj2 LTWell2)).
 
  Ltac wellConstant2 HSeq :=
    let HS := type of HSeq in
    match HS with
    | flln ?Rules ?n ?Gamma (atom (up ?H)::LEncode ?N) (DW (makeLRuleC ?C)) =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (ctWellFormed2 Rules Gamma N H C);intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ];
          destruct bpEnum;[ apply LTWell' in HSeq; contradiction (* fail case *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell' (* axiom *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell'] (* one premise *)
    end.
  
        
 Lemma ConstantLEFT n n' n0 n1  C FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ccon C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 ( LEncode Gamma) ((⌈ FCut ⌉) :: LEncode N) (DW (makeLRuleC C)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleC C) ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.

  wellConstant2 Hseq1'.
  * Cases H. 
     LLPerm ( (⌊ t_ccon C ⌋) :: LEncode x++M)...
  * Cases H. 
     + cutOL H1 Hseq2.
        apply OLInPermutationL' in H. OLSolve.
         LLPerm ( (⌊ t_ccon C ⌋) ::(M++ LEncode x2)).
         apply H7...
        rewrite app_assoc_reverse.
        rewrite <- LEncodeApp...
    +  rewrite <- LEncodeApp in H3.  
         cutOL H3 Hseq2.
         LLtheory (makeLRuleC C).
         LLtensor (@nil oo) (M++LEncode N).
         apply H7... 
        rewrite app_assoc_reverse.
        rewrite <- LEncodeApp...
Qed.                  
  
  Ltac wellUnary2 HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (flln ?Rules ?n ?Gamma ?M (DW (makeLRuleU ?C ?F))) =>
        generalize  (unWellFormed2  HSeq);
        intro
    end.
  
 Lemma UnaryLEFT n n' n0 n1 C F FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 ( LEncode Gamma) ((⌈ FCut ⌉) :: LEncode N) (DW (makeLRuleU C F)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleU C F) ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellUnary2 Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2. 
        apply OLInPermutationL' in H. OLSolve.
         LLPerm ( (⌊ t_ucon C F ⌋) ::(M++ LEncode x2)).
         apply H7...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
     + rewrite <- LEncodeApp in H3.
        cutOL H3 Hseq2.
         LLtheory (makeLRuleU C F).
         LLtensor (@nil oo) (M++LEncode N).
         apply H7... 
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
Qed.       

  Ltac wellBinary2 HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (flln ?Rules ?n ?Gamma (atom( up ?H)::LEncode ?M) (DW (makeLRuleB ?C ?F ?G))) =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize  (biWellFormed2  Rules Gamma M H C);intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ]; 
         destruct bpEnum;generalize (LTWell' _ _ _ HSeq);intro;clear LTWell'
     end.

 Lemma BinaryLEFT n n' n0 n1 C F G FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_bcon C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 (LEncode Gamma) ((⌈ FCut ⌉) ::LEncode N) (DW (makeLRuleB C F G)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleB C F G) ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellBinary2 Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
        apply OLInPermutationL' in H. OLSolve.
         LLPerm ( (⌊ t_bcon C F G ⌋) ::(M++ LEncode x2)).
         apply H7...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
     + rewrite <- LEncodeApp in H3.
         cutOL H3 Hseq2.
         LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) (M++LEncode N).
         apply H7...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
  * Cases H. 
     + cutOL H4 Hseq2.
        apply OLInPermutationL' in H3.
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
(*         rewrite LEncodeApp. *)
         LLPerm ( (⌊ t_bcon C F G ⌋) ::(M++ LEncode x)).
         apply H9...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
         apply WeakTheoryN with (theory' := OLTheoryCutI PnN (pred n)) in H5...
         apply seqNtoSeq in H5...
     + cutOL H5 Hseq2.
        apply LEncodePermutation in H1... OLSolve.
         LLtheory (makeLRuleB C F G).
         LLtensor (@nil oo) (M++LEncode N).
        rewrite H1. simpl...
        apply H10...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
         apply WeakTheoryN with (theory' := OLTheoryCutI PnN (pred n)) in H6...
         apply seqNtoSeq in H6...
  * Cases H. 
     + assert(Hseq2': flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP [])) by auto.
         cutOL H4 Hseq2.
         apply OLInPermutationL' in H3. 
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
         cutOL H5 Hseq2'.
         apply OLInPermutationL' in H3.
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
         LLPerm ( (⌊ t_bcon C F G ⌋) ::(M++ LEncode x)).
         apply H9...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
     + assert(Hseq2': flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP [])) by auto.
         rewrite <- LEncodeApp in H4, H5. 
         cutOL H4 Hseq2.
         cutOL H5 Hseq2'.
        LLtheory (makeLRuleB C F G).
         LLtensor (@nil oo) (M++LEncode N).
         apply H9...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
Qed.

  Ltac wellQuantifier2 HSeq :=
    let HS := type of HSeq in
    match HS with
    | (flln ?Rules ?n ?Gamma (atom (up ?H)::?N) (DW (makeLRuleQ ?C ?F))) =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
         let HUniform := fresh "HUniform" in
        generalize  (quWellFormed2  Rules Gamma N H C F); intro LTWell';
        destruct LTWell' as [HUniform LTWell'];
          generalize (LTWell'  _ HSeq); intro;clear LTWell' 
    end.

 Lemma QuantifierLEFT n n' n0 n1 C FX FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) ::LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 (LEncode Gamma) ( (⌈ FCut ⌉) :: LEncode N) (DW (makeLRuleQ C FX)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleQ C FX) ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellQuantifier2 Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
        apply OLInPermutationL' in H.
         rewrite H in PosN.
         inversion PosN...
         OLSolve.
         LLPerm ( (⌊ t_qcon C FX ⌋) ::(M++ LEncode x2)).
         apply H7...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
     + rewrite <- LEncodeApp in H3. 
        cutOL H3 Hseq2.
         LLtheory (makeLRuleQ C FX).
         LLtensor (@nil oo) (M++LEncode N).
         apply H7...
         rewrite app_assoc_reverse.
         rewrite <- LEncodeApp...
Qed.
 
Theorem ConstantPrincipalCase :
    forall n Gamma M N C,
      (flls (OLTheoryCutI PnN n) Gamma M (DW (rc_lftBody (rulesC C)))) ->
      (flls (OLTheoryCutI PnN n) Gamma N (DW (rc_rgtBody (rulesC C)))) ->
      flls (OLTheoryCutI PnN n) Gamma (M ++ N) (UP []).
     Proof with sauto.     
    intros.  LLPerm (N++M).
    apply seqtoSeqN in H, H0... 
    generalize( ctCutCo C);intro CutC.
    unfold CutCoherenceC in CutC.
    destruct CutC as [Hc CutC]. 
    apply EmptySubSet with (theory:= (OLTheoryCutI PnN n) ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    apply seqtoSeqN in CutC.   destruct CutC as [h CutC].
    rewrite app_nil_r in CutC.
    assert(HCut1: flls (OLTheoryCutI PnN n) Gamma ([] ++ N)  ( UP [ (rc_lftBody (rulesC C)) ^])).
    eapply @GeneralCut with  (C:=  rc_rgtBody (rulesC C) ^);eauto. 
    rewrite <- ng_involutive;eauto.
    
    apply seqtoSeqN in HCut1.  destruct HCut1 as [h2 HCut1].
    eapply @GeneralCut with  (C:= (rc_lftBody (rulesC C)) ^); eauto. 
    rewrite <- ng_involutive;eauto.
  Qed.

Theorem ConstantPrincipalCaseUP :
    forall n Gamma M N C,
      (flls (OLTheoryCutI PnN n) Gamma M (UP [rc_lftBody (rulesC C)])) ->
      (flls (OLTheoryCutI PnN n) Gamma N (DW (rc_rgtBody (rulesC C)))) ->
      flls (OLTheoryCutI PnN n) Gamma (M ++ N) (UP []).
     Proof with sauto.
     intros. 
    destruct (PositiveOrNegative (rc_lftBody (rulesC C))).              
    2:{ apply tri_rel' in H...
          refine (ConstantPrincipalCase _ H H0). }
    apply PositiveDualNegative in H1. 
    generalize( ctCutCo C);intro CutC.
    unfold CutCoherenceC in CutC.
    destruct CutC as [Hc CutC]. 
    apply EmptySubSet with (theory:= (OLTheoryCutI PnN n) ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    rewrite app_nil_r in CutC.
    assert(HCut1: flls (OLTheoryCutI PnN n) Gamma ([] ++ N)  ( UP [ (rc_lftBody (rulesC C)) ^])).
    eapply @GeneralCut' with  (C:=  rc_rgtBody (rulesC C) ^);eauto. 
    rewrite <- ng_involutive;eauto.
    eapply @GeneralCut' with  (C:= (rc_lftBody (rulesC C))); eauto. 
  Qed.
  
  (** This is the case when a unary connective is principal in both premises *)
  Theorem UConnectivePrincipalCase :
    forall Gamma M N C F n n',
      (flls (OLTheoryCutI PnN (pred n)) Gamma M (DW (ru_lftBody (rulesU C) F))) ->
      (flls (OLTheoryCutI PnN (pred n)) Gamma N (DW (ru_rgtBody (rulesU C) F))) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      flls (OLTheoryCutI PnN (pred n)) Gamma (M++N) (UP []).
  Proof with sauto.
    intros. LLPerm (N++M).
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply seqtoSeqN in H.     
    apply seqtoSeqN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize( unCutCo C);intro CutC.
    unfold CutCoherenceU in CutC.
    
    generalize (CutC F n1);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply seqtoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCutI PnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCutI PnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCutI PnN n) in H0;auto using TheoryEmb1.
    assert(Cut1': flls (OLTheoryCutI PnN n) Gamma ([] ++N) ( UP[(ru_lftBody (rulesU C) F) ^] )).
    eapply @GeneralCut with(C := (ru_rgtBody (rulesU C) F)  ^) ;eauto.
    
    rewrite <- ng_involutive;eauto.

    apply seqtoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= (ru_lftBody (rulesU C) F) ^); eauto.
    rewrite <- ng_involutive;eauto.
  Qed.

  Theorem UConnectivePrincipalCaseUP :
    forall Gamma M N C F n n',
      (flls (OLTheoryCutI PnN (pred n)) Gamma M (UP [ru_lftBody (rulesU C) F])) ->
      (flls (OLTheoryCutI PnN (pred n)) Gamma N (DW (ru_rgtBody (rulesU C) F))) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      flls (OLTheoryCutI PnN (pred n)) Gamma (M++N) (UP []).
  Proof with sauto.
      intros. 
    destruct (PositiveOrNegative (ru_lftBody (rulesU C) F)).              
    2:{ apply tri_rel' in H...
          refine (UConnectivePrincipalCase _ _ _  H2 H3)... }
    apply PositiveDualNegative in H4. 
   inversion H1;subst.
    inversion H2;subst. inversion H5.
    destruct n ;[ lia | simpl].
    generalize( unCutCo C);intro CutC.
    unfold CutCoherenceU in CutC.
    
    generalize (CutC F n1);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H0;auto using TheoryEmb1.
    assert(Cut1': flls (OLTheoryCutI PnN n) Gamma ([] ++N) ( UP[(ru_lftBody (rulesU C) F) ^] )).
    eapply @GeneralCut' with(C := (ru_rgtBody (rulesU C) F)  ^) ;eauto.
    
    rewrite <- ng_involutive;eauto.
    eapply @GeneralCut' with (C:= (ru_lftBody (rulesU C) F) ); eauto.
   Qed.
  
  (** This is the case when a binary connective is principal in both premises *)
  Theorem BinConnectivePrincipalCase :
    forall Gamma M N C F G n n',
      (flls (OLTheoryCutI PnN (pred n)) Gamma M (DW (rb_lftBody (rulesB C) F G))) ->
      (flls (OLTheoryCutI PnN (pred n)) Gamma N (DW (rb_rgtBody (rulesB C) F G))) ->
      lengthUexp (t_bcon C F G) n' ->
      isOLFormula (t_bcon C F G) ->
      n' <= n ->
      flls (OLTheoryCutI PnN (pred n)) Gamma (M ++ N) (UP []).
  Proof with sauto.
    intros.  LLPerm (N++M).
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply seqtoSeqN in H.     apply seqtoSeqN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize (biCutCo C);intro CutC.
    unfold CutCoherenceB in CutC.
    
    generalize (CutC F G n1 n2);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply seqtoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCutI PnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCutI PnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCutI PnN n) in H0;auto using TheoryEmb1.
    
    assert(Cut1': flls (OLTheoryCutI PnN n) Gamma ([] ++ N) ( UP[ (rb_lftBody (rulesB C) F G) ^] )).
    eapply @GeneralCut with (C := (rb_rgtBody (rulesB C) F G) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
 
    apply seqtoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= (rb_lftBody (rulesB C) F G) ^); eauto.     rewrite <- ng_involutive;eauto.
  Qed.

  Theorem BinConnectivePrincipalCaseUP :
    forall Gamma M N C F G n n',
      (flls (OLTheoryCutI PnN (pred n)) Gamma M (UP [rb_lftBody (rulesB C) F G])) ->
      (flls (OLTheoryCutI PnN (pred n)) Gamma N (DW (rb_rgtBody (rulesB C) F G))) ->
      lengthUexp (t_bcon C F G) n' ->
      isOLFormula (t_bcon C F G) ->
      n' <= n ->
      flls (OLTheoryCutI PnN (pred n)) Gamma (M ++ N) (UP []).
  Proof with sauto.
        intros. 
    destruct (PositiveOrNegative (rb_lftBody (rulesB C) F G)).              
    2:{ apply tri_rel' in H...
          refine (BinConnectivePrincipalCase _ _ _  H2 H3)... }
    apply PositiveDualNegative in H4. 
    inversion H1;subst.
    inversion H2;subst. inversion H5.
    destruct n ;[ lia | simpl].
    generalize (biCutCo C);intro CutC.
    unfold CutCoherenceB in CutC.
    
    generalize (CutC F G n1 n2);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H0;auto using TheoryEmb1.
    
    assert(Cut1': flls (OLTheoryCutI PnN n) Gamma ([] ++ N) ( UP[ (rb_lftBody (rulesB C) F G) ^] )).
    eapply @GeneralCut' with (C := (rb_rgtBody (rulesB C) F G) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
    eapply @GeneralCut' with (C:= (rb_lftBody (rulesB C) F G)); eauto.    
  Qed.

  (** This is the case when a quantifier is principal in both premises *)
  Theorem QuantifierPrincipalCase :
    forall Gamma M N C FX FX0 n n',
      (flls (OLTheoryCutI PnN (pred n)) Gamma M (DW (rq_lftBody (rulesQ C) FX0))) ->
      (flls (OLTheoryCutI PnN (pred n)) Gamma  N (DW (rq_rgtBody (rulesQ C) FX))) ->
      isOLFormula (t_qcon C FX) ->
      isOLFormula (t_qcon C FX0) ->
      lengthUexp (t_qcon C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0%nat FX0 = lbind 0%nat FX ->
      n' <= n ->
      flls (OLTheoryCutI PnN (pred n)) Gamma (M ++ N) (UP []).
  Proof with sauto.
    intros.  LLPerm (N++M).
    inversion H1. inversion H8.
    inversion H2. inversion H12.
    subst.
    assert (ext_eq FX FX0).
    eapply lbindEq;eauto.
    assert (ext_eq FX FX1). eapply lbindEq;eauto.
    assert (ext_eq FX FX2). eapply lbindEq;eauto.  rewrite <- H6. auto.
    inversion H3...
    destruct n ;[ lia | simpl].
    assert (ext_eq FX M0). eapply lbindEq;eauto.
    generalize ( quCutCo C) ;intro CutC.
    assert (Hsize: lengthUexp (FX (Var 0%nat)) n0).
    { rewrite H17...  apply proper_VAR.  }
    assert(HIs: (forall t : expr Econ, proper t -> isOLFormula (FX t))).
    {intros t pt. rewrite H12... }
    unfold CutCoherenceQ in *.
    generalize (CutC FX FX0 n0); intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H0;auto using TheoryEmb1.
   
    apply seqtoSeqN in H.  apply seqtoSeqN in H0. apply seqtoSeqN in Cut1.
    destruct H as [h1 H]. 
    destruct H0 as [h2 H0]. destruct Cut1 as [h3 Cut1].
    

    assert(Cut1': flls (OLTheoryCutI PnN n) Gamma ([] ++N) ( UP[(rq_lftBody (rulesQ C) FX0) ^] )).
    eapply @GeneralCut with  (C := (rq_rgtBody (rulesQ C) FX) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
    simpl in Cut1'.
    apply seqtoSeqN in Cut1'.
    destruct Cut1' as [h4 Cut1']. 

    
    eapply @GeneralCut with (C := (rq_lftBody (rulesQ C) FX0) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
  Qed.

  Theorem QuantifierPrincipalCaseUP :
    forall Gamma M N C FX FX0 n n',
      (flls (OLTheoryCutI PnN (pred n)) Gamma M (UP [rq_lftBody (rulesQ C) FX0])) ->
      (flls (OLTheoryCutI PnN (pred n)) Gamma  N (DW (rq_rgtBody (rulesQ C) FX))) ->
      isOLFormula (t_qcon C FX) ->
      isOLFormula (t_qcon C FX0) ->
      lengthUexp (t_qcon C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0%nat FX0 = lbind 0%nat FX ->
      n' <= n ->
      flls (OLTheoryCutI PnN (pred n)) Gamma (M ++ N) (UP []).
  Proof with sauto.
        intros. 
    destruct (PositiveOrNegative (rq_lftBody (rulesQ C) FX0)).              
    2:{ apply tri_rel' in H...
          refine (QuantifierPrincipalCase _ _ _  _ H3 _ _ H6 H7)...  }
    apply PositiveDualNegative in H8.  
    inversion H1. inversion H9.
    inversion H2. inversion H13.
    subst.
    assert (ext_eq FX FX0).
    eapply lbindEq;eauto.
    assert (ext_eq FX FX1). eapply lbindEq;eauto.
    assert (ext_eq FX FX2). eapply lbindEq;eauto.  rewrite <- H6. auto.
    inversion H3...
    destruct n ;[ lia | simpl].
    assert (ext_eq FX M0). eapply lbindEq;eauto.
    generalize ( quCutCo C) ;intro CutC.
    assert (Hsize: lengthUexp (FX (Var 0%nat)) n0).
    { rewrite H18...  apply proper_VAR.  }
    assert(HIs: (forall t : expr Econ, proper t -> isOLFormula (FX t))).
    {intros t pt. rewrite H13... }
    unfold CutCoherenceQ in *.
    generalize (CutC FX FX0 n0); intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCutI PnN n) in H0;auto using TheoryEmb1.
 
    assert(Cut1': flls (OLTheoryCutI PnN n) Gamma ([] ++N) ( UP[(rq_lftBody (rulesQ C) FX0) ^] )).
    eapply @GeneralCut' with  (C := (rq_rgtBody (rulesQ C) FX) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
    
    eapply @GeneralCut' with (C := (rq_lftBody (rulesQ C) FX0) ) ;eauto.
  Qed.


Lemma ConstantRIGHT n n' n0 n1  C FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_ccon C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL Gamma ->
  isOLFormulaL N ->
  flln (OLTheory PnN) (S n0)  (LEncode Gamma) (⌈ FCut ⌉ :: LEncode N) (UP []) ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 (LEncode Gamma) (⌈ FCut ⌉ ::LEncode N) (DW (makeRRuleC C)) ->
  flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleC C) ->
  buildTheory F0 ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellConstant Hseq1'.
  * Cases H.
     2:{ apply NoUinL' in H1... }
     rewrite <- H4 in H2. clear H4. 
           inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H0.
               rewrite <- app_comm_cons...
               inversion H1...
               Cases H0. 
               cutOL Hseq1 H4.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H10...
               LLPerm ((x2 ++ x) ++ LEncode N)...
               inversion H4...
               apply NoUinL in H0...
           -- wellConstant Hseq2'.   
               Cases H0.
               rewrite <- app_comm_cons...
               inversion H1...
               inversion H0...
               assert( rc_rgtBody (rulesC C0) = Zero).
            { generalize( ctCutCo C0).
              intro CutC.
              unfold CutCoherenceC in CutC.
              inversion CutC...
              inversion H5...
              rewrite <- H10 in H4. simpl in H4... }
             rewrite H0 in H2. 
             inversion H2...
             inversion H4.

               Cases H0.
               cutOL Hseq1 H4.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H10...
               LLPerm ((x2 ++ x) ++ LEncode N)...
               inversion H4...
               inversion H0...
               cutOL Hseq1 H6.

                assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [rc_lftBody (rulesC C0)])). 
               apply H10...
               LLPerm ( (M ++ x) ++ LEncode N)...
               apply ContractionLinearPos...
               rewrite app_assoc.
apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H2;auto using TheoryEmb1.
             refine (ConstantPrincipalCaseUP _ H0 H2).
             cutOL Hseq1 H6.
          assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H10...
               LLPerm ( (M ++ x) ++ LEncode N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
  * Cases H.
     2:{ apply NoUinL' in H5... }
     2:{ apply NoUinL in H1... }
     rewrite <- H6 in H3, H1. clear H6. 
           inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               apply NoUinL in H2...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               inversion H2...
               assert( rc_rgtBody (rulesC C0) = Zero).
            { generalize( ctCutCo C0).
              intro CutC.
              unfold CutCoherenceC in CutC.
              inversion CutC...
              inversion H8...
              rewrite <- H13 in H6. simpl in H6... }
             rewrite H2 in H3. 
             inversion H3...
             inversion H6.

               Cases H2.
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               inversion H2...
               cutOL Hseq1 H9.
               assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [rc_lftBody (rulesC C0)])).
               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)...
               apply ContractionLinearPos...
               rewrite app_assoc.
apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H3;auto using TheoryEmb1.
              refine (ConstantPrincipalCaseUP _ H2 H3).
               cutOL Hseq1 H9.
    assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
Qed.

    
Lemma UnaryRIGHT n n' n0 n1  C F FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n0) (LEncode Gamma) ( (⌈ FCut ⌉) :: LEncode N) (UP []) ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 (LEncode Gamma) ( (⌈ FCut ⌉) :: LEncode N) (DW (makeRRuleU C F)) ->
  flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleU C F) ->
  buildTheory F0 ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellUnary Hseq1'.
  * Cases H.
     2:{ apply NoUinL' in H5... }
     2:{ apply NoUinL in H1... }
     rewrite <- H6 in H1, H3. clear H6.

         inversion Hth'... 
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               apply NoUinL in H2...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               cutOL Hseq1 H9.
               assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)...
           -- permuteUnary.
           -- wellUnary Hseq2'. 
               Cases H2.
               cutOL Hseq1 H6.
               OLSolve.
               LLPerm ( (⌊ t_ucon C0 F1 ⌋) :: x5++ LEncode N).
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               inversion H2...
               cutOL Hseq1 H9.
               assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [ru_lftBody (rulesU C0) F1] )).
               apply H13...
               LLPerm ((M ++ x2) ++ LEncode N)...
               apply ContractionLinearPos...
               rewrite app_assoc.
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H3;auto using TheoryEmb1.
               refine (UConnectivePrincipalCaseUP H2 H3 _ _ HL' )...
               cutOL Hseq1 H9.
                assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleU C0 F1))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 

               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)...
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
Qed.            



Ltac doubleH H :=
let tH := type of H in
   let H := fresh H in assert(H:tH) by auto.


Lemma BinaryRIGHT n n' n0 n1  C F G FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_bcon C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n0) ( LEncode Gamma) (⌈ FCut ⌉ :: LEncode N) (UP []) ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) ::LEncode  Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 (LEncode  Gamma) (⌈ FCut ⌉ :: LEncode N) (DW (makeRRuleB C F G)) ->
  flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleB C F G) ->
  buildTheory F0 ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellBinary Hseq1'.
  * Cases H. 
     2:{ apply NoUinL' in H5... }
     2:{ apply NoUinL in H1... }
     rewrite <- H6 in H1, H3. clear H6.
    inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               apply NoUinL in H2...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               cutOL Hseq1 H9.
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- wellBinary Hseq2'. 
               { Cases H2.
               cutOL Hseq1 H6.
               OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x5++ LEncode N).
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               inversion H2...
               cutOL Hseq1 H9.
               assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0] )).
               apply H13...
                LLPerm ((M ++ x2) ++ LEncode N)...               
               apply ContractionLinearPos...
               rewrite app_assoc.
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H3;auto using TheoryEmb1.
               refine (BinConnectivePrincipalCaseUP H2 H3 _ _ HL' )...
               cutOL Hseq1 H9.
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)... }
               { Cases H2.
               cutOL Hseq1 H10.
             cutOL Hseq1 H11.
               rewrite H9 in PosM.
               inversion PosM... 
               OLSolve.
              apply PosSetP...
               apply H15...
              1-2: apply AbsorptionLSet'...
               inversion H9...
               inversion H2...
               cutOL Hseq1 H10.
              cutOL Hseq1 H11.
 
          assert(flls (OLTheoryCutI PnN (pred n)) (LEncode N ++ ⌞ Gamma ⌟) M (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H15... 1-2: apply AbsorptionLSet'...
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H3;auto using TheoryEmb1.
             apply ContractionLinearPos... rewrite app_assoc.
             apply PosSetP... 
            eapply weakeningGen with (CC':= LEncode N) in H3.
             refine (BinConnectivePrincipalCaseUP H2 H3 _ _ HL' )...
      cutOL Hseq1 H10.
              cutOL Hseq1 H11.
apply PosSetP...            
   assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M).
         eapply InvTensorT'. exact mTh.
        solveLL.  apply weakeningGen. LLfocus1.

               apply H15... 1-2: apply AbsorptionLSet'...  }  
               { Cases H2.
               cutOL Hseq1 H10.
               rewrite H9 in PosM.
               inversion PosM... 
               OLSolve.
              cutOL Hseq1 H11.
               rewrite H9 in PosM.
               inversion PosM... 
               OLSolve.
               rewrite <- app_comm_cons. apply H15...
               LLPerm ((x2++ x3) ++ LEncode N)...
               LLPerm ((x2 ++ x4) ++ LEncode N)...
               inversion H9...
               inversion H2...
               cutOL Hseq1 H10.
              cutOL Hseq1 H11.
               assert(flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) (M++ LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H15...
              LLPerm ((M ++ x3) ++ ⌞ N ⌟)...
              LLPerm ((M ++ x4) ++ ⌞ N ⌟)...
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H3;auto using TheoryEmb1.
              apply ContractionLinearPos...
              rewrite app_assoc.
             refine (BinConnectivePrincipalCaseUP H2 H3 _ _ HL' )...
               cutOL Hseq1 H10.
              cutOL Hseq1 H11.
              assert(flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) (M++ LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H15...
              LLPerm ((M ++ x3) ++ ⌞ N ⌟)...
              LLPerm ((M ++ x4) ++ ⌞ N ⌟)...
   assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL.  LLfocus1.
                apply H15...
            1-2: rewrite <- Permutation_assoc_comm...
           }  
           -- permuteQuantifier.
           -- permuteQuantifier.
  * Cases H. 
     2:{ apply NoUinL' in H7... }
     2:{ apply NoUinL in H3... }
 clear H9 H4 H5. 
     rewrite <- H8 in H1. clear H8.
    inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H4...
               Cases H3. 
               cutOL Hseq1 H5.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H12...
               LLPerm ((x6 ++ x) ++ LEncode N)...
               inversion H5...
               apply NoUinL in H3...
           -- wellConstant Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H4...
               Cases H3. 
               cutOL Hseq1 H5.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H12...
               LLPerm ((x6 ++ x) ++ LEncode N)...
               inversion H5...
               cutOL Hseq1 H8.
assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H12...
               LLPerm ( (M ++ x) ++ LEncode N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- wellBinary Hseq2'. 
               { Cases H3.
               cutOL Hseq1 H5.
               OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x6++ LEncode N).
               apply H12...
               LLPerm ((x6 ++ x) ++ LEncode N)...
               inversion H5...
               inversion H3...
               cutOL Hseq1 H8.
               assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0] )).
               apply H12...
                LLPerm ((M ++ x) ++ LEncode N)...               
               apply ContractionLinearPos...
               rewrite app_assoc.
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H1;auto using TheoryEmb1.
               refine (BinConnectivePrincipalCaseUP H3 _ _ _ HL' )...
               cutOL Hseq1 H8.
assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H12...
               LLPerm ( (M ++ x) ++ LEncode N)... }
               { Cases H3.
               cutOL Hseq1 H9.
           cutOL Hseq1 H10.
               rewrite H8 in PosM.
               inversion PosM... 
               OLSolve.
             apply PosSetP...
             apply H14... 1-2: apply AbsorptionLSet'...
               inversion H8...
               inversion H3...
               cutOL Hseq1 H10.
              cutOL Hseq1 H9.
assert(flls (OLTheoryCutI PnN (pred n)) (LEncode N++ ⌞ Gamma ⌟) M (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H14...
              1-2: apply AbsorptionLSet'...
             apply ContractionLinearPos... rewrite app_assoc.
             apply PosSetP... 
           eapply weakeningGen with (CC':= LEncode N) in H1. 
    apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H1;auto using TheoryEmb1.
             refine (BinConnectivePrincipalCaseUP H3 H1 _ _ HL' )... 
      cutOL Hseq1 H10.
              cutOL Hseq1 H9.
apply PosSetP...            
   assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M).
         eapply InvTensorT'. exact mTh.
        solveLL.  apply weakeningGen. LLfocus1.

               apply H14... 1-2: apply AbsorptionLSet'...  
 }  
               { Cases H3.
               cutOL Hseq1 H9.
               rewrite H8 in PosM.
               inversion PosM... 
               OLSolve.
              cutOL Hseq1 H10.
               rewrite H8 in PosM.
               inversion PosM... 
               OLSolve.
               rewrite <- app_comm_cons. apply H14...
               1-2: rewrite Permutation_assoc_comm...
               inversion H8...
               inversion H3...
               cutOL Hseq1 H9.
              cutOL Hseq1 H10.
               assert(flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) (M++ LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H14...
              1-2: rewrite Permutation_assoc_comm... 
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H1;auto using TheoryEmb1.
              apply ContractionLinearPos...
              rewrite app_assoc.
             refine (BinConnectivePrincipalCaseUP H3 _ _ _ HL' )...
               cutOL Hseq1 H9.
              cutOL Hseq1 H10.
              assert(flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) (M++ LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H14...
1-2: rewrite Permutation_assoc_comm...
   assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL.  LLfocus1.

               apply H14... 1-2: rewrite Permutation_assoc_comm... }  
           -- permuteQuantifier.
           -- permuteQuantifier.
  * Cases H. 
     2:{ apply NoUinL' in H7... }
     2:{ apply NoUinL in H3... }
    clear H9 H4 H5. 
     rewrite <- H8 in H1. clear H8.
    inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H4...
               Cases H3. 
               cutOL Hseq1 H5.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H12...
               LLPerm ((x6 ++ x) ++ LEncode N)...
               inversion H5...
               apply NoUinL in H3...
           -- wellConstant Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H4...
               Cases H3. 
               cutOL Hseq1 H5.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H12...
               LLPerm ((x6 ++ x) ++ LEncode N)...
               inversion H5...
               cutOL Hseq1 H8.
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H12...
               LLPerm ( (M ++ x) ++ LEncode N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- wellBinary Hseq2'. 
               { Cases H3.
               cutOL Hseq1 H5.
               OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x6++ LEncode N).
               apply H12...
               LLPerm ((x6 ++ x) ++ LEncode N)...
               inversion H5...
               inversion H3...
               cutOL Hseq1 H8.
               assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0] )).
               apply H12...
                LLPerm ((M ++ x) ++ LEncode N)...               
               apply ContractionLinearPos...
               rewrite app_assoc.
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H1;auto using TheoryEmb1.
               refine (BinConnectivePrincipalCaseUP H3 _ _ _ HL' )...
               cutOL Hseq1 H8.
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 

               apply H12...
               LLPerm ( (M ++ x) ++ LEncode N)... }
               { Cases H3.
               cutOL Hseq1 H9.
       
              cutOL Hseq1 H10.
               rewrite H8 in PosM.
               inversion PosM... 
               OLSolve.
              apply PosSetP...
               apply H14... 1-2: apply AbsorptionLSet'...
               inversion H8...
               inversion H3...
               cutOL Hseq1 H10.
              cutOL Hseq1 H9.
              
assert(flls (OLTheoryCutI PnN (pred n)) ( LEncode N++⌞ Gamma ⌟) M (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H14... 1-2: apply AbsorptionLSet'... 
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H1;auto using TheoryEmb1.
              apply ContractionLinearPos...
             rewrite app_assoc.
             apply PosSetP...
               apply weakeningGen with (CC':= LEncode N) in H1.
             refine (BinConnectivePrincipalCaseUP H3 _ _ _ HL' )... 
               cutOL Hseq1 H10.
              cutOL Hseq1 H9.
       
assert(flls (OLTheoryCutI PnN (pred n)) (LEncode N++ ⌞ Gamma ⌟) M (UP [rb_lftBody (rulesB C0) F1 G0])). 
               apply H14... 1-2: apply AbsorptionLSet'...
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
          apply PosSetP...
        LLPerm ([]++M).
         eapply InvTensorT'. exact mTh.
        solveLL. apply weakeningGen. LLfocus1. auto.  }  
               { Cases H3.
               cutOL Hseq1 H9.
               rewrite H8 in PosM.
               inversion PosM... 
               OLSolve.
              cutOL Hseq1 H10.
               rewrite H8 in PosM.
               inversion PosM... 
               OLSolve.
               rewrite <- app_comm_cons. apply H14...
              1-2: rewrite Permutation_assoc_comm... 
               inversion H8...
               inversion H3...
               cutOL Hseq1 H9.
              cutOL Hseq1 H10.
               assert(flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) (M++ LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H14...
1-2: rewrite Permutation_assoc_comm...
              apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H1;auto using TheoryEmb1.
              apply ContractionLinearPos...
              rewrite app_assoc.
             refine (BinConnectivePrincipalCaseUP H3 _ _ _ HL' )...
               cutOL Hseq1 H9.
              cutOL Hseq1 H10.
              assert(flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) (M++ LEncode N) (UP [rb_lftBody (rulesB C0) F1 G0])).
               apply H14... 1-2: rewrite Permutation_assoc_comm...
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleB C0 F1 G0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1.  apply H14... 1-2: rewrite Permutation_assoc_comm...
               }  
           -- permuteQuantifier.
           -- permuteQuantifier.
Qed.
   
Lemma QuantifierRIGHT n n' n0 n1  C FX FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomBFormulaL M ->
  isOLFormulaL N ->
  isOLFormulaL Gamma ->
  flln (OLTheory PnN) (S n0) (LEncode Gamma)  (⌈ FCut ⌉ :: LEncode N) (UP []) ->
  flln (OLTheory PnN) (S n1) ( (⌊ FCut ⌋) :: LEncode Gamma) M (UP []) ->
  flln (OLTheory PnN) n0 ( LEncode Gamma) (⌈ FCut ⌉ ::LEncode N) (DW (makeRRuleQ C FX)) ->
  flln (OLTheory PnN) n1 ( (⌊ FCut ⌋) :: LEncode Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleQ C FX) ->
  buildTheory F0 ->
  flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellQuantifier Hseq1'.
  Cases H.
     2:{ apply NoUinL' in H5... }
     2:{ apply NoUinL in H1... }
     rewrite <- H6 in H1, H3. clear H6.

         inversion Hth'... 
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
                OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               apply NoUinL in H2...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H2. 
               cutOL Hseq1 H6.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H6...
               cutOL Hseq1 H9.
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleC C0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
               apply H13...
               LLPerm ( (M ++ x2) ++ LEncode N)...
           -- permuteUnary.
           -- permuteUnary. 
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- wellQuantifier Hseq2'. 
               Cases H5.
               cutOL Hseq1 H8.
               OLSolve.
               LLPerm ( (⌊t_qcon C0 FX0 ⌋) :: x5++ LEncode N).
               apply H14...
               LLPerm ((x5 ++ x2) ++ LEncode N)...
               inversion H8...
               inversion H...
               cutOL Hseq1 H10.
               assert(flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M++LEncode N) (UP [rq_lftBody (rulesQ C0) FX0] )).
               apply H14... 
               LLPerm ((M ++ x2) ++ LEncode N)...
                apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H3;auto using TheoryEmb1. 
              apply ContractionLinearPos...
              rewrite app_assoc.
               refine (QuantifierPrincipalCaseUP H5 H3 _ _ _ _ _ _ HL')...    
               cutOL Hseq1 H10.
 assert (mTh: (OLTheoryCutI PnN (pred n)) (makeLRuleQ C0 FX0))...
        LLPerm ([]++M++LEncode N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 

               apply H14...
               LLPerm ((M ++ x2) ++ LEncode N)...
Qed.
           


   (** Main theorem showing that it is possible to fins a proof with
  the theory [ (OLTheoryCutI PnN (pred n))] *)
  Theorem OLCutElimStep :
    forall h1 h2 n N M Gamma FCut n',
      isOLFormula FCut ->
      isOLFormulaL Gamma ->
      isOLFormulaL N ->
      IsPositiveAtomBFormulaL M ->
      flln (OLTheory PnN) h1 (LEncode Gamma) (atom (up FCut)::LEncode N) (UP []) ->
      flln (OLTheory PnN) h2 (atom (down FCut)::LEncode Gamma) M (UP []) ->
      lengthUexp FCut n' -> n'<=n ->
      (flls (OLTheoryCutI PnN (pred n)) (LEncode Gamma) (M ++ LEncode N) (UP [])) .
  Proof with sauto.
    intros h1 h2 n N M Gamma FCut n' HisF PosG PosN PosM Hseq1 Hseq2 HL HL'.
    remember (plus h1 h2) as h.
    generalize dependent Gamma.
    generalize dependent N.
    generalize dependent M.
    generalize dependent FCut.
    generalize dependent n. 
    generalize dependent h1.
    generalize dependent h2.
  
    induction h using lt_wf_ind; intros. 

    inversion Hseq1...
    cut(False);intros...
    refine (onlyAtomsLinear _ H0 H1)...
    OLSolve. 
    apply isOLLEncode... 
    cut(False);intros...
    refine (onlyAtomsClassical _ H0 H1)...
    apply isOLLEncode... 

    inversion Hseq2...  
    pose proof (onlyAtomsLinearB PosM H3 H4 )...
    inversion H5...   2:{  inversion H8. }
   inversion H11... 
   apply PosSetP... LLfocus1. solveLL.
   apply  AbsorptionLSet'.
assert( Hc:   flln (OLTheory PnN) (S n0) (⌞ Gamma ⌟) (⌈ FCut ⌉ :: ⌞ N ⌟) (UP []) ->
    flln (OLTheory PnN) n1 (⌊ FCut ⌋ :: ⌞ Gamma ⌟) ([⌈ x ⌉]) (UP []) ->
    flls (OLTheoryCutI PnN (pred n)) (⌞ Gamma ⌟) ([⌈ x ⌉] ++ ⌞ N ⌟) (UP [])).
   eapply H with (m:=S n0 + n1)...
apply Hc... 
  
cut(False);intros...
    refine (onlyAtomsClassical _ H3 H4)...
     OLSolve. 
    apply isOLLEncode... 

    assert(OOCut n' (S n0 + S n1)).
    {
    unfold OOCut; intros.
    revert H13 H14.
    eapply H with  (m:=h1 + h2)... }
    clear H.
   (* Now we proceed by cases on the last rule applied on both derivations *)
    inversion H1;inversion H4... 
    all: try match goal with
    H: neg PnN |- _ => inversion H 
    end.
    
    * inversion H...
       - refine(ConstantRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - refine(ConstantLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
       - refine(UnaryRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - refine(UnaryLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
       - refine(BinaryRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - refine(BinaryLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
       - refine(QuantifierRIGHT 
                           HL' 
                           H9 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)...        
       - refine(QuantifierLEFT 
                           HL' 
                           H9 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
    * apply FocusingInitRuleU in H5...
       - apply WeakeningLinearPos...
          rewrite H7.
          LLtheory (RINIT OO0).
          LLtensor [ (⌈ OO0 ⌉)]  [ (⌊ OO0 ⌋)].
       - inversion H10...
          inversion H5...
          LLtheory F. 
          apply seqNtoSeq in H2...
          apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H2;auto using TheoryEmb1.
          apply WeakeningLinearPos...
          LLtheory (RINIT OO0).
          LLtensor [ (⌈ OO0 ⌉)] (@nil oo).
        - inversion H10...
           apply NoUinL in H5...
       - inversion H9...
          apply NoUinL in H5...
    * apply FocusingStruct in H5...
      assert(flln (OLTheory PnN) x (⌊ FCut ⌋ :: ⌞ [OO0]++Gamma ⌟ )
        x0 (UP []))... simpl... LLExact H11.
       clear H11. 
        apply weakeningGenN with (CC':= LEncode [OO0]) in Hseq1.
         rewrite <- LEncodeApp in Hseq1.         
        cutOL Hseq1 H5.
        assert(flls (OLTheoryCutI PnN (pred n)) (⌞ [OO0] ++ Gamma ⌟)
          (x0 ++ ⌞ N ⌟) (UP []))... 
         rewrite H10.
        rewrite <- app_comm_cons. 
        apply PosF... simpl in H7. LLExact H7.
        
        inversion H10... inversion H5...
        rewrite Permutation_app_comm in H11.
        simpl in H11. 
        apply contractionN in H11...
        cutOL Hseq1 H11.
        LLPermH H11 (⌊ OO0 ⌋::(⌊ FCut ⌋ :: ⌞ Gamma ⌟)).
        apply contractionN in H11...
        cutOL Hseq1 H11.
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9... 
          apply PosSetP...
          rewrite H10.
         apply seqNtoSeq in H5.
apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H5;auto using TheoryEmb1.
          LLtheory F0...  
       - inversion H7...
         apply contractionN in Hseq2...
         apply seqNtoSeq in Hseq2...
        apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in Hseq2;auto using TheoryEmb1.
   * apply FocusingInitRuleU in H5...
       - apply WeakeningLinearPos...
          rewrite H7.
          LLtheory (RINIT OO0).
          LLtensor [ (⌈ OO0 ⌉)]  [ (⌊ OO0 ⌋)].
       - inversion H10...
          inversion H5...
          apply seqNtoSeq in H2...
          apply WeakTheory with (theory' := OLTheoryCutI PnN (pred n)) in H2;auto using TheoryEmb1.
          LLtheory (RINIT OO).
          apply WeakeningLinearPos...
          LLtheory (RINIT OO0).
          LLtensor [ (⌈ OO0 ⌉)] (@nil oo).
        - inversion H10...
           apply NoUinL in H5...
       - inversion H9...
          apply NoUinL in H5...
    * apply FocusingStruct in H5...
      assert(flln (OLTheory PnN) x (⌊ FCut ⌋ :: ⌞ [OO0]++Gamma ⌟ )
        x0 (UP []))... simpl... LLExact H11.
       clear H11. 
        apply weakeningGenN with (CC':= LEncode [OO0]) in Hseq1.
         rewrite <- LEncodeApp in Hseq1.         
        cutOL Hseq1 H5.
        assert(flls (OLTheoryCutI PnN (pred n)) (⌞ [OO0] ++ Gamma ⌟)
          (x0 ++ ⌞ N ⌟) (UP []))... 
         rewrite H10.
        rewrite <- app_comm_cons. 
        apply PosF... simpl in H7. LLExact H7.
        
        inversion H10... inversion H5...
        rewrite Permutation_app_comm in H11.
        simpl in H11. 
        apply contractionN in H11...
        cutOL Hseq1 H11.
        LLPermH H11 (⌊ OO0 ⌋::(⌊ FCut ⌋ :: ⌞ Gamma ⌟)).
        apply contractionN in H11...
        cutOL Hseq1 H11.
    * apply FocusingStruct in H2...
      rewrite <- perm_takeit_7 in H10.
      change ([⌈ FCut ⌉]) with (REncode [FCut]) in H10 .
      apply checkEncodeCasesD in H10...
      rewrite Permutation_app_comm in H7.
      rewrite <- H7 in H11.
      change ([⌊ OO ⌋]) with (LEncode [OO]) in H11 .
     apply weakeningGenN_rev with (CC':=LEncode [OO]) in Hseq2.
     rewrite <- app_comm_cons in Hseq2.
     rewrite <- LEncodeApp in H11, Hseq2.
     simpl in H11.
     cutOL H11 Hseq2.
     apply OLInPermutationL' in H2. OLSolve. 
    rewrite H2. rewrite <- Permutation_middle.
    apply PosF...
      change ([⌊ OO ⌋]) with (LEncode [OO])  .
     rewrite <- LEncodeApp...
    rewrite Permutation_app_comm in H11. simpl in H11.
     apply contractionN in H11...
     cutOL H11 Hseq2.
    * apply FocusingStruct in H2...
      rewrite <- perm_takeit_7 in H10.
      change ([⌈ FCut ⌉]) with (REncode [FCut]) in H10 .
      apply checkEncodeCasesD in H10...
      rewrite Permutation_app_comm in H7.
      rewrite <- H7 in H11.
      change ([⌊ OO ⌋]) with (LEncode [OO]) in H11 .
     apply weakeningGenN_rev with (CC':=LEncode [OO]) in Hseq2.
     rewrite <- app_comm_cons in Hseq2.
     rewrite <- LEncodeApp in H11, Hseq2.
     simpl in H11.
     cutOL H11 Hseq2.
     apply OLInPermutationL' in H2. OLSolve. 
    rewrite H2. rewrite <- Permutation_middle.
    apply PosF...
      change ([⌊ OO ⌋]) with (LEncode [OO])  .
     rewrite <- LEncodeApp...
    rewrite Permutation_app_comm in H11. simpl in H11.
     apply contractionN in H11...
     cutOL H11 Hseq2.
    * apply FocusingStruct in H5...
      rewrite <- app_comm_cons in H11.
      change ([⌊ OO0 ⌋]) with (LEncode [OO0]) in H11 .
     apply weakeningGenN_rev with (CC':=LEncode [OO0]) in Hseq1.
     rewrite <- LEncodeApp in H11, Hseq1.
     cutOL Hseq1 H11.
    rewrite H10.
    rewrite <- app_comm_cons.
    apply PosF...
      change ([⌊ OO0 ⌋]) with (LEncode [OO0])  .
     rewrite <- LEncodeApp...
     inversion H10... inversion H5...
    
    rewrite Permutation_app_comm in H11. simpl in H11.
     apply contractionN in H11...
     cutOL Hseq1 H11.
  rewrite Permutation_app_comm in H11. simpl in H11.
     apply contractionN in H11...
     cutOL Hseq1 H11.
  Qed.

  Theorem OLCutElimAux:
      forall n h B N,
      isOLFormulaL B ->
      IsPositiveAtomBFormulaL N ->
      flln  (OLTheoryCutI PnN n) h  (LEncode B) N (UP[] ) ->
      flls  (OLTheoryCutI PnN 0) (LEncode B) N (UP[] ) .
  Proof with sauto;try OLSolve.
    induction n ; induction h using lt_wf_ind; intros *;intros isFB isFN Hh.
    * eapply seqNtoSeq;eauto.
    * inversion Hh...
      pose proof (onlyAtomsLinearB isFN H0 H1 ) as Ht...
      inversion H2...   2:{  inversion H5. }
       inversion H8...
      LLfocus1. solveLL.
         refine (H _ _ _ _ _ _ H10)...
       cut(False);intros...
       refine (onlyAtomsClassical _ H0 H1)...
      apply isOLLEncode...
       inversion H1...
       inversion H3...
       inversion H4...
      + (* constant *)
         wellConstant H2.
         Cases H6.
         apply H10...
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolveB. 
        apply NoUinL in H8...
      + (* constant *)
         wellConstant H2.
         Cases H6.
         apply H10...
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
 assert (mTh: (OLTheoryCutI PnN 0) (makeLRuleC C))...
        LLPerm ([]++N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* unary *)
         wellUnary H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
        apply NoUinL in H8...
      + (* unary *)
         wellUnary H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
assert (mTh: (OLTheoryCutI PnN 0) (makeLRuleU C F0))...
        LLPerm ([]++N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
 
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* binary *)
         wellBinary H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
        apply NoUinL in H8...
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         refine (H _ _ _ _ _ _ H12)...
         rewrite H10 in isFN.
         inversion isFN...
        apply NoUinL in H10...
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         OLSolve.
        apply NoUinL in H10...
      + (* binary *)
         wellBinary H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
assert (mTh: (OLTheoryCutI PnN 0) (makeLRuleB C F0 G))...
        LLPerm ([]++N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
 
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         refine (H _ _ _ _ _ _ H12)...
         rewrite H10 in isFN.
         inversion isFN...
     assert (mTh: (OLTheoryCutI PnN 0) (makeLRuleB C F0 G))...
        LLPerm ([]++N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1.  
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         refine (H _ _ _ _ _ _ H12)...
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         OLSolve.
assert (mTh: (OLTheoryCutI PnN 0) (makeLRuleB C F0 G))...
        LLPerm ([]++N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         refine (H _ _ _ _ _ _ H12)...
      + (* quantifier *)
         wellQuantifier H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
         OLSolve.
        apply NoUinL in H9...
      + (* quantifier *)
         wellQuantifier H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
         OLSolve.
        assert (mTh: (OLTheoryCutI PnN 0) (makeLRuleQ C FX))...
        LLPerm ([]++N).
         eapply InvTensorT'. exact mTh.
        solveLL. LLfocus1. 

         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* init *)
         apply FocusingInitRuleU in H2...
         rewrite H5.
         LLtheory (RINIT OO).
         LLtensor [ (⌈ OO ⌉)] [ (⌊ OO ⌋)].
         LLtheory (RINIT OO).
         LLtensor [ (⌈ OO ⌉)] (@nil oo).
         LLtheory (RINIT OO).
         LLtensor (@nil oo) [ (⌊ OO ⌋)].
         LLtheory (RINIT OO).
         LLtensor.
      + (* pos *)
         apply FocusingStruct in H2...
         rewrite H7.
        apply PosF...
        change  [⌊ OO ⌋] with (LEncode [OO]).
        rewrite <- LEncodeApp.
        change  [⌊ OO ⌋] with (LEncode [OO]) in H8.
        rewrite <- LEncodeApp in H8. 
        refine (H _ _ _ _ _ _ H8)...
        rewrite Permutation_app_comm in H8.
        simpl in H8. apply contractionN in H8...
        refine (H _ _ _ _ _ _ H8)...
      + inversion f. 
      + (* cut *)
         inversion H3... inversion f.
         inversion H2...
         2:{ inversion H8. }
         invTri H13.
         invTri H14.
         invTri H12.
         invTri H15.
         clear H0 H1 H2 H3 Hh.
         apply H in H16...
         apply H in H14...
         apply WeakTheory with (theory' := OLTheory PnN) in H16;auto;try apply OOTheryCutI0.
         apply WeakTheory with (theory' := OLTheory PnN) in H14;auto;try apply OOTheryCutI0.
         rewrite H9.
         apply WeakTheory with (theory := OLTheory PnN).
         apply OOTheryCutI0.
  
         destruct m.
         generalize(LengthFormula H4 H5);intro;lia.
         apply seqtoSeqN in H16...
         apply seqtoSeqN in H14...
         apply absorptionLN in H14.
                 
assert (flls (OLTheoryCutI PnN (pred  (S (n)))) (LEncode B) (N0 ++ LEncode []) (UP [])) .
         
         refine(OLCutElimStep _ _ _ _ _ _ H5 _)... 
        simpl. exact H16. exact H14.   
         apply seqtoSeqN in H0... simpl in H0...
         apply IHn in H0...
         apply WeakTheory with (theory' := OLTheory PnN) in H0;auto;try apply  OOTheryCutI0.
         OLSolve.         
 Qed.        
        
     
  (** Cut-elimination theorem for Object Logics satisfying cut-coherence *)
  Theorem OLCutElimination :
    forall n  B N ,
      isOLFormulaL B ->
      IsPositiveAtomBFormulaL N ->
      flls (OLTheoryCutI PnN n) (LEncode B) N (UP [] ) ->
      flls (OLTheory PnN) (LEncode B) N (UP [] ) .
  Proof with sauto.
    intros.
    apply seqtoSeqN in H1...
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (theory':= OLTheory PnN) in H1 ...
    apply OOTheryCutI0.
  Qed.     
  
End CutElimination.

 #[export] Hint Resolve OLHasPos : core. 
#[export] Hint Resolve OLCutHasPos  : core. 