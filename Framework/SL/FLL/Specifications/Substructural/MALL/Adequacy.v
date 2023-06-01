(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Import LL.Misc.Permutations.
Require Import LL.Framework.SL.FLL.Specifications.Substructural.MALL.Cut.

Set Implicit Arguments.

(** ** Adequacy 

Now we prove that the encoding is sound and complete. For that, we
define the provability relation of MALL as an inductive definition *)

Notation "F *** G" := (t_bcon TENSOR F G) (at level 10) .
Notation "F $$$ G" := (t_bcon PAR F G) (at level 10) .
Notation "F 'ooo' G" := (t_bcon OPLUS F G) (at level 10) .
Notation "F &* G" := (t_bcon WITH F G) (at level 10) .

Record cutrule := {
  cut : bool   }.


Inductive MALLSeq {P} {n} : list uexp -> list uexp -> Prop :=
| MALLInit : forall F , MALLSeq [F] [F]
| MALLTensorR : forall L1 L2 L1' L2' F G, MALLSeq L1 (F :: L2) -> MALLSeq L1' (G :: L2') -> MALLSeq  (L1 ++ L1') (F *** G :: (L2 ++ L2'))
| MALLTensorL : forall L1 L2 F G, MALLSeq (F :: G :: L1) L2 -> MALLSeq (F *** G :: L1) L2
| MALLParR : forall L1 L2 F G, MALLSeq L1 (F :: G :: L2) -> MALLSeq L1 (F $$$ G :: L2)
| MALLParL :forall L1 L2 L1' L2' F G, MALLSeq (F :: L1) L2 -> MALLSeq (G :: L1') L2' -> MALLSeq (F $$$ G :: L1 ++ L1') (L2 ++ L2')
| MALLOpRE1 : forall L1 L2 F G, MALLSeq L1 (F :: L2) -> MALLSeq L1 (F ooo G :: L2)
| MALLOpRE2 : forall L1 L2 F G, MALLSeq L1 (G :: L2) -> MALLSeq L1 (F ooo G :: L2)
| MALLOpL : forall L1 L2 F G, MALLSeq (F :: L1) L2 -> MALLSeq (G :: L1) L2 -> MALLSeq (F ooo G :: L1) L2
| MALLWithR : forall L1 L2 F G, MALLSeq L1 (F :: L2) -> MALLSeq L1 (G :: L2) -> MALLSeq L1 (F &* G :: L2)
| MALLWithL1 : forall L1 L2 F G, MALLSeq (F :: L1) L2 ->  MALLSeq (F &* G :: L1) L2
| MALLWithL2 : forall L1 L2 F G, MALLSeq (G :: L1) L2 ->  MALLSeq (F &* G :: L1) L2
| MALLExR : forall  L1 L2 L2', Permutation L2 L2' -> MALLSeq L1 L2' -> MALLSeq L1 L2
| MALLExL : forall  L1 L2 L1', Permutation L1 L1' -> MALLSeq L1' L2 -> MALLSeq L1 L2
| MALLCut {f : cut P = true}: forall F L1 L2 R1 R2, lengthUexp F n ->  isOLFormula F -> MALLSeq (F::L1) R1 -> MALLSeq L2 (F::R2) -> MALLSeq (L1++L2) (R1++R2).

Definition wc := {| cut:= true |}. (* with cut *)
Definition wnc :=  {| cut:= false |}. (* with no cut *)


Global Instance MALLL_morph w n: 
  Proper ((@Permutation uexp) ==> (@Permutation uexp) ==> iff) (MALLSeq (P:=w) (n:=n)).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply MALLExR with (L2':=x0);auto.
  eapply MALLExL with (L1':=x);auto.
  eapply MALLExR with (L2':=y0);auto.
  eapply MALLExL with (L1':=y);auto. 
Qed.

Local Hint Constructors MALLSeq : core.

(** MALL -> MALL+CUT *)
Theorem SoundnessMALL: forall n L1 L2, 
                   MALLSeq (P:=wnc) (n:=n) L1 L2 -> MALLSeq (P:=wc) (n:=n) L1 L2.
Proof with sauto. 
    intros *. 
    intros HM.
   induction HM;simpl...
   rewrite H...
  rewrite H...
Qed.

 
(** MALL -> LL (MALL) *)
Theorem SoundenessFLL: forall n L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                  MALLSeq (P:=wnc) (n:=n) L1 L2 ->
                                flls (OLTheory nPnN) []  ( (LEncode L1) ++  (REncode L2)) (UP []).
Proof with sauto; try OLSolve. 
    intros *. 
    intros isFL1 isFL2 HM.
   induction HM;simpl...
  + LLtheory (RINIT F).
      inversion H.
     apply ooth_init.
     inversion isFL2...
     LLtensor [⌈ F ⌉] [⌊ F ⌋] ;solveLL.
  + simpl in IHHM1,IHHM2...
     LLtheory (makeRRuleB TENSOR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F *** G ⌉] (⌞ L1 ++ L1' ⌟ ++ ⌜ L2 ++ L2' ⌝) ;solveLL.
    LLtensor (⌞ L1⌟ ++ ⌜ L2⌝)  (⌞L1' ⌟ ++ ⌜ L2' ⌝);solveLL .
   rewrite LEncodeApp;
   rewrite REncodeApp... 
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉:: ⌜ L2 ⌝).
   apply IHHM1...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
   LLPerm (⌞ L1' ⌟ ++ ⌈ G ⌉ :: ⌜ L2' ⌝).
   apply IHHM2...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeLRuleB TENSOR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F *** G ⌋ ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
   LLPerm (⌊ F ⌋ :: ⌊ G ⌋ :: ⌞ L1 ⌟ ++ ⌜ L2 ⌝).
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeRRuleB PAR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F $$$ G ⌉  ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌈ G ⌉ :: ⌜ L2 ⌝).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB PAR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F $$$ G ⌋ ] (⌞ L1 ++ L1' ⌟ ++ ⌜ L2 ++ L2' ⌝) ;solveLL.
    LLtensor (⌞ L1⌟ ++ ⌜ L2⌝)  (⌞L1' ⌟ ++ ⌜ L2' ⌝);solveLL .
   rewrite LEncodeApp;
   rewrite REncodeApp... 

   apply IHHM1...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
   apply IHHM2...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeRRuleB OPLUS F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ooo G ⌉  ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
    LLleft;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌜ L2 ⌝).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeRRuleB OPLUS F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ooo G ⌉  ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
    LLright;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ G ⌉ :: ⌜ L2 ⌝).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB OPLUS F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ooo G ⌋ ] (⌞ L1⌟ ++ ⌜ L2 ⌝) ;solveLL.
    simpl;solveLL.
   apply IHHM1...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
   apply IHHM2...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeRRuleB WITH F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [ ⌈ F &* G ⌉  ] (⌞ L1⌟ ++ ⌜ L2 ⌝) ;solveLL.
    simpl;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌜ L2 ⌝) .
   apply IHHM1...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  LLPerm (⌞ L1 ⌟ ++ ⌈ G ⌉ :: ⌜ L2 ⌝).
   apply IHHM2...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeLRuleB WITH F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F &* G ⌋ ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
    LLleft;solveLL.
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeLRuleB WITH F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F &* G ⌋ ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
    LLright;solveLL.
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + rewrite H in isFL2. 
     eapply Permutation_map with (f:=(fun x : uexp => ⌈ x ⌉) ) in H.
      rewrite H. apply IHHM...
  + rewrite H in isFL1. 
     eapply Permutation_map with (f:=(fun x : uexp => ⌊ x ⌋) ) in H.
      rewrite H. apply IHHM...
Qed.

Require Import LL.Framework.SL.FLL.Reasoning.
  
(** LL (MALL) -> MALL  *)
Theorem CompletenessFLL: forall x n L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                 flln (OLTheory nPnN) x []  ( (LEncode L1) ++  (REncode L2)) (UP []) ->
                 MALLSeq (P:=wnc) (n:=n) L1 L2.
Proof with sauto;try solveLL; try OLSolve.
  induction x using lt_wf_ind; intros *.  
  intros HisL1 HisL2  Hseq. 
  inversion Hseq...
 cut(False);intros...
 refine (onlyAtomsLinear _ H0 H1)...
 apply isOLLEncode... 
 apply isOLREncode...
  inversion H1...
  inversion H3...
  1-4:  destruct C...
  3-4:  destruct C...
 + apply FocusingClause in H2...
    apply checkEncodeCasesU in H7... 
    apply OLInPermutation' in H2...
    rewrite H2...
    destruct C...
    ++ apply FocusingTensor in H8... 
          rewrite H9 in H5.
         apply destructEncode in H5...
         rewrite H8, H13.
         eapply MALLTensorR.
         eapply H with (m:=x2)...
         inversion H4...
         inversion H5...
         rewrite H13 in H2.
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H7.
         rewrite H6...
         eapply H with (m:=x2)...
        inversion H4...
         inversion H5...
         rewrite H13 in H2.
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H11.
         rewrite H10...
    ++ apply FocusingPar in H8... 
          eapply MALLParR.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H7.
         rewrite <- H5...
    ++ apply FocusingWith in H8... 
          eapply MALLWithR.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H9.
         rewrite <- H5...
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H10.
         rewrite <- H5...
    ++ apply FocusingPlus in H8... 
          eapply MALLOpRE1.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H8.
         rewrite <- H5...
          eapply MALLOpRE2.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL2.
         inversion HisL2...
         LLExact H8.
         rewrite <- H5...
 + apply FocusingClause in H2...
    apply checkEncodeCasesD in H7... 
    apply OLInPermutationL' in H2...
    rewrite H2...
    destruct C...
    ++ apply FocusingPar in H8... 
          eapply MALLTensorL.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H7.
         rewrite <- H5...
    ++ apply FocusingTensor in H8... 
          rewrite H9 in H5.
         apply destructEncode in H5...
         rewrite H8, H13.
         eapply MALLParL.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H5...
         rewrite H8 in H2.
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H7.
         rewrite H6...
         eapply H with (m:=x2)...
          inversion H4...
         inversion H5...
         rewrite H8 in H2.
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H11.
         rewrite H10...
    ++ apply FocusingPlus in H8... 
          eapply MALLWithL1.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H8.
         rewrite <- H5...
          eapply MALLWithL2.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H8.
         rewrite <- H5...
    ++ apply FocusingWith in H8... 
          eapply MALLOpL.
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H9.
         rewrite <- H5...
         eapply H with (m:=x2)...
          inversion H4...
         inversion H6...
         rewrite H2 in HisL1.
         inversion HisL1...
         LLExact H10.
         rewrite <- H5...
 + apply FocusingInitRuleU in H2...
     simpl in H4. 
    apply checkEncodeCasesU in H4...
    assert(In (⌊ OO ⌋) (⌜ L2 ⌝)).
    rewrite H2. rewrite H7.
    firstorder.
   apply NoDinR in H4...
   rewrite H7 in H2...
   assert(L1 = [OO]).
   eapply MapLEncodeEqual... 
   assert(L2 = [OO]).
   eapply MapREncodeEqual...
   rewrite H4, H5...
+ inversion f.
+ inversion f.
Qed.

(** MALL+CUT -> LL(MALL) *)
Theorem SoundenessCFLL: forall x L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                  MALLSeq (P:=wc) (n:=x) L1 L2 ->
                     flls (OLTheoryCut nPnN x) []  ( (LEncode L1) ++  (REncode L2)) (UP []).
Proof with sauto; try solveLL; try OLSolve. 
    intros *. 
    intros isFL1 isFL2 HM.
   induction HM;simpl...
  +  LLtheory (RINIT F).
      inversion H.
     apply oothc_theory.
     apply ooth_init.
     inversion isFL2...
     LLtensor [⌈ F ⌉] [⌊ F ⌋] ;solveLL.
  + simpl in IHHM1,IHHM2...
     LLtheory (makeRRuleB TENSOR F G). 
    apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F *** G ⌉] (⌞ L1 ++ L1' ⌟ ++ ⌜ L2 ++ L2' ⌝) ;solveLL.
    LLtensor (⌞ L1⌟ ++ ⌜ L2⌝)  (⌞L1' ⌟ ++ ⌜ L2' ⌝);solveLL .
   rewrite LEncodeApp;
   rewrite REncodeApp... 
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉:: ⌜ L2 ⌝).
   apply IHHM1... 
     inversion isFL2...
     inversion H1...
     inversion H...
     inversion isFL2...
   LLPerm (⌞ L1' ⌟ ++ ⌈ G ⌉ :: ⌜ L2' ⌝).
   apply IHHM2... 
     inversion isFL2...
     inversion H1...
     inversion H...
     inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeLRuleB TENSOR F G). 
    apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F *** G ⌋ ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
   LLPerm (⌊ F ⌋ :: ⌊ G ⌋ :: ⌞ L1 ⌟ ++ ⌜ L2 ⌝)...
   apply IHHM...
 inversion isFL1...
     inversion H1...
     inversion H...
 inversion isFL1...
     inversion H1...
     inversion H...
 inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeRRuleB PAR F G). 
     apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F $$$ G ⌉  ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌈ G ⌉ :: ⌜ L2 ⌝)...
   apply IHHM... 
   inversion isFL2...
     inversion H1...
     inversion H...
   inversion isFL2...
   
     inversion H1...
     inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB PAR F G). 
    apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F $$$ G ⌋ ] (⌞ L1 ++ L1' ⌟ ++ ⌜ L2 ++ L2' ⌝) ;solveLL.
    LLtensor (⌞ L1⌟ ++ ⌜ L2⌝)  (⌞L1' ⌟ ++ ⌜ L2' ⌝);solveLL .
   rewrite LEncodeApp;
   rewrite REncodeApp...
   apply IHHM1...
     inversion isFL1...
     inversion H1...
     inversion H...
     inversion isFL1...
      apply IHHM2...
 inversion isFL1...
     inversion H1...
     inversion H...
     inversion isFL1...
    + simpl in IHHM...
     LLtheory (makeRRuleB OPLUS F G). 
    apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ooo G ⌉  ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
    LLleft;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌜ L2 ⌝)...
    apply IHHM...
   inversion isFL2...
     inversion H1...
     inversion H...
     inversion isFL2...
   + simpl in IHHM...
     LLtheory (makeRRuleB OPLUS F G). 
    apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ooo G ⌉  ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
   simpl;solveLL.
    LLright;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ G ⌉ :: ⌜ L2 ⌝)...
   apply IHHM...
  inversion isFL2...
     inversion H1...
     inversion H...
     inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB OPLUS F G). 
    apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ooo G ⌋ ] (⌞ L1⌟ ++ ⌜ L2 ⌝) ;solveLL.
    simpl;solveLL.
   apply IHHM1...
   inversion isFL1...
     inversion H1...
     inversion H...
     inversion isFL1...
   apply IHHM2...
   inversion isFL1...
     inversion H1...
     inversion H...
     inversion isFL1...

  + simpl in IHHM1,IHHM2...
     LLtheory (makeRRuleB WITH F G). 
   apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [ ⌈ F &* G ⌉  ] (⌞ L1⌟ ++ ⌜ L2 ⌝) ;solveLL.
    simpl;solveLL.
   LLPerm (⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌜ L2 ⌝) .
  apply IHHM1... inversion isFL2...
     inversion H1...
     inversion H...
     inversion isFL2...
     
  LLPerm (⌞ L1 ⌟ ++ ⌈ G ⌉ :: ⌜ L2 ⌝).
  apply IHHM2... inversion isFL2...
     inversion H1...
     inversion H...
     inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeLRuleB WITH F G). 
     apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F &* G ⌋ ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
     simpl;solveLL.
     LLleft...
    apply IHHM...
   inversion isFL1...
     inversion H1...
     inversion H...
     inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeLRuleB WITH F G). 
     apply oothc_theory.
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F &* G ⌋ ] (⌞ L1⌟ ++ ⌜ L2⌝) ;solveLL.
     simpl;solveLL.
     LLright...
    apply IHHM...
   inversion isFL1...
     inversion H1...
     inversion H...
     inversion isFL1...
  + simpl in IHHM...
     rewrite H in isFL2. 
     eapply Permutation_map with (f:=(fun x : uexp => ⌈ x ⌉) ) in H.
      rewrite H... 
  + simpl in IHHM...
     rewrite H in isFL1. 
     eapply Permutation_map with (f:=(fun x : uexp => ⌊ x ⌋) ) in H.
      rewrite H... 
   + simpl in IHHM1,IHHM2...
     LLtheory (RCUT F).
     inversion H1.
    eapply oothc_cutn.
    eapply ctn with (m:=x)... firstorder.
    LLtensor ( ⌞ L2 ⌟ ++ ⌜ R2 ⌝) (⌞ L1 ⌟ ++ ⌜ R1 ⌝) .
    rewrite LEncodeApp, REncodeApp...
    1-2: solveLL.
   
    LLPerm (⌞ L2 ⌟ ++ ⌈ F ⌉ :: ⌜ R2 ⌝).
    apply IHHM2...
   inversion isFL2...
    apply IHHM1...
   inversion isFL2...
  Qed.

 Theorem CutElimMALL: forall x L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                  MALLSeq (P:=wc) (n:=x) L1 L2 -> MALLSeq (P:=wnc) (n:=x) L1 L2.
Proof with sauto.
 intros.
 apply  SoundenessCFLL in H1...
 specialize(OLCutElimination  wellTheoryMALL CutCoherenceMALL);intros.
 apply FLLStoFLLN in H1...
 apply H2 in H1... all:clear H2.
 apply FLLStoFLLN in H1...
eapply CompletenessFLL with (n:=x) in H1...
apply Forall_app...
apply isOLLEncode...
apply isOLREncode...
Qed.
 
 Theorem CutAdmMALL: forall x F L1 L2 R1 R2, 
      isOLFormulaL L1 ->  isOLFormulaL L2 -> isOLFormulaL R1 ->  isOLFormulaL R2 -> lengthUexp F x -> isOLFormula F -> 
MALLSeq (P:=wnc) (n:=x) (F::L1) R1 -> MALLSeq (P:=wnc) (n:=x) L2 (F::R2) -> MALLSeq (P:=wnc) (n:=x) (L1++L2) (R1++R2).
Proof with sauto.
  
 intros. 
 eapply CutElimMALL... 
1-2: apply Forall_app...
eapply MALLCut with (F:=F)... 
1-2: apply SoundnessMALL...
Unshelve.
eauto.
Qed.


Lemma OLFormulaLeng F: isOLFormula F -> exists x, lengthUexp F x.
Proof with sauto.
 intro H. induction H;intros...
 - eexists...
 - inversion H...
    eexists...
 - eexists (S x)...
 - eexists (S (x0+x))...
 - assert(proper  (Var 0%nat)). 
    apply proper_VAR. 
    apply H1 in H2... 
    eexists (S x)...
Qed.
   
