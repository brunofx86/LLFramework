(** * System LK for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system LK (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Import LL.Misc.Permutations.
Require Import LL.Framework.SL.FLL.Specifications.Classical.LK.Cut.

Set Implicit Arguments.

(** ** Adequacy 

Now we prove that the encoding is sound and complete. For that, we
define the provability relation of LK as an inductive definition *)

Notation "¬' F" := (t_ucon CNEG F) (at level 10) .
Notation "F ∧' G" := (t_bcon AND F G) (at level 10) .
Notation "F ∨' G" := (t_bcon OR F G) (at level 10) .
Notation "F ⇒' G" := (t_bcon IMP F G) (at level 10) .

Record cutrule := {
  cut : bool; nc : nat   }.

Inductive LKSeq {P} : list uexp -> list uexp -> Prop :=
| LKTRUE : forall L L', LKSeq L ((t_ccon TT)::L')
| LKFALSE : forall L L', LKSeq (t_ccon FF :: L) L' 
| LKInit : forall F , LKSeq [F] [F]
| LKNegR : forall L R F , LKSeq (F::L) R -> LKSeq L (¬' F :: R) 
| LKNegL : forall L R F , LKSeq L (F::R) -> LKSeq (¬' F :: L) R 
| LKAndR : forall L R F G, LKSeq L (F ::R) -> LKSeq L (G ::R) -> LKSeq  L (F ∧' G :: R)
| LKAndL1 : forall L R F G, LKSeq (F :: L) R -> LKSeq (F ∧' G :: L) R
| LKAndL2 : forall L R F G, LKSeq (G :: L) R -> LKSeq (F ∧' G :: L) R
| LKOrR1 : forall L R F G, LKSeq L (F :: R) -> LKSeq L (F ∨' G :: R)
| LKOrR2 : forall L R F G, LKSeq L (G :: R) -> LKSeq L (F ∨' G :: R)
| LKOrL : forall L R F G, LKSeq (F ::L) R -> LKSeq (G ::L) R -> LKSeq (F ∨' G :: L) R
| LKImpR : forall L R F G, LKSeq (F::L) (G ::R) -> LKSeq  L (F ⇒' G :: R)
| LKImpL : forall L1 L2 R1 R2 F G, LKSeq L1 (F ::R1) -> LKSeq (G::L2) R2 -> LKSeq (F ⇒' G :: L1++L2) (R1++R2)
| LKExR : forall  L1 L2 L2', Permutation L2 L2' -> LKSeq L1 L2' -> LKSeq L1 L2
| LKExL : forall  L1 L2 L1', Permutation L1 L1' -> LKSeq L1' L2 -> LKSeq L1 L2

| LKWR : forall  L R F, LKSeq L R -> LKSeq L (F::R)
| LKWL : forall  L R F, LKSeq L R -> LKSeq (F::L) R
| LKCR : forall  L R F, LKSeq L (F::F::R) -> LKSeq L (F::R)
| LKCL : forall  L R F, LKSeq (F::F::L) R -> LKSeq (F::L) R

| LKCut {f : cut P = true } : forall F L1 L2 R1 R2, lengthUexp F (nc P) ->  isOLFormula F -> LKSeq (F::L1) R1 -> LKSeq L2 (F::R2) -> LKSeq (L1++L2) (R1++R2).

Definition wc n := {| cut:= true; nc:= n |}. (* with cut *)
Definition wnc :=  {| cut:= false; nc:=0 |}. (* with no cut *)


Global Instance LKL_morph w : 
  Proper ((@Permutation uexp) ==> (@Permutation uexp) ==> iff) (LKSeq (P:=w) ).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply LKExR with (L2':=x0);auto.
  eapply LKExL with (L1':=x);auto.
  eapply LKExR with (L2':=y0);auto.
  eapply LKExL with (L1':=y);auto. 
Qed.

Local Hint Constructors LKSeq : core.

Ltac LKExact H :=
  let G:= type of H in
  match G with
  | (LKSeq ?L ?R) =>
    match goal with
    | [ |- LKSeq ?L' ?R' ] =>
      apply LKExL with (L1':= L);[ 
           try perm | 
          apply LKExR with (L2':= R);
         [ try perm | auto ] ]
    end
  end;auto.



Lemma GenLKCR : forall  w L R R1, LKSeq (P:=w)   L (R1++R1++R) -> LKSeq (P:=w)  L (R1++R).
Proof with sauto.
 intros. revert dependent R. induction R1; intros *...
 intro H.
 eapply LKExR with (L2:= R1++ R1 ++ a::a::R) in H...
 apply IHR1 in H.
 rewrite <- app_comm_cons. 
 apply LKCR. LKExact H.   
Qed.

Lemma GenLKCL : forall  w L R L1, LKSeq (P:=w)  (L1++L1++L) R -> LKSeq (P:=w)  (L1++L) R.
Proof with sauto.
 intros. revert dependent L. induction L1; intros *...
 intro H. 
 eapply LKExL with (L1:= L1++ L1 ++ a::a::L) in H...
 apply IHL1 in H.
 rewrite <- app_comm_cons. 
 apply LKCL. LKExact H.   
Qed.

Lemma GenLKCR_rev : forall  w L R R1, LKSeq (P:=w)  L (R++R1++R1) -> LKSeq (P:=w)  L (R++R1).
Proof with sauto.
 intros. rewrite Permutation_app_comm.
 apply GenLKCR. LKExact H.
Qed.

Lemma GenLKCL_rev : forall  w L R L1, LKSeq (P:=w)  (L++L1++L1) R -> LKSeq (P:=w)  (L++L1) R.
Proof with sauto.
 intros. rewrite Permutation_app_comm.
 apply GenLKCL. LKExact H.

Qed.

Lemma GenLKWR : forall  w L R R1, LKSeq (P:=w)  L R -> LKSeq (P:=w)  L (R1++R).
Proof with sauto.
 intros. revert dependent R. induction R1; intros *...
 intro H.
 eapply LKExR with (L2':= R1++ a::R)...
Qed.

Lemma GenLKWL : forall  w L R L1, LKSeq (P:=w)  L R -> LKSeq (P:=w)  (L1++L) R.
Proof with sauto.
 intros. revert dependent L. induction L1; intros *...
 intro H. 
 eapply LKExL with (L1':= L1 ++ a::L)... 
Qed.

Lemma GenLKWR_rev : forall  w L R R1, LKSeq (P:=w)  L R -> LKSeq (P:=w)  L (R++R1).
Proof with sauto.
 intros. rewrite Permutation_app_comm.
 apply GenLKWR. LKExact H.
Qed.

Lemma GenLKWL_rev : forall  w L R L1, LKSeq (P:=w) L R -> LKSeq (P:=w)  (L++L1) R.
Proof with sauto.
 intros. rewrite Permutation_app_comm.
 apply GenLKWL. LKExact H.

Qed.

(** LK -> LK+CUT *)
Theorem SoundnessLK: forall n L1 L2, 
                   LKSeq (P:=wnc)  L1 L2 -> LKSeq (P:=wc n)  L1 L2.
Proof with sauto. 
    intros *. 
    intros HM.
   induction HM;simpl...
   rewrite H...
  rewrite H...
Qed.

Require Import LL.Framework.SL.FLL.InvPositivePhase.
 
(** LK -> LL (LK) *)
Theorem SoundenessFLL: forall  L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                  LKSeq (P:=wnc)  L1 L2 ->
                                FLLS (OLTheory PN) []  ( (LEncode L1) ++  (REncode L2)) (UP []).
Proof with sauto; try OLSolve. 
    intros *. 
    intros isFL1 isFL2 HM.
   induction HM;simpl...
   + LLtheory (makeRRuleC TT).
      LLtensor [⌈ t_ccon TT ⌉]  (⌞ L ⌟ ++ ⌜ L' ⌝)... 
      simpl. solveLL.
   + LLtheory (makeLRuleC FF).
      LLtensor [⌊ t_ccon FF ⌋]  (⌞ L ⌟ ++ ⌜ L' ⌝)... 
      simpl. solveLL.
  + LLtheory (RINIT F).
      inversion H.
     apply ooth_init.
     inversion isFL2...
     LLtensor [⌈ F ⌉] [⌊ F ⌋] ;solveLL.
  + LLtheory (makeRRuleU CNEG F).  
      apply ooth_rules .
     constructor.
     inversion isFL2...
     LLtensor [ ⌈ ¬' F ⌉] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
   simpl in IHHM. 
   apply IHHM...
   inversion isFL2...
  inversion H1... inversion H...
  + LLtheory (makeLRuleU CNEG F).  
      apply ooth_rules .
     constructor.
     inversion isFL1...
     LLtensor [⌊ ¬' F ⌋] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
   simpl in IHHM.
   LLPerm   (⌞ L ⌟ ++ ⌈ F ⌉ :: ⌜ R ⌝).
   apply IHHM...
   inversion isFL1...
  inversion H1... inversion H...

  + simpl in IHHM1,IHHM2...
     LLtheory (makeRRuleB AND F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ∧'  G ⌉] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
   LLPerm (⌞ L ⌟ ++ ⌈ F ⌉:: ⌜ R ⌝).
   apply IHHM1...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
   LLPerm (⌞ L ⌟ ++ ⌈ G ⌉ :: ⌜ R ⌝).
   apply IHHM2...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeLRuleB AND F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ∧'  G ⌋ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLleft. solveLL.
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeLRuleB AND F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ∧'  G ⌋ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLright. solveLL.
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeRRuleB OR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ∨' G ⌉ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLleft. solveLL. 
    LLPerm ((⌞ L ⌟ ++ ⌈ F ⌉ :: ⌜ R ⌝) ).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeRRuleB OR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ∨' G ⌉ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLright. solveLL. 
    LLPerm ((⌞ L ⌟ ++ ⌈ G ⌉ :: ⌜ R ⌝) ).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB OR F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ∨' G ⌋] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
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
     LLtheory (makeRRuleB IMP F G). 
    apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ⇒' G ⌉] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL.
   LLPerm((⌊ F ⌋ :: ⌞ L ⌟ ++ ⌈ G ⌉ :: ⌜ R ⌝)).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB IMP F G). 
    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ⇒' G ⌋] (⌞ L1 ++ L2 ⌟ ++ ⌜ R1 ++ R2 ⌝) ;solveLL.
   simpl. 
    LLtensor (⌞ L1 ⌟ ++  ⌜ R1 ⌝) (⌞L2 ⌟ ++ ⌜ R2 ⌝);solveLL.
    rewrite LEncodeApp, REncodeApp...
   LLPerm((⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌜ R1 ⌝) ).
   apply IHHM1...
   inversion isFL1...
  inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
   apply IHHM2...
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
  +  LLtheory (NEG F ). inversion H. 
       apply ooth_strneg.
    constructor. inversion isFL2...
      LLtensor  [ ⌈ F ⌉ ]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.
      apply weakening. 
     apply IHHM...
  +  LLtheory (POS F ). inversion H. 
       apply ooth_strpos.
    constructor. inversion isFL1...
      LLtensor  [⌊ F ⌋]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.
      apply weakening. 
     apply IHHM...
  +  LLtheory (NEG F ). inversion H. 
       apply ooth_strneg.
    constructor. inversion isFL2...
      LLtensor  [⌈ F ⌉]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.

      eapply AbsorptionClassic' with (F:=⌈ F ⌉)...
      eapply AbsorptionClassic' with (F:=⌈ F ⌉)...
      apply weakening;simpl;solveLL...
      simpl in IHHM... 
      LLPerm( (⌞ L ⌟ ++ ⌈ F ⌉ :: ⌈ F ⌉ :: ⌜ R ⌝)).
      apply IHHM...
      inversion isFL2...
  +  LLtheory (POS F ). inversion H. 
       apply ooth_strpos.
    constructor. inversion isFL1...
      LLtensor  [⌊ F ⌋ ]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.

      eapply AbsorptionClassic' with (F:=⌊ F ⌋ )...
      eapply AbsorptionClassic' with (F:=⌊ F ⌋ )...
      apply weakening;simpl;solveLL...
      simpl in IHHM... 
      apply IHHM...
      inversion isFL1...
Qed.

Require Import LL.Framework.SL.FLL.Reasoning.
  

Ltac LKPerm LI :=
  match goal with
  | [ |- LKSeq _ _ ] =>
          first[ apply LKExL with (L1' := LI);[perm|]
               | apply LKExR with (L2' := LI);[perm|]]
end.


(** LL (LK) -> LK  *)
Theorem CompletenessFLL: forall x L1 L2 R1 R2, 
        isOLFormulaL L1 -> isOLFormulaL L2 ->
        isOLFormulaL R1 ->  isOLFormulaL R2 ->                      
   FLLN (OLTheory PN) x ((LEncode R1) ++  (REncode R2))  ( (LEncode L1) ++  (REncode L2)) (UP []) ->
                 LKSeq (P:=wnc)  (L1++R1) (L2++R2).
Proof with sauto;try solveLL; try OLSolve.
  induction x using lt_wf_ind; intros *.  
  intros HisL1 HisL2  HisR1 HisR2 Hseq. 
  inversion Hseq...
 cut(False);intros...
 refine (onlyAtomsLinear _ H0 H1)...
 apply isOLLEncode... 
 apply isOLREncode...
 apply onlyAtomsClassical in H1...
 apply isOLLEncode... 
 apply isOLREncode...
  inversion H1...
  inversion H3...
  + apply FocusingClause in H2...
      apply checkEncodeCasesU in H7...
      apply OLInPermutation' in H2...
      rewrite H2... rewrite <- app_comm_cons...
      destruct C... 
      simpl in H8. inversion H8...
      apply upRight in H7.
      apply OLInPermutation in H7...
      rewrite H7. 
      rewrite <- Permutation_middle...
      destruct C... 
      simpl in H8. inversion H8...
  + apply FocusingClause in H2...
      apply checkEncodeCasesD in H7...
      apply OLInPermutationL' in H2...
      rewrite H2... rewrite <- app_comm_cons...
      destruct C...
      simpl in H8. inversion H8...
      apply downLeft in H7. 
      apply OLInPermutationL in H7...
      rewrite H7. 
      rewrite <- Permutation_middle...
      destruct C... 
      simpl in H8. inversion H8...
  + apply FocusingClause in H2...
      apply checkEncodeCasesU in H7...
      apply OLInPermutation' in H2...
      rewrite H2... rewrite <- app_comm_cons...
      destruct C...
      simpl in H8. 
      apply LKNegR. rewrite app_comm_cons...
      invTri H8. invTri H12.
      eapply H with (m:=n0)...
      inversion H4... inversion H6...
      LLExact H13. 
      rewrite <- H5...
      apply upRight in H7.
      apply OLInPermutation in H7...
      rewrite H7. 
      rewrite <- Permutation_middle...
      destruct C...
      simpl in H8. 
      apply LKCR.
      apply LKNegR. 
      rewrite (Permutation_middle L2)...
      rewrite <-  H7. 
      invTri H8. invTri H11.
     rewrite app_comm_cons.
      eapply H with (m:=n0)...
      inversion H4... inversion H2...
  + apply FocusingClause in H2...
      apply checkEncodeCasesD in H7...
      apply OLInPermutationL' in H2...
      rewrite H2... rewrite <- app_comm_cons...
      destruct C...
      simpl in H8. 
      apply LKNegL. 
      invTri H8. invTri H12. rewrite app_comm_cons.
      eapply H with (m:=n0)...
      inversion H4... inversion H6...
      LLExact H13. 
      rewrite <- H5...
     apply downLeft in H7. 
      apply OLInPermutationL in H7...
      rewrite H7. 
      rewrite <- Permutation_middle...
      destruct C...
      simpl in H8. 
      apply LKCL.
      apply LKNegL. 
      rewrite (Permutation_middle L1)...
      rewrite <-  H7. 
      invTri H8. invTri H11.
     rewrite app_comm_cons.
      eapply H with (m:=n0)...
      inversion H4... inversion H2...
      LLExact H12. simpl... 
  + apply FocusingClause in H2...
      apply checkEncodeCasesU in H7...
      apply OLInPermutation' in H2...
      rewrite H2...
      destruct C...
      -
      simpl in H8. rewrite <- app_comm_cons...
      apply LKAndR. 
      invTri H8. invTri H12. 
      invTri H11. rewrite app_comm_cons. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL2...
      LLExact H13. 
      rewrite <- H5...
      invTri H8. invTri H12. 
      invTri H14. rewrite app_comm_cons.
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL2...
      LLExact H13. 
      rewrite <- H5...
      -
      simpl in H8. rewrite <- app_comm_cons.
      invTri H8.  
      apply LKOrR1. 
      invTri H11. invTri H12. rewrite app_comm_cons. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL2...
      LLExact H13. 
      rewrite <- H5...
      apply LKOrR2. 
      invTri H11. invTri H12. rewrite app_comm_cons. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL2...
      LLExact H13. 
      rewrite <- H5...
      -
      simpl in H8. rewrite <- app_comm_cons. 
      apply LKImpR. rewrite !app_comm_cons.
       
      invTri H8. invTri H12. 
      invTri H10. invTri H13. 
      eapply H with (m:=n0)...
      inversion H4... inversion H6...
      inversion H4... inversion H6...
      rewrite H2 in HisL2...
      LLExact H12. 
      rewrite <- H5...
      -
      apply upRight in H7.
      apply OLInPermutation in H7...
      rewrite H7. 
      rewrite <- Permutation_middle...
      destruct C...
      { simpl in H8. 
        apply LKCR.
        apply LKAndR. 
        rewrite (Permutation_middle L2)...
        rewrite <-  H7.
        invTri H8. invTri H11. 
        invTri H10. rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...
        LLExact H12. simpl...
        rewrite (Permutation_middle L2)...
        rewrite <-  H7.
        invTri H8. invTri H11. 
        invTri H13. rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...
        LLExact H12. simpl... }
      { simpl in H8. 
        invTri H8. 
        apply LKCR.
        apply LKOrR1. 
        rewrite (Permutation_middle L2)...
        rewrite <-  H7.
        invTri H10. invTri H11. 
        rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...
        LLExact H12. simpl...
        apply LKCR.
        apply LKOrR2. 
        rewrite (Permutation_middle L2)...
        rewrite <-  H7.
        invTri H10. invTri H11. 
        rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...
        LLExact H12. simpl... }
       { simpl in H8. 
        apply LKCR.
        apply LKImpR. 
        rewrite (Permutation_middle L2)...
        rewrite <-  H7.
        invTri H8. invTri H11. 
        invTri H9. invTri H12. rewrite !app_comm_cons. 
        eapply H with (m:=n0)...
        inversion H4... inversion H2...
        inversion H4... inversion H2...
        LLExact H11. simpl... }
  + apply FocusingClause in H2...
      apply checkEncodeCasesD in H7...
      apply OLInPermutationL' in H2...
      rewrite H2...
      destruct C...
      -
      simpl in H8. 
      invTri H8. rewrite <- app_comm_cons.  
      apply LKAndL1. rewrite app_comm_cons. 
      invTri H11. invTri H12. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL1...
      LLExact H13. 
      rewrite <- H5... rewrite <- app_comm_cons.
      apply LKAndL2. rewrite app_comm_cons. 
      invTri H11. invTri H12. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL1...
      LLExact H13. 
      rewrite <- H5...
      -
      simpl in H8. rewrite <- app_comm_cons. 
      apply LKOrL. 
      invTri H8. invTri H12. 
      invTri H11. rewrite app_comm_cons. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL1...
      LLExact H13. 
      rewrite <- H5...
      invTri H8. invTri H12. 
      invTri H14. rewrite app_comm_cons. 
      eapply H with (m:=n)...
      inversion H4... inversion H6...
      rewrite H2 in HisL1...
      LLExact H13. 
      rewrite <- H5...
      -
      simpl in H8.
      invTri H8. 
      invTri H13. invTri H14.
      invTri H12. invTri H13.
      rewrite H9 in H5.
      apply destructEncode in H5...
      rewrite H7, H11. rewrite  !app_comm_cons.
      apply GenLKCR_rev. 
      apply GenLKCL_rev.
      LKPerm ((x2 ++ R2) ++ (x4++R2)).
      LKPerm (F0 ⇒' G :: (x ++ R1) ++ (x3++R1)).

      apply LKImpL. 1-2:rewrite app_comm_cons. 
      1-2: eapply H with (m:=n)...
      rewrite H7 in H2. 
      rewrite H2 in HisL1... inversion HisL1...
      inversion H4... inversion H5...
      rewrite H11 in HisL2...  
      rewrite H7 in H2. 
      rewrite H2 in HisL1... inversion HisL1...
      LLExact H15. rewrite H6...
      inversion H4... inversion H5...
      rewrite H7 in H2. 
      rewrite H2 in HisL1... inversion HisL1...
      LLExact H14. rewrite H8...
      -
      apply downLeft in H7.
      apply OLInPermutationL in H7...
      rewrite H7. 
      rewrite <- Permutation_middle...
      destruct C...
      { simpl in H8. 
        invTri H8. 
        apply LKCL.
        apply LKAndL1. 
        rewrite (Permutation_middle L1)...
        rewrite <-  H7.
        invTri H10. invTri H11. 
        rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...
        apply LKCL.
        apply LKAndL2. 
        rewrite (Permutation_middle L1)...
        rewrite <-  H7.
        invTri H10. invTri H11. 
        rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...  }
      { simpl in H8. 
        apply LKCL.
        apply LKOrL. 
        rewrite (Permutation_middle L1)...
        rewrite <-  H7.
        invTri H8. invTri H11. 
        invTri H10. rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...
        rewrite (Permutation_middle L1)...
        rewrite <-  H7.
        invTri H8. invTri H11. 
        invTri H13. rewrite app_comm_cons. 
        eapply H with (m:=n)...
        inversion H4... inversion H2...  }
       { simpl in H8.
        invTri H8. invTri H12. 
        invTri H13. invTri H11.
        invTri H12.
        apply destructEncode in H6...
         apply LKCL.
        rewrite (Permutation_middle L1)...
        rewrite <-  H7. rewrite app_comm_cons.
       apply GenLKCR_rev. 
       apply GenLKCL_rev.
       rewrite H5, H10.
      LKPerm ((x1 ++ R2) ++ (x3++R2)).
      LKPerm (F0 ⇒' G :: (x ++ R1) ++ (x2++R1)).
        apply LKImpL. 
       1-2: rewrite !app_comm_cons. 
        1-2: eapply H with (m:=n)...
        inversion H4... inversion H6...
        rewrite H5 in HisL1... 
       LLExact H14. rewrite H2... 
        inversion H4... inversion H6...
        rewrite H5 in HisL1... 
       LLExact H13. rewrite H8... }
  + destruct C. 
  + destruct C. 
  + apply FocusingInitRuleU in H2...
     - simpl in H4. 
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
     apply GenLKWL_rev. apply GenLKWR_rev.
      rewrite H4, H5... 
     - apply downLeft in H6. 
       apply OLInPermutationL in H6...
       apply GenLKWL.  
       assert(L2 = [OO]).
      eapply MapREncodeEqual...  apply GenLKWR_rev.
      rewrite H2, H6...
      LKPerm ([OO]++x). apply GenLKWL_rev...
     - assert(  In (⌈ OO ⌉) (⌞ L1 ⌟) ). 
       rewrite H5...
       apply  NoUinL in H2...
     - assert(  In (⌊ OO ⌋)  (⌜ L2 ⌝ ) ). 
       rewrite H7...
       apply  NoDinR in H2...
     - apply upRight in H6. 
       apply OLInPermutation in H6...
       apply GenLKWL_rev.  
       assert(L1 = [OO]).
      eapply MapLEncodeEqual...  apply GenLKWR.
      rewrite H2, H6...
      LKPerm ([OO]++x). apply GenLKWR_rev...
     - apply upRight in H5. 
       apply OLInPermutation in H5...
       apply downLeft in H4. 
       apply OLInPermutationL in H4...
       apply GenLKWL.  apply GenLKWR.  
       rewrite H5, H4...
      LKPerm ([OO]++x). LKPerm ([OO]++x0). apply GenLKWR_rev...
     apply GenLKWL_rev...
  + apply FocusingClause in H2...
     - apply checkEncodeCasesD in H6...
        apply OLInPermutationL' in H2...
        rewrite H2...
        invTri H7. invTri H11.
        LKPerm(x1 ++ (OO::R1)) .
        eapply H with (m:=n0)...
        LLExact H9.
     - apply downLeft in H6...
        apply OLInPermutationL in H6...
        rewrite H6...
        invTri H7. invTri H10.
        LKPerm(OO::L1++x0).
        apply LKCL. 
        rewrite (Permutation_middle L1)...
        rewrite <-  H6. rewrite (Permutation_middle L1)...
         eapply H with (m:=n0)...
  + apply FocusingClause in H2...
     - apply checkEncodeCasesU in H6...
        apply OLInPermutation' in H2...
        rewrite H2...
        invTri H7. invTri H11.
        LKPerm(x1 ++ (OO::R2)) .
        eapply H with (m:=n0)...
        LLExact H9. simpl... 
     - apply upRight in H6...
        apply OLInPermutation in H6...
        rewrite H6...
        invTri H7. invTri H10.
        LKPerm(OO::L2++x0).
        apply LKCR. 
        rewrite (Permutation_middle L2)...
        rewrite <-  H6. rewrite (Permutation_middle L2)...
         eapply H with (m:=n0)...
        LLExact H8. simpl...
 Qed.

(** LK+CUT -> LL(LK) *)
Theorem SoundenessCFLL: forall n L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                  LKSeq (P:=wc n) L1 L2 -> 
                     FLLS (OLTheoryCut PN n) []  ( (LEncode L1) ++  (REncode L2)) (UP []).
Proof with sauto; try solveLL; try OLSolve. 
    intros *. 
    intros isFL1 isFL2 HM.
   induction HM;simpl...
   + LLtheory (makeRRuleC TT).
      LLtensor [⌈ t_ccon TT ⌉]  (⌞ L ⌟ ++ ⌜ L' ⌝)... 
      simpl. solveLL.
   + LLtheory (makeLRuleC FF).
      LLtensor [⌊ t_ccon FF ⌋]  (⌞ L ⌟ ++ ⌜ L' ⌝)... 
      simpl. solveLL.

  +  LLtheory (RINIT F).
      inversion H.
     apply oothc_theory.
     apply ooth_init.
     inversion isFL2...
     LLtensor [⌈ F ⌉] [⌊ F ⌋] ;solveLL.
  + LLtheory (makeRRuleU CNEG F).  
     apply oothc_theory. apply ooth_rules .
     constructor.
     inversion isFL2...
     LLtensor [ ⌈ ¬' F ⌉] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
   simpl in IHHM. 
   apply IHHM...
   inversion isFL2...
  inversion H1... inversion H...
  + LLtheory (makeLRuleU CNEG F).  
     apply oothc_theory.  apply ooth_rules .
     constructor.
     inversion isFL1...
     LLtensor [⌊ ¬' F ⌋] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
   simpl in IHHM.
   LLPerm   (⌞ L ⌟ ++ ⌈ F ⌉ :: ⌜ R ⌝).
   apply IHHM...
   inversion isFL1...
  inversion H1... inversion H...
+ simpl in IHHM1,IHHM2...
     LLtheory (makeRRuleB AND F G). 
   apply oothc_theory.  apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ∧'  G ⌉] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
   LLPerm (⌞ L ⌟ ++ ⌈ F ⌉:: ⌜ R ⌝).
   apply IHHM1...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
   LLPerm (⌞ L ⌟ ++ ⌈ G ⌉ :: ⌜ R ⌝).
   apply IHHM2...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeLRuleB AND F G). 
  apply oothc_theory.   apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ∧'  G ⌋ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLleft. solveLL.
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeLRuleB AND F G). 
apply oothc_theory.     apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ∧'  G ⌋ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLright. solveLL.
   apply IHHM...
   inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
  + simpl in IHHM...
     LLtheory (makeRRuleB OR F G). 
    apply oothc_theory. apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ∨' G ⌉ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLleft. solveLL. 
    LLPerm ((⌞ L ⌟ ++ ⌈ F ⌉ :: ⌜ R ⌝) ).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM...
     LLtheory (makeRRuleB OR F G). 
   apply oothc_theory.  apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ∨' G ⌉ ] (⌞ L⌟ ++ ⌜ R⌝) ;solveLL.
   simpl;solveLL.
    LLright. solveLL. 
    LLPerm ((⌞ L ⌟ ++ ⌈ G ⌉ :: ⌜ R ⌝) ).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB OR F G). 
 apply oothc_theory.    apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ∨' G ⌋] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL. 
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
     LLtheory (makeRRuleB IMP F G). 
apply oothc_theory.     apply ooth_rules .
    constructor.
    inversion isFL2...
     LLtensor [⌈ F ⇒' G ⌉] (⌞ L ⌟ ++ ⌜ R ⌝) ;solveLL.
   simpl. solveLL.
   LLPerm((⌊ F ⌋ :: ⌞ L ⌟ ++ ⌈ G ⌉ :: ⌜ R ⌝)).
   apply IHHM...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  inversion H1...
  inversion H...
   inversion isFL2...
  + simpl in IHHM1,IHHM2...
     LLtheory (makeLRuleB IMP F G). 
   apply oothc_theory.  apply ooth_rules .
    constructor.
    inversion isFL1...
     LLtensor [⌊ F ⇒' G ⌋] (⌞ L1 ++ L2 ⌟ ++ ⌜ R1 ++ R2 ⌝) ;solveLL.
   simpl. 
    LLtensor (⌞ L1 ⌟ ++  ⌜ R1 ⌝) (⌞L2 ⌟ ++ ⌜ R2 ⌝);solveLL.
    rewrite LEncodeApp, REncodeApp...
   LLPerm((⌞ L1 ⌟ ++ ⌈ F ⌉ :: ⌜ R1 ⌝) ).
   apply IHHM1...
   inversion isFL1...
  inversion isFL1...
  inversion H1...
  inversion H...
   inversion isFL1...
   apply IHHM2...
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
  +  LLtheory (NEG F ). inversion H. 
   apply oothc_theory.     apply ooth_strneg.
    constructor. inversion isFL2...
      LLtensor  [ ⌈ F ⌉ ]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.
      apply weakening. 
     apply IHHM...
  +  LLtheory (POS F ). inversion H. 
   apply oothc_theory.     apply ooth_strpos.
    constructor. inversion isFL1...
      LLtensor  [⌊ F ⌋]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.
      apply weakening. 
     apply IHHM...
  +  LLtheory (NEG F ). inversion H. 
  apply oothc_theory.      apply ooth_strneg.
    constructor. inversion isFL2...
      LLtensor  [⌈ F ⌉]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.

      eapply AbsorptionClassic' with (F:=⌈ F ⌉)...
      eapply AbsorptionClassic' with (F:=⌈ F ⌉)...
      apply weakening;simpl;solveLL...
      simpl in IHHM... 
      LLPerm( (⌞ L ⌟ ++ ⌈ F ⌉ :: ⌈ F ⌉ :: ⌜ R ⌝)).
      apply IHHM...
      inversion isFL2...
  +  LLtheory (POS F ). inversion H. 
    apply oothc_theory.    apply ooth_strpos.
    constructor. inversion isFL1...
      LLtensor  [⌊ F ⌋ ]   (⌞ L ⌟ ++ ⌜ R ⌝);solveLL.

      eapply AbsorptionClassic' with (F:=⌊ F ⌋ )...
      eapply AbsorptionClassic' with (F:=⌊ F ⌋ )...
      apply weakening;simpl;solveLL...
      simpl in IHHM... 
      apply IHHM...
      inversion isFL1...
 + simpl in IHHM1,IHHM2...
     LLtheory (RCUT F).
     inversion H1.
    eapply oothc_cutn.
    eapply ctn with (m:=n)... firstorder.
    LLtensor ( ⌞ L2 ⌟ ++ ⌜ R2 ⌝) (⌞ L1 ⌟ ++ ⌜ R1 ⌝) .
    rewrite LEncodeApp, REncodeApp...
    1-2: solveLL.
   
    LLPerm (⌞ L2 ⌟ ++ ⌈ F ⌉ :: ⌜ R2 ⌝).
    apply IHHM2...
   inversion isFL2...
    apply IHHM1...
   inversion isFL2...
  Qed.

Theorem SoundenessCFLL': forall x L1 L2 R1 R2, 
              isOLFormulaL L1 -> isOLFormulaL L2 ->
                 isOLFormulaL R1 ->  isOLFormulaL R2 ->
                  LKSeq (P:=wc x) (L1++R1) (L2++R2) ->
                     FLLS (OLTheoryCut PN x)  ((LEncode R1) ++  (REncode R2))  ( (LEncode L1) ++  (REncode L2)) (UP []).
Proof with sauto.
   intros .
   apply SoundenessCFLL in H3...
   apply AbsorptionLSet'.
   LLPerm (⌜ R2 ⌝ ++ []). apply AbsorptionLSet'.
   LLExact H3. rewrite LEncodeApp, REncodeApp...
  1-2: apply Forall_app...
Qed. 

 Theorem CutElimLK: forall x L1 L2, 
                            isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                  LKSeq (P:=wc x) L1 L2 -> LKSeq (P:=wnc) L1 L2.
Proof with sauto.
 intros.
 assert(exists R1 R2, Permutation L1 (R1++R2)).
 eexists []. eexists L1... 
 assert(exists R1 R2, Permutation L2 (R1++R2)).
 eexists []. eexists L2... 
  CleanContext. 
 rewrite H2, H3 in H1.  
assert(isOLFormulaL x0 /\ isOLFormulaL x1 /\ isOLFormulaL x2 /\ isOLFormulaL x3)...
rewrite H3 in  H0; OLSolve.
rewrite H3 in  H0; OLSolve.
rewrite H2 in  H; OLSolve.
 rewrite H2 in  H; OLSolve.
 
apply  SoundenessCFLL' in H1...
 
 specialize(OLCutElimination  wellTheoryLK CutCoherenceLK);intros.
 apply H4 in H1... all: try clear H4.
2,3: apply Forall_app...
2,4: apply isOLLEncode...
2,3: apply isOLREncode...
  apply FLLStoFLLN in H1...
eapply CompletenessFLL  in H1... 
rewrite H2, H3...  
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

 Theorem CutAdmLK: forall F L1 L2 R1 R2, 
      isOLFormulaL L1 ->  isOLFormulaL L2 -> isOLFormulaL R1 ->  isOLFormulaL R2 ->  isOLFormula F -> 
LKSeq (P:=wnc) (F::L1) R1 -> LKSeq (P:=wnc) L2 (F::R2) -> LKSeq (P:=wnc) (L1++L2) (R1++R2).
Proof with sauto.
intros. pose proof ( OLFormulaLeng H3)...
 eapply CutElimLK... 
1-2: apply Forall_app...
eapply LKCut with (F:=F). exact H6. auto.
1-2: apply SoundnessLK...
Unshelve.
eauto.
Qed.


   
