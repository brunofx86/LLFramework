
(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export LL.Misc.Utils. 
Require Export LL.Misc.Permutations. 
Require Export LL.Framework.SL.SELLF.PreTactics.
Require Import Coq.Program.Equality.

Export ListNotations.
Export LLNotations .
Set Implicit Arguments.


Section FLLBasicTheory.
  Context `{SI : SigSELL}.
  Context `{OLS: OLSig}.

  Section StructuralProperties.
    Variable theory : oo -> Prop. (* Theory Definition *)
    
    Notation " n '|-F-' B ';' L ';' X " := (seqN theory n B L X)  (at level 80).
    Hint Constructors seqN : core .
    Notation " '|-f-' B ';' L ';' X " := (seq theory B L X)  (at level 80).
     
    Hint Constructors seqN : core.
    Hint Constructors seq : core.
   
 Theorem WeakTheoryN : forall n CC LC X (th th':oo->Prop),
        (forall F, th F -> th' F) ->
        (seqN th n CC LC X -> seqN th' n CC LC X).
    Proof with sauto.    
      induction n using lt_wf_ind. 
     intros...
     inversion H1; subst. 
     
     1-20: eauto using H.
     LLWith.
     1-2: eauto using H.
     LLTensor M N B C D .
     1-2: eauto using H.
     Qed.
     
  (**************** Exchange Rules ****************)
      
 Theorem exchangeLCN : forall n CC LC LC'  (X: Arrow),
        Permutation LC LC' ->
        (n |-F- CC ; LC ; X) -> n |-F- CC ; LC' ; X.
    Proof with sauto;solveLL.
      induction n using strongind;intros.
      + inversion H0 ...
      + inversion H1...
         1-12: eauto. 
         LFocus F L'...
         1-3: eauto.
      Qed.

  Theorem exchangeLC LC : forall CC LC'  (X: Arrow),
        Permutation LC LC' ->
        ( |-f- CC ; LC ; X) -> |-f- CC ; LC' ; X.
    Proof with sauto;solveLL.
    intros.
    revert dependent LC'.
    induction H0;intros...
    * LLTensor M N B C D.
    * LLExists t.   
    * LFocus F L'. 
    * UFocus i F.
    * BFocus i F. sauto.
    * TFocus F.
  Qed.  
    
 
 Lemma exchangeCCN : forall n CC CC' D (X:Arrow),
        Permutation CC CC' ->
        n |-F- CC ; D ; X ->
        n |-F- CC' ; D ; X.
  Proof with sauto.
  intro.
  induction n using strongind;intros.
  * inversion H0...
    - srewrite H in H1...
    - srewrite H in H2...
      solveLL.
    - srewrite H in H1... 
  * inversion H1...
    2-14: eauto using Permutation_in.
    4-9: eauto using Permutation_in.
    srewrite H0 in H2...
    init2 i C.
    srewrite H0 in H2...
    solveLL.
    assert(Permutation (getLtX a CC) (getLtX a CC')).
    rewrite H0...
    rewrite <- H0...
    eapply H.
    3: exact H4.
    all:eauto.
    rewrite H0...
    BFocus i F B'...
   Qed.
 
 Lemma exchangeCC : forall CC CC' D (X:Arrow),
        Permutation CC CC' ->
        |-f- CC ; D ; X ->
        |-f- CC' ; D ; X.
  Proof with sauto.
  intros *.
  intros Hp Hseq.
  generalize dependent CC'.
  induction Hseq;intros...
  srewrite Hp in H...
  srewrite Hp in H0. solveLL.
  srewrite Hp in H...
  srewrite Hp in H...
  try rewrite Hp in *...
  LLTensor M N B C D.
  eauto using Permutation_in. 
  eauto using Permutation_in. 
  eapply tri_bang'...
  rewrite <- Hp...
  eapply IHHseq.
  rewrite Hp...
  eauto using Permutation_in. 
  eauto using Permutation_in.
  eauto using Permutation_in.
  BFocus i F B'...
  eauto using Permutation_in.
 Qed. 
   
  Global Instance seq_morphismN  n:
      Proper ((@Permutation TypedFormula) ==> (@Permutation oo) ==> eq ==> iff)
             (seqN theory n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCCN H _);auto.
         refine (exchangeLCN H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCCN H _);auto.
        refine (exchangeLCN H0 _);auto.
    Qed.
   
   Global Instance seq_morphism  :
      Proper ((@Permutation TypedFormula) ==> (@Permutation oo) ==> eq ==> iff)
             (seq theory).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCC H _);auto.
         refine (exchangeLC H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCC H _);auto.
        refine (exchangeLC H0 _);auto.
    Qed.
    
  (**************** End Exchange Rules ****************)
   
  (** We can generalize the exponential phase in order to 
     avoid mutual induction *)  
  
  Ltac classic_or_linear sub :=
    destruct(uDec sub);simplSignature. 
    
    
 Theorem BangUnb n i BD M P: 
    u i = true -> n |-F- BD; M ; DW (Bang i P) -> SetU BD.
 Proof with sauto.
 intros.   
 inversion H0... 
 2: inversion H2.
 apply getUtoSetU'.
 symmetry.
 eapply bangUnb with (i:=i)... Qed.
    
 Theorem BangUnb' i BD M P: 
    u i = true -> |-f- BD; M ; DW (Bang i P) -> SetU BD.
 Proof with sauto.
 intros.   
 inversion H0... 2: inversion H2.
 apply getUtoSetU'.
 symmetry.
 eapply bangUnb with (i:=i)...
 Qed.
 
(* Soundness using inversion lemma of bang *)   
Lemma seqNtoSeq : forall n B C X,
    seqN theory n B C X -> seq theory B C X.
     Proof with sauto. 
      induction n using strongind;intros;eauto.
      + inversion H... eauto.
      + inversion H0... 
        1- 17: eauto.  
  Qed.
  
     Lemma HeightGeq : forall n B O (X:Arrow),
        seqN theory n B O X ->
        forall m, m>=n -> seqN theory m B O X.
    Proof with sauto;solveLL.
     intro.
      induction n;intros. 
      + inversion H ...
      + inversion H;subst; try mgt0. 
       1-4: eauto.
        1-5: intuition;eauto using Hp...
         (* LLTensor *)
         LLTensor M N B0 C D. 
         eapply IHn;try lia ...
         eapply IHn;try lia ...
         1-2: intuition;eauto using Hp...
        LLExists t;eauto;eapply IHn;try lia...
       1-3:   intuition;eauto using Hp...
      (* dec *)
        LFocus F;eauto;eapply IHn;try lia...
        UFocus i F;eauto;eapply IHn;try lia...
        BFocus i F;eauto;eapply IHn;try lia...
        TFocus F;eauto;eapply IHn;try lia...
     Qed. 
     
     
    (** HeightGeq with Exchange Classic Context *)
    Theorem HeightGeqCEx : forall n CC LC CC' X, 
        Permutation CC' CC ->
        (seqN theory n  CC LC X) ->
        forall m, m>=n -> (seqN theory m  CC' LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      eapply exchangeCCN;eauto.
    Qed.

    (** HeightGeq with Exchange Linear Context *)
    Theorem HeightGeqLEx : forall n CC LC LC' X, 
        Permutation LC LC' ->
        (seqN theory n  CC LC' X) ->
        forall m, m>=n -> (seqN theory m  CC LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      eapply exchangeLCN;eauto.
    Qed.  
    
   Theorem HeightGeqEx : forall n CC CC' LC LC' X, 
        Permutation CC CC' ->
        Permutation LC LC' ->
        (seqN theory n CC' LC' X) ->
        forall m, m>=n -> (seqN theory m CC LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      symmetry in H0.
      eapply exchangeLCN;eauto.
      eapply exchangeCCN;eauto.
    Qed.  
 
  (**  Weakening using inversion lemma of bang *)
  Theorem weakeningN : forall n CC LC F X ,
      u (fst F) = true -> n |-F- CC ; LC ; X -> n |-F- F :: CC ; LC ; X.
   Proof with sauto;try solveLL.
    induction n using strongind;intros.
    * inversion H0...
       init2 i (F::C).
       rewrite <- H2...
    * inversion H1...
       init2 i (F::C).
       rewrite <- H3...
      LLTensor M N (F::B) C D...
      rewrite H4...
      rewrite <- app_comm_cons...
      rewrite <- app_comm_cons... 
      eapply exchangeCCN with (CC:=F::(i,F0)::CC)...

      3-4: eauto using Permutation_in. 
      4:{ BFocus i F0 (F::B')...
            rewrite <- H5... }
      destruct F.
      simpl in *...
      destruct F.
      simpl in *...
      destruct (lt_dec a s)...
     UFocus i F0.
      TFocus F0.
   Qed.    
     
    Theorem weakeningGenN CC LC  CC' X n:
      n |-F- CC ; LC ; X -> SetU CC' -> n |-F- CC'++ CC ; LC ; X.
    Proof.
      intros.
      induction CC';simpl;intros;auto.
      destruct a.
      apply weakeningN ;sauto.
      solveSE.
      apply IHCC'. solveSE.
    Qed.

    Theorem weakeningGenN_rev CC LC CC' X n:
      n |-F- CC ; LC ; X -> SetU CC' -> n |-F- CC++ CC' ; LC ; X.
    Proof.  
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
    Qed.
  
  
 
   
  Axiom seqtoSeqN : forall D O X, 
        seq theory  D O X -> exists n, (seqN theory n D O X).
  
    (**  Weakening on the classical context *)  
     Lemma weakening : forall CC LC F X ,
     u (fst F) = true -> |-f- CC ; LC ; X ->  |-f- F :: CC ; LC ; X.
    Proof with sauto;try solveLL.
    intros.
    revert dependent F.
    induction H0;intros...
    init2 i (F::C).
    rewrite <- H0...
    * LLTensor M N (F0::B) C D... 
         rewrite H0...
     rewrite <- app_comm_cons...
     rewrite <- app_comm_cons... 
    * rewrite perm_swap...
    * destruct F0. 
       simpl in *...
    * destruct F0. 
       simpl in *...
       destruct (lt_dec a s)...
    * LLExists t.
    * LFocus F...
    * UFocus i F.
    * BFocus i F (F0::B'). rewrite <- H1...
    * TFocus F. 
   Qed.
   
   
    Theorem weakeningGen CC LC CC' X:
    SetU CC' -> |-f- CC ; LC ; X -> |-f- CC' ++ CC ; LC ; X.
    Proof with auto;try SLSolve. 
      induction CC';simpl;intros;auto.
      apply weakening... 
      solveSE.
      apply IHCC'...
      solveSE.
    Qed.
    
    Theorem weakeningAll CC LC X:
    SetU CC -> |-f- [] ; LC ; X -> |-f- CC ; LC ; X.
    Proof with auto. 
      intros. 
      rewrite <- (app_nil_r CC).
      apply weakeningGen...
    Qed.
    
    Theorem weakeningGen_rev CC LC CC' X :
      |-f- CC ; LC ; X -> SetU CC' -> |-f- CC++ CC' ; LC ; X.
    Proof.  
      intros.
      eapply exchangeCC with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGen;auto.
    Qed.
    

    (**  Exchange Rule: Classical Context *)
    Theorem exchangeCC' CC CC' LC (X: Arrow):
      Permutation CC CC' ->
    |-f- CC ; LC ; X -> |-f- CC' ; LC ; X.
     Proof with sauto. 
     intros.
     revert dependent CC'.
     induction H0;intros...
     * init1. rewrite <- H0... 
     * init2 i C.
     * LLOne.
       rewrite <- H0...
     * LLTensor M N B C D. 
     * LLBang. rewrite <- H1...
        eapply IHseq.
        rewrite H1...
     * LLExists t.
     * LFocus F... 
     * UFocus i F.
       rewrite <- H3... 
     * BFocus i F B'.
     * TFocus F.
    Qed.  
     
     Theorem weakeningGenSubSet CC LC CC' X:
    (exists Y, (Permutation CC' (CC++Y)) /\ SetU Y) ->
    |-f- CC ; LC ; X -> |-f- CC' ; LC ; X.
    Proof.
      intros.
      do 2 destruct H.
      assert(Permutation (x ++ CC) CC').
      rewrite H. perm.
      eapply (exchangeCC H2).
      apply weakeningGen;auto.
    Qed.
    
        Theorem weakeningGenNSubSet n CC LC CC' X:
    (exists Y, (Permutation CC' (CC++Y)) /\ SetU Y) ->
   n  |-F- CC ; LC ; X -> n |-F- CC' ; LC ; X.
    Proof.
      intros.
      do 2 destruct H.
      assert(Permutation (x ++ CC) CC').
      rewrite H. perm.
      eapply (exchangeCCN H2).
      apply weakeningGenN;auto.
    Qed. 
   
     
 Lemma lt_S n x :
  n >= S x -> n >= x.
 Proof.
    induction x;simpl;intros;
    [inversion H; lia | lia].
 Qed.
    (** Contraction on the classical context *)
   
  Lemma BangMax a n i B L P : lt a i -> 
  n |-F- B ; L ; (DW (Bang i P)) -> 
  n |-F- B ; L ; (DW (Bang a P)).
  Proof with CleanContext.
    intros.
    inversion H0... 
    LLBang. 
    pose proof (ltConv' _ _ _ H H6)...
    eapply weakeningGenNSubSet with (CC:=getLtX i B)...
    exists (getU x)...
  Qed.  
   
     Lemma BangMax' a i B L P : lt a i -> 
   |-f- B ; L ; (DW (Bang i P)) -> 
   |-f- B ; L ; (DW (Bang a P)).
  Proof with CleanContext.
    intros.
    inversion H0... 
    LLBang. 
    pose proof (ltConv' _ _ _ H H5)...
    eapply weakeningGenSubSet with (CC:=getLtX i B)...
    exists (getU x)...
  Qed.  
  
  End StructuralProperties.

  
  Definition EmptyTheory (F :oo) := False.
  Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      seqN EmptyTheory n CC LC X -> seqN theory n CC LC X.
  Proof with sauto. 
    intros.
    eapply @WeakTheoryN with (th:= EmptyTheory)...
    intros.
    inversion H0.
  Qed.
  
 
  (** Admissible rules including alternative definitions for the initial rule *)
  Section AdmissibleRules.
    Variable theory : oo -> Prop. 

Lemma Init2In th i A L (USB: USigSELL): In (i, atom A) L -> seq th L [] (DW (perp A)).
Proof with sauto.
  intros.
  apply InPermutation in H...
  init2 i x.
Qed.

 Theorem InitPosNegN : forall Gamma A, SetU Gamma ->
        seqN theory 2 Gamma [atom A ; perp A ] (UP []).
      intros.
      solveLL.
    Qed.
    
    Theorem InitPosNegDwN : forall Gamma A, SetU Gamma ->
        seqN theory 4 Gamma [perp A ] (DW (atom A)).
      intros.
      solveLL.
    Qed.

    Theorem InitPosNeg : forall Gamma A,
    SetU Gamma -> seq theory Gamma [atom A ; perp A ] (UP []).
      intros.
      solveLL. 
    Qed. 

    Theorem InitPosNeg' : forall Gamma A,
     SetU Gamma -> seq theory Gamma [perp A ; atom A ] (UP []).
      intros.
      solveLL.
    Qed.
    
  End AdmissibleRules.

  (** Some simple invertibility lemmas *)
  Section Invertibility.
    Variable theory : oo -> Prop. (* Theory Definition *)


 Theorem FocusAtomN: forall n Gamma Delta A,
        (seqN theory n Gamma Delta (DW ((perp A ) ))) ->
     SetU Gamma /\ Delta = [ (atom A)] \/ 
     (exists i C, Delta = [] /\ SetU C /\ Permutation ((i,atom A )::C) Gamma).
    Proof with subst;auto.
      intros.
      inversion H ...
      2: inversion H1. 
      right.
      exists i;exists C;firstorder.
    Qed.


  Theorem FocusAtom: forall Gamma Delta A,
        (seq theory Gamma Delta (DW ((perp A ) ))) ->
     SetU Gamma /\ Delta = [ (atom A)] \/ 
     (exists i C, Delta = [] /\ SetU C /\ Permutation ((i,atom A )::C) Gamma).
  Proof with subst;auto.
      intros.
       inversion H ...
      2: inversion H1. 
      right.
      exists i;exists C;firstorder.
    Qed. 
 
   Theorem InvUnb (SIU: USigSELL) C : SetL C -> C = []. 
   Proof with sauto.  
   intro H.
   apply Permutation_nil.
   rewrite (cxtDestruct C).
   assert(SetU C) by auto.
   rewrite (SetU_then_empty  _ H0).
   rewrite (SetL_then_empty _ H)... 
  Qed.  
  
   Theorem InvTensorNUnb (SIU: USigSELL) : forall n Gamma D F G,
   seqN theory n Gamma D (DW (MAnd F G)) ->
   exists M N, Permutation D (M++N) /\
   (seqN theory (n -1) Gamma M (DW F)) /\ 
   (seqN theory (n -1) Gamma N (DW G)).
  Proof with sauto.
  intros.
  inversion H...
  2: inversion H1. 
  exists M.
  exists N.
  split;auto.
  apply InvUnb in H5, H6...
  1-2:rewrite H3...
  Qed.
   
    Theorem InvTensorNUnb' (SIU: USigSELL) : forall n Gamma D F G,
   seqN theory n Gamma D (DW (MAnd F  G)) ->
   exists M N m, Permutation D (M++N) /\ S m <= n /\ 
   (seqN theory m Gamma M (DW F)) /\ 
   (seqN theory m Gamma N (DW G)).
  Proof with sauto.
  intros.
  inversion H...
  2: inversion H1. 
  exists M.
  exists N.
  exists n0.
  split;auto.
  split;auto.
  apply InvUnb in H5, H6...
  1-2:rewrite H3...
  
  Qed.
   
    Theorem FocusAtomTensorInvN: forall n  A F,
        (seqN theory n []  [atom A] (DW (MAnd (perp A) F))) ->
        (seqN theory (sub n  1 ) [] [] (DW (F))).
    Proof with sauto.
      intros.
      inversion H... 
      * simpl in *.
        apply FocusAtomN in H10. 
        destruct H10...
      * inversion H1.  
    Qed.   
    

    Theorem FocusAtomTensorTop: forall A B,
        (seq theory B [atom A] (DW (MAnd (perp A) Top))).
    Proof with sauto.
      intros.
      LLTensor [atom A] (@nil oo) (getU B) (getL B) (getL [])...
    Abort.
    
    Theorem FocusTopOplus1: forall F B D,
        seq theory B D (DW (AOr Top F)).
    Proof with sauto.
      intros.
      solveLL.
    Qed.  
    
    Theorem FocusTopOplus2: forall F B D,
        seq theory B D (DW (AOr F Top )).
    Proof with sauto.
      intros.
      solveLL.
    Qed.  
   
    
  End Invertibility.

  Section GeneralResults.
    Variable theory : oo -> Prop. (* Theory Definition *)
    Hint Constructors seqN : core .
    Hint Constructors seq : core . 

    
  Lemma PProp_select B D CC F : Permutation (B++ getL D)
       (F :: CC) ->  u (fst F) = true -> 
       (exists L1' : list (subexp * oo),
        Permutation B (F :: L1') /\
        Permutation (L1' ++ getL D) CC).
  Proof with sauto.
   intros.
   checkPermutationCases H.
   exists x.
   split;auto.
   apply getLPerm_SetL in H.
   assert(u (fst F) = false).   
   inversion H...
   sauto.
   apply getLPerm_SetL in H.
   assert(u (fst F) = false).   
   inversion H...
   sauto.
   Qed.   

Lemma aux_c F BD B C D : SetU B -> SetL C -> SetL D -> u (fst F) = true -> Permutation (F :: BD) (B ++ C ++ D) -> In F B.
Proof with sauto.
  intros.
  checkPermutationCases H3.
  rewrite H3...
  checkPermutationCases H3.
  rewrite H3 in H0.
  inversion H0...
  rewrite H3 in H1.
  inversion H1...
 Qed. 
   
   
  Theorem contractionN  : forall n CC LC F X,
       u (fst F) = true -> seqN theory n (F :: CC) LC X -> In F CC -> seqN theory n CC LC X. 
  Proof with CleanContext;try solveLL.
  induction n using strongind;intros. 
  * inversion H0...
     solveSE.
    checkPermutationCases H3.
    apply InPermutation in H1...
    rewrite H6 in H2.
    rewrite H1 in H2. solveSE.
    init2 i x. rewrite H5 in H2. solveSE. solveSE.
   * inversion H1;sauto;solveLL;solveSE.
     
    checkPermutationCases H4.
    apply InPermutation in H2.
    destruct H2.
    init2 i x. rewrite H7 in H3.
    rewrite H2 in H3.
    solveSE.
    solveLL. rewrite H6 in H3. solveSE.
    1-6: eauto.
    pose proof (aux_c H6 H7 H8 H0 H5).
 apply InPermutation in H3...
    assert(SetU x).
   rewrite H3 in H6.
   solveSE.
    apply InPermutation in H2...
    rewrite H3 in H5.
    rewrite H2 in H5.
    rewrite <- app_comm_cons in H5. 
   apply Permutation_cons_inv in H5;auto.
   
    LLTensor M N x C D ...
 
    pose proof (aux_c H11 H7 H8 H0 H5).
   eapply H with (F:=F)...
    rewrite app_comm_cons.
    rewrite <- H3...
     
    pose proof (aux_c H11 H7 H8 H0 H5).
   eapply H with (F:=F)...
    rewrite app_comm_cons.
    rewrite <- H3...
   
    4-8:eauto.
    apply H with (F:=F)...
      eapply exchangeCCN with (CC:=(i,F0)::F::CC)...
    
apply InPermutation in H2.
    destruct H2.
    destruct F.
    simpl in H4.
    simpl in H0...
  destruct F.
    simpl in H0, H4, H5...
    destruct (lt_dec a s)... 
    eapply H with (F:=(s, o))...
    apply InPermutation in H2...
    rewrite H2...
    simpl...
    destruct (lt_dec a s)...

inversion H6...
    UFocus i F0... 
    eapply H with (F:=(i, F0))...
    UFocus i F0...
    eapply H with (F:=F)...
    checkPermutationCases H6.
    simpl in H0...
    rewrite H6 in  H2.
    inversion H2...
    BFocus i F0 x...
    eapply H with (F:=F)...
    rewrite <- H8...
    
    all:eauto. 

   Qed.  
    
                                                                                         
 Theorem contraction  : forall CC LC F X,
     u (fst F) = true -> seq theory (F :: CC) LC X -> In F CC -> seq theory  CC LC X. 
  Proof with subst;eauto.
  intros.
  apply seqtoSeqN in H0.
  destruct H0.
  apply contractionN in H0...
  apply seqNtoSeq in H0...
 Qed.
 
  
   Theorem contractionSet  : forall CC LC X L, (forall F, In F L -> In F CC) -> SetU L ->
        ( seq theory (L ++ CC) LC X) -> (seq theory CC LC  X).
   Proof.
      intros.
      induction L.
      simpl in H0;auto.
      apply IHL;intros.
      apply H. firstorder.
      solveSE.
      eapply exchangeCC with (CC':=a :: (L ++ CC)) in H1;[|auto].
      apply contraction in H1;auto.
      solveSE.
      apply in_or_app.
      firstorder.
  Qed.  

       
     Theorem contractionSet'  : forall  C1 C2 CC LC X, Permutation CC (C1++C2) -> SetU C1 ->
        ( seq theory (C1 ++ CC) LC X) -> (seq theory CC LC  X).
   Proof with sauto.
      intro.
      induction C1;intros.
      simpl in H0;auto.
      inversion H0...
      rewrite <- app_comm_cons in H1.
      apply contraction in H1;auto.
      
      eapply IHC1 with (C2:=a::C2) in H1...
      rewrite H...
      apply in_or_app.
      right. rewrite H.
      apply in_or_app.
      left.
      firstorder.
  Qed. 
  
    Theorem contractionGetU  : forall  C CC LC X, 
        ( seq theory (getU C ++ getU C ++ CC) LC X) -> (seq theory (getU C ++ CC) LC  X).
   Proof with sauto.
      intros.
      eapply contractionSet'
      with (C1:=getU C) (C2:=CC)...
  Qed. 
  
  Theorem contractionGetU_rev  : forall  C CC LC X, 
        ( seq theory (CC ++ getU C ++ getU C) LC X) -> (seq theory (CC ++ getU C) LC  X).
   Proof with sauto.
      intros.
      eapply contractionSet'
      with (C1:=getU C) (C2:=CC)...
      eapply exchangeCC.
      2:{ exact H. }
      perm.
  Qed.
 
 
 Lemma Derivation1 D M F : 
 seq theory D M (DW F) -> seq theory D M (UP [F]).
 Proof with sauto.
 intros.
 destruct(PositiveOrNegative F).
 LLStore...
 LFocus F.  
 inversion H0;inversion H...
Qed. 
  
  Lemma InvBangTN i j B P : u i = true -> 
          seqN theory  j B [] (DW (Bang i P) ) -> seqN theory (j-1) B [] (UP [P]).
  Proof with sauto.
  intros Hu Hj.
  inversion Hj...
 2: inversion H0.
  apply bangUnb in H3...
  pose proof (cxtDestructLtX i B (getUtoSetU' _ (symmetry H3)))...
  rewrite H.
  eapply weakeningGenN_rev...
 Qed. 
 
  Lemma InvBangT i j B P : u i = true -> 
          seqN theory j B [] (DW (Bang i P)) -> seq theory B [] (UP [P]).
  Proof with sauto.
  intros Hu Hj.
  apply InvBangTN in Hj...
  apply seqNtoSeq in Hj...
 Qed. 


             
End GeneralResults.

  (** Adequacy relating the system with and without inductive meassures *)
  

  (** Weakening in the linear context when the formula belongs to the theory *)
  Section MoreWeakening.
    Variable theory : oo -> Prop .
    
    Theorem WeakLinearTheoryN : forall n CC LC F X ,
        ~ IsPositiveAtom F ->
        (seqN theory n CC (F::LC) X) -> theory F ->
        seqN theory n CC LC X.
    Proof with sauto.
      induction n;intros;subst.
      + inversion H0...
        contradict H ...
      + inversion H0... 
        - contradict H ...
        - LLPlusL.
          apply IHn with (F:=F)...
        - LLPlusR. 
          apply IHn with (F:=F)...
        - LLWith. 
          apply IHn with (F:=F)...
          apply IHn with (F:=F)...
        - LLBot.
          apply IHn with (F:=F)...
        - LLPar. 
          apply IHn with (F:=F)...
        - checkPermutationCases H3. 
          LLTensor x N B C D.
          apply IHn with (F:=F)...
          apply (exchangeLCN H3)...
          LLTensor M x B C D.
          apply IHn with (F:=F)...
          apply (exchangeLCN H3)...
        - LLStoreC.
          apply IHn with (F:=F)...
        - LLExists t.
          apply IHn with (F:=F)...
        - LLForall. 
          apply IHn with (F:=F)...
        - LLRelease.
          apply IHn with (F:=F)...
        - LLStore.
          apply IHn with (F:=F)...
          eapply (exchangeLCN (perm_swap F F0 LC))...
        - checkPermutationCases H4. 
          TFocus F.
          rewrite <- H7... 
          LFocus F0 x.
          apply IHn with (F:=F)...
          rewrite <- H6...
        - UFocus i F0. 
          apply IHn with (F:=F)...
        - BFocus i F0 B'. 
          apply IHn with (F:=F)...
        - TFocus F0. 
          apply IHn with (F:=F)...
 Qed.         
     
  Theorem WeakLinearTheory : forall CC LC F X,
        ~ IsPositiveAtom F ->
        (seq theory CC (F::LC) X) -> theory F -> seq theory CC LC X.
      intros.
      apply seqtoSeqN in H0.
      destruct H0.
      apply WeakLinearTheoryN in H0;auto.
      apply seqNtoSeq in H0;auto.
  Qed.    
 
 Lemma WeakTheory
     : forall (CC : list TypedFormula)
         (LC : list oo) (X : Arrow) (th th' : oo -> Prop),
       (forall F : oo, th F -> th' F) ->
       seq th CC LC X -> seq th' CC LC X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0...
  eapply @WeakTheoryN with (th':=th') in H0...
  apply seqNtoSeq in H0...
 Qed.

  End MoreWeakening.
End FLLBasicTheory.
