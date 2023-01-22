(** * Invertibility results for the negative phase

This file proves that exchange is admissible also in the list L in
[seq Gamma Delta (UP L)]. For that, some invertibility lemmas are
needed.
 *)
Require Export LL.SL.FLL.Tactics.
Require Import Lia.
Require Import FunInd.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Local Hint Unfold isFormulaL : core.

Section InvNPhase .
  Context `{OLS: OLSig}.

  Variable th : oo -> Prop.
  
 Theorem exp_weight0LF : forall l L, 0%nat = complexity l + complexityL L -> False.
  Proof.
    intros.
    assert(complexity l > 0%nat) by (apply Complexity0).
    lia.
  Qed. 
  
  Ltac solveComplexity :=
  match goal with
  | [H: complexityL _ = 0%nat |- _] => 
    apply ComplexityL0 in H  
  | [H: 0%nat = complexityL _ |- _] => 
    symmetry in H; apply ComplexityL0 in H
  end;sauto.
  
 Lemma EquivAuxBot :  forall CC LC M M',
  flls th CC LC (UP (M ++ M'))  ->
  flls th CC LC (UP (M ++ Bot :: M') ) .
Proof with sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    solveComplexity.
   
    destruct M as [ | a]... 
    rewrite <- app_comm_cons in H0.
    
    destruct a; simpl in *; invTri' H0 ;solveLL; 
    try repeat rewrite app_comm_cons; 
   match goal with
          |  [ |- flls _ _ _ (UP (?M ++ Bot :: _)) ] =>
             eapply H with (m:= complexityL M);simpl in *; try inversion HeqSizeM
          end...
    assert (Hvar : proper (VAR con 0%nat)) by constructor.
    generalize (ComplexityUniformEq H5 properX Hvar);intro...
  Qed.

Lemma EquivAuxWith :  forall F G CC LC M M',
  flls th CC LC (UP (M ++ [F] ++ M') ) ->
  flls th CC LC (UP (M ++ [G] ++ M') ) ->
  flls th CC LC (UP (M ++ (AAnd F G) :: M') ) .
  Proof with sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    solveComplexity.
  
    destruct M as [ | a]... 
    rewrite <- app_comm_cons in H0, H1.
    
    destruct a; simpl in *; invTri' H0 ;solveLL; 
    try repeat rewrite app_comm_cons; 
   match goal with
          |  [ |- flls _ _ _ (UP (?M ++ (AAnd _ _) :: _)) ] =>
             eapply H with (m:= complexityL M);simpl in *; try inversion HeqSizeM;InvTriAll'
          end...
    assert (Hvar : proper (VAR con 0%nat)) by constructor.
    generalize (ComplexityUniformEq H8 properX Hvar);intro...
  Qed.

Lemma EquivAuxPar : forall F G CC LC M M',
  flls th CC LC  (UP (M ++ [F ; G] ++ M') ) ->
  flls th CC LC  (UP (M ++ (MOr F G) :: M') ) .
Proof with  sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    solveComplexity.
  
    destruct M as [ | a]... 
    rewrite <- app_comm_cons in H0.
     destruct a; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons;
      match goal with
      |  [ |- flls _ _ _ (UP (?M ++ (MOr F G) :: _)) ] =>
         eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveLL;try lia
      end.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0%nat));intro...
  Qed.
  
Lemma EquivAuxStore :
    forall F CC LC M M', positiveLFormula F ->
  flls th CC  (F::LC) (UP (M ++ M') ) ->
  flls th CC  LC  (UP (M ++ F :: M') ) .
  Proof with  sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
        solveComplexity.
  
    destruct M as [ | a]... 
    rewrite <- app_comm_cons in H1.
    destruct a; simpl in *; invTri' H1;solveLL;
      repeat rewrite app_comm_cons;
      match goal with
      |  [ |- flls _ _ _ (UP (?M ++ _ :: _)) ] =>
         eapply H0 with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveLL;try lia
      end.
    LLExact H7.
     LLExact H7.
      LLExact H7.
       LLExact H7.
        LLExact H7.
         LLExact H7.
          LLExact H7.
    generalize (ComplexityUniformEq H6 properX (proper_VAR con 0%nat));intro...
    LLExact H7.
   Qed.
  
  
Lemma EquivAuxQuest : forall F CC LC M M',
  flls th (CC ++[F]) LC  (UP (M ++  M') ) ->
  flls th CC  LC (UP (M ++ [? F] ++ M') ) .
Proof with  sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    solveComplexity.
    simpl... 
  
    destruct M as [ | a]... 
    rewrite <- app_comm_cons in H0.
    destruct a; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons;
            match goal with
            |  [ |- flls _ _ _ (UP (?M ++ (? _) :: _)) ] =>
               eapply H with (m:= complexityL M);simpl in *; try inversion HeqSizeM;solveLL;InvTriAll';sauto
            end.
    LLExact H4.        
            
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0%nat));intro...
  Qed.
  
Lemma EquivAuxTop :  forall CC LC M M',
  isFormulaL M ->
  flls th CC LC (UP (M ++ Top :: M') ) .
  Proof with  sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
     solveComplexity.
  
    destruct M as [ | a]... 
    destruct a; simpl in *;solveLL;
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- flls _ _ _ (UP (?M ++ Top :: _)) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveLL; inversion H0;subst;sauto
            end].
    
    eapply H with (m:= complexityL (a1 ::M));simpl in * ; inversion HeqSizeM; solveLL; inversion H0;subst;sauto. 
    inversion H4;subst...
    eapply H with (m:= complexityL (a2 ::M));simpl in * ; inversion HeqSizeM; solveLL; inversion H0;subst;sauto.
    inversion H4;subst...
    eapply H with (m:= complexityL (a1 :: a2 ::M));simpl in * ; inversion HeqSizeM; solveLL; inversion H0;subst;sauto.
    inversion H4;subst...

    inversion H0... inversion H3...
    
    rewrite <- app_comm_cons.
    solveLL.
    eapply H with (M:= o x :: M) (m:= complexityL (o x ::M));simpl in * ; inversion HeqSizeM; solveLL; inversion H0;subst;auto.

    
    rewrite (ComplexityUniformEq  H2 properX (proper_VAR con 0%nat));auto.
  Qed.

Lemma EquivAuxForAll : forall FX CC LC M M' ,
  isFormulaL M -> uniform_oo FX ->
  (forall t, proper t ->  
       flls th CC LC (UP (M ++ (FX t) ::M') )) ->
       flls th CC LC (UP (M ++ ∀{ FX} :: M') ) .
  Proof with  sauto;solveLL.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    solveComplexity.
    destruct M as [ | a]...
    
    destruct a; simpl in *;solveLL;
      try solve [eapply H with (m:= complexityL M);inversion HeqSizeM;subst;solveLL;intros;solveLL; inversion H1;subst;sauto;
                 generalize (H2 _ H3);intros Hs;invTri' Hs ;solveLL].

  - eapply H with (M:= a1 :: M) (m:= complexityL (a1 :: M));intros...
     inversion HeqSizeM;simpl... 
     inversion H1;subst;sauto.
     inversion H5;auto. 
     generalize (H2 _ H3);intros Hs;invTri' Hs ;solveLL.
     
  - eapply H with (M:= a2 :: M) (m:= complexityL (a2 :: M));intros...
     inversion HeqSizeM;simpl... 
     inversion H1;subst;sauto.
     inversion H5;auto. 
     generalize (H2 _ H3);intros Hs;invTri' Hs ;solveLL.
     
  - eapply H with (M:= a1 :: a2 :: M) (m:= complexityL (a1 :: a2 :: M));intros...
     inversion HeqSizeM;simpl... 
     inversion H1;subst;sauto.
     inversion H5;auto. 
     generalize (H2 _ H3);intros Hs;invTri' Hs ;solveLL.
    
  -  inversion H1... inversion H5...
     solveLL. eapply H with (M:= o x :: M) (m:= complexityL (o x :: M));intros...
     inversion HeqSizeM;simpl... 
     generalize (ComplexityUniformEq H4 properX (proper_VAR con 0%nat));intro...
     generalize (H2 _ H3);intros Hs;invTri' Hs ;solveLL.

    generalize (H13 _ H3);intros...
    rewrite <- app_comm_cons...
  Qed.
  

Theorem EquivUpArrow : forall n B L L' M,
  isFormulaL L' ->
  flln th n B M (UP L) ->
  Permutation L L' ->
  flls th B M (UP L').
Proof with sauto;solveLL.
  induction n;intros...
  - inversion H0...
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxTop.
    SLFormulaSolve.
  - inversion H0...
    +
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxTop.
    SLFormulaSolve.
    +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxWith.
    refine(IHn _ _ _ _ _ H4 _).
    inversion H... 
    SLFormulaSolve.
    rewrite H3...
    refine(IHn _ _ _ _ _ H7 _).
    inversion H... 
    SLFormulaSolve.
    rewrite H3... 
     +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxBot.
    refine(IHn _ _ _ _ _ H6 H3).
    rewrite H3 in H.
    inversion H...
    +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxPar.
    refine(IHn _ _ _ _ _ H6 _).
    rewrite H3 in H.
    inversion H...
    apply Forall_app...
    2:{
    inversion H4...
    apply Forall_cons...
     apply Forall_cons...
     apply Forall_app in H5...
     }
     apply Forall_app in H5...
     rewrite H3...

    +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxQuest.
    LLPerm (F::B).
    refine(IHn _ _ _ _ _ H6 _)...
    inversion H... 
    SLFormulaSolve.
    + 
    rewrite <- H1 in H.
    symmetry in H1.
    inversion H... 
    inversion H5... 
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxForAll;intros...
    SLFormulaSolve.
    apply H7 in H1.
    refine(IHn _ _ _ _ _ H1 _)...
    SLFormulaSolve.
    rewrite H4...
     +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxStore...
    refine(IHn _ _ _ _ _ H7 _)...
    inversion H... 
    SLFormulaSolve.
    +
    LFocus F L'0. 
    HProof. 
    +
    CFocus F. 
    HProof.
    +
    TFocus F. 
    HProof.
 Qed.

Theorem EquivUpArrow2' : forall B L L' M ,
 isFormulaL L' ->
 flls th B M (UP L) -> Permutation L L' ->
 flls th B M  (UP L').
 Proof with sauto.
    intros.
    revert dependent L'.
    dependent induction H0;intros...
    +
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxTop.
    SLFormulaSolve.
     +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxWith.
    eapply IHflls1...
    inversion H... 
    SLFormulaSolve.
    rewrite H2...
    eapply IHflls2...
    inversion H... 
    SLFormulaSolve.
    rewrite H2...
       +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxBot.
    refine(IHflls _ _ _ _ H3)...
    inversion H... 
    SLFormulaSolve.
    +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxPar.
    eapply IHflls...
    inversion H... 
    SLFormulaSolve.
    rewrite H3...

    +
    rewrite <- H1 in H.
    symmetry in H1.
    apply Permutation_vs_cons_inv' in H1...
    apply EquivAuxQuest.
    eapply IHflls...
    inversion H... 
    SLFormulaSolve.
    + 
    symmetry in H3.
    apply Permutation_vs_cons_inv' in H3...
    apply EquivAuxForAll;intros...
    SLFormulaSolve.
    specialize (H0 t  H3).
    eapply H1 with (x:=t)...
    rewrite Permutation_midle in H2.
    inversion H2...
    
    SLFormulaSolve.
    rewrite H5...
        +
    symmetry in H2.
    apply Permutation_vs_cons_inv' in H2...
    apply EquivAuxStore...
    eapply IHflls...
    rewrite Permutation_cons_append in H1.
    SLFormulaSolve.
    +
    LFocus F L'. 
    +
    CFocus F. 
    +
    TFocus F. 

 Qed.
   
Theorem EquivUpArrow2 : forall B L L' M ,
 isFormulaL L' ->
 flls th B M (UP L) -> Permutation L L' ->
 flls th B M  (UP L').
 Proof.
    intros.
    apply seqtoSeqN in H0.
    destruct H0.
    eapply EquivUpArrow in H0;eauto.
  Qed.

Lemma UpExtension: forall B M L F n,
  positiveLFormula F ->
  flln th n B (F::M) (UP L) ->
  exists m, m<= S n /\ flln th m B M (UP (L ++ [F])).
  Proof with subst;auto.
  intros.
    remember (complexityL L) as w.
    generalize dependent L .
    generalize dependent B .
    generalize dependent F .
    generalize dependent M .
    generalize dependent n .
    generalize dependent w .

    induction w as [| w' IH] using strongind .
    intros n M F HNA B L HD Hw.
    + (* w = 0 *)
      destruct L. (* L must be empty. The second case is trivial *)
      { exists ((S n)). firstorder.
      simpl.
      FLLstore. }
      apply exp_weight0LF in Hw;contradiction.
      
    + intros.
      destruct L. (* L cannot be empty *)
      inversion Heqw.
      rewrite <- app_comm_cons.
      inversion H0;auto;subst;inversion Heqw;subst.
      ++ (* top *)
        exists 0%nat.
        firstorder; try lia. 
      ++ (* with *)
        apply IH with (m:= complexity  F0 + complexityL  L) in H6;try lia;auto.
        apply IH with (m:= complexity  G + complexityL L) in H7;try lia;auto.
        destruct H6 as [n'  [IHn IHd]].
        destruct H7 as [m'  [IHn' IHd']].
        simpl.
        exists (S (S n0)).
        firstorder; eapply tri_with;auto.
        eapply HeightGeq with (n:=n');try firstorder.  
       eapply HeightGeq with (n:=m');try firstorder.       
        ++ (* bot *)
        apply IH with (m:= complexityL L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder; try lia. 
      ++  (* PAR *)
        apply IH with (m:= complexity F0 + complexity  G + complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ; simpl;try lia. 
        simpl. lia.

      ++  (* quest *)
        apply IH with (m:= complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ; try lia. 
        lia.
     ++  (* FORALL *)
        assert(forall x, proper x -> exists m, m <= S n0 /\ flln th m B M (UP ((FX x :: L)  ++ [F]))).
        intros.
        generalize (H7 x H1);intro.
        eapply IH with (m:=complexity (FX x) + complexityL L);auto.
        assert(complexity (FX (VAR con 0%nat)) = complexity (FX x) ).
        
        apply ComplexityUniformEq;auto. 
        
        constructor.
        lia.
        
        simpl.
        exists (S (S n0)). 
        split ; [auto|eapply tri_fx;auto;intros].
        
        generalize (H1 _ H2);intro.
        
        destruct H3 as [n H3].
        destruct H3 as [H3 H3'].
        eapply @HeightGeq with (n:=n);try firstorder.   
              ++ (* Store *)
        assert(exists m0 : nat, m0 <= S n0 /\ flln th m0 B (M ++ [o]) (UP (L ++ [F]))).
        apply IH with (m:= complexityL L);auto.
        assert (complexity o > 0) by (apply Complexity0);lia.
        eapply exchangeLCN;[|exact H7].
        perm.
        
        destruct H1 as [n'  [IHn IHd]].
        exists (S n').
        split;auto. lia.
        eapply tri_store;auto.
        LLExact IHd. 
 Qed.
  
Lemma UpExtension2': forall B M L F,
  positiveLFormula F ->
 flls th B (F::M) (UP L) -> flls th B M (UP (L ++ [F])).
  Proof with sauto.
  intros.
    remember (complexityL L) as w.
    generalize dependent L .
    generalize dependent B .
    generalize dependent F .
    generalize dependent M .
    generalize dependent w .

    induction w as [| w' IH] using strongind .
    intros M F HNA B L HD Hw.
    + (* w = 0 *)
      destruct L. (* L must be empty. The second case is trivial *)
      {  
      simpl.
      FLLstore. }
      apply exp_weight0LF in Hw;contradiction.
      
    + intros.
      destruct L. (* L cannot be empty *)
      inversion Heqw.
      rewrite <- app_comm_cons.
      inversion H0;auto;subst;inversion Heqw;subst.
      ++ (* with *)
        apply IH with (m:= complexity  F0 + complexityL  L) in H5;try lia;auto.
        apply IH with (m:= complexity  G + complexityL L) in H6;try lia;auto.
     ++ (* bot *)
        apply IH with (m:= complexityL L) in H4;auto.
      ++  (* PAR *)
        apply IH with (m:= complexity F0 + complexity  G + complexityL  L) in H4;auto.
        simpl. lia.
       ++  (* quest *)
        apply IH with (m:= complexityL  L) in H4;auto.
        lia.
       ++  (* FORALL *)
        FLLforall.
        specialize (H6 x H1). 
        eapply IH with (m:=complexity (FX x) + complexityL L) in H6;auto.
        assert(complexity (FX (VAR con 0%nat)) = complexity (FX x) ).
        
        apply ComplexityUniformEq;auto. 
        
        constructor.
        lia.    ++ (* Store *)
      rewrite perm_swap in H6.
      apply IH with (m:= complexityL  L) in H6;try lia;auto.
        assert (complexity o > 0) by (apply Complexity0);lia.

  Qed.
  

Lemma UpExtension': forall B M L F,
  positiveLFormula F ->
 flls th B (F::M) (UP L) -> flls th B M (UP (L ++ [F])).
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0.
  destruct H0.
  apply UpExtension in H0...
  apply seqNtoSeq in H2...
  Qed.
  
  
Lemma UpExtensionInv n F B M L :
   positiveLFormula F ->  flln th n B M (UP (L++[F])) -> 
   flls th B  (F::M) (UP L).
  Proof with sauto; solvePolarity;solveLL.
  intros.
  
  revert dependent F. 
  revert B M L.
  induction n using strongind;intros.
  + inversion H0...
    apply ListConsApp in H5... 
  + inversion H1... 
    -
    apply ListConsApp in H6...
    -
    apply ListConsApp in H3...
    rewrite app_comm_cons in H4. 
    eapply H in H4...    
    rewrite app_comm_cons in H7.
    eapply H in H7...
 
    -
    apply ListConsApp in H3...
    eapply H in H6...
    -
    apply ListConsApp in H3...
    rewrite app_comm_cons in H6.
    rewrite app_comm_cons in H6. 
    eapply H in H6...
    -
    apply ListConsApp in H3...
    eapply H in H6...
    LLPerm (F0::B)...
    - 
    apply ListConsApp in H3...
    solveLL. 
    apply H7 in properX...
    rewrite app_comm_cons in properX.
    eapply H in properX...
    -
    apply ListConsApp in H3...
    HProof.
    eapply H in H7...
    solveLL.
    LLExact H7.          
 Qed. 
  
Lemma UpExtensionInv2' F B M L : 
  positiveLFormula F -> 
  flls th B M (UP (L++[F])) -> flls th B (F::M) (UP L).
  Proof with sauto.
  intros.
    remember (complexityL L) as w.
    generalize dependent L .
    generalize dependent B .
    generalize dependent F .
    generalize dependent M .
   
    induction w as [| w' IH] using strongind .
    intros M F HNA B L HD Hw.
    + (* w = 0 *)
      destruct L. (* L must be empty. The second case is trivial *)
      {  
      simpl in HD.
      inversion HD;inversion HNA...
      }
      apply exp_weight0LF in Hw;contradiction.
      
    + intros.
      destruct L. (* L cannot be empty *)
      inversion Heqw.
      inversion H0;auto;subst;inversion Heqw;subst.
      ++ (* with *)
       rewrite app_comm_cons in H5. 
        apply IH with (m:= complexity  F0 + complexityL  L) in H5;try lia;auto.
        rewrite app_comm_cons in H6. 
        apply IH with (m:= complexity  G + complexityL L) in H6;try lia;auto.
         ++ (* bot *)
        apply IH with (m:= complexityL L) in H4;auto.
      ++  (* PAR *)
       do 2 rewrite app_comm_cons in H4. 
        apply IH with (m:= complexity F0 + complexity  G + complexityL  L) in H4;auto.
        simpl. lia.
   ++  (* quest *)
        apply IH with (m:= complexityL  L) in H4;auto.
        lia.
     ++  (* FORALL *)
        FLLforall.
        specialize (H6 x H1).
        rewrite app_comm_cons in H6.  
        eapply IH with (m:=complexity (FX x) + complexityL L) in H6;auto.
        assert(complexity (FX (VAR con 0%nat)) = complexity (FX x) ).
        
        apply ComplexityUniformEq;auto. 
        
        constructor.
        lia.     ++ (* Store *)
      apply IH with (m:= complexityL  L) in H6;try lia;auto.
      FLLstore. LLExact H6.
        assert (complexity o > 0) by (apply Complexity0);lia.
 
  Qed.
  
Lemma UpExtensionInv' F B M L : 
  positiveLFormula F -> 
  flls th B M (UP (L++[F])) -> flls th B (F::M) (UP L).
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0.
  destruct H0.
  apply UpExtensionInv in H0... 
  Qed. 
  
End InvNPhase.
