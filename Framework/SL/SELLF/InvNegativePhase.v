
(** * Invertibility results for the negative phase

This file proves that exchange is admissible also in the list L in
[SELLS Gamma Delta (> L)]. For that, some invertibility lemmas are
needed.
 *)
Require Export LL.Misc.UtilsForall.
Require Export LL.Framework.SL.SELLF.Tactics.
Require Import Lia.
Require Import LL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section InvNPhase .
    Context `{SI : SigSELL}.
  Context `{OLS: OLSig}.
  Hint Constructors isFormula  SELLN posAtom : core .

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (SELLN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (SELLS theory B L X) (at level 80).

  Theorem exp_weight0LF : forall l L, 0%nat = complexity l + complexityL L -> False.
  Proof.
    intros.
    assert(complexity l > 0%nat) by (apply Complexity0).
    lia.
  Qed.

  
  Theorem EquivAuxBot :  forall CC LC M M',
      |-- CC ; LC ; (UP (M ++ M') ) ->
     |-- CC ;  LC ; (UP (M ++ Bot :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    destruct a; simpl in *; invTri' H0;solveLL; 
      repeat rewrite app_comm_cons.
    all:  try match goal with
          |  [ |- SELLS _ _ _ (UP (?M ++ Bot :: _)) ] =>
             eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF
          end. 
    assert (Hvar : proper (VAR con 0%nat)) by constructor.
    generalize (ComplexityUniformEq H5 properX Hvar);intro.
    lia.
  Qed.

  Theorem EquivAuxWith :  forall F G CC LC M M',
      |-- CC ; LC ; (UP (M ++ [F] ++ M') ) ->
      |-- CC ; LC ;(UP (M ++ [G] ++ M') ) ->
      |-- CC ; LC ; (UP (M ++ (AAnd F G) :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons.
   all: try solve[  match goal with
            |  [ |- SELLS _ _ _ (UP (?M ++ (AAnd _ _) :: _)) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto
            end] .
     assert (Hvar : proper (VAR con 0%nat)) by constructor.
    generalize (ComplexityUniformEq H6 properX Hvar);intro...
 apply H with (M:= o x:: M) (m:= complexityL (o x:: M));simpl in *...
    FLLInversionAll;auto. inversion H8.
  Qed.
  
  
  
  Theorem EquivAuxPar : forall F G CC LC M M',
      |-- CC ; LC ; (UP (M ++ [F ; G] ++ M') ) ->
      |-- CC ; LC ;(UP (M ++ (MOr F G) :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons;
      match goal with
      |  [ |- SELLS _ _ _ (UP (?M ++ (MOr F G) :: _)) ] =>
         eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF
      end.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0%nat));intro...
  Qed.
  
  Theorem EquivAuxStore :
    forall F CC LC M M', posLFormula  F ->
                         |-- CC ; (LC ++ [F]) ;(UP (M ++ M') ) ->
                         |-- CC ; LC ; (UP (M ++ F :: M') ) .
  Proof with sauto.
  
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC;
    revert dependent LC;
    revert dependent M;
    revert dependent M'.
    induction SizeM using strongind;intros ...
    - symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
      LLStore.
      LLExact H0.
    - destruct M as [ | a]; simpl in HeqSizeM.
      inversion HeqSizeM.
      destruct a;CleanContext;invTri' H1;try rewrite <- app_comm_cons;solveLL.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;auto.
      -- rewrite app_comm_cons. 
         eapply H0 with (m:= complexityL (a1 :: M))...
         inversion HeqSizeM;simpl;try lia.
      -- rewrite app_comm_cons. 
         eapply H0 with (m:= complexityL (a2 :: M))...
         inversion HeqSizeM;simpl;try lia.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.                  
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.                  
      -- rewrite app_comm_cons.
         rewrite app_comm_cons. 
         eapply H0 with (m:= complexityL (a1 :: a2 :: M))...
         inversion HeqSizeM;simpl;try lia.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.        
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.              
      -- rewrite app_comm_cons.
         eapply H0 with (m:= complexityL (o x :: M))...
         inversion HeqSizeM;simpl;try lia.       
         generalize (ComplexityUniformEq H6 properX (proper_VAR con 0%nat));intro...  rewrite <- app_comm_cons...
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.
      -- eapply H0 with (m:= complexityL M)...
         inversion HeqSizeM;try lia.
 
  Qed.
  
  
  Theorem EquivAuxQuest : forall a F CC LC M M',
      |--  (a,F)::CC ; LC ;(UP (M ++  M') ) ->
      |-- CC ; LC ; (UP (M ++ [Quest a F] ++ M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    simpl;solveLL...
  
    destruct M; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct o; simpl in *; invTri' H0;solveLL;
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- SELLS _ _ _ (UP (?M ++ (Quest _ _) :: _)) ] =>
              eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto
            end] .
        
       rewrite perm_swap in H4.     
      eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto.
            
    eapply H with (m:= complexityL (o x :: M));simpl in *; inversion HeqSizeM;solveF;FLLInversionAll;auto.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0%nat));intro...
  Qed.
  
  
  Theorem EquivAuxTop :  forall CC LC M M',
      isFormulaL M ->
      |-- CC ; LC ; (UP (M ++ Top :: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
   
    destruct M as [ | a]; simpl in HeqSizeM.
    
    inversion HeqSizeM.
   
    destruct a; simpl in *;solveLL;
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- SELLS _ _ _ (UP (?M ++ Top :: _)) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF; inversion H0;subst;auto
            end].
    
    eapply H with (m:= complexityL (a1 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
    eapply H with (m:= complexityL (a2 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
    eapply H with (m:= complexityL (a1 :: a2 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
  
    rewrite <- app_comm_cons. 
    
    LLStore.
    eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    
     inversion H0... inversion H3...
   rewrite <- app_comm_cons. 
    LLForall.
    eapply H with (M:= o x :: M) (m:= complexityL (o x ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.

    
    rewrite (ComplexityUniformEq  H2 H1 (proper_VAR con 0%nat));auto.
  Qed.

  Theorem EquivAuxForAll : forall FX CC LC M M' ,
      isFormulaL M -> uniform_oo FX ->
      (forall t, proper t ->  |-- CC ; LC ; (UP (M ++ (FX t) ::M') )) ->
      |--  CC ; LC ; (UP (M ++ All FX:: M') ) .
  Proof with sauto.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    inversion H1...
    
    destruct a; simpl in *;solveLL;
      try solve [eapply H with (m:= complexityL M);inversion HeqSizeM;subst;solveF;intros;solveLL; inversion H1;subst;auto;
                 generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF]...

    
    eapply H with (M:= a1 :: M)(m:= complexityL (a1 :: M));inversion HeqSizeM;subst...  simpl. lia.
    inversion H5... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    eapply H with (M:= a2 :: M)(m:= complexityL (a2 :: M));inversion HeqSizeM;subst... simpl. lia.
    inversion H5... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    eapply H with (M:= a1 :: a2 :: M)(m:= complexityL (a1 :: a2 :: M));inversion HeqSizeM;subst... simpl. lia.
    inversion H5... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.
    
   inversion H5...
   LLStore.
    eapply H with (M:= M)(m:= complexityL (M));inversion HeqSizeM;subst... intros. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.
    inversion H5...
    
   LLForall.
   
    eapply H with (M:=  o x :: M)(m:= complexityL (o x :: M));inversion HeqSizeM;subst...
    generalize (ComplexityUniformEq H4 H3 (proper_VAR con 0%nat));intros... simpl...
    intros...
    
    generalize (H2 _ H8);intros Hs. invTri' Hs...
    apply H14 in H3...
    inversion H13.

  Qed.
  

  Theorem EquivUpArrow : forall B L L' M n,
      isFormulaL L' ->
      (n |--- B ; M ; UP L) ->
      Permutation L L' ->
      |-- B ; M ;  UP L'.
  Proof with sauto.
    intros.
    remember (complexityL L) as w.
    generalize dependent n .
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind;  intros ;  destruct L as [|l]...
    +  apply seqNtoSeq in H0;auto.
    + inversion Heqw.
      apply exp_weight0LF in H3...
    +  destruct L' as [| l']...
       
       assert
         ((l = l' /\ Permutation L L') \/
          (exists L1 L2 L1' L2', L = L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2' /\ Permutation (L1 ++ L2) (L1' ++ L2') )) .
       { checkPermutationCases H1.
         right.
         assert (exists T1 T2, L' = T1 ++ [l] ++ T2).
         { induction x.
           do 2 eexists []...
           sauto.
           assert (In l  L') as Hm.
           rewrite H1...
           apply in_split;auto. } 
         assert (exists T1 T2, L = T1 ++ [l'] ++ T2).
         { induction x.
           do 2 eexists []...
           sauto.
           assert (In l'  L) as Hm.
           rewrite H3...
           apply in_split;auto. }
          simplifier.
       eexists x0; eexists x1;eexists x2; eexists x3. 
       intuition. 
      rewrite H4 in H3.
      simpl in H3.
      rewrite Permutation_midle in H3. 
      apply Permutation_cons_inv in H3.
      sauto. 
      simpl in H1.
      rewrite Permutation_midle in H1. 
      apply Permutation_cons_inv in H1.
      rewrite H1. rewrite H3. auto. }
      destruct H2 as [Heq | Heq].
        ++ destruct Heq;subst.
           inversion H0;subst;try(simpl in Heqw; inversion Heqw; subst;simpl;try(lia)).
           +++  (* top *)
             LLTop.
          +++ (* with *)
             eapply IH with (m:= complexityL (F::L)) (L:= F ::L) (L' := F :: L') in H8;auto.
             eapply IH with (m:= complexityL (G::L)) (L := G :: L) (L' := G :: L') in H9;auto.
             simpl. lia.
             inversion H;subst.
             inversion H5;subst.
             SLSolve.
             simpl. lia.
             inversion H;subst.
             inversion H5;subst.
             change (F :: L') with ([F] ++ L').
             apply Forall_app;auto.           
           +++ (* bottom *)
             eapply IH with (L' :=L') in H7;auto.
             inversion H;subst;auto.
           +++ (* par *)
             eapply IH with (L' := F::G::L') in H7;auto.
             inversion H;subst.
             inversion H5;subst.
             SLSolve.
             simpl. lia.
            +++  (* quest *)
             eapply IH with (m:= complexityL L) (L' :=L') in H7;auto.
             lia.
             inversion H;subst;auto.
           +++ (* forall *)
             eapply tri_fx';auto;intros.
             generalize (H9 x H2);intro.
             eapply IH with (m:= complexity (FX x) + complexityL L) (L' := FX x :: L') in H4;auto.
             assert(complexity (FX (VAR con 0%nat)) = complexity (FX x) ).
             apply ComplexityUniformEq;auto.          
             constructor.
             lia.
             inversion H;subst.
             inversion H7;subst.
             change (FX x  :: L') with ([FX x ] ++ L').
             apply Forall_app;auto.
             
        +++  (* store *)
             eapply IH with (m:= complexityL L) (L' :=L') in H9;auto.
             assert (complexity l' > 0) by (apply Complexity0).
             lia.
             inversion H;subst;auto.
           ++
          destruct Heq as [L1 [L2 [L1' [L2' Heq]]]].
          destruct Heq as [Heq [Heq1 Heq2]];subst.
          
          inversion H0;subst.
          
          +++ (* top *)
            eapply EquivAuxTop with (M:= l' :: L1').
            rewrite app_comm_cons in H.
            autounfold in H.
            autounfold.
            solveForall.
  +++ (* with *)
            eapply IH with (m:= complexityL (F :: L1 ++ l' :: L2))
                           (L:=F :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [F ] ++ L2') in H7;auto .
            eapply IH with (m:= complexityL (G :: L1 ++ l' :: L2))
                           (L:=G :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [G ] ++ L2') in H8;auto .
            
            apply EquivAuxWith with (M := l' :: L1'); simpl;auto.
            inversion Heqw. simpl. lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H. 
                autounfold in H.
            autounfold.
            solveForall.  
          
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H10...
            
            rewrite Permutation_midle. rewrite Heq2. perm.
            inversion Heqw. simpl. lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.
                autounfold in H.
            autounfold.
            solveForall.  
          
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H10...
            simpl.
            
            rewrite Permutation_midle. rewrite Heq2. perm.
            
          
          +++ (* bottom *)
            eapply IH with (m:= complexityL (L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H6 .
            simpl in H6. 
            apply EquivAuxBot with (M:= l' :: L1');auto.
            simpl in Heqw. inversion Heqw. auto.
            inversion H;subst;auto.
              rewrite app_comm_cons in H. 
              
                autounfold in H.
            autounfold.
            solveForall.  
          
            rewrite Permutation_midle.
            apply Permutation_cons;auto. 
            auto.
            
          +++ (* par *)
            eapply IH with (m:= complexityL (F :: G :: L1 ++ l' :: L2))
                           (L:=F :: G :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [F ; G] ++ L2') in H6.
            apply seqtoSeqN in H6. destruct H6.
            eapply EquivAuxPar with (M:= l' :: L1');simpl;simpl in H2;eauto using seqNtoSeq.
            simpl in Heqw. inversion Heqw. simpl.  lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.
                autounfold in H.
            autounfold.
            solveForall.
            
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H9...
             apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H9...
            rewrite Permutation_midle. 
            rewrite Heq2. perm.
            auto.


          +++ (* quest *)
            eapply IH with (m:= complexityL (L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H6;auto .
            apply seqtoSeqN in H6. destruct H6.   
            eapply EquivAuxQuest with (M := l' :: L1');simpl in H2.
            eauto using seqNtoSeq.
            
            inversion Heqw. simpl. lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.
                autounfold in H.
            autounfold.
            solveForall.  
          
            rewrite Permutation_midle. rewrite Heq2. perm.
+++ (* forall *)
            
            
            assert(forall x, proper x -> |-- B; M; UP ((l' :: L1' ) ++ [FX x] ++ L2')).
            intros x pX.
            eapply IH with (m:= complexityL(FX x :: L1 ++ l' :: L2)) (L:=FX x :: L1 ++ l' :: L2)  ;auto.
            inversion Heqw.
            simpl. 
            assert(complexity (FX (VAR con 0%nat)) = complexity (FX x) ).
            
            apply ComplexityUniformEq;auto. 
            constructor. lia.
            
            inversion H;subst;auto.
            change ((l' :: L1') ++ [FX x] ++ L2') with ([l'] ++ L1' ++ [FX x] ++ L2').
              inversion H;subst;auto.
              rewrite app_comm_cons in H.
                autounfold in H.
            autounfold.
            solveForall.  
            apply Forall_app in H5;auto.
            inversion H5;subst;auto.
            inversion H3;subst;auto.
            inversion H12...
            rewrite Permutation_midle. rewrite Heq2. perm.

            assert(forall B  L L' M   FX, 
                      isFormulaL L -> uniform_oo FX ->  (forall x, proper x -> |-- B ; M ; UP (L ++ [FX x]++ L')) ->  |-- B ; M ;  UP (L ++ [All FX] ++ L')).
            intros.
            eapply EquivAuxForAll;auto.
            
            apply H3 in H2;auto.
            inversion H;subst.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.
                autounfold in H.
            autounfold.
            solveForall.  
          
          +++ (* copy *)
            eapply IH with (m:= complexityL(L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H8;auto .

            eapply EquivAuxStore with (M:=l' :: L1');eauto.
            rewrite Permutation_app_comm;eauto. 
            inversion Heqw.
            assert (complexity l > 0) by (apply Complexity0).
            lia.
              inversion H;subst;auto.
              rewrite app_comm_cons in H.
                autounfold in H.
            autounfold.
            solveForall.  
            rewrite Permutation_midle. rewrite Heq2. perm.
          
  Qed.

  Theorem EquivUpArrow2 : forall B L L' M ,
      isFormulaL L' ->
      (|-- B ; M ; UP L) -> Permutation L L' ->
      |-- B ; M ;  UP L'.
    intros.
    apply seqtoSeqN in H0.
    destruct H0.
    eapply EquivUpArrow in H0;eauto.
  Qed.



  Generalizable All Variables.
  Global Instance Forall_morph : 
    Proper ((@Permutation oo) ==> Basics.impl) (Forall posLFormula).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl.
    intros.
    rewrite <- H;eauto.
  Qed. 

  
  
  Lemma UpExtension: forall B M L F n,
      posLFormula F ->
      (n |--- B; F::M ; UP L) ->
      exists m, m<= S n /\ m |--- B; M ; UP (L ++ [F]).
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
      eapply tri_store;auto. }
      simpl in Hw.
      apply exp_weight0LF in Hw;contradiction.
    + intros.
      destruct L. (* L cannot be empty *)
      inversion Heqw.
      inversion H0;auto;subst;inversion Heqw;subst.
      ++ (* top *)
        exists 0%nat. 
        firstorder;[lia | eapply tri_top ].
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
        firstorder;[lia | eapply tri_bot;auto ].
      ++  (* PAR *)
        apply IH with (m:= complexity F0 + complexity  G + complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ;[lia | eapply tri_par;auto ].
        simpl. lia.
      ++  (* quest *)
        apply IH with (m:= complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ;[lia | eapply tri_quest;auto ]. 
        lia.
     ++  (* FORALL *)
        assert(forall x, proper x -> exists m, m <= S n0 /\  m |--- B; M; UP ((FX x :: L)  ++ [F])).
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
        assert(exists m0 : nat, m0 <= S n0 /\ m0 |--- B; M ++ [o]; UP (L ++ [F])).
        apply IH with (m:= complexityL L);auto.
        assert (complexity o > 0) by (apply Complexity0);lia.
        eapply exchangeLCN;[|exact H7].
        perm.
        
        destruct H1 as [n'  [IHn IHd]].
        exists (S n').
        firstorder ;[lia | eapply tri_store;[auto | LLExact IHd] ].
       
  Qed.
  
    Lemma UpExtension': forall B M L F,
      posLFormula F ->
      (|-- B; F::M ; UP L) -> |-- B; M ; UP (L ++ [F]).
  Proof with sauto.
  intros.
  apply seqtoSeqN in H0.
  destruct H0.
  apply UpExtension in H0...
  apply seqNtoSeq in H2...
  Qed.

End InvNPhase.
