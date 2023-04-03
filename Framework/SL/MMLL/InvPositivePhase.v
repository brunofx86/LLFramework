(** Invertibility lemmas: Positive phase

This file proves some invertibility lemmas showing that positive rules
can be switched.
 *)

Require Export LL.Misc.Hybrid.
Require Export LL.Framework.SL.MMLL.Tactics.
Require Import LL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export LL.Framework.SL.MMLL.InvNegativePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


Section Absorption.
  Context `{SI : SigMMLL}.
  Context `{OLS: OLSig}.
         
 Lemma AbsorptionC : forall th n i Gamma Delta F X,
   u i = true -> mt i = true ->  MLLN th n ((i,F) :: Gamma) ( F::Delta)  X ->
      MLLN th n ((i,F) :: Gamma) Delta  X.
  Proof with sauto.
  do 2 intro.
    induction n using strongind ;intros.
    * inversion H1...
      solveLL. solveSE.
    * inversion H2;solveF;solveLL... solveSE.
      + apply PermutationInCons in H4 as H4'.
        apply in_app_or in H4'.
        destruct H4'.
        { apply InPermutation in H3;
          destruct H3.
          rewrite H3 in H4;simpl in H4.
          apply Permutation_cons_inv in H4.
          LLtensor x N B C D.
         apply aux_c in H5...
          apply InPermutation in H5...
          rewrite H5 in H9.
          rewrite H3 in H9.
          rewrite <- app_comm_cons in H9.
          apply H in H9...
          LLExact H9. rewrite H5...
      }
      {
        apply InPermutation in H3;
        destruct H3.
        rewrite H3 in H4;simpl in H4.
        rewrite <- perm_takeit_2 in H4.
        apply Permutation_cons_inv in H4.
        LLtensor M x B C D.
        apply aux_c in H5...
          apply InPermutation in H5...
          rewrite H5 in H10.
          rewrite H3 in H10.
          rewrite <- app_comm_cons in H10.
          apply H in H10...
          LLExact H10. rewrite H5...
      }
    + LLSwap. apply H... LLExact H4.  
    + apply H... LLExact H5.  
    +  checkPermutationCases H5.
      LLfocus2 i F. inversion H3;inversion H4...
      eapply exchangeLCN with (LC:=L')... 
      rewrite H7 in H6...
      eapply H in H6...
      rewrite H5.
      LLfocus1 F0.
    + inversion H7... 
      { apply H in H8...
        LLfocus2 i0 F0... }
      { apply H in H8...
        LLfocus2 i0 F0... }
    + checkPermutationCases H7...    
      LLfocus3 i0 F0 ((i, F) :: x)... rewrite H7...
      rewrite H9 in  H8...
    + apply H in H6...
      LLtheory F0.
    + apply H in H6...
      LLexists t.
  Qed.


 Lemma AbsorptionL : forall th n i Gamma Delta F X,
   mt i = true ->  MLLN th n (Gamma) ( F::Delta)  X ->
      MLLN th n ((i,F) :: Gamma) Delta  X.
  Proof with sauto.
  intros.
  destruct (uDec i).
  - apply AbsorptionC...
    apply weakeningN... 
  - 
  revert dependent X.
  revert dependent i.
  revert Gamma Delta F.
    induction n using strongind ;intros.
    * inversion H0...
      solveLL.
    * inversion H1;solveF;solveLL...
      + apply PermutationInCons in H3 as H4'.
        apply in_app_or in H4'.
        destruct H4'.
        { apply InPermutation in H2;
          destruct H2.
          rewrite H2 in H3;simpl in H3.
          apply Permutation_cons_inv in H3.
          LLtensor x N B ((i,F)::C) D.
           rewrite H4...
          rewrite <- Permutation_middle.
          apply H...
          LLExact H8. 
      }
      {
        apply InPermutation in H2;
        destruct H2.
        rewrite H2 in H3;simpl in H3.
        rewrite <- perm_takeit_2 in H3.
        apply Permutation_cons_inv in H3.
        LLtensor M x B C ((i,F)::D).
           rewrite H4...
          rewrite <- Permutation_middle.
          apply H...
          LLExact H9. 
      }
     + LLSwap...    
    + apply H... LLExact H4.    
    +  checkPermutationCases H4. 
      LLfocus3 i F. inversion H2;inversion H3...
      rewrite <- H7...
      rewrite H4.
      LLfocus1 F0.
      rewrite H6 in H5...
    + LLfocus2 i0 F0... 
    + LLfocus3 i0 F0 ((i, F) :: B')...
        rewrite <- H6...
    + LLtheory F0.
    + LLexists t.
  Qed.


     Lemma AbsorptionC'
     : forall th i Gamma Delta F X,
       u i = true ->
       mt i = true ->
       MLLS th ((i, F) :: Gamma) (F :: Delta) X ->
       MLLS th ((i, F) :: Gamma) Delta X.
 Proof.
      intros *. 
      intros Hui Hti Hyp.
      apply MLLStoSeqN in Hyp.
      destruct Hyp as [n Hyp].
      apply AbsorptionC in Hyp;auto.
      apply MLLNtoSeq in Hyp;auto.
 Qed.       
          
Lemma AbsorptionL'
     : forall th i Gamma Delta F X,
       mt i = true ->
       MLLS th Gamma (F :: Delta) X ->
       MLLS th ((i, F) :: Gamma) Delta X.
 Proof.
      intros *. 
      intros Hti Hyp.
      apply MLLStoSeqN in Hyp.
      destruct Hyp as [n Hyp].
      apply AbsorptionL with (i:=i) in Hyp;auto.
      apply MLLNtoSeq in Hyp;auto.
 Qed.     
 
Lemma AbsorptionCSet : forall th n C Gamma Delta X,
  SetT C -> SetU C -> MLLN th n (C++Gamma) (Delta++ (second C))  X ->
      MLLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  destruct a as [i F].
  apply AbsorptionC. 
  solveSE. solveSE.
  LLPerm (C ++ Gamma ++ [(i, F)]).
  eapply IHC.
  solveSE. solveSE.
  LLExact H1...
  Qed. 
  
    Lemma AbsorptionCSet' : forall th C Gamma Delta X,
  SetT C ->  SetU C -> MLLS th (C++Gamma) (Delta++ (second C))  X ->
      MLLS th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply MLLStoSeqN in H1...
  apply AbsorptionCSet in H1...
  HProof.
  Qed. 
  
 Lemma AbsorptionCSet_rev : forall th  C Gamma Delta X,
  SetT C ->  SetU C -> MLLS th (Gamma++C) (Delta++ (second C))  X ->
      MLLS th (Gamma++C) Delta  X.
  Proof with sauto.
  intros.
  apply MLLStoSeqN in H1...
  LLPermH H1 (C++Gamma).
  eapply AbsorptionCSet in H1...
  apply MLLNtoSeq in H1...
  LLExact H1.
  Qed.
  
 Lemma AbsorptionLSet : forall th n C Gamma Delta X,
  SetT C ->  MLLN th n (Gamma) (Delta++ (second C))  X ->
      MLLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  rewrite app_comm_cons.
  destruct a as [i F].
  apply AbsorptionL.
  solveSE.
  apply IHC.
  solveSE.
  LLExact H0...
  Qed. 
 
  Lemma AbsorptionLSet' : forall th C Gamma Delta X,
  SetT C ->  MLLS th (Gamma) (Delta++ (second C))  X ->
      MLLS th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply MLLStoSeqN in H0...
  apply AbsorptionLSet in H0...
  HProof.
  Qed. 
   
 Lemma AbsorptionLSet_rev : forall th  C Gamma Delta X,
  SetT C ->  MLLS th (Gamma) (Delta++ (second C))  X ->
      MLLS th (Gamma++C) Delta  X.
  Proof with sauto.
  intros.
  apply MLLStoSeqN in H0...
  apply AbsorptionLSet in H0...
  apply MLLNtoSeq in H0...
  LLExact H0.
  Qed.
 
 
End Absorption.


Section InvPosPhase.
  Context `{SI : SigMMLL}.
  Context `{OLS: OLSig}.

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (MLLN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (MLLS theory B L X) (at level 80).

  Ltac solveList :=
    match goal with
      [ H : [] = ?M ++ [?F] |- _ ] =>
      symmetry in H; apply app_eq_nil in H;inversion H as [H' H''];inversion H''
    | [ H :  ?M ++ [?F] = [ ] |- _ ] =>
      apply app_eq_nil in H; inversion H as [H' H''];inversion H''
    end.

  Ltac MLLSPermutation := 
    match goal with
      [ H : Permutation ?M ?T ,
            Hs : |-- ?B ; ?M ; ?Arrow |- _ ] =>
      assert(|-- B ; T ; Arrow) by (refine(exchangeLC _ Hs); rewrite H; auto)
    | [ H : Permutation ?T ?M ,
            Hs : |-- ?B ; ?M ; ?Arrow |- _ ] =>
      assert(|-- B ; T ; Arrow) by (refine(exchangeLC _ Hs); rewrite <- H; auto)  
    end.

  Ltac MLLSPerm H S := 
    match type of H with
      Permutation ?M ?T => match type of S with
                             |-- ?B ; ?M ; ?Arrow => 
                             assert(|-- B ; T ; Arrow); refine(exchangeLC _ S);rewrite H;auto
                           | ?n |--- ?B ; ?M ; ?Arrow => 
                             assert(n |--- B ; T ; Arrow); refine(exchangeLCN _ S);rewrite H;auto
                           end
    | Permutation ?T ?M => match type of S with
                             |-- ?B ; ?M ; ?Arrow => 
                             assert(|-- B ; T ; Arrow); refine(exchangeLC _ S);rewrite <- H;auto
                           | ?n |--- ?B ; ?M ; ?Arrow => 
                             assert(n |--- B ; T ; Arrow); refine(exchangeLCN _ S);rewrite <- H;auto
                           end                      
    end.   

  Section AbsorptionTheory.

    Theorem AbsorptionPerp :  forall n B M A X , theory (perp A) -> n |--- B; (perp A) ::  M; X -> n |--- B; M; X.
    Proof with solveF.
      induction n;intros ;inversion H0;subst;eauto;clear H0...
      + (* LLtensor: A+ is in N or in M0 *)
        assert (In (perp A)  ( M0 ++ N)).
        apply Permutation_in with (l:= (perp A) :: M)...
        apply in_app_or in H0;destruct H0.
        ++ (* A+  in H0 *)
          apply InPermutation in H0;destruct H0.
          eapply exchangeLCN in H7.
          2: rewrite H0...
          apply IHn in H7...
          rewrite H0 in H2;simpl in H2.
          apply Permutation_cons_inv in H2.
          eapply exchangeLCN.
          rewrite H2...
          LLtensor x N B0 C D.
        ++ (* A+ in N *)
          apply InPermutation in H0;destruct H0.
          eapply exchangeLCN in H8.
          2: rewrite H0...
          apply IHn in H8...
          
          rewrite H0 in H2;simpl in H2.
          apply Permutation_cons_app_inv in H2.
          eapply exchangeLCN.
          rewrite H2...
          LLtensor M0 x B0 C D.
      + LLstore.
        eapply exchangeLCN with (LC':= perp A :: F:: M) in H3...
        eapply IHn in H3;auto.
      + (*dec1 *)
        checkPermutationCases H3. 
        LLtheory (perp A).
        rewrite <- H5...
        rewrite H1.
        LLfocus1 F.
        rewrite H3 in H4...
        apply IHn in H4...
    Qed.
   
   Theorem AbsorptionPerp2 :  forall n B M A L , theory (perp A) -> n |--- B; M; UP (L++[perp A]) -> n |--- B; M; (UP L).
    Proof with sauto;solveF.
      intro.
      induction n;intros.
      inversion H0... 
      + apply ListConsApp in H5...
      + inversion H0...
        -  apply ListConsApp in H5...
        - apply ListConsApp in H2...
          LLbot.
          apply IHn with (A:=A)...
        -  apply ListConsApp in H2...
          LLpar.
          apply IHn with (A:=A)...
        - apply ListConsApp in H2...
          LLwith.
          apply IHn with (A:=A)...
          apply IHn with (A:=A)...   
        - apply ListConsApp in H2...
          LLstorec.
          apply IHn with (A:=A)...
        - apply ListConsApp in H2...
          CleanContext.
          eapply AbsorptionPerp with (A:=A)...
          eapply HeightGeqLEx.
          2:{ exact H6. }
          perm. lia.
          LLstore.
          apply IHn with (A:=A)...
        - apply ListConsApp in H2...
          LLforall.
          apply H6 in H1.
          apply IHn with (A:=A)...
    Qed.      
    
   Theorem AbsorptionPerp' :  forall B M A L , theory (perp A) -> |-- B; M; UP (L++[perp A]) -> |-- B; M; (UP L).
    Proof with auto.
   intros.
   apply MLLStoSeqN in H0.
   destruct H0.
   apply  AbsorptionPerp2 in H0...
   apply MLLNtoSeq in H0...
   Qed.
      
          
       
    Lemma app_eq_unit_sym : forall (A : Type) (y : list A) (a b : A),
        [a] = y ++ [b] -> y = [] /\ b = a.
    Proof.
       intros.
       symmetry in H.
      apply app_eq_unit in H.
      destruct H. 
      inversion H. inversion H1.
      firstorder.
      inversion H. inversion H1. Qed.
      
    Definition RUpTheory (n:nat) := forall B L  F  M , 
        theory F -> ~ IsPositiveAtom F -> ~ IsNegativeAtom F ->
        n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).

    Definition RDownTheory (n:nat) := forall B  F  M  H, 
         positiveFormula F ->  ~ IsPositiveAtom F -> ~ IsNegativeAtom F -> theory F -> 
        n |--- B ; F::M ; DW H -> |-- B ; M  ; DW H.

    Definition RIndTheory (n:nat) := RUpTheory n /\ RDownTheory (n -1). 

    Lemma RDownTheory0 : RDownTheory 0.
    Proof with sauto.
      unfold RDownTheory. intros B F M H FNA FNP FNN FT HD.
      inversion HD... 
       solveF. 
    Qed.

    Lemma RUpTheory0 : RUpTheory 0.
    Proof with subst;auto.
      unfold RUpTheory. intros B L F M FT FNP FNN HD.
      destruct L.
      + inversion HD...
        LLtheory Top.
      + inversion HD ...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUpTheory *)
    (* =============================================== *)   

    Theorem InvTheoryUP: forall  n ,
        (forall m : nat, m <= n -> RIndTheory m) -> RUpTheory (S n).
    Proof with subst;auto;solveF;solveLL.
      intros n IH.
      unfold RUpTheory.
      intros B L1 F M1 FT FNA FNN HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
          LLtheory Top. 
        ++ 
          apply MLLNtoSeq in H3;auto. 
        ++ 
          LLtheory (MOr F0 G). 
          apply MLLNtoSeq in H3;auto. 
        ++ 
          LLtheory (AAnd F0 G). 
          apply MLLNtoSeq in H4;auto.
          apply MLLNtoSeq in H5;auto. 
        ++ 
          LLtheory (Quest i F0).
          apply MLLNtoSeq in H3;auto. 
        ++ 
          assert(RIndTheory n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * checkPermutationCases H0.
          **
            LLtheory F.
            apply MLLNtoSeq in H1;auto.
            rewrite <- H6;auto.
          **   
            LLfocus1 F0 x.
            eapply HDown with (F:= F);auto.
            inversion H4...
            eapply exchangeLCN with (LC:=L')...
        *
          LLfocus2 i F0. 
          eapply HDown with (F:= F);auto.
            inversion H4...
        *
          LLfocus3 i F0 B'. 
          eapply HDown with (F:= F);auto.
            inversion H4...
         *
          LLtheory F0 ...
          eapply HDown with (F:= F);auto.
            inversion H4...
          ++ 
           LLtheory (All FX) ...
            generalize (H5 x);intros.
            apply H in properX .
            apply MLLNtoSeq in properX;auto. 
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndTheory n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        all: eapply HUp with (F:=F);auto. 
        generalize (H5 x properX);intros...
    Qed.

    (* =============================================== *)
    (* PROOF OF RDownTheory *)
    (* =============================================== *)   

    Theorem InvTheoryDW: forall  n ,
        (forall m : nat, m <= n -> RIndTheory m) -> RDownTheory (n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RDownTheory.  intros B F M H FNA FNP FNN FT HD1.
      inversion HD1;subst ... 
      +
        checkPermutationCases  H1.
        ++
          assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
         
          assert(n0 |--- B0++C; (F::x); (DW F0)).
          MLLSPerm H0 H6. 
(*           apply HDown in H... *)
          LLtensor x N B0 C D.  
          apply HDown in H... 
          apply MLLNtoSeq in H10;auto.
        ++
          assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0++D; (F::x); (DW G)).
          MLLSPerm H0 H10. 

          apply HDown in H...

          LLtensor M0 x B0 C D.   
       
          apply MLLNtoSeq in H6;auto.
      +
        assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        apply HDown in H4 ...
      + 
        assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        apply HDown in H4 ... 
      + eapply UpExtension in H5...
        assert(HRI: RIndTheory x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H2 ...
      +
        assert(HRI: RIndTheory (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        apply HDown in H6 ...
        LLexists t.
    Qed.

    Theorem InvAuxTheory : forall n, RIndTheory n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndTheory.
        split; [apply RUpTheory0 | apply RDownTheory0].
      + unfold RIndTheory in *.
        split;[|simpl; rewrite Nat.sub_0_r].
        apply InvTheoryUP; assumption.
        apply InvTheoryDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionTheory : forall B L F  M,   
        theory F -> ~ IsPositiveAtom F -> ~ IsNegativeAtom F  -> 
        |-- B ; M ; UP (L++[F]) -> |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUpTheory n) by (apply InvAuxTheory).
      apply MLLStoSeqN in H2;auto. 
      destruct H2.
      generalize (HRn x);intros.
      eapply H3;eauto.
    Qed.

  End AbsorptionTheory.


  Section AbsorptionClassic.

    Definition RUp (n:nat) := forall i B L  F  M , 
      u i = true -> mt i = true -> In (i,F) B -> n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).  

    Definition RDown (n:nat) := forall i B F  M  H, 
        positiveLFormula F ->
    u i = true ->  mt i = true -> In (i,F) B -> n |--- B ; F::M ; DW H -> |-- B ; M  ; DW H.

    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 

    Lemma RDown0 : RDown 0.
    Proof with sauto;solveLL.
      unfold RDown. intros i B F M H FNA U MT FB HD.
      inversion HD...
    Qed.

    Lemma RUp0 : RUp 0.
    Proof with subst;auto;solveLL.
      unfold RUp. intros i B L F M U MT FB HD.
      destruct L.
      + inversion HD...
        LLfocus2 i Top.
      + inversion HD ...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvCopyUP: forall  n ,
        (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    Proof with sauto;solveF;solveLL.
      intros n IH.
      unfold RUp. intros i B L1 F M U MT FB HD.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD... 
        ++
        LLfocus2 i Top.
        ++ 
          apply MLLNtoSeq in H3;auto. 
        ++
        LLfocus2 i (MOr F0 G).
        apply MLLNtoSeq in H3;auto.
        ++ 
          LLfocus2 i (AAnd F0 G). 
          apply MLLNtoSeq in H4;auto.
          apply MLLNtoSeq in H5;auto. 
        ++ 
          LLfocus2 i (Quest i0 F0). 
          apply MLLNtoSeq in H3;auto. 
        ++ 
          assert(RInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          checkPermutationCases H0.
          **
            apply MLLNtoSeq in H1;auto.
            rewrite <- H6;auto.
            LLfocus2 i F.
            inversion H;inversion H0;sauto.
          **    
            LLfocus1 F0 x. 
            eapply HDown with (F:= F) (i:=i);auto.
            
            eapply exchangeLCN with (LC:=F :: x)...
            MLLSPerm H3 H1...
        *
          LLfocus2 i0 F0.
            eapply HDown with (F:= F) (i:=i);auto.
            
        * rewrite <- H2 in FB;sauto.
          inversion FB...
          LLfocus3 i0 F0 B'.
          eapply HDown with (F:= F) (i:=i);auto.
        *
          LLtheory F0. 
          eapply HDown with (F:= F) (i:=i);auto.
          ++ 
            LLfocus2 i (All FX).
            solveLL. generalize (H5 x);intro.
            apply H in properX.
            apply MLLNtoSeq in properX;auto. 
      + (* L is not empty *)
        inversion HD;subst; try(
                                 assert(RInd n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        all: eapply HUp with (F:=F) (i:=i);auto.
        intuition.   
        generalize (H5 x properX);intros...
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   

    Theorem InvCopyDW: forall  n ,
        (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RDown.  intros i B F M H FNA U MT FB HD.
      inversion HD...
       apply InPermutation in FB...
      
      + 
        checkPermutationCases H1.
        ++ 
          assert(HRI: RInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0++C; F::x0; (DW F0)).
          MLLSPerm H0 H6.

          eapply HDown in H...
          LLtensor x0 N B0 C D.  
         
          apply MLLNtoSeq in H10;auto.
          exact U. auto.
          apply in_or_app;left.
          rewrite FB in H2.
         apply aux_c in H2...
        ++
          assert(HRI: RInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0++D; F::x0; (DW G)).
          MLLSPerm H0 H10.

          eapply HDown in H...
          LLtensor M0 x0 B0 C D.  
   
          apply MLLNtoSeq in H6;auto.
          exact U. auto.
  apply in_or_app;left.
          rewrite FB in H2.
         apply aux_c in H2...
      + 
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        eapply HDown in H4 ...
        exact U. auto. auto.
      +
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        eapply HDown in H4 ...
        exact U. auto. auto.
      + eapply UpExtension in H5...
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...

        eapply HUp in H2 ...
        exact U. auto. auto.
      +
        assert(HRI: RInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HDown in H6 ...
        LLexists t.
        exact U. auto. auto.
    Qed.


    Theorem InvAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvCopyUP; assumption.
        apply InvCopyDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionClassic : forall i B L F  M,
        u i = true -> mt i = true -> In (i,F) B -> 
        (|-- B ; M ; UP (L++[F])) ->
        |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUp n) by (apply InvAux).
      apply MLLStoSeqN in H2;auto. 
      destruct H2.
      generalize (HRn x);intros. eapply H3;eauto.
    Qed.

Theorem AbsorptionClassicN : forall n i B L F  M,
        u i = true -> mt i = true -> In (i,F) B -> 
        (n |--- B ; M ; UP (L++[F])) ->
        |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUp n) by (apply InvAux).
      generalize (HRn n);intros. eapply H3;eauto.
    Qed.

    Theorem AbsorptionClassic' : forall i B L F  M,
        u i = true -> mt i = true -> In (i,F) B ->
        (|-- B ; M ; UP (L++[F])) ->
        |-- B; M  ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUp n) by (apply InvAux).
      apply MLLStoSeqN in H2;auto. 
      destruct H2.
      generalize (HRn x);intros. eapply H3;eauto.
    Qed.
    
  Theorem AbsorptionClassicSet : forall B B' L C M,
        SetU C -> SetT C -> Permutation B (C++B') -> 
        |-- B ;M ; UP (L ++ second C) -> |-- B ; M ; UP L .
    Proof with sauto.
    intros.
    revert dependent L.
    revert dependent B.
    revert dependent B'.
    revert dependent M.
    induction C;intros...
    simpl in H2...
    destruct a as [b F].
    rewrite H1.
    eapply AbsorptionClassic' with (i:=b) (F:=F)...
    solveSE.
    solveSE.
    firstorder.
    eapply IHC with (B':= (b, F) :: B')... 
    solveSE. solveSE.
    rewrite app_assoc_reverse.
    rewrite <- H1. exact H2.
    Qed.
    
 
  End AbsorptionClassic. 
  
 
Section AbsorptionLinear.

    Definition RLUp (n:nat) := forall i B B' L F M , 
      u i = false -> mt i = true -> Permutation ((i,F)::B') B -> n |--- B' ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).  

    Definition RLDown (n:nat) := forall i B B' F  M  H, 
       positiveLFormula F ->
    u i = false ->  mt i = true -> Permutation ((i,F)::B') B -> n |--- B' ; F::M ; DW H -> |-- B ; M  ; DW H.

    Definition RLInd (n:nat) := RLUp n /\ RLDown (n -1). 

    Lemma RLDown0 : RLDown 0.
    Proof with sauto;solveLL.
      unfold RLDown. intros i B B' F M H NAF ML MT FB HD.
      inversion HD...
     Qed.

    Lemma RLUp0 : RLUp 0.
    Proof with subst;auto;solveLL.
      unfold RLUp. intros i B B' L F M ML MT FB HD.
      destruct L.
      + inversion HD...
        LLfocus3 i Top B'. 
      + inversion HD ...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvCopyLUP: forall  n ,
        (forall m : nat, m <= n -> RLInd m) -> RLUp (S n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RLUp. intros i B B' L1 F M MU MT FB HD.
    (*   assert(HPR: Permutation B ((i,F)::B')).
      apply Remove_Permute in FB...
     *)  destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD... 
        ++
        LLfocus3 i Top B'.
        ++
           LLfocus3 i Bot B'.
          apply MLLNtoSeq in H3;auto. 
        ++
        LLfocus3 i (MOr F0 G) B'.
        apply MLLNtoSeq in H3;auto.
        ++ 
          LLfocus3 i (AAnd F0 G) B'. 
          apply MLLNtoSeq in H4;auto.
          apply MLLNtoSeq in H5;auto. 
        ++ 
          LLfocus3 i (Quest i0 F0) B'. 
          apply MLLNtoSeq in H3;auto. 
        ++ 
          assert(RLInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
         checkPermutationCases H0.
          **
            LLfocus3 i F B'.
            inversion H0... 
            apply MLLNtoSeq in H1;auto.
            rewrite <- H6;auto.
          **    
            LLfocus1 F0 x. 
            eapply HDown with (F:= F) (i:=i) (B':=B') ;auto.
            
            eapply exchangeLCN with (LC:=F :: x)...
            MLLSPerm H3 H1...
        *
           LLfocus2 i0 F0.
           rewrite <- FB...  
            eapply HDown with (F:= F) (i:=i) (B':=B');auto.
        *
           rewrite <- H2 in FB.
           rewrite  <- FB.
           eapply exchangeCC' with (CC:=(i0, F0) :: (i, F) :: B'0).
           perm.
           LLfocus3 i0 F0 ( (i, F) :: B'0).
           eapply HDown with (F:= F) (i:=i);auto.
        *
          LLtheory F0. 
          eapply HDown with (F:= F) (i:=i) (B':=B');auto.
          ++ 
            LLfocus3 i (All FX) B'.
            solveLL. 
            generalize (H5 x);intro.
            apply H in properX.
            apply MLLNtoSeq in properX;auto. 
      + (* L is not empty *)
        inversion HD;subst; try(
                                 assert(RLInd n) by ( apply IH;auto);
                                 destruct H as [HLUp  HLDown]; clear HLDown) ...
        1-4: eapply HLUp with (F:=F) (i:=i) (B':=B');auto.
        eapply HLUp with (F:=F) (i:=i) (B':=(i0, F0)::B')...
        rewrite <- FB...
        eapply HLUp with (F:=F) (i:=i) (B':=B')...       
        generalize (H5 x properX);intros...
        eapply HLUp with (F:=F) (i:=i) (B':=B')...       
        
        
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   

    Theorem InvCopyLDW: forall  n ,
        (forall m : nat, m <= n -> RLInd m) -> RLDown (n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RLDown.  intros i B B' F M H FNA MU MT FB HD.
      inversion HD...
      + 
        checkPermutationCases H1.
        ++ 
          assert(HRI: RLInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0++C; F::x ; (DW F0)).
          MLLSPerm H0 H6.
           
          assert(|-- (i, F) :: B0++C; x; (DW F0)). 
          eapply HDown with (i:=i) (F:=F) (B':=B0++C)...
          LLtensor x N B0 ((i, F) :: C) D.
          rewrite <- FB, H2.
          simpl... 
          LLExact H7.   
          apply MLLNtoSeq in H10;auto.
        ++
          assert(HRI: RLInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          assert(n0 |--- B0++D; F::x; (DW G)).
          MLLSPerm H0 H10.
          assert(|-- (i, F) :: B0++D; x; (DW G)). 
          eapply HDown with (i:=i) (F:=F) (B':=B0++D)...
         
          LLtensor M0 x B0 C ((i, F) :: D).
          rewrite <- FB, H2...
          apply MLLNtoSeq in H6;auto.
         LLExact H7.
      + 
        assert(HRI: RLInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        assert(|-- (i, F) :: B'; M; (DW F0)). 
        eapply HDown with (i:=i) (F:=F) (B':=B')...
        LLleft.
        rewrite <- FB...
      +
        assert(HRI: RLInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        assert(|-- (i, F) :: B'; M; (DW G)). 
        eapply HDown with (i:=i) (F:=F) (B':=B')...
        LLright.
        rewrite <- FB...
      + eapply UpExtension in H5...
        assert(HRI: RLInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        assert( |-- (i, F) :: B'; M; (UP [H])).
        eapply HUp...
        rewrite <- FB... 
      + 
        assert(HRI: RLInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        assert(|-- (i, F) :: B'; M; (DW (FX t))).
        eapply HDown with (i:=i) (F:=F)...
        LLexists t.
        rewrite <- FB... 
    Qed.


    Theorem InvLAux : forall n, RLInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RLInd.
        split; [apply RLUp0 | apply RLDown0].
      + unfold RLInd in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvCopyLUP; assumption.
        apply InvCopyLDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionLinear : forall i B B' L F  M,
        mt i = true -> Permutation ((i,F)::B') B  -> 
        |-- B' ;M ; UP (L ++ [F]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      destruct (uDec i).
      eapply AbsorptionClassic with (i:=i) (F:=F);auto.
      rewrite <- H0;firstorder.
      rewrite <- H0.
      apply weakening;auto.
      
      assert(HRn:  forall n, RLUp n) by (apply InvLAux).
      apply MLLStoSeqN in H1;auto. 
      destruct H1.
      generalize (HRn x);intros. eapply H2;eauto.
    Qed.

  Theorem AbsorptionLinearSet : forall B B' L C M,
        SetT C -> Permutation B (C++B') -> 
        |-- B' ;M ; UP (L ++ second C) -> |-- B ; M ; UP L .
    Proof with sauto.
    intros.
    revert dependent L.
    revert dependent B.
    revert dependent B'.
    revert dependent M.
    induction C;intros...
    simpl in H1...
    rewrite H0...
    destruct a as [b F].
    rewrite  H0.
    eapply AbsorptionLinear with (i:=b) (F:=F) (B':=C++B')...
    solveSE.
    eapply IHC... solveSE. 
    rewrite app_assoc_reverse.
    exact H1.
    Qed.
    
  End AbsorptionLinear. 


  Section InvExists.


    Definition RUpExists (n:nat) := forall B L M FX t, 
      uniform_oo FX -> proper t -> 
      n |--- B ;M ; UP (L ++ [FX t])  -> |-- B ; (Some FX):: M; UP L.

    Definition RDownExists (n:nat) := forall B M H FX t, 
        ~ IsPositiveAtom (FX t) -> positiveLFormula (FX t) -> uniform_oo FX -> proper t ->
        n |--- B ; (FX t)::M; DW H -> |-- B ;Some FX :: M; DW H.


    Definition RIndExists (n:nat) := RUpExists n /\ RDownExists (n -1). 

    Lemma RDownE0 : RDownExists 0.
    Proof with sauto;solveF;solveLL.
    unfold RDownExists.
     
    intros B M H FX t FNA FP Uni Ft HD.
      inversion HD...
      
      rewrite <- H0 in FNA.
      solveF.
    Qed.

   
    Lemma RUpE0 : RUpExists 0.
    Proof with subst;auto;solveF;solveLL.
      unfold RUpExists.
      intros.
      destruct L.
      + inversion H1...
        LLfocus1 (Some FX) M ...
        LLexists t.  
          rewrite <- H6.
          LLrelease... 
      + inversion H1...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   
    Theorem InvExUP: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RUpExists (S n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RUpExists.  intros B L1 M1 FX t  Hu Hp HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
        LLfocus1 (Some FX) M1...
        LLexists t.  
          rewrite <- H3.
         LLrelease...
        ++ LLfocus1 (Some FX) M1...
           LLexists t.  
           rewrite <- H0.
           LLrelease...
           apply MLLNtoSeq in H3;auto. 
        ++ LLfocus1 (Some FX) M1...
           LLexists t.  
           rewrite <- H0.
           LLrelease...
           apply MLLNtoSeq in H3;auto. 
        ++ LLfocus1 (Some FX) M1...
           LLexists t.  
           rewrite <- H0.
           LLrelease...
           apply MLLNtoSeq in H4;auto. 
           apply MLLNtoSeq in H5;auto.
        ++ LLfocus1 (Some FX) M1...
           LLexists t.  
           rewrite <- H0.
           LLrelease...
           apply MLLNtoSeq in H3;auto. 
        ++ 
          assert(RIndExists n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          checkPermutationCases H0. 
          
          LLfocus1 (Some FX) M1...
          LLexists t.  
          rewrite <- H6.
          apply MLLNtoSeq in H1;auto.
          
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H2...
            LLfocus1 (Some FX) M1... 
            LLexists t.
             rewrite <- H7.
             rewrite <- H7 in H5.
           LLrelease...
           apply MLLNtoSeq in H5;auto.
          }
          assert( n0 |--- B; (FX t)::x; (DW F)).
          MLLSPerm H3 H1.

          apply HDown in H6...
          LLfocus1 F ((Some FX)::x) ...
          rewrite H0...
          inversion H7...
          
          rewrite <- H9 in H2... 
        *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H6...
            LLfocus1 (Some FX) M1... 
            LLexists t.
             rewrite <- H8.
             rewrite <- H8 in H5.
           LLrelease...
           apply MLLNtoSeq in H5;auto. }
          eapply HDown in H3...
          LLfocus2 i F.
          eauto. 
        *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H6...
            LLfocus1 (Some FX) M1... 
            LLexists t.
             rewrite <- H8.
             rewrite <- H8 in H5.
           LLrelease...
           apply MLLNtoSeq in H5;auto.
          }
          apply HDown in H3 ...
          LLfocus3 i F B'.
          eauto.
         *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
          inversion H2...
            LLfocus1 (Some FX) M1... 
            LLexists t.
             rewrite <- H6.
             rewrite <- H6 in H5.
           LLrelease...
           apply MLLNtoSeq in H5;auto.
          }
          apply HDown in H1 ...
          LLtheory F. eauto.
        ++ 
            LLfocus1 (Some FX) M1... 
            LLexists t.
            rewrite <- H0...
            generalize(H5 x properX);intro.
            apply MLLNtoSeq in H;auto.
      +
        (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndExists n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        
        all: try eapply HUp with (t:=t);eauto.
        rewrite perm_swap.
          eapply HUp;eauto.
  
    Qed.


    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvExDW: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RDownExists (n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RDownExists.  
      intros B M H FX t HNA HP Hu Ht HD1.
      inversion HD1;subst ...
      + rewrite <- H0 in HNA.
      solveF.
      +
        checkPermutationCases H1. 
        ++ 
          eapply exchangeLCN in H6.
          2: rewrite H0...
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H6 ...
          LLtensor (Some FX::x ) N B0 C D.
          rewrite <- H1...
          apply MLLNtoSeq in H10;auto.
        ++ 
          eapply exchangeLCN in H10.
          2: rewrite H0...
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H10 ...
          LLtensor M0 (Some FX::x) B0 C D.
          rewrite <- H1...
          apply MLLNtoSeq in H6;auto.
      +                   
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H4...
      +                   
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H4...
      + eapply UpExtension in H5...
        assert(HRI: RIndExists x) by auto.
        destruct HRI as [HUp  HDown] ...

        apply HUp in H2 ...
      +
        assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          apply HDown in H6...
          LLexists t0.
    Qed.

    Theorem InvExAux : forall n, RIndExists n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndExists.
        split; [apply RUpE0 | apply RDownE0].
      + unfold RIndExists in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvExUP; assumption.
        apply InvExDW; assumption.
    Qed.


    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   

    Theorem InvEx : forall B L FX t  M, 
        uniform_oo FX -> proper t -> 
        |-- B  ;M ; UP (L++[FX t ]) -> |-- B ; Some FX::M ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUpExists n) by (apply InvExAux).
      apply MLLStoSeqN in H1.
      destruct H1.
      generalize (HRn x);intros.
      apply H2 in H1;auto.
    Qed.


    Theorem InvExC : forall i B L FX t  M, u i = true -> mt i = true ->
       In (i,Some FX) B ->
        uniform_oo FX -> proper t -> 
        |-- B ;M ; UP (L ++ [FX t]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'.
      solveF.
      apply InvEx with (t:=t);auto.
    Qed.  
    
     Theorem InvExL : forall i B B' L FX t M, u i = false -> mt i = true ->
        uniform_oo FX -> proper t -> Permutation ((i,Some FX)::B') B ->
        |-- B'  ;M ; UP (L++[FX t ]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionLinear;eauto.
      apply UpExtension'.
      solveF.
      apply InvEx with (t:=t);auto.
    Qed.
  
       Theorem InvExT : forall B L FX t M, 
        uniform_oo FX -> proper t -> theory (Some FX) ->
        |-- B  ;M ; UP (L++[FX t ]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      apply UpExtension'.
      solveF.
      apply InvEx with (t:=t);auto.
    Qed.
      
   
     
  End InvExists.

  Section InvOPlus.

    Definition RUpPlus (n:nat) := forall B L M F G, 
      n |--- B ;M ; UP (L ++ [F])  -> |-- B ; (AOr F G)::M; UP L.

    Definition RDownPlus (n:nat) := forall B M H F G, 
        positiveFormula F ->
        n |--- B ; F::M  ; DW H -> |-- B ; (AOr F G)::M; DW H.

    Definition RIndPlus (n:nat) := RUpPlus n /\ RDownPlus (n -1). 

    Lemma RDownP0 : RDownPlus 0.
    Proof with sauto;solveF;solveLL.
      unfold RDownPlus.
      intros B M H F G FP HD.
      inversion HD;subst...
    Qed.

    Lemma RUpP0 : RUpPlus 0.
    Proof with sauto;solveF;solveLL.
      unfold RUpPlus.
      intros B L M F G HD.
      destruct L.
      + inversion HD;subst...
        LLfocus1 (AOr Top G) M...
      + inversion HD...
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvPlusUP: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RUpPlus (S n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RUpPlus.  intros B L1 M1 F G HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1;subst ...
        ++
          LLfocus1 (AOr Top G). 
        ++ 
          LLfocus1 (AOr Bot G). 
          LLleft.
          apply MLLNtoSeq in H3;auto.
        ++
          LLfocus1 (AOr (MOr F0 G0) G). 
          LLleft.
          apply MLLNtoSeq in H3;auto.
        ++ 
          LLfocus1 (AOr (AAnd F0 G0) G). 
          LLleft.
          apply MLLNtoSeq in H4;auto.
          apply MLLNtoSeq in H5;auto.
        ++
          LLfocus1 (AOr (Quest i F0) G). 
          LLleft.
          apply MLLNtoSeq in H3;auto.
        ++ 
          assert(RIndPlus n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        *  
          checkPermutationCases H0. 
          LLfocus1 (AOr F G) M1...
          LLleft.
          rewrite <- H6.
          apply MLLNtoSeq in H1;auto.

          destruct (NotAsynchronousPosAtoms H4).
          2:{
            LLfocus1 (AOr F G) M1...
            LLleft.
            inversion H2...
            apply MLLNtoSeq in H5;auto.
          }
          assert(n0 |--- B; (F::x); (DW F0)).
          MLLSPerm H3 H1.
          LLfocus1 F0 ((AOr F G)::x)...
          rewrite H0...
        * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
            LLfocus1 (AOr F G) M1...
            LLleft.
            inversion H6...
            apply MLLNtoSeq in H5;auto.
          }
          eapply HDown in H3 ...
          LLfocus2 i F0. 
          exact H3. 
        * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
           LLfocus1 (AOr F G) M1...
            LLleft.
            inversion H6...
            apply MLLNtoSeq in H5;auto.
          }
          eapply HDown in H3 ...
          LLfocus3 i F0 B'. 
          exact H3. 
         * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
           LLfocus1 (AOr F G) M1...
            LLleft.
            inversion H2...
            apply MLLNtoSeq in H5;auto.
          }
          eapply HDown in H1 ...
          LLtheory F0. 
          exact H1.          
          ++
            LLfocus1 (AOr (All FX) G) M1...
            LLleft.
            solveLL.
            generalize (H5 x properX);intro.
            apply MLLNtoSeq in H;auto.
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndPlus n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown)...

        all: try eapply HUp...
        rewrite perm_swap... 
          generalize (H5 x properX);intro...
        
    Qed.    

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvPlusDW: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RDownPlus (n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RDownPlus.  intros B M  H  F G HPosF HD1.
      inversion HD1;subst ...
      + 
    
       assert(HRI: RIndPlus (S n0)) by auto.
       destruct HRI as [HUp  HDown] ...
       checkPermutationCases H1.
       ++
       eapply exchangeLCN in H6.
       2: rewrite H0...
       LLtensor ((AOr F G) ::x) N B0 C D...
       rewrite <- H1...  
       apply MLLNtoSeq in H10...
       ++
       eapply exchangeLCN in H10.
       2: rewrite H0...
       LLtensor M0  ((AOr F G) ::x) B0 C D...  
       rewrite <- H1...
       apply MLLNtoSeq in H6...
     +
       assert(HRI: RIndPlus (S n0)) by auto.
       destruct HRI as [HUp  HDown] ...
     +
       assert(HRI: RIndPlus (S n0)) by auto.
       destruct HRI as [HUp  HDown] ...
     + 
       apply UpExtension in H5...
        assert(HRI: RIndPlus x)  by auto.
        destruct HRI as [HUp  HDown] ...
      +
        assert(HRI: RIndPlus (S n0)) by auto.
        destruct HRI as [HUp  HDown] ...
        LLexists t.
    Qed.


    Theorem InvPlusAux : forall n, RIndPlus n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndPlus.
        split; [apply RUpP0 | apply RDownP0].
      + unfold RIndPlus in *.
        split.
        apply InvPlusUP; assumption.
        simpl;  rewrite Nat.sub_0_r.
        apply InvPlusDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem InvPlus : forall B L F G  M, 
    |-- B  ;M ; UP (L++[F]) -> |-- B ; (AOr F G) :: M ; UP L .
    Proof.
      intros.
      assert(HRn:  forall n, RUpPlus n) by (apply InvPlusAux).
      apply MLLStoSeqN in H.
      destruct H.
      generalize (HRn x);intros.
      eapply H0 in H;eauto.
    Qed.

   Theorem InvPlusC : forall i B L F G M, u i = true -> mt i = true ->
       In (i,AOr F G) B ->
        |-- B ;M ; UP (L++[F]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'.
      auto.
      apply InvPlus ;auto.
    Qed.  
    
     Theorem InvPlusL : forall i B B' L F G M, u i = false -> mt i = true ->
        Permutation ((i,AOr F G)::B') B  ->
        |-- B'  ;M ; UP (L++[F]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionLinear;eauto.
      apply UpExtension'. auto.
      apply InvPlus;auto.
    Qed.

     Theorem InvPlusT : forall L F G B M, 
        theory (AOr F G) ->
        |-- B  ;M ; UP (L++[F]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      apply UpExtension'.
      auto.
      apply InvPlus ;auto.
    Qed.
    
    Lemma OPlusComm : forall B M F G X n,
     n |--- B ; AOr F G::M ; X -> n |--- B ; AOr G F::M ; X.
    Proof with sauto;solveF;try solveLL.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + 
        inversion H...
      + 
        inversion H0...
        ++
        checkPermutationCases H2. 
          eapply exchangeLCN in H7.
           2: rewrite H2...
          eapply H in H7...
          LLtensor (AOr G F::x) N B0 C D...
          rewrite <- H9...
          eapply exchangeLCN in H8.
           2: rewrite H2...
          eapply H in H8...
          LLtensor M0 (AOr G F::x) B0 C D...
          rewrite <- H9... 
        ++
          assert (n |--- B; AOr F G::(M ++ [F0]); (UP M0)).
          LLExact H3.
          eapply H in H1...
          LLExact H1.
        ++
        checkPermutationCases H3. 
          LLfocus1...
          eapply exchangeLCN. 
          rewrite <- H6... 
          inversion H4...

          LLfocus1 F0  (AOr G F::x)...
          rewrite H3...
          eapply exchangeLCN in H4. 
          2: rewrite H5... 
          apply H in H4...
       ++
       LLfocus2 i F0.
       ++
       LLfocus3 i F0 B'.
          
        ++
       LLtheory F0.
        ++ 
          LLexists t. 
       
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM (FLIPPING F and G)   *)
    (* =============================================== *)   
    Theorem InvPlusComm: forall B L F G  M, 
     |-- B  ;M ; UP (L++[G]) -> |-- B ; (AOr F G)::M ; UP L .
    Proof.
      intros.
      apply InvPlus with (G:=F)in H;auto.
      apply MLLStoSeqN in H.
      destruct H.
      apply OPlusComm in H.
      apply MLLNtoSeq with (n:=x) in H;auto.
    Qed.

    Theorem InvPlusCComm : forall i B L F G M, u i = true -> mt i = true ->
       In (i,AOr F G) B ->
        |-- B ;M ; UP (L++[G]) -> |-- B ; M ; UP L .
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply UpExtension'. auto.
      apply InvPlusComm ;auto.
    Qed.  
    
     Theorem InvPlusLComm : forall i B B' L F G M, u i = false -> mt i = true ->
        Permutation ((i, AOr F G):: B') B ->
        |-- B'  ;M ; UP (L++[G]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionLinear;eauto.
      apply UpExtension'. auto.
      apply InvPlusComm;auto.
    Qed.
    
    Theorem InvPlusTComm : forall L F G B M, 
        theory (AOr F G) ->
        |-- B  ;M ; UP (L++[G]) -> |-- B ; M ; UP L .
    Proof.
       intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      apply UpExtension'. auto.
      apply InvPlusComm ;auto.
    Qed.
    
    
  End InvOPlus.

  (* =============================================== *)
  (** Invertibility of Tensor *)
  (* =============================================== *)   
  Section InvTensor.

 Definition RUpTensor (nm:nat) := forall B C D L M L' M' F G n m, 
      nm = n + m ->  (* isFormulaL L -> *)
      SetU B ->
      SetL C ->
      SetL D ->
      n |--- B++C ;M ; UP (L ++ [F]) -> 
      m |--- B++D ;M' ; UP (L' ++ [G])  -> 
        |-- B++C++D ; (MAnd F  G) :: M ++ M'; UP (L ++ L').

    Definition RDownTensor (nm:nat) := forall B C D M M' H F G n m, 
        nm = n + m -> positiveFormula F -> 
        SetU B ->
        SetL C ->
        SetL D ->
        n |--- B++C ; F::M; DW H -> 
        m |--- B++D ; M' ; UP [G] -> 
          |-- B++C++D; (MAnd F G) :: M ++ M'  ; DW H.

    Definition RIndTensor (n:nat) := RUpTensor n /\ RDownTensor (n -1). 

    Lemma RDownT0 : RDownTensor 0.
    Proof with sauto;solveF;try solveLL.
      unfold RDownTensor. 
      intros *. intros MN FP P1 P2 P3 HD1 HD2.
    
      symmetry in MN. 
      apply Nat.eq_add_0 in MN.
      destruct MN...

      inversion HD1...
     Qed.

    Lemma RUpT0 : RUpTensor 0.
    Proof with sauto;solveF;try solveLL.
      unfold RUpTensor. 
      intros *.
      intros MN  P1 P2 P3 HD1 HD2.
      symmetry in MN. apply Nat.eq_add_0 in MN.
      destruct MN...
      inversion HD1...
      destruct L;destruct L';simpl in *.
      +
        inversion HD1...
        inversion HD2...
        LLfocus1 (MAnd Top  Top) (M++M')... 
        LLtensor M M' B C D. 
      + 
        inversion H3... inversion HD2...
      + 
        inversion H3 ...
      + 
        inversion H3 ...
    Qed.
    (* =============================================== *)
    (* MAnd F G COMMUTES *)
    (* =============================================== *)
    Lemma TensorComm : forall B M F G X n, n |--- B ; MAnd F G::M; X -> n |--- B ; MAnd G F::M; X.
    Proof with sauto;solveF;try solveLL.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + 
        inversion H...
      + 
        inversion H0...
        ++ 
          checkPermutationCases H2. 
        * eapply exchangeLCN in H7.
         2: rewrite H2...
          apply H in H7...
          LLtensor (MAnd G F::x) N B0 C D.
          rewrite <- H9...
        * eapply exchangeLCN in H8.
         2: rewrite H2...
          apply H in H8...
          LLtensor M0 (MAnd G F::x) B0 C D.
          rewrite <- H9... 
          ++ 
            assert(n |--- B; MAnd F G::(M ++ [F0]); (UP M0)).
            LLExact H3.
            apply H in H1...
            LLExact H1.
          ++
          checkPermutationCases H3. 
            2:{ 
             LLfocus1 F0 (MAnd G F::x).
             rewrite H3...
              apply H...
              LLExact H4.   }
              inversion H4...
            LLfocus1.
            LLtensor N  M0 B0 D C.
            rewrite <- H6... rewrite H5...
            rewrite H7...
          ++  
            LLfocus2 i F0 ...
          ++  
            LLfocus3 i F0 B' ...
         
          ++  
            LLtheory F0 ...
         
          ++ 
            LLexists t. 
           
    Qed.


    Lemma TensorComm' : forall B M F G X , |-- B ; MAnd F  G::M ; X -> |-- B ; MAnd G  F::M; X.
    Proof.
      intros.
      apply MLLStoSeqN in H.
      destruct H.
      apply TensorComm in H.
      eapply MLLNtoSeq in H;eauto.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Cases when one of the lists is not empty *)
    (* =============================================== *)
    Lemma InvTensorConsNil (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) B C D (L1 M1 : list oo)
     (l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
       isFormulaL L1 -> 
       SetU B ->
       SetL C ->
       SetL D ->
       n' |--- B++C; M1; UP (L1 ++ [F]) -> 
       m' |--- B++D; M2; UP (l :: L2 ++ [G]) -> 
          |-- B++C++D; (MAnd F G) :: M1 ++ M2; UP (L1 ++ l :: L2).
    Proof with sauto;solveF;try solveLL.
      intros. 
      inversion H5...
      + apply EquivAuxTop...
      + apply EquivAuxBot...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with (n:=n') (m:=n) (B:=B) (D:=D)...
      + apply EquivAuxPar...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n:=n') (m:=n) (B:=B) (D:=D)...
      + apply EquivAuxWith...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n:=n') (m:=n) (B:=B) (D:=D)...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n:=n') (m:=n) (B:=B) (D:=D)...
      + destruct (uDec i).
        apply EquivAuxQuest...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        rewrite app_comm_cons.
        eapply HUp with(n:=n') (m:=n)...
        rewrite <- app_comm_cons.
         eapply weakeningN;auto.
        apply EquivAuxQuest...
        LLPerm (B ++ C ++ (i, F0) :: D).
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        eapply HUp with(n:=n') (m:=n)...
        LLExact H10. 
      +
        apply EquivAuxStore...
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
        assert(|-- B++C++D; F ⊗ G :: M1 ++ l::M2; UP (L1 ++ L2)).
        eapply HUp with(n:=n') (m:=n)...
        LLExact H6.
      +
        apply EquivAuxForAll;intros...
        generalize (H12 t H6);intro.
        assert(HUp : RUpTensor(n' + n)) by (apply IH;lia).
        eapply HUp with(n:=n') (m:=n) (B:=B) (D:=D)...
    Qed.

Lemma InvTensorConsNil' (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) B C D (L1 M1 : list oo)
     (l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
       L1 <> [] -> 
       SetU B ->
       SetL C ->
       SetL D ->
       n' |--- B++C; M1; UP (L1 ++ [F]) -> 
       m' |--- B++D; M2; UP (l :: L2 ++ [G]) -> 
          |-- B++C++D; (MAnd F G) :: M1 ++ M2; UP (L1 ++ l :: L2).
    Proof with sauto;solveF;try solveLL.
      intros. 
      inversion H4...
      + apply ListConsApp in H10...
         rewrite <- app_comm_cons...
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        rewrite <- app_comm_cons...
        eapply HUp with (n:=n) (m:=m')...  
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        rewrite <- app_comm_cons...
        repeat rewrite app_comm_cons...
        eapply HUp with (n:=n) (m:=m') (B:=B) (D:=D)... 
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        rewrite <- app_comm_cons...
           repeat rewrite app_comm_cons.
        eapply HUp with (n:=n) (m:=m') (B:=B) (D:=D)...
           repeat rewrite app_comm_cons.
        eapply HUp with (n:=n) (m:=m') (B:=B) (D:=D)...
      + apply ListConsApp in H6...
        destruct (uDec i).
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        rewrite <- app_comm_cons...
        rewrite app_comm_cons. 
        eapply HUp with (n:=n) (m:=m')... 
        rewrite <- app_comm_cons.  
        eapply weakeningN;auto.
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        rewrite <- app_comm_cons...
        LLPerm(B ++ ((i, F0) :: C) ++ D).
        eapply HUp with (n:=n) (m:=m')... 
        LLExact H10...
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
         rewrite <- app_comm_cons...
         assert(|-- B++C++D; F ⊗ G :: (F0:: M1) ++ M2; UP (x ++ l :: L2)).
        eapply HUp with (n:=n) (m:=m') (B:=B) (D:=D)...
        LLExact H6. 
      + apply ListConsApp in H6...
        assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
        rewrite <- app_comm_cons...
                repeat rewrite app_comm_cons.

        eapply HUp with (n:=n) (m:=m') (B:=B) (D:=D)...
       rewrite <- app_comm_cons...
 
    Qed.


    (* ================================================ *)
    (* PROOF OF RUP *)
    (* Case when the 2 formulas are async. or pos. atoms*)
    (* ================================================ *)

    Lemma ITCaseAsyncAsync:
      forall n m B C D M1 M2 F G, 
      negativeFormula F -> 
      negativeFormula G -> 
       SetU B ->
       SetL C ->
       SetL D ->
       (n |--- B++C; M1; UP [F]) -> 
       (m |--- B++D; M2; UP [G]) -> 
       |-- B++C++D; (MAnd F  G):: M1 ++ M2; UP [].
    Proof.
      intros.
      LLfocus1 (MAnd F G). 
      LLtensor M1 M2 B C D.
      LLrelease.
      apply MLLNtoSeq in H4;auto.

      LLrelease.
      apply MLLNtoSeq in H5;auto.
   Qed.

    (** We assume that the theory produces only well-formed LL formulas *)
    Hypothesis TheoryIsFormula: forall P, theory P -> isFormula P.

    Lemma ITAsyncSync  :
      forall nm n m B C D M1 M2 F G,
        negativeFormula F ->  positiveLFormula G ->         
        (forall m : nat, m <= nm -> RIndTensor m) -> nm = n + m -> 
       SetU B ->
       SetL C ->
       SetL D ->
        n |--- B++C; M1; UP [F] ->  
        m |--- B++D; G::M2; UP [] ->  
          |-- B++C++D; (MAnd F G) :: M1 ++ M2; UP [].
    Proof with subst;auto;auto;solveF;try solveLL.
      intros. 
      apply NotAsynchronousPosAtoms in H0; destruct H0 as [AG | AG].
       
      2:{
        (* G is a positive atom... then, LLrelease works (Lemma  ITCaseAsyncAsync) *)
        eapply ITCaseAsyncAsync with (n:=n) (m:=S m) (B:=B) (D:=D);eauto. }
      +
        (* G cannot do LLrelease *)
       
        inversion H7...
        ++ checkPermutationCases H8.  
        * LLfocus1 (MAnd F G). 
          LLtensor M1 M2 B C D.
          LLrelease. 
          apply MLLNtoSeq in H6;auto. 
          rewrite <- H11.
          apply MLLNtoSeq in H9;auto. 
        * 
          LLfocus1 F0 ((MAnd F G) ::M1 ++ x)...
          rewrite H8...
          
          assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto); destruct IH2 as [HUp HDw].
          assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
          apply TensorComm'.
          rewrite (Permutation_app_comm M1).
          LLPerm (B++D++C).
           eapply HDw with (m:= n) (n:= n0);try(lia)...
          eapply exchangeLCN in H9.
          2:rewrite H10... 
          LLExact H9.
      
     ++ LLPerm (B++D++C).
            LLfocus2 i F0.  apply in_or_app.
            left.
            apply in_app_or in H10...
            apply InPermutation in H2...
            rewrite H2 in H5. 
            inversion H5... 
          assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
         destruct IH2 as [HUp HDw].
         assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).
            eapply HDw with (m:= n) (n:= n0);try(lia)...
          ++ 
           checkPermutationCases H10.
           rewrite H10 in H3.
           inversion H3...
          LLfocus3 i F0 (B++x++C).
          rewrite app_comm_cons. 
          rewrite H10...
             assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
         destruct IH2 as [HUp HDw].
         assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).
              
            eapply HDw with (m:= n) (n:= n0);try(lia)...
            rewrite H10 in H5.
            inversion H5...
             rewrite H12...
          ++
            LLtheory F0.
            LLPerm(B++D++C). 
            assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
              destruct IH2 as [HUp HDw].
            assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).  
            eapply HDw with (m:= n) (n:= n0);try(lia)...
        
Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Case when Both formulas are not Async *)
    (* =============================================== *)
    Lemma ITSyncSync : forall nm n m B C D M1 M2 F G, 
   positiveLFormula F -> positiveLFormula G ->  
    (forall m : nat, m <= nm -> RIndTensor m) -> S nm = S n + S m -> 
       SetU B ->
       SetL C ->
       SetL D ->     
              S n |--- B++C; M1 ; UP [F] -> 
              S m |--- B++D; M2 ; UP [G] ->  
              |-- B++C++D; (MAnd F G)::M1 ++ M2; UP [].
    Proof with subst;auto;solveF;try solveLL.
      intros * . 
      intros AF AG IH Hnm P1 P2 P3 HD1 HD2. 
      apply NotAsynchronousPosAtoms in AF; destruct AF as [AF | AF];
        apply NotAsynchronousPosAtoms in AG; destruct AG as [AG | AG].
              4:{  (* Both are positive atoms *)
        eapply ITCaseAsyncAsync with (B:=B) (D:=D);eauto. }
      3:{  (* F is a positive atom *)
        assert(positiveLFormula G)...
        assert(positiveLFormula F)...
          inversion HD2...
        eapply ITAsyncSync with (nm:=nm) (n:= S n) (m:= m) (B:=B) (D:=D)... lia. }
        2:{ (* G is a positive atom *) 
        assert(positiveLFormula G)...
        assert(positiveLFormula F)...
          inversion HD1...
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).  
            LLPerm (B++D++C).
            eapply ITAsyncSync with (nm:=nm) (n:= S m) (m:= n) ;try lia... }
 
  (* F nor G can do LLrelease *)
        inversion HD1...
        inversion HD2...
          
        inversion H5;subst...
        2:{
        
        LLfocus2 i F0.
        rewrite app_assoc.
        apply in_or_app... 
          assert (IH' : RIndTensor (m + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : m + S (S n0) - 1 = m + (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n:= n0) (m:= S m);try lia...
        }
       3:{ 
        LLtheory F0. 
          assert (IH' : RIndTensor (m + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : m + S (S n0) - 1 = m + (S n0)) by lia;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n:= n0) (m:= S m);try lia...
          }

        ++ (* DEC1 DEC1 *)
          assert (IH' : RIndTensor (m + S (S n0))) by ( apply IH; lia).
          destruct IH' as [HUp  HDw].
          assert(Hn : m + S (S n0) - 1 = m + (S n0)) by lia;rewrite Hn in HDw;clear Hn.
       
        checkPermutationCases H0.
       2:{   LLfocus1 F0 ((MAnd F G) :: x++M2).
          rewrite H0...
       
          eapply HDw with (n:= n0) (m:= S m) (B:=B) (D:=D);try lia... 
           eapply exchangeLCN in H1.
          2: rewrite H3... 
          auto.  }
          
           eapply exchangeLCN in H1.
          2: rewrite  H8... 
          clear H8.
          inversion H7...
          -
          checkPermutationCases H2.
        2:{ LLfocus1 F0 ((MAnd F G)::M1++x).
          rewrite H2...
       LLPerm (B++D++C).
            
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).  
                 eapply HDw with (n:= n) (m:= S (S n0));try lia... 
             
                 LLExact H3. }
 
          LLfocus1 (MAnd F G).  
          LLtensor M1 L'0 B C D.
          rewrite H10...
          apply MLLNtoSeq in H1...
          apply MLLNtoSeq in H3...
          -
          LLPerm (B++D++C).
            
           LLfocus2 i F0.
            rewrite app_assoc.
            apply in_or_app... 
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).  
            
          eapply  HDw with (n:= n) (m:= S (S n0));try lia...
          -
            checkPermutationCases H8. 
            rewrite H8 in P1.
            inversion P1...
             LLfocus3 i F0 (B++ x ++ C). 
           rewrite H8...  
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).  
          eapply  HDw with (n:= n) (m:= S (S n0));try lia...
          rewrite H8 in P3.
          inversion P3...
          rewrite H11...
         -
          LLPerm(B++D++C).
         LLtheory F0. 
            apply TensorComm'.
            rewrite (Permutation_app_comm M1).
             
          eapply  HDw with (n:= n) (m:= S (S n0));try lia...
    ++
       checkPermutationCases H2. 
       rewrite H2 in P1.
       inversion P1...
       LLfocus3 i F0 (B ++ x ++ D)...
      rewrite H2...
       assert (IH' : RIndTensor (S m + S n0)) by ( apply IH; lia).
       destruct IH' as [HUp  HDw].
       assert(Hn : S m + S n0 - 1 = m + S n0) by lia;rewrite Hn in HDw;clear Hn.
            
       eapply  HDw with (n:= n0) (m:=S m) ;try lia...
        rewrite H2 in P2.
        inversion P2...
        rewrite H9...
       Qed.
     (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)
    Theorem InvTensorUP: forall  nm , 
    (forall m : nat, m <= nm-> RIndTensor m) -> RUpTensor (S nm).
    Proof with sauto;solveF; try solveLL.
      intros nm IH.
      unfold RUpTensor.
      intros B C D L1  M1 L2 M2 F  G n' m' HNM  P1 P2 P3 HD1 HD2.
      destruct L1;destruct L2;simpl in *.
      + (* L1 and L2 are Empty *)   
        inversion HD1;inversion HD2;subst;
         
          try(
              match goal with
              | [  |- |-- ?B++?C++?D; (MAnd ?F ?G)::?M1 ++ ?M2; UP [] ]
                => tryif (assert(HAFG : negativeFormula F /\ negativeFormula G) by (split;constructor;auto))
                then
                  eapply ITCaseAsyncAsync;eauto
                else idtac
              end)... 
 
       eapply ITAsyncSync with  (nm := nm) (n:= n') (m:=n0) ;try lia...
       
 1-4:       eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) (D:=D);try lia...

  1-5:        LLPerm(B++D++C).
  1-5:          apply TensorComm'.
  1-5:          rewrite (Permutation_app_comm M1).  
        eapply ITAsyncSync with  (nm := nm) (n:= m') (m:=n) ;try lia...
         
  1-4:
        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n);try lia...
        
        (* Both F and G are not asynchronous formulas *)
        eapply  ITSyncSync with (nm := nm) (n:=n) (m:=n0) (B:=B) (D:=D)...

LLPerm(B++D++C).
            apply TensorComm'.
            rewrite (Permutation_app_comm M1). 
        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) ;try lia...
      
        eapply ITAsyncSync with  (nm := nm) (n:=S n) (m:=n0);try lia...
      + (* L1 is empty and L2 is not empty *)
        eapply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m')  (L1 := [])...
        
       + (* L1 is not empty and L2 is empty *)
        sauto.
        LLPerm (B++D++C). 
            apply TensorComm'.
            rewrite (Permutation_app_comm M1). 
        rewrite <- (app_nil_l (o::L1)).
        eapply InvTensorConsNil with (nm:=nm) (n':=m') (m':=n') ;try lia...
      +  (* L1 and L2 are not empty *)
        apply InvTensorConsNil' with (nm:=nm) (n':=n') (m':=m') (L1 := o :: L1)...
        discriminate.
   Qed.


Lemma PermSetUSetL B C B0 C0 D0: 
     SetU B -> SetL C
-> Permutation (B ++ C) (B0 ++ C0 ++ D0)
-> SetU B0
-> SetL C0
-> SetL D0 -> Permutation B B0 /\ Permutation C (C0++D0).
Proof with sauto.
   revert B C B0 C0 D0. 
  induction B;intros.
  -
  simpl in H1.
  rewrite H1 in H0.
  apply Forall_app in H0...
  pose proof (SetKK4_then_empty B0 H2 H5)... (* SETXempty *)
  destruct B0...
  inversion H2;inversion H5...
  -
  simpl in H1.
  checkPermutationCases H1.
  assert(Permutation B x /\ Permutation C (C0 ++ D0)).
  eapply IHB...
  solveSE.
  rewrite H1 in H2. solveSE.
  rewrite H1...
  assert(Permutation B x /\ Permutation C (C0 ++ D0)).
  eapply IHB...
  solveSE.
  rewrite H1 in H2. solveSE.
  sauto.
1-2:  checkPermutationCases H1.
 1,3: rewrite H1 in H3.
 1-2: inversion H; inversion H3...
 1,2: rewrite H1 in H4.
 1-2: inversion H; inversion H4...
Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)
    Theorem InvTensorDW: forall  n , (forall m : nat, m <= n -> RIndTensor m) -> RDownTensor (n).
    Proof with sauto;solveF;try solveLL.
      intros n IH.
      unfold RDownTensor.
      intros *. intros Hnm HPosF P1 P2 P3 HD1 HD2.
      inversion HD1...
      +
      checkPermutationCases H1.
        ++ 
          assert(HRI: RIndTensor (S m + n1)).  apply IH. lia. 
          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          pose proof  (PermSetUSetL P1 P2 H2 H3 H4 H5)...
          LLtensor (MAnd F G::x ++ M') N B0 (C0++D) D0.
          rewrite <- H1...
          rewrite H7, H8...
          apply Forall_app...
          eapply HDown with (m:=m) (n:=n1);try lia...
          rewrite <- H0...
          rewrite <- H7...
          
          apply MLLNtoSeq in H10;auto.
          
        ++ 
          assert(HRI: RIndTensor (S m + n1)).  apply IH. lia. 

          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.
           pose proof  (PermSetUSetL P1 P2 H2 H3 H4 H5)...
          LLtensor M0 (MAnd F G::x ++ M') B0 C0 (D0++D).
          rewrite <- H1...
          rewrite H7, H8...
          apply Forall_app...
          apply MLLNtoSeq in H6;auto.
          eapply HDown with (m:=m) (n:=n1);try lia...
          rewrite <- H0...
          rewrite <- H7...
       +
        assert(HRI: RIndTensor (S m +n1)) by (apply IH ; lia).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : S m + n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
        LLleft. 
        eapply HDown  with (n:=n1) (m:=m)  (B:=B) (D:=D) ... lia. 
      +
        assert(HRI: RIndTensor (S m +n1)) by (apply IH ; lia).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : S m + n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
        LLright. 
        eapply HDown  with (n:=n1) (m:=m)  (B:=B) (D:=D)... lia. 
      +
        apply UpExtension in H5 ...
        assert(HRI: RIndTensor (m + x)). apply IH. lia.
        destruct HRI as [HUp  HDown]. clear HDown.
        rewrite <- (app_nil_r [H]). 
        eapply HUp with (n:= x )(m:= m) (B:=B) (D:=D)...
        lia.
      +   
        assert(HRI: RIndTensor (m + S n1 )) by ( apply IH;lia).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : m + S n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
        LLexists t. 
                eapply HDown with (n:=n1) (m:=m) (B:=B) (D:=D)...  
        lia.
    Qed.

    Theorem InvTensorAux : forall n, RIndTensor n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndTensor.
        split; [apply RUpT0 | apply RDownT0].
      + unfold RIndTensor in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvTensorUP; assumption.
        apply InvTensorDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)

    Theorem InvTensor : forall B C D L L' F G  M M',
      SetU B ->
       SetL C ->
       SetL D ->  
        |-- B++C ; M ; UP (L++[F]) -> 
        |-- B++D ; M'; UP (L'++[G]) -> 
        |-- B++C++D ; MAnd F G :: M ++ M' ; UP (L ++ L') .
    Proof with sauto;solveF;solveLL.
      intros.
      assert(HRn:  forall n, RUpTensor n) by (apply InvTensorAux).
      apply MLLStoSeqN in H2.
      apply MLLStoSeqN in H3.
      destruct H2.
      destruct H3.
      generalize (HRn (x + x0));intros.
      eapply H4 with (B:=B) (D:=D)...
    Qed.

    Theorem InvTensorPerm : forall B C D L L' F G  M M',
      SetU B ->
       SetL C ->
       SetL D ->  
        |-- B++C ; M ; UP (L++[F]) -> 
        |-- B++D ; M'; UP (L'++[G]) -> 
        |-- B++C++D ; MAnd F G :: M ++ M' ; UP (L ++ L') .
    Proof with sauto;solveF;solveLL.
      intros.
      assert(HRn:  forall n, RUpTensor n) by (apply InvTensorAux).
      apply MLLStoSeqN in H2.
      apply MLLStoSeqN in H3.
      destruct H2.
      destruct H3.
      generalize (HRn (x + x0));intros.
      eapply H4 with (B:=B) (D:=D)...
    Qed.


    Theorem InvTensorC : forall i B C D L L' F G M M', u i = true ->   mt i =   true ->   In (i,MAnd F G) B ->
      SetU B ->
       SetL C ->
       SetL D ->  
        |-- B++C ; M ; UP (L++[F]) -> 
        |-- B++D ; M'; UP (L'++[G]) -> 
        |-- B++C++D ; M ++ M' ; UP (L ++ L').
    Proof.
      intros.
      eapply @AbsorptionClassic;eauto.
      apply in_or_app. left.
      exact H1.
      apply UpExtension'. auto.
      eapply InvTensor;auto. 
    Qed.  
    
     Theorem InvTensorL1 : forall i B C D C' L L' F G M M', u i = false ->   mt i = true -> Permutation ((i,MAnd F G):: C') C ->
      SetU B ->
       SetL C ->
       SetL D ->  
         |-- B++C' ; M ; UP (L++[F]) -> 
         |-- B++D ; M'; UP (L'++[G]) -> 
         |-- B++C++D ; M ++ M' ; UP (L ++ L').
    Proof with sauto.
      intros.
      LLPerm((i, MAnd F G) :: B++C'++ D).
      rewrite <- H1...
      eapply @AbsorptionLinear with (F:=MAnd F G)...       apply UpExtension'. auto.
      eapply InvTensor...
      rewrite <- H1 in H3. 
      solveSE.
 Qed.     
     
     Theorem InvTensorL2 : forall i B C D D' L L' F G M M', u i = false ->   mt i = true -> Permutation ((i,MAnd F G):: D') D ->
      SetU B ->
       SetL C ->
       SetL D ->  
         |-- B++C ; M ; UP (L++[F]) -> 
         |-- B++D' ; M'; UP (L'++[G]) -> 
         |-- B++C++D ; M ++ M' ; UP (L ++ L').
    Proof with sauto.
      intros.
      LLPerm((i, MAnd F G) :: B++C++ D').
      rewrite <- H1...
      eapply @AbsorptionLinear with (F:=MAnd F G)...       apply UpExtension'. auto.
      eapply InvTensor...
      rewrite <- H1 in H4. 
      solveSE.
 Qed.     
     
    Theorem InvTensorT : forall B C D L L' F G M M', 
       theory (MAnd F G) ->
      SetU B ->
       SetL C ->
       SetL D -> 
        |-- B++C ; M ; UP (L++[F]) -> 
        |-- B++D ; M'; UP (L'++[G]) -> 
        |-- B++C++D ; M ++ M' ; UP (L ++ L').
    Proof.
      intros.
      eapply @AbsorptionTheory;eauto.
      intro Hc. inversion Hc.
      apply UpExtension'. auto.
      eapply InvTensor;auto.
    Qed.  
      
  End InvTensor.
End InvPosPhase.
