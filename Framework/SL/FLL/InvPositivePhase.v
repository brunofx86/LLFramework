(** Invertibility lemmas: Positive phase

This file proves some invertibility lemmas showing that positive rules
can be switched.
*)

Require Export LL.Misc.Hybrid.
Require Export LL.Framework.SL.FLL.Tactics.
Require Export LL.Framework.SL.FLL.Reasoning.
Require Export LL.Framework.SL.FLL.InvNegativePhase.

Set Implicit Arguments.

Section InvPosPhase.
Context `{OLS: OLSig}.
Variable th : oo -> Prop.

Ltac solveList :=
  match goal with
  [ H : [] = ?M ++ [?F] |- _ ] =>
    symmetry in H; apply app_eq_nil in H;inversion H as [H' H''];inversion H''
  | [ H :  ?M ++ [?F] = [ ] |- _ ] =>
    apply app_eq_nil in H; inversion H as [H' H''];inversion H''
  end.

Ltac seqPermutation := 
  match goal with
  [ H : Permutation ?M ?T ,
    Hs : seq ?th ?B ?M ?Arrow |- _ ] =>
    assert(seq th B T Arrow) by (refine(exchangeLC _ Hs); rewrite H; auto)
  | [ H : Permutation ?T ?M ,
    Hs : seq ?th ?B ?M ?Arrow |- _ ] =>
    assert(seq th B T Arrow) by (refine(exchangeLC _ Hs); rewrite <- H; auto)  
  end.

Ltac seqPerm H S := 
  match type of H with
    Permutation ?M ?T => match type of S with
    seq ?th ?B ?M ?Arrow => 
      assert(seq th B T Arrow); refine(exchangeLC _ S);rewrite H;auto
      | flln ?th ?n ?B ?M ?Arrow => 
      assert(flln th n B T Arrow); refine(exchangeLCN _ S);rewrite H;auto
    end
      | Permutation ?T ?M => match type of S with
      seq ?th ?B ?M ?Arrow => 
      assert(seq th B T Arrow); refine(exchangeLC _ S);rewrite H;auto
      | flln ?th ?n ?B ?M ?Arrow => 
      assert(flln th n B T Arrow); refine(exchangeLCN _ S);rewrite H;auto
    end                      
  end.   

Section AbsorptionTheory.

Theorem AbsorptionPerp :  forall n B M A X , th (perp A) -> flln th n B ((perp A) :: M) X -> flln th n B M X.
Proof with solveLL.
  induction n;intros *; intros Ht H;inversion H.
  all: subst;eauto;clear H...
  * checkPermutationCases H1. 
    + LLtensor x N. 
        eapply IHn with (A:=A)...
        HProof.
    + LLtensor M0 x. 
       eapply IHn with (A:=A)...
       HProof.
  * eapply IHn with (A:=A)...
     HProof.
  * checkPermutationCases H2. 
    + LLtheory (perp A).
       HProof.
    + LLfocus1 F x.
       eapply IHn with (A:=A)...
       HProof.
Qed.

Theorem AbsorptionPerp2 :  forall n B M A L , th (perp A) -> flln th n B M (UP (L++[perp A])) -> flln th n B M (UP L).
Proof with sauto;solveLL.
  intro.
  induction n;intros.
  inversion H0... 
  * apply ListConsApp in H5...
  * inversion H0...
     all: try match goal with
     [H: _ :: _ = _ ++ [_] |- _] => apply ListConsApp in H
    end;sauto; solveLL; try solve [apply IHn with (A:=A);sauto].
    -  apply H6 in properX.
      apply IHn with (A:=A)...
    - eapply AbsorptionPerp with (A:=A)...
      eapply heightGeqFLLNLEx.
      2: exact H6. 
      perm. lia.
 Qed.      

Theorem AbsorptionPerp' :  forall B M A L , th (perp A) -> flls th B M (UP (L++[perp A])) -> flls th B M (UP L).
Proof with sauto.
  intros.
  apply FLLStoFLLN in H0...
  apply  AbsorptionPerp2 in H0...
  apply FLLNtoFLLS in H0...
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
    th F -> ~ posAtom F -> ~ negAtom F ->
    flln th n B M (UP (L ++ [F]))  -> flls th B M (UP L ).

Definition RDownTheory (n:nat) := forall B  F  M  H, 
    posLFormula F -> ~ posAtom F -> ~ negAtom F -> th F -> 
    flln th n B (F::M) (DW H) -> flls th B M (DW H).

Definition RIndTheory (n:nat) := RUpTheory n /\ RDownTheory (n -1). 

Lemma RDownTheory0 : RDownTheory 0.
Proof with sauto.
  unfold RDownTheory. intros B F M H FP FNP FNN TH HD.
  inversion HD... 
  solvePolarity.
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
Proof with subst;auto;solvePolarity;solveLL.
  intros n IH.
  unfold RUpTheory.
  intros B L1 F M1 FT FNA FNN HD1.
  destruct L1;simpl in *.
  + (* L1 is Empty *)
    inversion HD1... 
    - LLtheory Top. 
    - LLtheory (F0 & G). 
      apply FLLNtoFLLS in H4;auto.
      apply FLLNtoFLLS in H5;auto. 
    - apply FLLNtoFLLS in H3;auto. 
    - LLtheory (F0 ⅋ G). 
      apply FLLNtoFLLS in H3;auto. 
    - LLtheory (? F0).
      apply FLLNtoFLLS in H3;auto.
      solveLL. LLPerm (F0::B)... 
    - LLtheory (∀{ FX}) ...
      generalize (H5 x);intros.
      apply H in properX .
      apply FLLNtoFLLS in properX;auto. 
   - assert(RIndTheory n) by ( apply IH;auto).
     destruct H as [HUp  HDown].
     inversion H5;subst ...
    { checkPermutationCases H0.
       +  LLtheory F.
           apply FLLNtoFLLS in H1;auto.
           rewrite <- H6;auto.
      + LLfocus1 F0 x.
         eapply HDown with (F:= F)...
         HProof. }
   { LLfocus2  F0. 
      eapply HDown with (F:= F);auto. }
   { LLtheory F0 ...
     eapply HDown with (F:= F);auto. }
  + (* L is not empty *)
    inversion HD1;subst; try(
    assert(RIndTheory n) by ( apply IH;auto);
    destruct H as [HUp  HDown]; clear HDown) ...
    all: eapply HUp with (F:=F);auto.
    LLPerm (F0::B)...  
    generalize (H5 x properX);intros...
Qed.

(* =============================================== *)
(* PROOF OF RDownTheory *)
(* =============================================== *)   

Theorem InvTheoryDW: forall  n ,
(forall m : nat, m <= n -> RIndTheory m) -> RDownTheory (n).
Proof with sauto;solvePolarity;solveLL.
  intros n IH.
  unfold RDownTheory.  intros B F M H FNA FNP FNN FT HD1.
  inversion HD1;subst ...
  + assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
     destruct HRI as [HUp  HDown] ...
     apply HDown in H4 ...
  + assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
     destruct HRI as [HUp  HDown] ...
     apply HDown in H4 ... 
  + checkPermutationCases  H1.
     - assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
       destruct HRI as [HUp  HDown] ...
      assert(flln th n0 B (F::x) (DW F0)).
      seqPerm H0 H2. 
      LLtensor x N.  
      apply HDown in H...
      HProof. 
    - assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
      destruct HRI as [HUp  HDown] ...
      assert(flln th n0 B (F::x) (DW G)).
      seqPerm H0 H6. 
      apply HDown in H...
      LLtensor M0 x.   
      HProof.
  + assert(HRI: RIndTheory (S n0)) by ( apply IH;auto).
     destruct HRI as [HUp  HDown] ...
     apply HDown in H6 ...
     LLexists t.
  + eapply UpExtension in H5...
    assert(HRI: RIndTheory x)  by (apply IH ;auto).
    destruct HRI as [HUp  HDown] ...
    apply HUp in H2 ...
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
th F -> ~ posAtom F -> ~ negAtom F  -> 
flls th B M (UP (L++[F])) -> flls th B M (UP L) .
Proof.
  intros.
  assert(HRn:  forall n, RUpTheory n) by (apply InvAuxTheory).
  apply FLLStoFLLN in H2;auto. 
  destruct H2.
  generalize (HRn x);intros.
  eapply H3;eauto.
Qed.

End AbsorptionTheory.

Section AbsorptionClassic.

Definition RUp (n:nat) := forall  B L  F  M , 
    In F B -> flln th n B M  (UP (L ++ [F]))  -> flls th B M (UP L ).  

Definition RDown (n:nat) := forall B F  M  H, 
    posLFormula F ->
    In F B -> flln th n B (F::M) (DW H) -> flls th B M (DW H).

Definition RInd (n:nat) := RUp n /\ RDown (n -1). 

Lemma RDown0 : RDown 0.
Proof with sauto;solveLL.
  unfold RDown. intros B F M H FNA FB HD.
  inversion HD...
Qed.

Lemma RUp0 : RUp 0.
Proof with subst;auto;solveLL.
  unfold RUp. intros B L F M FB HD.
  destruct L.
  + inversion HD...
      LLfocus2 Top.
  + inversion HD ...
Qed.

(* =============================================== *)
(* PROOF OF RUP *)
(* =============================================== *)   

Theorem InvCopyUP: forall  n ,
(forall m : nat, m <= n -> RInd m) -> RUp (S n).
Proof with sauto;solvePolarity;solveLL.
  intros n IH.
  unfold RUp. intros B L1 F M FB HD.
  destruct L1;simpl in *.
  + (* L1 is Empty *)
    inversion HD... 
    - LLfocus2 Top.
    - LLfocus2 (F0 & G). 
      apply FLLNtoFLLS in H4;auto.
      apply FLLNtoFLLS in H5;auto. 
    - apply FLLNtoFLLS in H3;auto. 
    - LLfocus2 (F0 ⅋ G).
      apply FLLNtoFLLS in H3;auto.
    - LLfocus2 (? F0). 
     apply FLLNtoFLLS in H3;auto.
     solveLL. LLPerm (F0::B)... 
    - LLfocus2 (∀{ FX}).
      solveLL. 
      generalize (H5 x);intro.
      apply H in properX.
      apply FLLNtoFLLS in properX;auto. 
    - assert(RInd n) by ( apply IH;auto).
      destruct H as [HUp  HDown].
      inversion H5;subst ...
     {  checkPermutationCases H0. 
        + LLfocus2 F.
           inversion H0;inversion H...
           HProof. 
        + LLfocus1 F0 x. 
            eapply HDown with (F:= F) ;auto.
            HProof. }
     { LLfocus2 F0.
      eapply HDown with (F:= F) ;auto. }
    {  LLtheory F0.
        eapply HDown with (F:= F) ;auto. }
  + (* L is not empty *)
    inversion HD;subst; try(
    assert(RInd n) by ( apply IH;auto);
    destruct H as [HUp  HDown]; clear HDown) ...
    all: eapply HUp with (F:=F) ;auto.
    intuition.  LLPerm (F0::B)...    
    generalize (H5 x properX);intros...
Qed.

(* =============================================== *)
(* PROOF OF RDOWN *)
(* =============================================== *)   

Theorem InvCopyDW: forall  n ,
(forall m : nat, m <= n -> RInd m) -> RDown (n).
Proof with sauto;solvePolarity;solveLL.
  intros n IH.
  unfold RDown.  intros B F M H FNA FB HD.
  inversion HD...
  apply InPermutation in FB...
  + assert(HRI: RInd (S n0)) by (apply IH ; auto).
    destruct HRI as [HUp  HDown] ...
    eapply HDown in H4 ... 
    rewrite FB...
  + assert(HRI: RInd (S n0)) by (apply IH ; auto).
    destruct HRI as [HUp  HDown] ...
    eapply HDown in H4 ...
  + checkPermutationCases H1.
     - assert(HRI: RInd (S n0)) by (apply IH;auto).
       destruct HRI as [HUp  HDown] ...
       assert(flln th n0 B (F::x) (DW F0)).
       HProof.
      eapply HDown in H...
      LLtensor x N.  
      HProof.
     - assert(HRI: RInd (S n0)) by (apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        assert(flln th n0 B (F::x) (DW G)).
        HProof.

        eapply HDown in H...
        LLtensor M0 x.  
        HProof.
  +
    assert(HRI: RInd (S n0)) by ( apply IH;auto).
    destruct HRI as [HUp  HDown] ...
    eapply HDown in H6 ...
    LLexists t.
  + eapply UpExtension in H5...
    assert(HRI: RInd x)  by (apply IH ;auto).
    destruct HRI as [HUp  HDown] ...
    eapply HUp in H2 ...
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
Theorem AbsorptionClassic : forall B L F  M,
    In F B -> 
    flls th B M (UP (L++[F])) ->
    flls th B M (UP L).
Proof.
  intros.
  assert(HRn:  forall n, RUp n) by (apply InvAux).
  apply FLLStoFLLN in H0;auto. 
  destruct H0.
  generalize (HRn x);intros. eapply H1;eauto.
Qed.


Theorem AbsorptionClassic' : forall  B L F  M,
    In F B ->
    flls th B M (UP (L++[F])) ->
    flls th B M (UP L ).
Proof.
  intros.
  assert(HRn:  forall n, RUp n) by (apply InvAux).
  apply FLLStoFLLN in H0;auto. 
  destruct H0.
  generalize (HRn x);intros. eapply H1;eauto.
Qed.

Theorem AbsorptionClassicSet : forall B B' L C M,
    Permutation B (C++B') -> 
    flls th B M (UP (L ++ C)) -> flls th B M (UP L).
Proof with sauto.
  intros.
  revert dependent L.
  revert dependent B.
  revert dependent B'.
  revert dependent M.
  induction C;intros...
  CleanContext... 
  rewrite H.
  rewrite <- app_comm_cons.
  eapply AbsorptionClassic' with (F:=a)...
  eapply IHC with (B':= a :: B')... 
  rewrite app_assoc_reverse.
  simpl.
  LLExact H0.
Qed.


End AbsorptionClassic. 

Section InvExists.


Definition RUpExists (n:nat) := forall B L M FX t, 
    uniform_oo FX -> proper t -> 
    flln th n B M (UP (L ++ [FX t]))  -> flls th B (∃{ FX}:: M) (UP L).

Definition RDownExists (n:nat) := forall B M H FX t, 
    posFormula (FX t) -> uniform_oo FX -> proper t ->
    flln th n B (FX t::M) (DW H) -> flls th B (∃{ FX} :: M) (DW H).

Definition RIndExists (n:nat) := RUpExists n /\ RDownExists (n -1). 

Lemma RDownE0 : RDownExists 0.
Proof with sauto;solvePolarity;solveLL.
  unfold RDownExists.

  intros B M H FX t FP Uni Ft HD.
  inversion HD...
  rewrite <- H3 in FP.
  inversion FP... 
Qed.

Lemma Remove_app_in' :
    forall (F:oo) (L: list oo), Remove F (L ++ [F]) (L).
Proof.  intros.
  assert(Remove (F) (L ++ [F]) (L++[])).
  eapply Remove_app_in with (F:=F) (L1:=L) (L2:=nil).
  rewrite app_nil_r in H.
  assumption.
Qed.

Lemma RUpE0 : RUpExists 0.
Proof with sauto;solvePolarity.
  unfold RUpExists.
  intros.
  destruct L.
  + inversion H1...
    LLfocus1 (∃{ FX}) M ...
    LLexists t.  
    rewrite <- H6.
    LLrelease... 
  + inversion H1...
Qed.

(* =============================================== *)
(* PROOF OF RUP *)
(* =============================================== *)   
Theorem InvExUP: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RUpExists (S n).
Proof with sauto;solvePolarity.
  intros n IH.
  unfold RUpExists.  intros B L1 M1 FX t  Hu Hp HD1.
  destruct L1;simpl in *.
  + (* L1 is Empty *)
      inversion HD1... 
      - LLfocus1 (∃{ FX}) M1...
        LLexists t.  
        rewrite <- H3.
        LLrelease...
     - LLfocus1 (∃{ FX}) M1...
      LLexists t.  
      rewrite <- H0.
      LLrelease...
      apply FLLNtoFLLS in H4;auto. 
      apply FLLNtoFLLS in H5;auto.
     - LLfocus1 (∃{ FX}) M1...
      LLexists t.  
      rewrite <- H0.
      LLrelease...
      apply FLLNtoFLLS in H3;auto. 
     - LLfocus1 (∃{ FX}) M1...
      LLexists t.  
      rewrite <- H0.
      LLrelease...
      apply FLLNtoFLLS in H3;auto. 
     - LLfocus1 (∃{ FX}) M1...
      LLexists t.  
      rewrite <- H0.
      LLrelease...
      apply FLLNtoFLLS in H3;auto.
      solveLL. LLPerm (F::B)... 
     - LLfocus1... 
      LLexists t.
      rewrite <- H0...
      solveLL.
      generalize(H5 x properX);intro.
      apply FLLNtoFLLS in H;auto.
     - assert(RIndExists n) by ( apply IH;auto).
      destruct H as [HUp  HDown].
      inversion H5;subst ...
     { checkPermutationCases H0.
       + LLfocus1...
          LLexists t.
          HProof.
       + destruct (posLDestruct H4).
           LLfocus1 F ((∃{ FX})::x).
          rewrite H0...
          eapply HDown with (t:=t)...
          HProof.
          LLfocus1...
          LLexists t.
          LLrelease...
          LLstore...
          LLfocus1 F (FX t::x )...
          rewrite H0...
          HProof. }
    { destruct (posLDestruct H4).
      + eapply HDown in H1...
          LLfocus2 F.
      + LLfocus1... 
         LLexists t.
         LLrelease... 
          HProof. }
   { destruct (posLDestruct H4).
      +  eapply HDown in H1...
          LLtheory F.
      + LLfocus1... 
          LLexists t.
          LLrelease... 
          HProof. }
  + (* L is not empty *)
    inversion HD1;subst; try(
    assert(RIndExists n) by ( apply IH;auto);
    destruct H as [HUp  HDown]; clear HDown) ...
    all:solveLL.
    all: try eapply HUp with (t:=t);eauto.
    LLPerm (F::B)...
    rewrite perm_swap.
    eapply HUp;eauto.
Qed.


(* =============================================== *)
(* PROOF OF RDOWN *)
(* =============================================== *)   
Theorem InvExDW: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RDownExists (n).
Proof with sauto;solvePolarity.
  intros n IH.
  unfold RDownExists.  
  intros B M H FX t HP Hu Ht HD1.
  inversion HD1;subst ...
  + rewrite <- H3 in HP.
      inversion HP.
  + assert(HRI: RIndExists (S n0)).
      auto using le_n_S.
      destruct HRI as [HUp  HDown] ...
      apply HDown in H4...
  + assert(HRI: RIndExists (S n0)).
      auto using le_n_S.
      destruct HRI as [HUp  HDown] ...
      apply HDown in H4...
  + checkPermutationCases H1. 
      - eapply exchangeLCN in H2.
        2: rewrite H0...
      assert(HRI: RIndExists (S n0)).
      auto using le_n_S.
      destruct HRI as [HUp  HDown] ...
      apply HDown in H2 ...
      LLtensor (∃{ FX}::x ) N.
      rewrite <- H1...
      HProof.
      - eapply exchangeLCN in H6.
      2: rewrite H0...
      assert(HRI: RIndExists (S n0)).
      auto using le_n_S.
      destruct HRI as [HUp  HDown] ...
      apply HDown in H6 ...
      LLtensor M0 (∃{ FX}::x).
      rewrite <- H1; perm.
      HProof.
  + assert(HRI: RIndExists (S n0)).
      auto using le_n_S.
      destruct HRI as [HUp  HDown] ...
      apply HDown in H6...
      LLexists t0.
  + eapply UpExtension in H5...
      assert(HRI: RIndExists x) by auto.
      destruct HRI as [HUp  HDown] ...
      apply HUp in H2 ...
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
    flls th B M (UP (L++[FX t ])) -> flls th B (∃{ FX}::M) (UP L ).
Proof.
  intros.
  assert(HRn:  forall n, RUpExists n) by (apply InvExAux).
  apply FLLStoFLLN in H1.
  destruct H1.
  generalize (HRn x);intros.
  apply H2 in H1;auto.
Qed.


Theorem InvExC : forall B L FX t  M, 
    In (∃{ FX}) B ->
    uniform_oo FX -> proper t -> 
    flls th B M (UP (L ++ [FX t])) -> flls th B M (UP L).
Proof.
  intros.
  eapply @AbsorptionClassic;eauto.
  apply UpExtension'.
  constructor.
  apply InvEx with (t:=t);auto.
Qed.  

Theorem InvExT : forall B L FX t  M, 
    th (∃{ FX}) ->
    uniform_oo FX -> proper t -> 
    flls th B M (UP (L ++ [FX t])) -> flls th B M (UP L).
Proof.
  intros.
  eapply @AbsorptionTheory;eauto.
  1-2:intro;solvePolarity.
  apply UpExtension'.
  constructor.
  apply InvEx with (t:=t);auto.
Qed.  


End InvExists.

Section InvOPlus.

Definition RUpPlus (n:nat) := forall B L M F G, 
    flln th n B M (UP (L ++ [F]))  -> flls th B (F ⊕ G::M) (UP L).

Definition RDownPlus (n:nat) := forall B M H F G, 
    posFormula F ->
    flln th n B (F::M) (DW H) -> flls th B (F ⊕ G::M) (DW H).

Definition RIndPlus (n:nat) := RUpPlus n /\ RDownPlus (n -1). 

Lemma RDownP0 : RDownPlus 0.
Proof with sauto;solvePolarity;solveLL.
  unfold RDownPlus.
  intros B M H F G FP HD.
  inversion HD;subst...
Qed.

Lemma RUpP0 : RUpPlus 0.
Proof with sauto;solvePolarity;solveLL.
  unfold RUpPlus.
  intros B L M F G HD.
  destruct L.
  + inversion HD;subst...
      LLfocus1 (Top ⊕ G) M...
  + inversion HD...
Qed.

(* =============================================== *)
(* PROOF OF RUP *)
(* =============================================== *)   

Theorem InvPlusUP: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RUpPlus (S n).
Proof with sauto;solvePolarity;solveLL.
  intros n IH.
  unfold RUpPlus.  intros B L1 M1 F G HD1.
  destruct L1;simpl in *.
  + (* L1 is Empty *)
      inversion HD1;subst ...
      - LLfocus1 (Top ⊕ G).
      - LLfocus1 ((F0 & G0) ⊕ G). 
         LLleft.
        apply FLLNtoFLLS in H4;auto.
        apply FLLNtoFLLS in H5;auto.
      - LLfocus1 (Bot ⊕ G). 
        LLleft.
        apply FLLNtoFLLS in H3;auto.
      - LLfocus1 ((F0 ⅋ G0) ⊕ G). 
        LLleft.
        apply FLLNtoFLLS in H3;auto.
      - LLfocus1 ((? F0) ⊕ G). 
        LLleft.
        apply FLLNtoFLLS in H3;auto.
        solveLL. LLPerm (F0::B)...
      - LLfocus1...
        LLleft.
        solveLL.
        generalize (H5 x properX);intro.
        apply FLLNtoFLLS in H;auto.
      - assert(RIndPlus n) by ( apply IH;auto).
        destruct H as [HUp  HDown].
        inversion H5;subst ...
        { checkPermutationCases H0. 
           + LLfocus1...
              LLleft.
              HProof.
           + destruct (posLDestruct H4).
              - LLfocus1 F0 ((F ⊕ G)::x).
                rewrite H0...
                eapply HDown... 
                HProof.
             - LLfocus1...
                LLleft.
                LLrelease.
                LLstore... 
                LLfocus1 F0 (F::x)...
                rewrite H0...
                HProof. }
        { destruct (posLDestruct H4).
          + LLfocus2 F0.
          + LLfocus1 (F ⊕ G) M1...
              LLleft.
              inversion H2...
              HProof.  }
        { destruct (posLDestruct H4).
           + LLtheory F0.
           + LLfocus1 (F ⊕ G) M1...
              LLleft.
              inversion H2...
              HProof. }
  + (* L is not empty *)
      inversion HD1;subst; try(
      assert(RIndPlus n) by ( apply IH;auto);
      destruct H as [HUp  HDown]; clear HDown)...
      all:solveLL.
      all: try eapply HUp...  LLPerm (F0::B)...
      apply H5...
      rewrite perm_swap...
Qed.    

(* =============================================== *)
(* PROOF OF RDOWN *)
(* =============================================== *)   
Theorem InvPlusDW: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RDownPlus (n).
Proof with sauto;solvePolarity.
  intros n IH.
  unfold RDownPlus.  intros B M  H  F G HPosF HD1.
  inversion HD1;subst ...
  + assert(HRI: RIndPlus (S n0)) by auto.
      destruct HRI as [HUp  HDown] ...
  + assert(HRI: RIndPlus (S n0)) by auto.
      destruct HRI as [HUp  HDown] ...
  + assert(HRI: RIndPlus (S n0)) by auto.
      destruct HRI as [HUp  HDown] ...
     checkPermutationCases H1.
      -  LLtensor ((F ⊕ G) ::x) N...
        rewrite <- H1...  
        apply HDown...
        HProof.
        HProof.
     - LLtensor M0 ((F ⊕ G) ::x)...
        rewrite <- H1...  
        HProof.
        apply HDown...
       HProof.
  + assert(HRI: RIndPlus (S n0)) by auto.
      destruct HRI as [HUp  HDown] ...
      LLexists t.
  + apply UpExtension in H5...
      assert(HRI: RIndPlus x)  by auto.
      destruct HRI as [HUp  HDown] ...
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
    flls th B M (UP (L++[F])) -> flls th B (F ⊕ G:: M) (UP L).
Proof.
  intros.
  assert(HRn:  forall n, RUpPlus n) by (apply InvPlusAux).
  apply FLLStoFLLN in H.
  destruct H.
  generalize (HRn x);intros.
  eapply H0 in H;eauto.
Qed.

Theorem InvPlusC : forall B L F G M,
    In (F ⊕ G) B ->
    flls th B M (UP (L++[F])) -> flls th B M (UP L).
Proof.
  intros.
  eapply @AbsorptionClassic;eauto.
  apply UpExtension'.
  constructor. 
  apply InvPlus ;auto.
Qed.  

Theorem InvPlusT : forall B L F G M,
    th (F ⊕ G) ->
    flls th B M (UP (L++[F])) -> flls th B M (UP L).
Proof.
  intros.
  eapply @AbsorptionTheory;eauto.
  1-2: intro;solvePolarity. 
  apply UpExtension'.
  constructor. 
  apply InvPlus ;auto.
Qed.  


Lemma OPlusComm : forall B M F G X n,
    flln th n B (F ⊕ G::M) X -> flln th n B (G ⊕ F::M) X.
Proof with sauto;solvePolarity;solveLL.
    intros.
    generalize dependent B.
    generalize dependent M.
    generalize dependent X.
    generalize dependent n.
    induction n using strongind;intros.
    + inversion H...
    + inversion H0...
      - checkPermutationCases H2.
        LLtensor (G ⊕ F::x) N...
        rewrite <- H5...
        apply H... HProof.

        LLtensor M0 (G ⊕ F::x)...
        rewrite <- H5...
        apply H... HProof.
    - LLexists t. 
    - assert (flln th n B (F ⊕ G::(M ++ [F0])) (UP M0)).
      LLExact H3.
      eapply H in H1...
      LLExact H1.
    - checkPermutationCases H3. 
       LLfocus1...
       apply OplusCommN.
       HProof.

       LLfocus1 F0  (G ⊕ F::x)...
       rewrite H3...
       apply H ...
       HProof.
    - LLfocus2 F0.
    - LLtheory F0.
Qed.

(* =============================================== *)
(* MAIN INVERTIBILITY THEOREM (FLIPPING F and G)   *)
(* =============================================== *)   
Theorem InvPlusComm: forall B L F G  M, 
    flls th B M (UP (L++[G])) -> flls th B (F ⊕ G::M) (UP L).
Proof.
  intros.
  apply InvPlus with (G:=F)in H;auto.
  apply FLLStoFLLN in H.
  destruct H.
  apply OPlusComm in H.
  apply FLLNtoFLLS with (n:=x) in H;auto.
Qed.

Theorem InvPlusCComm : forall  B L F G M, 
    In (F ⊕ G) B ->
    flls th B M (UP (L++[G])) -> flls th B M (UP L).
Proof.
  intros.
  eapply @AbsorptionClassic;eauto.
  apply UpExtension'.
  constructor. 
  apply InvPlusComm ;auto.
Qed.  

Theorem InvPlusTComm : forall  B L F G M, 
    th (F ⊕ G) ->
    flls th B M (UP (L++[G])) -> flls th B M (UP L).
Proof.
  intros.
  eapply @AbsorptionTheory;eauto.
  1-2:intro;solvePolarity.
  apply UpExtension'.
  constructor. 
  apply InvPlusComm ;auto.
Qed.  

End InvOPlus.

(* =============================================== *)
(** Invertibility of Tensor *)
(* =============================================== *)   
Section InvTensor.

Definition RUpTensor (nm:nat) := forall B L M L' M' F G n m, 
    nm = n + m ->  (* isFormulaL L -> *)
    flln th n B M (UP (L ++ [F])) -> 
    flln th m B M' (UP (L' ++ [G]))  -> 
    flls th B (F ⊗ G:: M ++ M') (UP (L ++ L')).

Definition RDownTensor (nm:nat) := forall B M M' H F G n m, 
    nm = n + m -> posFormula F -> 
    flln th n B (F::M) (DW H) -> 
    flln th m B M' (UP [G]) -> 
    flls th B (F ⊗ G :: M ++ M') (DW H).

Definition RIndTensor (n:nat) := RUpTensor n /\ RDownTensor (n -1). 

Lemma RDownT0 : RDownTensor 0.
Proof with sauto;solvePolarity;solveLL.
  unfold RDownTensor. 
  intros *. intros MN FP HD1 HD2.
  symmetry in MN. 
  apply Nat.eq_add_0 in MN.
  destruct MN...
  inversion HD1...
Qed.

Lemma RUpT0 : RUpTensor 0.
Proof with sauto;solvePolarity.
  unfold RUpTensor. 
  intros *.
  intros MN HD1 HD2.
  symmetry in MN. apply Nat.eq_add_0 in MN.
  destruct MN...
  inversion HD1...
  destruct L;destruct L';simpl in *.
  + inversion HD1...
     inversion HD2...
     LLfocus1 (Top ⊗ Top) (M++M')... 
     LLtensor M M' . 
  + inversion H3...
     solveLL. 
  + inversion H3 ...
  + inversion H3 ...
Qed.

(* =============================================== *)
(* F ⊗ G COMMUTES *)
(* =============================================== *)

Lemma TensorComm : forall B M F G X n, flln th n B (F⊗G::M) X -> flln th n B (G⊗F::M) X.
Proof with sauto;solvePolarity;solveLL.
  intros.
  generalize dependent B.
  generalize dependent M.
  generalize dependent X.
  generalize dependent n.
  induction n using strongind;intros.
  + inversion H...
  + inversion H0...
     - checkPermutationCases H2.
       LLtensor (G ⊗ F::x) N.
       rewrite <- H5...
      apply H... HProof.
      
      LLtensor M0 (G ⊗ F::x).
      rewrite <- H5...
      apply H... HProof. 
     - LLexists t. 
     - assert(flln th n B (F ⊗ G::(M ++ [F0])) (UP M0)).
        LLExact H3.
        apply H in H1...
       HProof.
     - checkPermutationCases H3. 
        LLfocus1.
        apply TensorCommN.
        HProof.

        LLfocus1 F0 (G ⊗ F::x).
        rewrite H3...
        apply H...
        HProof. 
     - LLfocus2 F0 ...
     - LLtheory F0 ...
Qed.


Lemma TensorComm' : forall B M F G X , flls th B (F ⊗ G::M) X -> flls th B (G ⊗ F::M) X.
Proof.
  intros.
  apply FLLStoFLLN in H.
  destruct H.
  apply TensorComm in H.
  eapply FLLNtoFLLS in H;eauto.
Qed.


(* =============================================== *)
(* PROOF OF RUP *)
(* Cases when one of the lists is not empty *)
(* =============================================== *)
Lemma InvTensorConsNil (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) B (L1 M1 : list oo)
(l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
    isFormulaL L1 -> 
    flln th n' B M1 (UP (L1 ++ [F])) -> 
    flln th m' B M2 (UP (l :: L2 ++ [G])) -> 
    flls th B (F ⊗ G :: M1 ++ M2) ( UP (L1 ++ l :: L2)).
Proof with sauto;solvePolarity;solveLL.
  intros. 
  inversion H2...
  + apply EquivAuxTop...
  + apply EquivAuxWith...
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
      eapply HUp with(n:=n') (m:=n) (B:=B)...
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
      eapply HUp with(n:=n') (m:=n) (B:=B)...
  + apply EquivAuxBot...
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
      eapply HUp with (n:=n') (m:=n) (B:=B)...
  + apply EquivAuxPar...
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
      eapply HUp with(n:=n') (m:=n) (B:=B)...
  + apply EquivAuxQuest...
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
      eapply HUp with (m:=n) ;auto.  
      eapply weakeningGenN_rev;auto. LLPerm (F0::B)...
  +  apply EquivAuxForAll;intros...
      generalize (H9 t H3);intro.
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia).
      eapply HUp with (m:=n)...
  + apply EquivAuxStore...
      assert(HUp : RUpTensor(n' + n)) by (apply IH;lia) ...
      LLPerm ( F ⊗ G :: M1 ++ (l::M2)).
      eapply HUp with (m:=n)... 
Qed.

Lemma InvTensorConsNil' (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) B (L1 M1 : list oo)
(l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
L1 <> [] -> 
    flln th n' B M1 (UP (L1 ++ [F])) -> 
    flln th m' B M2 (UP (l :: L2 ++ [G])) -> 
    flls th B (F ⊗ G :: M1 ++ M2 ) (UP (L1 ++ l :: L2)).
Proof with sauto;solvePolarity.
  intros. 
  inversion H1...
  + apply ListConsApp in H7... 
      rewrite <- app_comm_cons. 
      solveLL.
  + apply ListConsApp in H3...
      assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
      rewrite <- app_comm_cons.
      solveLL.
      do 2 rewrite app_comm_cons.
      rewrite <- app_comm_cons.
      eapply HUp with (m:=m')...

      do 2 rewrite app_comm_cons.
      rewrite <- app_comm_cons.
      eapply HUp with (m:=m')...
  + apply ListConsApp in H3...
      rewrite <- app_comm_cons. 
      solveLL.
      assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
      eapply HUp with (n:=n) (m:=m') (B:=B)... 
  + apply ListConsApp in H3...
      assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
      rewrite <- app_comm_cons.
      solveLL.
      do 3 rewrite app_comm_cons.
      rewrite <- app_comm_cons.
      eapply HUp with (m:=m')...
  + apply ListConsApp in H3...
      assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
      rewrite <- app_comm_cons.
      solveLL.
      eapply @HUp...
      LLPerm (F0::B)...
      eapply weakeningGenN_rev;auto.
  + apply ListConsApp in H3...
      assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
      rewrite <- app_comm_cons.
      solveLL.

      repeat rewrite app_comm_cons.
      rewrite <- app_comm_cons.
      eapply HUp with (n:=n) (m:=m') (B:=B)...
      apply H8...
  + apply ListConsApp in H3...
      assert(HUp : RUpTensor(n + m')) by (apply IH;lia) ...
      rewrite <- app_comm_cons.
      solveLL.
      do 2 rewrite app_comm_cons.
      rewrite Permutation_cons_append.
      repeat rewrite <- app_comm_cons.
      eapply HUp with (n:=n) (m:=m') (B:=B)...
      LLExact H8. 
Qed.


(* ================================================ *)
(* PROOF OF RUP *)
(* Case when the 2 formulas are async. or pos. atoms*)
(* ================================================ *)
Lemma ITCaseAsyncAsync:
forall n m B M1 M2 F G, 
    negFormula F -> 
    negFormula G -> 
    flln th n B M1 (UP [F]) -> 
    flln th m B M2 (UP [G]) -> 
    flls th B (F ⊗ G:: M1 ++ M2) (UP []).
Proof.
  intros.
  LLfocus1 (F ⊗ G). 
  all:LLtensor M1 M2...
  all: LLrelease.
  all:HProof.
Qed.  

Lemma ITAsyncSync  :
  forall nm n m B  M1 M2 F G,
  negFormula F ->  posLFormula G ->         
  (forall m : nat, m <= nm -> RIndTensor m) -> nm = n + m -> 
  flln th n B M1 (UP [F]) ->  
  flln th m B ( G::M2) (UP []) ->  
  flls th B (F ⊗ G :: M1 ++ M2) ( UP []).
Proof with subst;auto;solvePolarity;solveLL.
  intros. 
  apply posLDestruct in H0; destruct H0 as [AG | AG].
  2:{
  (* G is a positive atom... then, LLrelease works (Lemma  ITCaseAsyncAsync) *)
  eapply ITCaseAsyncAsync with (n:=n) (m:=S m) (B:=B) ;eauto. } 
  + (* G cannot do LLrelease *)
      inversion H4...
      - checkPermutationCases H5.
        { LLfocus1 (F ⊗ G). 
           LLtensor M1 M2.
           LLrelease. all:HProof. }
        { LLfocus1 F0 ((F ⊗ G) ::M1 ++ x)...
           rewrite H5...
          assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto); destruct IH2 as [HUp HDw].
          assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
          apply TensorComm'.
          rewrite (Permutation_app_comm M1).
          eapply HDw with (m:= n) (n:= n0) (B:=B) ;try(lia)...
          HProof. }
      - assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
        destruct IH2 as [HUp HDw].
        assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
        LLfocus2 F0.
        apply TensorComm'.
        rewrite (Permutation_app_comm M1).   
        eapply HDw with (m:= n) (n:= n0) (B:=B);try(lia)...
      - assert(IH2 : RIndTensor(n + S n0)) by(  apply H1;auto);
        destruct IH2 as [HUp HDw].
        assert(Hn : n + S n0 -1 = n + n0) by lia;rewrite Hn in HDw;clear Hn.
        LLtheory F0.
        apply TensorComm'.
        rewrite (Permutation_app_comm M1).   
        eapply HDw with (m:= n) (n:= n0) (B:=B);try(lia)...           
Qed.


(* =============================================== *)
(* PROOF OF RUP *)
(* Case when both formulas are not Async *)
(* =============================================== *)
Lemma ITSyncSync : forall nm n m  B M1 M2 F G, 
    posLFormula F -> posLFormula G ->  
    (forall m : nat, m <= nm -> RIndTensor m) -> 
    S nm = S n + S m -> 
    flln th (S n) B M1 (UP [F]) -> 
    flln th (S m) B M2  (UP [G]) ->  
    flls th B (F ⊗ G::M1 ++ M2) (UP []).
Proof with subst;auto;solvePolarity;solveLL.
  intros * . 
  intros AF AG IH Hnm HD1 HD2. 
  apply posLDestruct in AF; destruct AF as [AF | AF];
  apply posLDestruct in AG; destruct AG as [AG | AG].
  4:{ 
  eapply ITCaseAsyncAsync with (B:=B)...
  exact HD1. exact HD2. }
  3:{ (* F is a positive atom *)
  inversion HD2...
  eapply ITAsyncSync with (nm:=nm) (n:= S n) (m:= m) (B:=B) ... lia. }
  2:{ (* G is a positive atom *)
  inversion HD1...
  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 
  eapply ITAsyncSync with (nm:=nm) (n:= S m) (m:= n) (B:=B) ... lia. }
  1:{ (* F nor G can do LLrelease *)
  inversion HD1...
  inversion HD2...

  inversion H7;subst...
  2:{

  LLfocus2 F0. 
  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 

  assert (IH' : RIndTensor ( (S n0) + S n )) by ( apply IH; lia).
  destruct IH' as [HUp  HDw].
  assert(Hn :  (S n0) + S n - 1 =  n0 + S n ) by lia;rewrite Hn in HDw;clear Hn.
  eapply  HDw...
  }

  checkPermutationCases H0.
  2:{ LLfocus1 F0 ((F ⊗ G) :: M1++x).
  rewrite H0...
  assert (IH' : RIndTensor (n0 + S (S n))) by ( apply IH; lia).
  destruct IH' as [HUp  HDw].
  assert(Hn : n0 + S (S n) - 1 = n0 + (S n)) by lia;rewrite Hn in HDw;clear Hn.
  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 
  eapply HDw... HProof. }
  inversion H5;subst...
  2:{
  LLfocus2 F0. 

  assert (IH' : RIndTensor ( S (S (S n0)) + n1 )) by ( apply IH; lia).
  destruct IH' as [HUp  HDw].
  assert(Hn :  S (S (S n0)) + n1 - 1 =  n1 + (S (S n0)) ) by lia;rewrite Hn in HDw;clear Hn. 
  eapply  HDw... }

  checkPermutationCases H2.
  2:{ LLfocus1 F0 ((F ⊗ G) :: x++M2).
  rewrite H2...
  assert (IH' : RIndTensor (S n0 + S (S n1))) by ( apply IH; lia).
  destruct IH' as [HUp  HDw].
  assert(Hn : S n0 + S (S n1) - 1 = n1 + S (S n0)) by lia;rewrite Hn in HDw;clear Hn.
  eapply HDw...
  HProof. }
  - LLfocus1.
    LLtensor M1 M2...
    all:HProof.
  - LLtheory F0. 
    assert (IH' : RIndTensor (S (S n0) + S n1)) by ( apply IH; lia).
    destruct IH' as [HUp  HDw].
    assert(Hn : S (S n0) + S n1 - 1 = S (S n0) + n1) by lia;rewrite Hn in HDw;clear Hn.
    eapply  HDw with (n:= n1) (m:= S (S n0))...
    lia. 
  - LLtheory F0. 
    assert (IH' : RIndTensor (S (S n0) + n)) by ( apply IH; try lia).
    destruct IH' as [HUp  HDw].
    assert(Hn : S (S n0) + n - 1 = (S n0) + n) by lia;rewrite Hn in HDw;clear Hn.
    apply TensorComm'.
    rewrite (Permutation_app_comm M1).  

    eapply  HDw with (n:=n0) (m:= S n)...
    lia. }
Qed.   

(* =============================================== *)
(* PROOF OF RUP *)
(* =============================================== *)
Theorem InvTensorUP: forall  nm , 
    (forall m : nat, m <= nm-> RIndTensor m) -> RUpTensor (S nm).
Proof with sauto;solvePolarity;solveLL.
  intros nm IH.
  unfold RUpTensor.
  intros B L1  M1 L2 M2 F  G n' m' HNM HD1 HD2.
  destruct L1;destruct L2;simpl in *.
  + (* L1 and L2 are Empty *)   
      inversion HD1;inversion HD2;subst;

  try(
  match goal with
  | [ |- flls th ?B (?F ⊗ ?G::?M1 ++ ?M2) (UP []) ]
  => tryif (assert(HAFG : negFormula F /\ negFormula G) by (split;constructor;auto))
  then
  eapply ITCaseAsyncAsync ;eauto
  else idtac
  end)...


  eapply ITAsyncSync with  (nm := nm) (n:= n') (m:=n0) (B:=B) ;try lia...
  eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) ;try lia...
  eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) ;try lia...
  eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) ;try lia...
  eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) ;try lia...
  eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) (B:=B) ;try lia...

  apply TensorComm'.
  rewrite (Permutation_app_comm M1).  

  eapply ITAsyncSync with  (nm := nm) (n:= m') (m:=n) (B:=B);try lia...

  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 

  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=B);try lia...

  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 

  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=B);try lia...
  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 

  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=B);try lia...
  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 

  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=B);try lia...

  apply TensorComm'.
  rewrite (Permutation_app_comm M1). 
  eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) (B:=B);try lia...

  (* both F and G are not asynchronous formulas *)
  eapply  ITSyncSync with (nm := nm) (n:=n) (m:=n0) (B:=B) ...

  + (* L1 is empty and L2 is not empty *)
      eapply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m') (B:=B)  (L1 := [])...

  + (* L1 is not empty and L2 is empty *)
      sauto. 
      apply TensorComm'.
      rewrite (Permutation_app_comm M1). 
      rewrite <- (app_nil_l (o::L1)).
      eapply InvTensorConsNil with (nm:=nm) (n':=m') (m':=n') (B:=B);try lia...
  +  (* L1 and L2 are not empty *)
      apply InvTensorConsNil' with (nm:=nm) (n':=n') (m':=m') (L1 := o :: L1) (B:=B) ...
      discriminate.
Qed.

(* =============================================== *)
(* PROOF OF RDOWN *)
(* =============================================== *)
Theorem InvTensorDW: forall  n , 
    (forall m : nat, m <= n -> RIndTensor m) -> RDownTensor (n).
Proof with sauto;solvePolarity;solveLL.
  intros n IH.
  unfold RDownTensor.
  intros *. intros Hnm HPosF HD1 HD2.
  inversion HD1...
  + assert(HRI: RIndTensor (S m +n1)) by (apply IH ; lia).
      destruct HRI as [HUp  HDown] ...
      assert(Hn : S m + n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
      LLleft. 
      eapply HDown  with (n:=n1) (m:=m)  (B:=B)  ... lia. 
  + assert(HRI: RIndTensor (S m +n1)) by (apply IH ; lia).
      destruct HRI as [HUp  HDown] ...
      assert(Hn : S m + n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
      LLright. 
      eapply HDown  with (n:=n1) (m:=m)  (B:=B) ... lia. 
  + checkPermutationCases H1.
     - assert(HRI: RIndTensor (S m + n1)).  apply IH. lia. 
       destruct HRI as [HUp  HDown] ...
        simpl in HDown.
        CleanContext.
        LLtensor (F ⊗ G::x ++ M') N ...
        rewrite <- H1... 
        eapply HDown with (m:=m) (n:=n1) (B:=B)  ;try lia...
        HProof.
        HProof.
    - assert(HRI: RIndTensor (S m + n1)).  apply IH. lia. 
      destruct HRI as [HUp  HDown] ...
      simpl in HDown.
      rewrite Nat.sub_0_r in HDown.
      LLtensor M0 (F ⊗ G::x ++ M' ). 
      rewrite <- H1... 
      HProof.
      eapply HDown with (m:=m) (n:=n1) (B:=B)  ;try lia...
      HProof.
  + assert(HRI: RIndTensor (m + S n1 )) by ( apply IH;lia).
      destruct HRI as [HUp  HDown] ...
      assert(Hn : m + S n1 -1 =  m + n1) by lia;rewrite Hn in HDown;clear Hn.
      LLexists t. 
      eapply HDown with (n:=n1) (m:=m) (B:=B) ...  
      lia.
  + apply UpExtension in H5 ...
      assert(HRI: RIndTensor (m + x)). apply IH. lia.
      destruct HRI as [HUp  HDown]. clear HDown.
      rewrite <- (app_nil_r [H]). 
      eapply HUp with (n:= x )(m:= m) (B:=B) ...
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

Theorem InvTensor : forall B L L' F G  M M',
    flls th B M (UP (L++[F])) -> 
    flls th B M' (UP (L'++[G])) -> 
    flls th B (F ⊗ G :: M ++ M') (UP (L ++ L')) .
Proof with sauto;solvePolarity;solveLL.
  intros.
  assert(HRn:  forall n, RUpTensor n) by (apply InvTensorAux).
  apply FLLStoFLLN in H.
  apply FLLStoFLLN in H0...
  generalize (HRn (x0 + x));intros.
  eapply H1 with (B:=B) ...
Qed.

Theorem InvTensor' : forall B F G  M M',
    flls th B M (UP [F]) -> 
    flls th B M' (UP [G]) -> 
    flls th B (F ⊗ G :: M ++ M') (UP []) .
Proof with sauto;solvePolarity;solveLL.
  intros.
  rewrite <- (app_nil_l []). 
  apply InvTensor...
Qed.

Theorem InvTensorC : forall B L L' F G M M', 
    In (F ⊗ G) B ->
    flls th B M (UP (L++[F])) -> 
    flls th B M' (UP (L'++[G])) -> 
    flls th B (M ++ M') (UP (L ++ L')).
Proof.
  intros.
  eapply @AbsorptionClassic;eauto.
  apply UpExtension'. solvePolarity.
  eapply InvTensor with (B:=B);auto.
Qed.  

Theorem InvTensorT : forall B L L' F G M M', 
    th (F ⊗ G) ->
    flls th B M (UP (L++[F])) -> 
    flls th B M' (UP (L'++[G])) -> 
    flls th B (M ++ M') (UP (L ++ L')).
Proof.
  intros. 
  eapply @AbsorptionTheory;eauto.
  1-2:intro;solvePolarity.
  apply UpExtension'. solvePolarity.
  eapply InvTensor with (B:=B);auto.
Qed.  


Theorem InvTensorC' : forall B  F G M M', 
    In (F ⊗ G) B ->
    flls th B M (UP [F]) -> 
    flls th B M' (UP [G]) -> 
    flls th B (M ++ M') (UP []).
Proof with sauto.
  intros.
  rewrite <- (app_nil_l []). 
  apply InvTensorC with (F:=F) (G:=G)...
Qed.  

Theorem InvTensorT' : forall B F G M M', 
    th (F ⊗ G) ->
    flls th B M (UP [F]) -> 
    flls th B M' (UP [G]) -> 
    flls th B (M ++ M') (UP []).
Proof with sauto.
  intros.
  rewrite <- (app_nil_l []). 
  apply InvTensorT with (F:=F) (G:=G)...
Qed.  

End InvTensor.
End InvPosPhase.

