Require Export LL.FOLL.Dyadic.PreTactics.
Require Import Coq.Program.Equality.

Export LLNotations .
Import DyadicTactics.

Set Implicit Arguments.

Section LL2BasicTheory.
  Context `{OLS: OLSig}.
  
Section StructuralProperties.
    
Lemma exchangeLL2N : forall n B1 B2 L1 L2,  
     Permutation B1 B2 -> Permutation L1 L2 -> 
     LL2 n |-- B1 ; L1 -> LL2 n |-- B2 ; L2.
Proof with sauto.
  intros *. intros PB PL H.
  revert L1 L2 PL B1 B2 PB H;
  induction n using lt_wf_ind; intros...
  inversion H0...
  all: try rewrite PL in H1. 
  LLinit A.  
  LLtop M.  
  LLleft F G M.
  eapply H with (B1:=B1)...
  LLright F G M.
  eapply H with (B1:=B1)...  
  LLwith F G M.
  eapply H with (B1:=B1)...
  eapply H with (B1:=B1)...    
  LLbot M.
  eapply H with (B1:=B1)...                          
  LLpar F G M.
  eapply H with (B1:=B1)...
  LLtensor F G M N.
  eapply H with (B1:=B1)...
  eapply H with (B1:=B1)...
  LLstore F M.
  eapply H with (B1:=F::B1)...
  LLbang.
  eapply H with (B1:=B1)... 
  LLexists t FX M.
  eapply H with (B1:=B1)...
  LLforall FX M.
  eapply H with (B1:=B1)...
  LLcopy F.
  rewrite <- PB...
  eapply H with (B1:=B1) (L1:=F::L1)... 
 Qed.

Global Instance LL2N_morphism n:
  Proper (Permutation (A:=oo) ==> Permutation (A:=oo) ==> iff) (LL2N n).
Proof.
  unfold Proper; unfold respectful. 
  intros B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (exchangeLL2N PB PL H).
  refine (exchangeLL2N (symmetry PB) (symmetry PL) H).
Qed.

Lemma exchangeLL2S : forall B1 B2 L1 L2,  
     Permutation B1 B2 -> Permutation L1 L2 -> 
     LL2 |-- B1 ; L1 -> LL2 |-- B2 ; L2.
Proof with sauto.
  intros *. intros PB PL H.
  revert dependent B2.
  revert dependent L2. 
  induction H;intros L2 PL B2 PB... 
  LLinit A.
  all: try rewrite PL in H.
  LLtop M.   
  LLleft F G M.
  LLright F G M.
  LLwith F G M.
  LLbot M.
  LLpar F G M.
  LLtensor F G M N.
  LLstore F M.
  LLexists t FX M.
  LLforall FX M.
  eapply H2 with (x:=x)...
  rewrite PB in H.
  LLcopy F.
 Qed. 

Global Instance LL2S_morphism:
  Proper (Permutation (A:=oo) ==> Permutation (A:=oo) ==> iff) (LL2S).
Proof.
  unfold Proper; unfold respectful. 
  intros B1 B2 PB L1 L2 PL.
  split; intro H.
  refine (exchangeLL2S PB PL H).
  refine (exchangeLL2S (symmetry PB) (symmetry PL) H).
Qed.

Instance LL2S_morphism' B:
  Proper (Permutation (A:=oo) ==> Basics.flip Basics.impl) (LL2S B).
Proof.
  unfold Proper; unfold respectful. 
  intros L1 L2 PL H.
  rewrite PL;auto.
 Qed.

Theorem weakeningLL2N : forall n F B L,
        (LL2N n B L) -> LL2N n (F::B) L.
 Proof with sauto.
    induction n using lt_wf_ind;intros.
      inversion H0...
      LLinit A.
      LLtop M.
      LLleft F0 G M.
      LLright F0 G M.
      LLwith F0 G M.
      LLbot M.
      LLpar F0 G M.
      LLtensor F0 G M N.
      LLstore F0 M.
      rewrite perm_swap;auto.
      LLexists t FX M.
      LLforall FX M.
      LLcopy F0.
      firstorder.
  Qed.

Theorem weakeningLL2S : forall F B L,
    LL2S B L -> LL2S (F::B) L.
   Proof with sauto. 
    intros.
    revert dependent F.
    induction H;intros...
    LLinit A.
    LLtop M.
    LLleft F G M.
    LLright F G M.
    LLwith F G M.
    LLbot M.
    LLpar F G M.
    LLtensor F G M N.
    LLstore F M.
    rewrite perm_swap;auto.
    LLexists t FX M.
    LLforall FX M.
    LLcopy F.
    firstorder.
 Qed.     

Theorem contractionLL2N  : forall n F B L,
    In F B ->  LL2N n (F::B) L -> LL2N n B L.
  Proof with sauto.
  do 2 intro.
  induction n using lt_wf_ind;intros... 
    inversion H1...
    LLinit A.
    LLtop M.
    LLleft F0 G M.
    LLright F0 G M.
    LLwith F0 G M.
    LLbot M.
    LLpar F0 G M.
    LLtensor F0 G M N.
    LLstore F0 M.
    rewrite perm_swap in H3... 
    apply H in H3...
    LLexists t FX M.
    LLforall FX M.
    LLcopy F0.
    inversion H2...
Qed.

Theorem contractionLL2S  : forall F B L,
    LL2S (B++[F]) L -> In F B -> LL2S B L.
  Proof with sauto.
  intros.
  dependent induction H generalizing B... 
    LLinit A.
    LLtop M.
    LLleft F0 G M.
    LLright F0 G M.
    LLwith F0 G M.
    LLbot M.
    LLpar F0 G M.
    LLtensor F0 G M N.
    LLstore F0 M.
    apply IHLL2S...
    LLexists t FX M.
    LLforall FX M.
    apply in_app_or in H...
    LLcopy F0.
    inversion H2...
    LLcopy F0.
Qed.

End StructuralProperties.
 
(** Adequacy relating the system with and without inductive meassures *)
Section Adequacy.
 
Lemma LL2NtoLL2S : forall n B L,
    LL2N n B L -> LL2S B L.
 Proof with sauto. 
  induction n using lt_wf_ind;intros...
  inversion H0...
  all: clear H0. 
  LLinit A. 
  all:
  try repeat
    match goal with
    [H1: LL2N _ _ _ |- _] => 
    apply H in H1;sauto
    end.
   LLtop M. 
   LLleft F G M.
   LLright F G M.
   LLwith F G M.
   LLbot M.
   LLpar F G M.
   LLtensor F G M N.
   LLstore F M.
   LLexists t FX M.
   LLforall FX M.
   specialize (H3 x H0).
    apply H in H3...
   LLcopy F.
  Qed.

Axiom LL2StoLL2N : forall B L,
    LL2S B L -> exists n, LL2N n B L.

End Adequacy.

Section GeneralResults.

Theorem weakeningLL2SGen : forall B1 B2 L,
    LL2S B2 L -> LL2S (B1 ++ B2) L.
   Proof with sauto. 
    intros.
    revert dependent B2. 
    revert L.
    induction B1;intros...
    rewrite <- app_comm_cons.
    apply weakeningLL2S...
 Qed.   

Theorem storeGenLL2S : forall B1 B2 L,
    LL2S (B1++B2) L -> LL2S B2 (map Quest B1 ++ L).
   Proof with sauto. 
    intros.
    revert dependent B2. 
    revert L.
    induction B1;intros...
    simpl...
    LLstore a (map Quest B1 ++ L).
    eapply IHB1. 
    rewrite <- Permutation_middle...
 Qed.   

Theorem copyGenLL2S : forall B1 B2 L,
   LL2S B2 (B1 ++ L) ->  LL2S (B1++B2) L.
   Proof with sauto. 
    intros.
    revert dependent B2. 
    revert L.
    induction B1;intros...
    simpl...
    LLcopy a...
    apply weakeningLL2S...
    eapply IHB1. 
    rewrite <- Permutation_middle...
 Qed.   
    
Theorem initGenLL2S : forall B F, isFormula F -> isFormula (dual F) ->  LL2S B [F; dual F].
Proof with simpl;sauto.
   induction F;intros isF1 isF2. 
   1-2: LLinit A.
   1,3: LLtop [0].
   1-2: LLbot ['1].
   - LLpar (dual F1) (dual F2) [F1 ⊗ F2].
      LLtensor F1 F2 [dual F1] [dual F2]. 
      1-2: inversion isF1; inversion isF2...
   - LLpar F1 F2 [dual F1 ⊗ dual F2].
      LLtensor (dual F1) (dual F2) [F1] [F2].
     1-2: rewrite perm_takeit_8...
     1-2: inversion isF1; inversion isF2... 
   - LLwith F1 F2 [dual F1 ⊕ dual F2].
     LLleft (dual F1) (dual F2) [F1].
     rewrite perm_takeit_8... inversion isF1... inversion isF2...
     LLright (dual F1) (dual F2) [F2]...
     rewrite perm_takeit_8... inversion isF1... inversion isF2...  
   - LLwith (dual F1) (dual F2) [F1 ⊕ F2 ].
     LLleft F1 F2 [dual F1]. inversion isF1... inversion isF2...
     LLright F1 F2 [dual F2]. inversion isF1... inversion isF2...
   - LLstore F [! (dual F)].
     constructor.
     LLcopy F...
     apply weakeningLL2S...
     inversion isF1... inversion isF2...
   - LLstore (dual F) [! F].
     constructor.
     LLcopy (dual F)...
    apply weakeningLL2S.
     rewrite perm_takeit_8...
    inversion isF1... inversion isF2...
   - inversion isF1... inversion isF2...
    LLforall FX [∃{ fun x : expr con => (dual (FX x))}]...
    pose proof (H2 x).
   pose proof (H4 x).
    pose proof (H x H5 H6).
   rewrite perm_takeit_8 in H7...
   eapply ll2_ex' with (t:=x) (FX:=fun x0 : expr con => dual (FX x0)) (M:=[FX x])...
   - inversion isF1... inversion isF2...
    LLforall (fun x : expr con => dual (FX x)) [∃{ FX}]...
    pose proof (H2 x).
   pose proof (H4 x).
    pose proof (H x H5 H6).
   eapply ll2_ex' with (t:=x) (FX:=FX) (M:=[dual (FX x)])...
Qed.

  Lemma heightGeqLL2N : forall m n  B L,
        LL2N n B L ->
        m>=n -> LL2N m B L.
    Proof with sauto.
   intro. induction m ;intros...
   - inversion H0...
   - inversion H0...
     inversion H...
     LLinit A.
     LLtop M. 
     LLleft F G M.
     apply IHm in H3... 
     LLright F G M.
     apply IHm in H3... 
     LLwith F G M.
     apply IHm in H3...
     apply IHm in H4...
     LLbot M.
     apply IHm in H3... 
     LLpar F G M.
     apply IHm in H3... 
     LLtensor F G M N. 
     apply IHm in H3...
     apply IHm in H4...
     LLstore F M.
     apply IHm in H3... 
     LLbang.
     apply IHm in H1...
     LLexists t FX M.
     apply IHm in H5... 
     LLforall FX M.
     specialize(H4 x H5).
     apply IHm in H4...
     LLcopy F.
     apply IHm in H3...
 Qed.
 
 End GeneralResults.
 End LL2BasicTheory.