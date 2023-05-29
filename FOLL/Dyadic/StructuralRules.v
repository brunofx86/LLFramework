
Require Export LL.FOLL.Dyadic.PreTactics.
Require Import Coq.Program.Equality.

Export LLNotations .
Import DyadicTactics.

Set Implicit Arguments.


Section LL2BasicTheory.
  Context `{OLS: OLSig}.
  
Section StructuralProperties.
    
Lemma LL2N_compat : forall n B1 B2 L1 L2, 
     Permutation B1 B2 -> Permutation L1 L2 -> 
     LL2 n |-- B1 ; L1 -> LL2 n |-- B2 ; L2.
Proof with sauto.
  intros n B1 B2 L1 L2 PB PL H.
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
  refine (LL2N_compat PB PL H).
  refine (LL2N_compat (symmetry PB) (symmetry PL) H).
Qed.

Lemma LL2S_compat : forall B1 B2 L1 L2, 
     Permutation B1 B2 -> Permutation L1 L2 -> 
     LL2 |-- B1 ; L1 -> LL2 |-- B2 ; L2.
Proof with sauto.
  intros B1 B2 L1 L2 PB PL H.
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
  refine (LL2S_compat PB PL H).
  refine (LL2S_compat (symmetry PB) (symmetry PL) H).
Qed.

Instance LL2S_morphism' B:
  Proper (Permutation (A:=oo) ==> Basics.flip Basics.impl) (LL2S B).
Proof.
  unfold Proper; unfold respectful. 
  intros L1 L2 PL H.
  rewrite PL;auto.
 Qed.

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
      
Theorem LL2weakeningN : forall n CC LC F ,
        (LL2N n CC LC) -> LL2N n (F::CC) LC.
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

    
Theorem LL2weakening (CC LC : multiset oo) F:
    LL2S CC LC -> LL2S (F :: CC) LC.
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

Theorem LL2weakeningGen (CC' CC LC : multiset oo):
    LL2S CC LC -> LL2S (CC' ++ CC) LC.
   Proof with sauto. 
    intros.
    revert dependent CC. 
    revert LC.
    induction CC';intros...
    rewrite <- app_comm_cons.
    apply LL2weakening...
 Qed.   

Theorem LLstoreGen (CC' CC LC : multiset oo):
    LL2S (CC'++CC) LC -> LL2S CC (map Quest CC' ++ LC).
   Proof with sauto. 
    intros.
    revert dependent CC. 
    revert LC.
    induction CC';intros...
    simpl...
    LLstore a (map Quest CC' ++ LC).
    eapply IHCC'. 
    rewrite <- Permutation_middle...
 Qed.   

Theorem LLcopyGen (CC' CC LC : multiset oo):
   LL2S CC (CC' ++ LC) ->  LL2S (CC'++CC) LC.
   Proof with sauto. 
    intros.
    revert dependent CC. 
    revert LC.
    induction CC';intros...
    simpl...
    LLcopy a...
    apply LL2weakening...
    eapply IHCC'. 
    rewrite <- Permutation_middle...
 Qed.   
    
Theorem LL2contractionN  : forall n F CC LC,
    LL2N n (F :: CC) LC -> In F CC -> LL2N n CC LC.
  Proof with sauto.
  do 2 intro.
  induction n using lt_wf_ind;intros... 
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
    rewrite perm_swap in H3... 
    apply H in H3...
    LLexists t FX M.
    LLforall FX M.
    LLcopy F0.
    inversion H2...
Qed.

Theorem LL2contraction  : forall F CC LC,
    LL2S (CC++[F]) LC -> In F CC -> LL2S CC LC.
  Proof with sauto.
  intros.
  dependent induction H generalizing CC... 
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

Theorem LLinitGen : forall B F, isFormula F -> isFormula (dual F) ->  LL2S B [F; dual F].
Proof with simpl;sauto.
   induction F;intros isF1 isF2. 
   1-2: LLinit a.
   1,3: LLtop [0].
   1-2: LLbot ['1].
   - LLwith F1 F2 [F1 ^ ⊕ F2 ^].
     LLleft (dual F1) (dual F2) [F1].
     rewrite perm_takeit_8... inversion isF1... inversion isF2...
     LLright (dual F1) (dual F2) [F2]...
     rewrite perm_takeit_8... inversion isF1... inversion isF2...
   - LLpar (dual F1) (dual F2) [F1 ⊗ F2].
      LLtensor F1 F2 [dual F1] [dual F2]. 
      1-2: inversion isF1; inversion isF2...  
   - LLwith (dual F1) (dual F2) [F1 ⊕ F2 ].
     LLleft F1 F2 [dual F1]. inversion isF1... inversion isF2...
     LLright F1 F2 [dual F2]. inversion isF1... inversion isF2...
   - LLpar F1 F2 [dual F1 ⊗ dual F2].
      LLtensor (dual F1) (dual F2) [F1] [F2].
     1-2: rewrite perm_takeit_8...
     1-2: inversion isF1; inversion isF2... 
   - LLstore (dual F) [! F].
     constructor.
     LLcopy (dual F)...
    apply LL2weakening.
     rewrite perm_takeit_8...
    inversion isF1... inversion isF2...
   - LLstore F [! (dual F)].
     constructor.
     LLcopy F...
     apply LL2weakening...
     inversion isF1... inversion isF2...
   - inversion isF1... inversion isF2...
    LLforall o [∃{ fun x : expr con => (o x) ^}]...
    pose proof (H2 x).
   pose proof (H4 x).
    pose proof (H x H5 H6).
   rewrite perm_takeit_8 in H7...
   eapply ll2_ex' with (t:=x) (FX:=fun x0 : expr con => (o x0) ^) (M:=[o x])...
   - inversion isF1... inversion isF2...
    LLforall (fun x : expr con => (o x) ^) [∃{ o}]...
    pose proof (H2 x).
   pose proof (H4 x).
    pose proof (H x H5 H6).
   eapply ll2_ex' with (t:=x) (FX:=o) (M:=[dual (o x)])...
Qed.

End StructuralProperties.
 
 
Section GeneralResults.
  
  
  Lemma LL2_HeightGeq : forall m n  B L,
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