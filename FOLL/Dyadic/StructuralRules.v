
Require Export LL.FOLL.Dyadic.PreTactics.
Require Import Coq.Program.Equality.

Export LLNotations .
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
  LL2init A.  
  LL2top M.  
  LL2plus1 F G M.
  eapply H with (B1:=B1)...
  LL2plus2 F G M.
  eapply H with (B1:=B1)...  
  LL2with F G M.
  eapply H with (B1:=B1)...
  eapply H with (B1:=B1)...    
  LL2bot M.
  eapply H with (B1:=B1)...                          
  LL2par F G M.
  eapply H with (B1:=B1)...
  LL2tensor F G M N.
  eapply H with (B1:=B1)...
  eapply H with (B1:=B1)...
  LL2store F M.
  eapply H with (B1:=F::B1)...
  LL2bang.
  eapply H with (B1:=B1)... 
  LL2exist t FX M.
  eapply H with (B1:=B1)...
  LL2forall FX M.
  eapply H with (B1:=B1)...
  LL2copy F.
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
  LL2init A.
  all: try rewrite PL in H.
  LL2top M.   
  LL2plus1 F G M.
  LL2plus2 F G M.
  LL2with F G M.
  LL2bot M.
  LL2par F G M.
  LL2tensor F G M N.
  LL2store F M.
  LL2exist t FX M.
  LL2forall FX M.
  eapply H2 with (x:=x)...
  rewrite PB in H.
  LL2copy F.
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
  LL2init A. 
  all:
  try repeat
    match goal with
    [H1: LL2N _ _ _ |- _] => 
    apply H in H1;sauto
    end.
   LL2top M. 
   LL2plus1 F G M.
   LL2plus2 F G M.
   LL2with F G M.
   LL2bot M.
   LL2par F G M.
   LL2tensor F G M N.
   LL2store F M.
   LL2exist t FX M.
   LL2forall FX M.
   specialize (H3 x H0).
    apply H in H3...
   LL2copy F.
  Qed.    

  
Axiom LL2StoLL2N : forall B L,
    LL2S B L -> exists n, LL2N n B L.
      
Theorem LL2weakeningN : forall n CC LC F ,
        (LL2N n CC LC) -> LL2N n (F::CC) LC.
 Proof with sauto.
    induction n using lt_wf_ind;intros.
      inversion H0...
      LL2init A.
      LL2top M.
      LL2plus1 F0 G M.
      LL2plus2 F0 G M.
      LL2with F0 G M.
      LL2bot M.
      LL2par F0 G M.
      LL2tensor F0 G M N.
      LL2store F0 M.
      rewrite perm_swap;auto.
      LL2exist t FX M.
      LL2forall FX M.
      LL2copy F0.
      firstorder.
  Qed.

    
Theorem LL2weakening (CC LC : multiset oo) F:
    LL2S CC LC -> LL2S (F :: CC) LC.
   Proof with sauto. 
    intros.
    revert dependent F.
    induction H;intros...
    LL2init A.
    LL2top M.
    LL2plus1 F G M.
    LL2plus2 F G M.
    LL2with F G M.
    LL2bot M.
    LL2par F G M.
    LL2tensor F G M N.
    LL2store F M.
    rewrite perm_swap;auto.
    LL2exist t FX M.
    LL2forall FX M.
    LL2copy F.
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

Theorem LL2storeGen (CC' CC LC : multiset oo):
    LL2S (CC'++CC) LC -> LL2S CC (map Quest CC' ++ LC).
   Proof with sauto. 
    intros.
    revert dependent CC. 
    revert LC.
    induction CC';intros...
    simpl...
    LL2store a (map Quest CC' ++ LC).
    eapply IHCC'. 
    rewrite <- Permutation_middle...
 Qed.   

Theorem LL2copyGen (CC' CC LC : multiset oo):
   LL2S CC (CC' ++ LC) ->  LL2S (CC'++CC) LC.
   Proof with sauto. 
    intros.
    revert dependent CC. 
    revert LC.
    induction CC';intros...
    simpl...
    LL2copy a...
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
    LL2init A.
    LL2top M.
    LL2plus1 F0 G M.
    LL2plus2 F0 G M.
    LL2with F0 G M.
    LL2bot M.
    LL2par F0 G M.
    LL2tensor F0 G M N.
    LL2store F0 M.
    rewrite perm_swap in H3... 
    apply H in H3...
    LL2exist t FX M.
    LL2forall FX M.
    LL2copy F0.
    inversion H2...
Qed.

Theorem LL2contraction  : forall F CC LC,
    LL2S (CC++[F]) LC -> In F CC -> LL2S CC LC.
  Proof with sauto.
  intros.
  dependent induction H generalizing CC... 
    LL2init A.
    LL2top M.
    LL2plus1 F0 G M.
    LL2plus2 F0 G M.
    LL2with F0 G M.
    LL2bot M.
    LL2par F0 G M.
    LL2tensor F0 G M N.
    LL2store F0 M.
    apply IHLL2S...
    LL2exist t FX M.
    LL2forall FX M.
    apply in_app_or in H...
    LL2copy F0.
    inversion H2...
    LL2copy F0.
Qed.

Theorem LL2initGen : forall B F, isFormula F -> isFormula (dual F) ->  LL2S B [F; dual F].
Proof with simpl;sauto.
   induction F;intros isF1 isF2. 
   1-2: LL2init a.
   1,3: LL2top [0].
   1-2: LL2bot ['1].
   - LL2with F1 F2 [F1 ^ ⊕ F2 ^].
     LL2plus1 (dual F1) (dual F2) [F1].
     rewrite perm_takeit_8... inversion isF1... inversion isF2...
     LL2plus2 (dual F1) (dual F2) [F2]...
     rewrite perm_takeit_8... inversion isF1... inversion isF2...
   - LL2par (dual F1) (dual F2) [F1 ⊗ F2].
      LL2tensor F1 F2 [dual F1] [dual F2]. 
      1-2: inversion isF1; inversion isF2...  
   - LL2with (dual F1) (dual F2) [F1 ⊕ F2 ].
     LL2plus1 F1 F2 [dual F1]. inversion isF1... inversion isF2...
     LL2plus2 F1 F2 [dual F2]. inversion isF1... inversion isF2...
   - LL2par F1 F2 [dual F1 ⊗ dual F2].
      LL2tensor (dual F1) (dual F2) [F1] [F2].
     1-2: rewrite perm_takeit_8...
     1-2: inversion isF1; inversion isF2... 
   - LL2store (dual F) [! F].
     constructor.
     LL2copy (dual F)...
    apply LL2weakening.
     rewrite perm_takeit_8...
    inversion isF1... inversion isF2...
   - LL2store F [! (dual F)].
     constructor.
     LL2copy F...
     apply LL2weakening...
     inversion isF1... inversion isF2...
   - inversion isF1... inversion isF2...
    LL2forall o [∃{ fun x : expr con => (o x) ^}]...
    pose proof (H2 x).
   pose proof (H4 x).
    pose proof (H x H5 H6).
   rewrite perm_takeit_8 in H7...
   eapply ll2_ex' with (t:=x) (FX:=fun x0 : expr con => (o x0) ^) (M:=[o x])...
   - inversion isF1... inversion isF2...
    LL2forall (fun x : expr con => (o x) ^) [∃{ o}]...
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
     LL2init A.
     LL2top M. 
     LL2plus1 F G M.
     apply IHm in H3... 
     LL2plus2 F G M.
     apply IHm in H3... 
     LL2with F G M.
     apply IHm in H3...
     apply IHm in H4...
     LL2bot M.
     apply IHm in H3... 
     LL2par F G M.
     apply IHm in H3... 
     LL2tensor F G M N. 
     apply IHm in H3...
     apply IHm in H4...
     LL2store F M.
     apply IHm in H3... 
     LL2bang.
     apply IHm in H1...
     LL2exist t FX M.
     apply IHm in H5... 
     LL2forall FX M.
     specialize(H4 x H5).
     apply IHm in H4...
     LL2copy F.
     apply IHm in H3...
 Qed.
 
  End GeneralResults.

 End LL2BasicTheory.