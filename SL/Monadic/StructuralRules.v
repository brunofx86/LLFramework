Require Export LL.SL.Monadic.TacticsPre.
Require Import Coq.Program.Equality.

Export LLNotations .
Set Implicit Arguments.

Section LL1BasicTheory.
  Context `{OLS: OLSig}.
  
Section StructuralProperties.
    
Lemma LL1N_compat : forall n L1 L2, 
     Permutation L1 L2 -> 
     LL1 n |-- L1 -> LL1 n |-- L2.
Proof with sauto.
  intros n L1 L2 PL H.
  revert L1 L2 PL H;
  induction n using lt_wf_ind; intros...
  inversion H0... 
    + rewrite PL in H1.
      LL1init A.  
    + rewrite PL in H1.
      LL1tensor F G M N.
    + rewrite PL in H1.
      LL1plus1 F G M.
    + rewrite PL in H1.
      LL1plus2 F G M.
    + rewrite PL in H1. 
      LL1bang F M. 
    + rewrite PL in H1.
      LL1top M.
    + rewrite PL in H1.
      LL1bot M.
    + rewrite PL in H1.
      LL1par F G M.
    + rewrite PL in H1.
      LL1with F G M.
    + rewrite PL in H1.
      LL1store F M.
    + rewrite PL in H1.
      LL1exist t FX M.
    + rewrite PL in H1.
      LL1forall FX M.
    + rewrite PL in H1.
      LL1weak F M.
    + rewrite PL in H1.
      LL1contr F M.
      eapply H with (L1:=? F :: L1)...
Qed.

Global Instance LL1N_morphism n:
  Proper (Permutation (A:=oo) ==> iff) (LL1N n).
Proof.
  unfold Proper; unfold respectful. 
  intros L1 L2 PL.
  split; intro H.
  refine (LL1N_compat  PL H).
  refine (LL1N_compat  (symmetry PL) H).
Qed.

Lemma LL1S_compat : forall L1 L2, 
     Permutation L1 L2 -> 
     LL1 |-- L1 -> LL1 |--  L2.
Proof with sauto.
  intros L1 L2 PL H.
  revert dependent L2. 
  induction H;intros L2 PL...
  LL1init A.
  all: try rewrite PL in H. 
  LL1tensor F G M N.
  LL1plus1 F G M.
  LL1plus2 F G M.
      LL1bang F M. 
  LL1top M.
  LL1bot M.
  LL1par F G M.
  LL1with F G M.
  LL1store F M.
  LL1exist t FX M.
  LL1forall FX M.
      LL1weak F M.
      LL1contr F M.
 Qed. 

Global Instance LL1S_morphism:
  Proper (Permutation (A:=oo) ==> iff) (LL1S).
Proof.
  unfold Proper; unfold respectful. 
  intros L1 L2 PL.
  split; intro H.
  refine (LL1S_compat PL H).
  refine (LL1S_compat  (symmetry PL) H).
Qed.

Instance LL1S_morphism' :
  Proper (Permutation (A:=oo) ==> Basics.flip Basics.impl) (LL1S ).
Proof.
  unfold Proper; unfold respectful. 
  intros L1 L2 PL H.
  rewrite PL;auto.
 Qed.

Lemma LL1NtoLL1S : forall n L,
    LL1N n L -> LL1S L.
 Proof with sauto. 
  induction n using lt_wf_ind;intros...
  inversion H0...
  all: clear H0. 
  LL1init A. 
  all:
  try repeat
    match goal with
    [H1: LL1N _ _ |- _] => 
    apply H in H1;sauto
    end.
   LL1tensor F G M N.
   LL1plus1 F G M.
    LL1plus2 F G M.
    LL1bang F M.
    LL1top M.
    LL1bot M.
    LL1par F G M.
    LL1with F G M.
    LL1store F M.
    LL1exist t FX M.
    LL1forall FX M.
    specialize (H3 x H0).
    apply H in H3...
        LL1weak F M.
      LL1contr F M.
 
  Qed.    

  
Axiom LL1StoLL1N : forall L,
    LL1S L -> exists n, LL1N n L.

 Theorem LL1weakening B M L:
    Permutation L ((map Quest B) ++ M) -> 
    LL1 |-- M -> LL1 |-- L.
   Proof with sauto. 
    intros.
    revert dependent M.
    revert L.
    induction B;intros...
    simpl in H...
    rewrite H...
    simpl in H...
    rewrite H...
    LL1weak a (map Quest B ++ M). 
    eapply IHB with (M:=M)...
  Qed.
     
 Theorem LL1weakeningN n L M B:
    Permutation L ((map Quest B) ++ M) ->
    n>= length B -> LL1 (n-length B) |-- M -> LL1 n |-- L.
   Proof with sauto. 
    intros.
    revert dependent M.
    revert L.
    induction B;intros...
    simpl in H, H1...
    rewrite H...
    simpl in H1.
    simpl in H.
    simpl in H0.
    assert(n - S (length B) >= 0).
    inversion H1...
     inversion H0...
    eapply IHB with (M:= ? a ::M)... 
    rewrite H...
    rewrite <- minus_Sn_m...
    rewrite Nat.sub_diag in H1.
    rewrite Nat.sub_diag.
    LL1weak a M.
    eapply IHB with (M:= ? a ::M)... 
    rewrite H...
    rewrite <- minus_Sn_m...
    LL1weak a M.
    Qed.
 
 Theorem LL1contraction : forall B L M,
Permutation L (map Quest B ++ M) ->
       LL1 |-- map Quest B ++ L -> LL1 |-- L.
  Proof with sauto.
  intros.
  revert dependent M.
  revert dependent L.
    induction B;intros...
  simpl in H, H0...
   LL1contr a (map Quest B ++ M).
   eapply IHB with (M:=? a :: ? a :: M)...
  rewrite Permutation_midle...
  rewrite H...  
  Qed.

 Theorem LL1contractionN : forall n B L M,
Permutation L (map Quest B ++ M) ->  n >= length B ->
       LL1 (n - length B) |-- map Quest B ++ L -> LL1 n |-- L.
  Proof with sauto.
      intros.
    revert dependent M.
    revert dependent L.
    induction B;intros...
    simpl in H, H1...
    simpl in H, H0, H1...
     assert(n - S (length B) >= 0).
    inversion H1...
    inversion H0...
    clear H0 H2.
    rewrite Nat.sub_diag in H1.
    eapply IHB with (M:= ? a ::M)... 
    rewrite H...
    rewrite <- minus_Sn_m...
    rewrite Nat.sub_diag.
    LL1contr a (map Quest B ++ map Quest B ++ M).
    rewrite <- H...
    rewrite H...
     eapply IHB with (M:= ? a ::M)... 
    rewrite H...
    rewrite <- minus_Sn_m...
    LL1contr a (map Quest B ++ map Quest B ++ M).
    rewrite <- H...
    rewrite H...
   Qed. 
  
End StructuralProperties.
 
 
Section GeneralResults.
  
  
  Lemma LL1_HeightGeq : forall m n L,
        LL1N n L ->
        m>=n -> LL1N m L.
    Proof with sauto.
   intro. induction m ;intros...
   - inversion H0...
   - inversion H0...
     inversion H...
     LL1init A.  
     LL1tensor F G M N. 
     apply IHm in H3...
     apply IHm in H4...
     LL1plus1 F G M.
     apply IHm in H3... 
    LL1plus2 F G M.
    apply IHm in H3... 
    LL1bang F M.
    apply IHm in H3...
    LL1top M. 
    LL1bot M.
    apply IHm in H3... 
    LL1par F G M.
    apply IHm in H3... 
    LL1with F G M.
    apply IHm in H3...
    apply IHm in H4... 
    LL1store F M.
    apply IHm in H3... 
    LL1exist t FX M.
    apply IHm in H5... 
    LL1forall FX M.
    specialize(H4 x H5).
    apply IHm in H4...
    LL1weak F M.
    apply IHm in H3...
    LL1contr F M.
    apply IHm in H3...
 Qed.
 
  End GeneralResults.

 End LL1BasicTheory.