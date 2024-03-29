Require Export LL.FOLL.Monadic.PreTactics.
Require Import Coq.Program.Equality.

Export LLNotations .
Set Implicit Arguments.

Section LL1BasicTheory.
  Context `{OLS: OLSig}.
  
Section StructuralProperties.
    
Lemma exchangeLL1N : forall n L1 L2, 
     Permutation L1 L2 -> 
     LL1 n |-- L1 -> LL1 n |-- L2.
Proof with sauto.
  intros n L1 L2 PL H.
  revert L1 L2 PL H;
  induction n using lt_wf_ind; intros...
  inversion H0... 
  all: try rewrite PL in H1. 
  LL1init A.  
  LL1top M.  
  LL1plus1 F G M.
  LL1plus2 F G M.  
  LL1with F G M.    
  LL1bot M.                          
  LL1par F G M.
  LL1tensor F G M N.
  LL1store F M.
  LL1bang F M. 
  LL1exist t FX M.
  LL1forall FX M.
  LL1weak F M.
  LL1contr F M.
        eapply H with (L1:=? F :: L1)...
Qed.

Global Instance LL1N_morphism n:
  Proper (Permutation (A:=oo) ==> iff) (LL1N n).
Proof.
  unfold Proper; unfold respectful. 
  intros L1 L2 PL.
  split; intro H.
  refine (exchangeLL1N  PL H).
  refine (exchangeLL1N  (symmetry PL) H).
Qed.

Lemma exchangeLL1S : forall L1 L2, 
     Permutation L1 L2 -> 
     LL1 |-- L1 -> LL1 |--  L2.
Proof with sauto.
  intros L1 L2 PL H.
  revert dependent L2. 
  induction H;intros L2 PL...
    all: try rewrite PL in H. 
  LL1init A.  
  LL1top M.  
  LL1plus1 F G M.
  LL1plus2 F G M.  
  LL1with F G M.    
  LL1bot M.                          
  LL1par F G M.
  LL1tensor F G M N.
  LL1store F M.
  LL1bang F M. 
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
  refine (exchangeLL1S PL H).
  refine (exchangeLL1S  (symmetry PL) H).
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
    LL1top M.
    LL1plus1 F G M.
    LL1plus2 F G M.
    LL1with F G M.
    LL1bot M.
    LL1par F G M.
    LL1tensor F G M N.
    LL1store F M.
    LL1bang F M.
    LL1exist t FX M.
    LL1forall FX M.
    specialize (H3 x H0).
    apply H in H3...
    LL1weak F M.
    LL1contr F M.
  Qed.    

  
Axiom LL1StoLL1N : forall L,
    LL1S L -> exists n, LL1N n L.

 Theorem weakeningLL1S B M L:
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
     
 Theorem weakeningLL1N n L M B:
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
    rewrite Nat.sub_succ_l... 
    rewrite Nat.sub_diag in H1.
    rewrite Nat.sub_diag.
    LL1weak a M.
    eapply IHB with (M:= ? a ::M)... 
    rewrite H...
    rewrite Nat.sub_succ_l... 
    LL1weak a M.
    Qed.
 
 Theorem contractionLL1S : forall B L M,
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

 Theorem contractionLL1N : forall n B L M,
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
    rewrite Nat.sub_succ_l...
    rewrite Nat.sub_diag.
    LL1contr a (map Quest B ++ map Quest B ++ M).
    rewrite <- H...
    rewrite H...
     eapply IHB with (M:= ? a ::M)... 
    rewrite H...
    rewrite Nat.sub_succ_l...
    LL1contr a (map Quest B ++ map Quest B ++ M).
    rewrite <- H...
    rewrite H...
   Qed. 
  
End StructuralProperties.
 
 
Section GeneralResults.
  
  
  Lemma heightGeqLL1N : forall m n L,
        LL1N n L ->
        m>=n -> LL1N m L.
    Proof with sauto.
   intro. induction m ;intros...
   - inversion H0...
   - inversion H0...
     inversion H...

  LL1init A.  
  LL1top M.
  all: try apply IHm in H3...
  all: try apply IHm in H4...
  all: try apply IHm in H5...
  
  LL1plus1 F G M.
  LL1plus2 F G M.
  LL1with F G M.
  LL1bot M.                          
  LL1par F G M.
  LL1tensor F G M N.
  LL1store F M.
  LL1bang F M. 
  LL1exist t FX M.
  LL1forall FX M.
  specialize(H4 x H5).
  apply IHm in H4...  
  LL1weak F M.
  LL1contr F M.
 Qed.
 
  End GeneralResults.

 End LL1BasicTheory.