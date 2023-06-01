Require Import LL.FOLL.Dyadic.Tactics.
Require Import LL.FOLL.Monadic.StructuralRules.

Section LLAdequacy.
  Context `{OLS: OLSig}.

Theorem LL2N_to_LL1S n B L : LL2N n B L -> LL1S ((map Quest B)++L) .
Proof with sauto.
  intros.
  revert dependent B.
  revert L. 
  induction n;intros...
  + inversion H...
      apply weakeningLL1S with (B:=B) (M:=L)...
      LL1init A.
      apply weakeningLL1S with (B:=B) (M:=[One])...
      apply weakeningLL1S with (B:=B) (M:=L)...
      LL1top M.
  + inversion H...
      -
      apply weakeningLL1S with (B:=B) (M:=L)...
      LL1init A.
      -
      apply weakeningLL1S with (B:=B) (M:=L)...
      LL1top M.      
      -
      LL1plus1 F G  (map Quest B++M).
      rewrite H1...
      rewrite <- Permutation_midle...
      -
      LL1plus2 F G  (map Quest B++M).
      rewrite H1...
      rewrite <- Permutation_midle...
      -
      LL1with F G  (map Quest B++M).
      rewrite H1...
      rewrite <- Permutation_midle...
      rewrite <- Permutation_midle...
      -
      LL1bot   (map Quest B++M).
      rewrite H1...  
      -
      LL1par F G  (map Quest B++M).
      rewrite H1...
      rewrite <- Permutation_midle...
      rewrite <- Permutation_midle...
      -
      apply contractionLL1S with (B:=B) (M:=L)...
      LL1tensor F G (map Quest B++M) (map Quest B++N).
      rewrite H1...
      rewrite <- Permutation_midle...
      rewrite <- Permutation_midle...
      -
       eapply IHn in H2.
       simpl in H2...
       rewrite H1.
       rewrite  Permutation_midle... 
      -
       LL1bang F B...
       rewrite Permutation_cons_append...
       -
       LL1exist t  FX (map Quest B++M).
       rewrite H1...
       rewrite <- Permutation_midle...
       -
       LL1forall  FX (map Quest B++M).
       rewrite H1...
       specialize(H3 x H0).
       rewrite <- Permutation_midle...
       -
       eapply IHn in H2.
       apply InPermutation in H1...
       rewrite H1.
       simpl...
       LL1contr F (map Quest x ++ L).
       LL1store F (? F :: map Quest x ++ L).
       rewrite H1 in H2.
       simpl in H2...
       rewrite perm_swap.
       rewrite <- Permutation_midle...
 Qed.      
  
  (* TODO: generalize this result *)    
  Theorem destructMapQuest B C M N: 
    Permutation (map Quest B ++ C) (M ++ N) -> 
    exists B_1 B_2 C_1 C_2, 
    Permutation B ( (B_1 ++ B_2)) /\ 
    Permutation C (C_1 ++ C_2) /\ 
    Permutation M (map Quest B_1 ++ C_1) /\ 
    Permutation N (map Quest B_2 ++ C_2). 
  Proof with sauto.
    intros.
    revert dependent C.
    revert dependent M.
    revert dependent N.
    induction B;intros.
    * 
      eexists []. 
      eexists []. 
      eexists M.
      eexists N. 
      simpl.
      split;auto.
    *
    simpl in H.
    checkPermutationCases H.
      - symmetry in H1.
         eapply IHB in H1... 
           eexists (a::x0).
           eexists x1.
           eexists x2.
           eexists x3.
           split;auto.
           simpl...
           split;auto.
           split;auto.
           simpl...
       - symmetry in H1.
         eapply IHB in H1... 
          eexists x0.
        eexists (a::x1).
        eexists x2.
        eexists x3.
        split...
        simpl...
        rewrite H0...
        simpl...
        Qed. 
 
 (* TODO: generalize this result *)  
    Theorem destructMapQuest' B C M : 
    Permutation (map Quest B ++ C) (map Quest M) -> 
    exists C_1, 
    Permutation C ( map Quest C_1) /\ Permutation (B++C_1) M  .  
  Proof with sauto.
    intros.
    revert dependent B.
    revert dependent C.
    induction M;intros.
    + simpl in H.
        symmetry in H.
        apply Permutation_nil in H...
        exists nil...
    +
    simpl in H...
    checkPermutationCases H.
    2:{ apply IHM in H1...
          eexists (a::x0)...
          rewrite H.
          simpl...
          rewrite <- H2...
           }
      symmetry in H.    
    apply Permutation_map_inv in H...
    destruct x0...
    simpl in H0.
    inversion H0...
      eapply IHM in H1... 
    exists x...
    rewrite H2.
    rewrite <-  H0...  
   Qed.

Import DyadicTactics.
      
Theorem LL1N_to_LL2S n B L : LL1N n ((map Quest B)++L) -> LL2S B L.
Proof with sauto.
  intros.
  revert dependent B.
  revert L. 
  induction n;intros...
  + inversion H...
     - checkPermutationCases H0.
        { destruct B; simpl in H0;
           inversion H0... }
        { destruct B.
           simpl in H0. inversion H0...
           simpl in H0. 
          checkPermutationCases H0. }
        LLinit A.
        destruct B;
        simpl in H3; inversion H3...
     - destruct B;
        simpl in H1; inversion H1...
     - assert(In Top L).
           checkPermutationCases H0.
           2:{ rewrite H0... }
        assert(In Top (map Quest B) ).
        rewrite H0...
        apply in_map_iff in H1...
        apply InPermutation in H1...
        LLtop x.
  + inversion H...
     - checkPermutationCases H0.
        { destruct B; simpl in H0;
           inversion H0... }
        { destruct B.
           simpl in H0. inversion H0...
           simpl in H0. 
          checkPermutationCases H0. }
        LLinit A.
        destruct B;
        simpl in H3; inversion H3...
     - destruct B;
        simpl in H1; inversion H1...
     - assert(In Top L).
           checkPermutationCases H0.
           2:{ rewrite H0... }
        assert(In Top (map Quest B) ).
        rewrite H0...
        apply in_map_iff in H1...
        apply InPermutation in H1...
        LLtop x. 
       - assert(~ In (F ⊕ G)  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (F ⊕ G) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (F ⊕ G)  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLleft F G x.
        eapply IHn.
        rewrite Permutation_midle. 
        rewrite H5...
       - assert(~ In (F ⊕ G)  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (F ⊕ G) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (F ⊕ G)  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLright F G x.
        eapply IHn.
        rewrite Permutation_midle. 
        rewrite H5...
       - assert(~ In (F & G)  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (F & G) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (F & G)  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLwith F G x.
        eapply IHn.
        rewrite !Permutation_midle. 
        rewrite H6...
        eapply IHn.
        rewrite !Permutation_midle. 
        rewrite H6...
   - assert(~ In Bot  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In Bot L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In Bot  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLbot  x.
        eapply IHn.
        rewrite H5...
       - assert(~ In (F ⅋ G)  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (F ⅋ G) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (F ⅋ G)  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLpar F G x.
        eapply IHn.
        rewrite !Permutation_midle. 
        rewrite H5...     
        - assert(~ In (F ⊗ G)  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (F ⊗ G) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (F ⊗ G)  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        apply destructMapQuest in H6...
        LLtensor F G x2 x3.
        rewrite H7 in H2.
        rewrite <- Permutation_midle in H2.
        eapply IHn in H2.
        rewrite H5.
        rewrite Permutation_app_comm.
        apply weakeningLL2SGen...
        rewrite H10 in H3.
        rewrite <- Permutation_midle in H3.
        eapply IHn in H3.
        rewrite H5.
        apply weakeningLL2SGen...
   - 
       checkPermutationCases H1.
       assert(In F B).
       assert(In (? F)  (map Quest B) ).
       rewrite H1... 
       apply in_map_iff in H0...
       inversion H4...
       LLcopy F.
       apply InPermutation in H0...
       rewrite H0. 
       apply weakeningLL2S.
       eapply IHn.
       rewrite H0 in H1.
       simpl in H1.
       apply Permutation_cons_inv in H1.
       rewrite H1...
       rewrite !Permutation_midle. 
        rewrite H3...
      rewrite <- H3 in H2.
      rewrite <- !Permutation_midle in H2. 
        eapply IHn 
        in H2.
        LLstore F x.
        LLcopy F...
        apply weakeningLL2S... 
   - assert(~ In (! F )  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (! F) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (! F)  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        apply destructMapQuest' in H5...
        rewrite Permutation_cons_append in H2.
        eapply IHn in H2.
        rewrite H4 in H1.
        rewrite H1.
        rewrite Permutation_cons_append.
        apply storeGenLL2S.
        LLbang.
        rewrite Permutation_app_comm.
        rewrite H6...
        - assert(~ In (∃{ FX})  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (∃{ FX}) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (∃{ FX})  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLexists t FX x.
        eapply IHn.
        rewrite !Permutation_midle. 
        rewrite H7...
        - assert(~ In (∀{ FX})  (map Quest B) ).
        intro.
        apply in_map_iff in H0...
        assert(In (∀{ FX}) L ).
           checkPermutationCases H1.
           2:{ rewrite H1... }
        assert(In (∀{ FX})  (map Quest B) ).
        rewrite H1...
        contradiction.
        checkPermutationCases H1.
        rewrite H1 in H0.
        elim H0...
        LLforall FX x.
        specialize (H3 x0 H5).
        eapply IHn.
        rewrite !Permutation_midle. 
        rewrite H6...
        - checkPermutationCases H1. 
          symmetry in H1.    
    apply Permutation_map_inv in H1...
    destruct x0...
    simpl in H0.
    inversion H0...
    
    rewrite <- H3 in H2.
    apply IHn in H2.
    rewrite H4.
    apply weakeningLL2S...
    rewrite <- H3 in H2.
    apply IHn in H2.
    LLstore F x.
    apply weakeningLL2S...
        - checkPermutationCases H1. 
          symmetry in H1.    
    apply Permutation_map_inv in H1...
    destruct x0...
    simpl in H0.
    inversion H0...
    rewrite app_comm_cons in H2.
    rewrite <- map_cons in H2.
    apply IHn in H2.
    rewrite H4.
    apply contractionLL2S with (F:=o)...
    rewrite <- H4.
    rewrite Permutation_app_comm...
    rewrite H1 in H2.
    rewrite PermutConsApp in H2.
    rewrite !app_comm_cons in H2.
    rewrite <- !map_cons in H2.
    apply IHn in H2.
    LLstore F x.
    apply contractionLL2S with (F:=F)...
    rewrite Permutation_app_comm...
    Qed.
       
End LLAdequacy.

