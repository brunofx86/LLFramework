(** This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination. *)

Require Export LL.Misc.UtilsForall. 
Require Export LL.Framework.SL.FLL.Specifications.OL2FLL. 
Require Export LL.Framework.SL.FLL.Tactics. 

Set Implicit Arguments.

Section OLSyntax.
Context `{OL:OLSyntax}.

Section PositiveAtoms.

Lemma  positiveIsAtom A: IsPositiveAtomFormula A -> IsPositiveAtom A. 
Proof with subst;auto. 
  intros.
  inversion H...  
Qed.  

Lemma  OLFormula2PosUPFormulaL A: isOLFormula A ->IsPositiveAtomFormulaL [atom (up A)]. 
Proof with subst;auto. 
  intros.
  constructor...
Qed.  
  
Lemma  OLFormula2PosDWFormulaL A: isOLFormula A ->IsPositiveAtomFormulaL [atom (down A)]. 
Proof with subst;auto. 
  intros.
  constructor...
Qed.  



Global Instance perm_IsPositiveAtomFormulaL  :
      Proper (@Permutation oo ==> Basics.impl)
             (IsPositiveAtomFormulaL ).
Proof.
  unfold Proper; unfold respectful; unfold Basics.impl.
  intros.
  unfold IsPositiveAtomFormulaL.
  rewrite <- H;auto.
Qed.

Global Instance perm_IsPositiveAtomBFormulaL  :
      Proper (@Permutation oo ==> Basics.impl)
             (IsPositiveAtomBFormulaL ).
Proof.
  unfold Proper; unfold respectful; unfold Basics.impl.
  intros.
  unfold IsPositiveAtomBFormulaL.
  rewrite <- H;auto.
Qed.

Global Instance perm_IsOLFormulaL  :
      Proper (@Permutation uexp ==> Basics.impl)
             (isOLFormulaL ).
Proof.
  unfold Proper; unfold respectful; unfold Basics.impl.
  intros.
  unfold isOLFormulaL.
  rewrite <- H;auto.
Qed.

End PositiveAtoms.

Section OLEncodings.
 
Lemma LEncodeApp  L1 L2 : LEncode (L1++L2) = LEncode L1 ++ LEncode  L2.
Proof with sauto.
 unfold LEncode;
 rewrite map_app;auto.
Qed.

Lemma REncodeApp  L1 L2 : REncode (L1++L2) = REncode L1 ++ REncode  L2.
Proof with sauto.
  autounfold.
  rewrite map_app;auto.
Qed.

Lemma REncodeBApp  L1 L2 : REncodeB (L1++L2) = REncodeB L1 ++ REncodeB  L2.
Proof with sauto.
  autounfold.
  rewrite map_app;auto.
Qed.

Lemma LEncodePerm L1 L2 : Permutation L1 L2 -> Permutation (LEncode L1) (LEncode L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 

Lemma REncodePerm L1 L2 : Permutation L1 L2 -> Permutation (REncode L1) (REncode L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 

Lemma REncodeBPerm L1 L2 : Permutation L1 L2 -> Permutation (REncodeB L1) (REncodeB L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 

 Theorem posDestruct' K: IsPositiveAtomFormulaL K -> exists K1 K2, Permutation K (LEncode K1 ++ REncode K2).
 Proof with sauto.
 induction K;intros...
 exists [], [].
 simpl;auto.
 inversion H...
 inversion H2...
 - destruct IHK...
   exists (A::x), x0.
   simpl...
 - destruct IHK...
   exists x, (A::x0).
   simpl.
   rewrite H1...
 Qed.  

(*  Theorem posDestructB' K: IsPositiveAtomBFormulaL K -> exists K1 K2, Permutation K (LEncode K1 ++ REncodeB K2).
 Proof with sauto.
 induction K;intros...
 exists [], [].
 simpl;auto.
 inversion H...
 inversion H2...
 - destruct IHK...
   exists (A::x), x0.
   simpl...
 - destruct IHK...
   exists x, (A::x0).
   simpl.
   rewrite H1...
 Qed.  

 *) Theorem destructREncode C: forall D1 D2, Permutation (REncode C) (D1++D2) ->
       exists X Y, Permutation D1 (REncode X) /\ Permutation D2 (REncode Y) /\ Permutation C (X++Y). 
Proof with sauto.
  induction C;intros...
  simpl in H...
  exists [], []...
  simpl in H.
  checkPermutationCases H.
  - symmetry in H1.
    eapply IHC in H1...
    exists (a::x0), x1.
    simpl.
    rewrite <- H0...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0, (a::x1).
   simpl...
   rewrite H4...
Qed.

 Theorem destructREncodeB C: forall D1 D2, Permutation (REncodeB C) (D1++D2) ->
       exists X Y, Permutation D1 (REncodeB X) /\ Permutation D2 (REncodeB Y) /\ Permutation C (X++Y). 
Proof with sauto.
  induction C;intros...
  simpl in H...
  exists [], []...
  simpl in H.
  checkPermutationCases H.
  - symmetry in H1.
    eapply IHC in H1...
    exists (a::x0), x1.
    simpl.
    rewrite <- H0...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0, (a::x1).
   simpl...
   rewrite H4...
Qed.

Theorem destructLEncode C: forall D1 D2, Permutation (LEncode C) (D1++D2) ->
       exists X Y, Permutation D1 (LEncode X) /\ Permutation D2 (LEncode Y) /\ Permutation C (X++Y). 
Proof with sauto.
  induction C;intros...
  simpl in H...
  exists [], []...
  simpl in H.
  checkPermutationCases H.
  - symmetry in H1.
    eapply IHC in H1...
    exists (a::x0), x1...
    simpl.
    rewrite H...
    rewrite H4...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0, (a::x1)...
   rewrite H...
   simpl...
   rewrite H4...
Qed.
  
Theorem destructEncode C1 C1' C2 C2': 
    Permutation (LEncode C1 ++ REncode C2) (C1' ++ C2') -> 
    exists K4_1 K4_2 K4_3 K4_4, 
    Permutation C1' (LEncode K4_1 ++ REncode K4_2) /\ 
    Permutation C2' (LEncode K4_3 ++ REncode K4_4) /\ 
    Permutation C1 (K4_1 ++ K4_3) /\ 
    Permutation C2 (K4_2 ++ K4_4). 
Proof with sauto.
  intros.
  revert dependent C1'.
  revert dependent C2.
  revert dependent C2'.
  induction C1;intros...
  * simpl in *... 
     apply destructREncode in H...
     eexists [], x, [], x0... 
  *
     simpl in H.
     checkPermutationCases H.
     - symmetry in H1.  
       eapply IHC1 in H1...
       eexists (a::x0), x1, x2, x3...
       rewrite H...
       rewrite H0...
       rewrite <- app_comm_cons.
       rewrite H2...
    - symmetry in H1.  
       eapply IHC1 in H1...
       eexists x0, x1, (a::x2), x3...
       rewrite H...
       simpl.
       rewrite H3...
       rewrite H2...
 Qed.          

Theorem destructEncodeB C1 C1' C2 C2': 
    Permutation (LEncode C1 ++ REncodeB C2) (C1' ++ C2') -> 
    exists K4_1 K4_2 K4_3 K4_4, 
    Permutation C1' (LEncode K4_1 ++ REncodeB K4_2) /\ 
    Permutation C2' (LEncode K4_3 ++ REncodeB K4_4) /\ 
    Permutation C1 (K4_1 ++ K4_3) /\ 
    Permutation C2 (K4_2 ++ K4_4). 
Proof with sauto.
  intros.
  revert dependent C1'.
  revert dependent C2.
  revert dependent C2'.
  induction C1;intros...
  * simpl in *... 
     apply destructREncodeB in H...
     eexists [], x, [], x0... 
  *
     simpl in H.
     checkPermutationCases H.
     - symmetry in H1.  
       eapply IHC1 in H1...
       eexists (a::x0), x1, x2, x3...
       rewrite H...
       rewrite H0...
       rewrite <- app_comm_cons.
       rewrite H2...
    - symmetry in H1.  
       eapply IHC1 in H1...
       eexists x0, x1, (a::x2), x3...
       rewrite H...
       simpl.
       rewrite H3...
       rewrite H2...
 Qed.          

Lemma PositiveAtomREOLFormula L : IsPositiveAtomFormulaL (REncode L) -> isOLFormulaL L.
Proof with sauto.
  intros.
  induction L;intros... 
  inversion H...
  apply IHL in H3...
  apply Forall_cons;auto.
  inversion H2... 
Qed.

Lemma PositiveAtomREOLFormulaB L : IsPositiveAtomFormulaL (REncodeB L) -> isOLFormulaL L.
Proof with sauto.
  intros.
  induction L;intros... 
  inversion H...
  apply IHL in H3...
  apply Forall_cons;auto.
  inversion H2... 
Qed.

Lemma PositiveAtomLEOLFormula L : IsPositiveAtomFormulaL (LEncode L) -> isOLFormulaL L.
Proof with sauto.
  intros.
  induction L;intros... 
  inversion H...
  apply IHL in H3...
  apply Forall_cons;auto.
  inversion H2... 
Qed.

Lemma PositiveAtomLEOLFormulaB L : IsPositiveAtomBFormulaL (LEncode L) -> isOLFormulaL L.
Proof with sauto.
  intros.
  induction L;intros... 
  inversion H...
  apply IHL in H3...
  apply Forall_cons;auto.
  inversion H2... 
Qed.
   
Lemma isOLLEncode : forall L, isOLFormulaL L -> IsPositiveAtomFormulaL (LEncode L).
Proof with subst;auto.
  intros.
  induction L; simpl...
  constructor.
  inversion H...
  apply IHL...
  inversion H...
Qed.

Lemma isOLLEncodeB : forall L, isOLFormulaL L -> IsPositiveAtomBFormulaL (LEncode L).
Proof with subst;auto.
  intros.
  induction L; simpl...
  constructor.
  inversion H...
  apply IHL...
  inversion H...
Qed.
  
Lemma isOLREncode : forall L, isOLFormulaL L -> IsPositiveAtomFormulaL (REncode L).
Proof with sauto.
  intros.
  induction L; simpl...
  constructor.
  inversion H...
  apply IHL...
  inversion H...
Qed.
  
Lemma isOLREncodeB : forall L, isOLFormulaL L -> IsPositiveAtomBFormulaL (REncodeB L).
Proof with sauto.
  intros.
  induction L; simpl... 
  constructor. simpl.
  inversion H...
  apply IHL...
  inversion H...
Qed.

Lemma PermutationLEncode : forall L a x x1,
      Permutation (LEncode L) (atom (down  a ) :: x) -> Permutation (a :: x1) L -> Permutation x (LEncode x1).
Proof with sauto.
    intros.      
    assert(Permutation (atom (down  a )  :: x) (LEncode ((a :: x1)))).
    {  symmetry.
       symmetry in H.
       apply Permutation_map_inv in H.
       do 2 destruct H.
       rewrite H.
       apply Permutation_map.
       simpl.
       rewrite <- H1.
       unfold LEncode.
       rewrite <- H0;auto.
      }
    simpl in H1.
    eapply (Permutation_cons_inv H1).
  Qed.

Lemma PermutationREncode : forall L a x x1,
      Permutation (REncode L) (atom (up  a ) :: x) -> Permutation (a :: x1) L -> Permutation x (REncode x1).
Proof with sauto.
    intros.      
    assert(Permutation (atom (up  a )  :: x) (REncode ((a :: x1)))).
    {  symmetry.
       symmetry in H.
       apply Permutation_map_inv in H.
       do 2 destruct H.
       rewrite H.
       apply Permutation_map.
       simpl.
       rewrite <- H1.
       unfold REncode.
       rewrite <- H0;auto.
      }
    simpl in H1.
    eapply (Permutation_cons_inv H1).
  Qed.

Lemma PermutationREncodeB : forall L a x x1,
      Permutation (REncodeB L) (Bang (atom (up  a )) :: x) -> Permutation (a :: x1) L -> Permutation x (REncodeB x1).
Proof with sauto.
    intros.      
    assert(Permutation (Bang (atom (up  a) )  :: x) (REncodeB ((a :: x1)))).
    {  symmetry.
       symmetry in H.
       apply Permutation_map_inv in H.
       do 2 destruct H.
       rewrite H.
       apply Permutation_map.
       simpl.
       rewrite <- H1...
      }
    simpl in H1.
    eapply (Permutation_cons_inv H1).
  Qed.

Lemma InLEncode : forall L a,
      In (atom (down  a ) ) (LEncode L) <-> In a L.
Proof with sauto.
  split;induction L;simpl;intros...
  inversion H0...
Qed.

Lemma InREncode : forall L a,
      In (atom (up  a ) ) (REncode L) <-> In a L.
Proof with sauto.
  split;induction L;simpl;intros...
  inversion H0...
Qed.

Lemma InREncodeB : forall L a,
      In (Bang (atom (up  a )) ) (REncodeB L) <-> In a L.
Proof with sauto.
  split;induction L;simpl;intros...
  inversion H0...
Qed.

Lemma isOLFormulaIn : forall F L, 
      isOLFormulaL L -> In F L -> isOLFormula F. 
Proof.
  intros.
  unfold isOLFormulaL in H.
  generalize (Forall_forall isOLFormula L );intro.
  destruct H1.
  apply H1 with (x:= F) in H ;auto.
 Qed.

Theorem NoDinR : forall F L, In (atom (down  F ) ) (REncode L) -> False .
Proof with sauto.  
  intros.
  induction L;auto.
  simpl in H...
Qed.

Theorem NoDinRB : forall F L, In (atom (down  F ) ) (REncodeB L) -> False .
Proof with sauto.  
  intros.
  induction L;auto.
  simpl in H...
Qed.

Theorem NoUinL : forall F L, In (atom (up  F ) ) (LEncode L) -> False .
Proof with sauto.  
  intros.
  induction L;auto.
  simpl in H...
Qed.

Theorem NoUinLB : forall F L, In (Bang (atom (up  F )) ) (LEncode L) -> False .
Proof with sauto.  
  intros.
  induction L;auto.
  simpl in H...
Qed.

Theorem NoDinR' : forall F L x, Permutation (REncode L) (atom (down  F ) ::x) -> False .
Proof with sauto.  
  intros.
  eapply NoDinR with (F:=F) (L:=L).
  rewrite H...
Qed.

Theorem NoDinRB' : forall F L x, Permutation (REncodeB L) (atom (down  F ) ::x) -> False .
Proof with sauto.  
  intros.
  eapply NoDinRB with (F:=F) (L:=L).
  rewrite H...
Qed.

Theorem NoUinL' : forall F L x, Permutation (LEncode L) (atom (up  F ) ::x)  -> False .
Proof with sauto.  
  intros.
  eapply NoUinL with (F:=F) (L:=L).
  rewrite H...
Qed.

Theorem NoUinLB' : forall F L x, Permutation (LEncode L) (Bang (atom (up  F )) ::x)  -> False .
Proof with sauto.  
  intros.
  eapply NoUinLB with (F:=F) (L:=L).
  rewrite H...
Qed.
  
Theorem downLeft : forall L L' F,
      In (atom (down  F ) ) (LEncode L ++ REncode L') ->
      In (atom (down  F ) ) (LEncode L).
Proof with sauto.  
  intros.
  apply in_app_or in H...
  apply NoDinR in H0...
Qed.

Theorem downLeftB : forall L L' F,
      In (atom (down  F ) ) (LEncode L ++ REncodeB L') ->
      In (atom (down  F ) ) (LEncode L).
Proof with sauto.  
  intros.
  apply in_app_or in H...
  apply NoDinRB in H0...
Qed.
    
Theorem upRight : forall L L' F,
    In (atom (up  F ) ) (LEncode L ++ REncode L') ->
    In (atom (up  F ) ) (REncode L').
Proof with sauto.  
  intros.
  apply in_app_or in H...
  apply NoUinL in H0...
Qed.

Theorem upRightD : forall L L' F,
    In (Bang (atom (up  F )) ) (LEncode L ++ REncodeB L') ->
    In (Bang (atom (up  F )) ) (REncodeB L').
Proof with sauto.  
  intros.
  apply in_app_or in H...
  apply NoUinLB in H0... 
Qed.

Theorem OLInPermutation: forall L F,
      In (atom (up  F )) (REncode L) ->
      exists L', Permutation L (F:: L').
Proof with sauto. 
  induction L;intros...
  inversion H.
  simpl in H.
    
  inversion H...
  inversion H1... 
  eexists;eauto.
  inversion H0... 
  eexists;eauto.
  inversion H1... 
  eexists;eauto.
  apply IHL in H1...
  exists (a::x).
  rewrite perm_takeit_6...
Qed.

Theorem OLInPermutationB: forall L F,
      In (Bang (atom (up  F ))) (REncodeB L) ->
      exists L', Permutation L (F:: L').
Proof with sauto. 
  induction L;intros...
  inversion H.
  simpl in H.
    
  inversion H...
  inversion H1... 
  eexists;eauto.
  inversion H0... 
  eexists;eauto.
  inversion H1... 
  eexists;eauto.
  apply IHL in H1...
  exists (a::x).
  rewrite perm_takeit_6...
Qed.

Lemma MapREncodeEqual: forall L L', (REncode L) = (REncode L') -> L = L'.
Proof with sauto.
  induction L;intros;simpl in *...
  erewrite map_eq_nil...
  exact (symmetry H).
  destruct L'...
  simpl in H.
  inversion H...
  erewrite IHL;auto.
Qed.  

Lemma MapREncodeEqualB: forall L L', (REncodeB L) = (REncodeB L') -> L = L'.
Proof with sauto.
  induction L;intros;simpl in *...
  erewrite map_eq_nil...
  exact (symmetry H).
  destruct L'...
  simpl in H.
  inversion H...
  erewrite IHL;auto.
Qed.  

Lemma MapLEncodeEqual: forall L L', (LEncode L) = (LEncode L') -> L = L'.
Proof with sauto.
  induction L;intros;simpl in *...
  erewrite map_eq_nil...
  exact (symmetry H).
  destruct L'...
  simpl in H.
  inversion H...
  erewrite IHL;auto.
Qed.   

Lemma UpREncode P1 P2 L1 L2 :
    Permutation (atom (up  P1 )::REncode L1) (atom (up  P2 ):: REncode L2) ->
    (
      P1 = P2 /\ Permutation (REncode L1) (REncode L2)
    ) \/ (
      exists L2',
        Permutation (REncode L2) (atom (up  P1 )::REncode L2') /\
        Permutation (REncode L1) (atom (up  P2 )::REncode L2')
    ).
Proof with sauto.
  intro HP.
  assert (HI:=in_eq  (atom (up  P1 )) (REncode L1)).
  rewrite HP in HI.
  destruct HI as [HI|HI].
  - inversion HI... 
    left.
    split;auto.
    apply Permutation_cons_inv in HP;auto.
  - right.
    apply in_map_iff in HI...
    inversion H...
    destruct (in_split _ _ H0) as (L2A,(L2B,HL2)).
    exists (L2A++L2B).
    split.
    + rewrite HL2.
      rewrite !REncodeApp.
      simpl... 
    + 
      rewrite HL2 in HP.
      rewrite REncodeApp in HP.
      simpl in HP.
      rewrite app_comm_cons in HP.
      eapply Permutation_cons_app_inv  in HP... 
      rewrite HP.
      rewrite !REncodeApp.
      simpl...
 Qed.

Lemma UpREncodeB P1 P2 L1 L2 :
    Permutation (Bang (atom (up  P1 ))::REncodeB L1) (Bang (atom (up  P2 )):: REncodeB L2) ->
    (
      P1 = P2 /\ Permutation (REncodeB L1) (REncodeB L2)
    ) \/ (
      exists L2',
        Permutation (REncodeB L2) (Bang (atom (up  P1 ))::REncodeB L2') /\
        Permutation (REncodeB L1) (Bang (atom (up  P2 ))::REncodeB L2')
    ).
Proof with sauto.
  intro HP.
  assert (HI:=in_eq  (Bang (atom (up  P1 ))) (REncodeB L1)).
  rewrite HP in HI.
  destruct HI as [HI|HI].
  - inversion HI... 
    left.
    split;auto.
    apply Permutation_cons_inv in HP;auto.
  - right.
    apply in_map_iff in HI...
    inversion H...
    destruct (in_split _ _ H0) as (L2A,(L2B,HL2)).
    exists (L2A++L2B).
    split.
    + rewrite HL2.
      rewrite !REncodeBApp.
      simpl... 
    + 
      rewrite HL2 in HP.
      rewrite REncodeBApp in HP.
      simpl in HP.
      rewrite app_comm_cons in HP.
      eapply Permutation_cons_app_inv  in HP... 
      rewrite HP.
      rewrite !REncodeBApp.
      simpl...
 Qed.

Lemma DwLEncode P1 P2 L1 L2 :
    Permutation (atom (down  P1 )::LEncode L1) (atom (down  P2 )::LEncode L2) ->
    (
      P1 = P2 /\ Permutation (LEncode L1) (LEncode L2)
    ) \/ (
      exists L2',
        Permutation (LEncode L2) (atom (down  P1 )::LEncode L2') /\
        Permutation (LEncode L1) (atom (down  P2 )::LEncode L2')
    ).
Proof with sauto.
  intro HP.
  assert (HI:=in_eq  (atom (down  P1 )) (LEncode L1)).
  rewrite HP in HI.
  destruct HI as [HI|HI].
  - inversion HI... 
    left.
    split;auto.
    apply Permutation_cons_inv in HP;auto.
  - right.
    apply in_map_iff in HI...
    inversion H...
    destruct (in_split _ _ H0) as (L2A,(L2B,HL2)).
    exists (L2A++L2B).
    split.
    + rewrite HL2.
      rewrite !LEncodeApp.
      simpl... 
    + 
      rewrite HL2 in HP.
      rewrite LEncodeApp in HP.
      simpl in HP.
      rewrite app_comm_cons in HP.
      eapply Permutation_cons_app_inv  in HP... 
      rewrite HP.
      rewrite !LEncodeApp.
      simpl...
Qed.
    
   
Theorem OLInPermutation': forall L x F,
     Permutation (REncode L) (atom (up F ):: REncode x) ->
     Permutation L (F:: x).
Proof with sauto.
   induction L;intros...
   simpl in H...
   simpl in H...
   apply UpREncode in H...
   - apply Permutation_cons...
     apply Permutation_map_inv in H2...
     apply MapREncodeEqual in H...
   - apply IHL in H1.
     assert(Permutation (REncode x) (REncode (a :: x0))).
     rewrite H...
     apply Permutation_map_inv in H0...
     apply MapREncodeEqual in H2...
     rewrite H1.
     rewrite <- H3...
Qed. 

Theorem OLInPermutationB': forall L x F,
     Permutation (REncodeB L) (Bang (atom (up F )):: REncodeB x) ->
     Permutation L (F:: x).
Proof with sauto.
   induction L;intros...
   simpl in H...
   simpl in H...
   apply UpREncodeB in H...
   - apply Permutation_cons...
     apply Permutation_map_inv in H2...
     apply MapREncodeEqualB in H...
   - apply IHL in H1.
     assert(Permutation (REncodeB x) (REncodeB (a :: x0))).
     rewrite H...
     apply Permutation_map_inv in H0...
     apply MapREncodeEqualB in H2...
     rewrite H1.
     rewrite <- H3...
Qed. 
   
Theorem OLInPermutationL: forall L F,
      In (atom (down  F)) (LEncode L) ->
      exists L', Permutation L (F:: L').
Proof with sauto.
  induction L;intros.
  inversion H.  
  simpl in H.
  destruct H.
  inversion H... 
  eexists;eauto.
  apply IHL in H...
  exists (a:: x).
  rewrite H...
Qed.

Theorem OLInPermutationL': forall L x F,
     Permutation (LEncode L) (atom (down  F):: LEncode x) ->
     Permutation L (F:: x).
 Proof with sauto.
   induction L;intros...
   simpl in H...
   simpl in H...
   apply DwLEncode in H...
   - apply Permutation_cons...
     apply Permutation_map_inv in H2...
     apply MapLEncodeEqual in H...
   - apply IHL in H1.
     assert(Permutation (LEncode x) (LEncode (a :: x0))).
     rewrite H...
     apply Permutation_map_inv in H0...
     apply MapLEncodeEqual in H2...
     rewrite H1.
     rewrite <- H3...
Qed. 
  
Theorem LEncodePermutation: forall L M,
     Permutation (LEncode L) (LEncode M) ->
     Permutation L M.
 Proof with sauto.
   induction M;intros...
   simpl in H...
  apply map_eq_nil in H...
  apply OLInPermutationL' in H...
Qed.  

Theorem REncodePermutation: forall L M,
     Permutation (REncode L) (REncode M) ->
     Permutation L M.
 Proof with sauto.
   induction M;intros...
   simpl in H...
  apply map_eq_nil in H...
  apply OLInPermutation' in H...
Qed.  

Theorem REncodeBPermutation: forall L M,
     Permutation (REncodeB L) (REncodeB M) ->
     Permutation L M.
 Proof with sauto.
   induction M;intros...
   simpl in H...
  apply map_eq_nil in H...
  apply OLInPermutationB' in H...
Qed.  
  
Lemma LEncodePositiveAtom F L : In (F) (LEncode L) -> IsPositiveAtom F.
Proof with sauto.
  induction L;intros... 
  inversion H. 
  inversion H...
Qed.

Lemma REncodePositiveAtom F L : In (F) (REncode L) -> IsPositiveAtom F.
Proof with sauto.
  induction L;intros... 
  inversion H. 
  inversion H...
Qed.
  
Lemma InIsPositive : forall F L L', In F (LEncode L ++ REncode L') -> IsPositiveAtom F.
  Proof with sauto.
  intros.
  apply in_app_or in H...
  apply LEncodePositiveAtom in H0;auto.
  apply REncodePositiveAtom in H0;auto.
Qed.

Theorem checkEncodeCasesU L L' x F : 
      Permutation (LEncode L ++ REncode L') (atom (up  F) :: x) ->
      exists x1, Permutation (REncode L') (atom (up  F) :: REncode x1) /\ Permutation (LEncode L++ REncode x1 ) x.
Proof with sauto.
  intros.
  checkPermutationCases H...
  apply NoUinL' in H...
  assert(In (atom (up  F)) (REncode L')).
  rewrite H...
  apply in_map_iff in H0...
  inversion H2...
  apply InPermutation in H3...
  assert(Permutation (REncode L') (REncode (F :: x1))).
  apply Permutation_map...
  assert(Permutation x0 (REncode x1)).
  rewrite H0 in H. 
  simpl in H...
  apply Permutation_cons_inv in H...
   exists x1...
   rewrite <- H2...
 Qed. 
 
 Theorem checkEncodeCasesD L L' x F : 
      Permutation (LEncode L ++ REncode L') (atom (down  F):: x) ->
      exists x1, Permutation (LEncode L) (atom (down  F):: LEncode x1) /\ Permutation (LEncode x1++ REncode L' ) x.
Proof with sauto.
  intros.
  checkPermutationCases H...
  2:{ apply NoDinR' in H... }
  assert(In (atom (down  F)) (LEncode L)).
  rewrite H...
  apply in_map_iff in H0...
  inversion H2...
  apply InPermutation in H3...
  assert(Permutation (LEncode L) (LEncode (F :: x1))).
  apply Permutation_map...
  assert(Permutation x0 (LEncode x1)).
  rewrite H0 in H. 
  simpl in H...
  apply Permutation_cons_inv in H...
   exists x1...
   rewrite <- H2...
 Qed. 
 
 
  Lemma IsOLPositiveLREnc : forall L L',
      isOLFormulaL L -> isOLFormulaL L' -> 
      IsPositiveAtomFormulaL (LEncode L ++ REncode L').
Proof.      
  intros L L' HisL HisL'.
  apply isOLLEncode in HisL.
  apply isOLREncode in HisL'.
  apply Forall_app;auto.
Qed.

Lemma Remove_LEncode F D D' : Remove F D D' -> Remove (atom (down  F)) (LEncode D) (LEncode D').
Proof with sauto.
  intros.
  eapply Remove_Map in H.
  exact H.
Qed.
 
Lemma Remove_REncode F D D' : Remove F D D' -> Remove (atom (up F)) (REncode D) (REncode D').
Proof with sauto.
  intros.
  eapply Remove_Map in H.
  exact H.
Qed.

Lemma onlyAtomsLinear M L F :
     IsPositiveAtomFormulaL M ->
     positiveFormula F ->
     Permutation (F :: L) M -> False.
Proof with sauto;solvePolarity.
  intros HM HF HP.
  rewrite <- HP in HM.
  inversion HM...
  inversion H1...
Qed.

Lemma onlyAtomsLinearB M L F :
     IsPositiveAtomBFormulaL M ->
     positiveFormula F ->
     Permutation (F :: L) M -> exists A, isOLFormula A /\ F= (! ⌈ A ⌉).
Proof with sauto;solvePolarity.
  intros HM HF HP.
  rewrite <- HP in HM.
  inversion HM...
  inversion H1... exists A...
Qed.

Lemma onlyAtomsClassical M F:
     IsPositiveAtomFormulaL M ->
     ~ IsPositiveAtom F ->
     In F M
 -> False.
Proof with sauto;solvePolarity.
  intros HM HF HP.
  apply InPermutation in HP...
  rewrite HP in HM.
  inversion HM...
  inversion H1...
Qed.

Lemma AtomFtoAtomB M:
     IsPositiveAtomFormulaL M -> IsPositiveAtomBFormulaL M.
Proof with sauto.
  intros.
  induction H...
  inversion H...
Qed.
End OLEncodings.
End OLSyntax.

Ltac OLSolve :=   solveFoldFALL1 IsPositiveAtomFormulaL.
Ltac OLSolveB :=   solveFoldFALL1 IsPositiveAtomBFormulaL.
