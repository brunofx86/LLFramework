(** This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination. *)

Require Export LL.Misc.UtilsForall. 
Require Export LL.Framework.SL.MMLL.Specifications.OL2MLL. 
Require Export LL.Framework.SL.MMLL.Tactics. 

Set Implicit Arguments.

Section OLSyntax.
Context `{OL:OLSyntax}.
Context `{SI:SigMMLL}.

Section PositiveAtoms.

Lemma  positiveIsAtom A: IsPositiveAtomFormula A -> IsPositiveAtom A. 
Proof with subst;auto. 
  intros.
  inversion H...  
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

Lemma REncodeBApp  a L1 L2 : REncodeB a (L1++L2) = REncodeB a L1 ++ REncodeB  a L2.
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

Lemma REncodeBPerm a L1 L2 : Permutation L1 L2 -> Permutation (REncodeB a L1) (REncodeB a L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 

Add Parametric Morphism : (LEncode) with
  signature (@Permutation  uexp ) ==> (@Permutation  oo )
      as lencode_mor.
Proof.
  intros. apply LEncodePerm.  auto. 
Qed.

Add Parametric Morphism : (REncode) with
  signature (@Permutation  uexp ) ==> (@Permutation  oo )
      as rencode_mor.
Proof.
  intros. apply REncodePerm.  auto. 
Qed.

Add Parametric Morphism : (REncodeB) with
  signature eq ==>  (@Permutation  uexp ) ==> (@Permutation  oo )
      as rencodeb_mor.
Proof.
  intros. apply REncodeBPerm.  auto. 
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

 Theorem destructREncodeB a C: forall D1 D2, Permutation (REncodeB a C) (D1++D2) ->
       exists X Y, Permutation D1 (REncodeB a X) /\ Permutation D2 (REncodeB a Y) /\ Permutation C (X++Y). 
Proof with sauto.
  induction C;intros...
  simpl in H...
  exists [], []...
  simpl in H.
  checkPermutationCases H.
  - symmetry in H1.
    eapply IHC in H1...
    exists (a0::x0), x1.
    simpl.
    rewrite <- H0...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0, (a0::x1).
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

Theorem destructEncodeB a C1 C1' C2 C2': 
    Permutation (LEncode C1 ++ REncodeB a C2) (C1' ++ C2') -> 
    exists K4_1 K4_2 K4_3 K4_4, 
    Permutation C1' (LEncode K4_1 ++ REncodeB a K4_2) /\ 
    Permutation C2' (LEncode K4_3 ++ REncodeB a K4_4) /\ 
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
       eexists (a0::x0), x1, x2, x3...
       rewrite H...
       rewrite H0...
       rewrite <- app_comm_cons.
       rewrite H2...
    - symmetry in H1.  
       eapply IHC1 in H1...
       eexists x0, x1, (a0::x2), x3...
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

Lemma PositiveAtomREOLFormulaB a L : IsPositiveAtomFormulaL (REncodeB a L) -> isOLFormulaL L.
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
  
Lemma isOLREncodeB : forall a L, isOLFormulaL L -> IsPositiveAtomBFormulaL (REncodeB a L).
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

Lemma PermutationREncodeB : forall L i a x x1,
      Permutation (REncodeB i L) (Bang i (atom (up  a )) :: x) -> Permutation (a :: x1) L -> Permutation x (REncodeB i x1).
Proof with sauto.
    intros.      
    assert(Permutation (Bang i (atom (up  a) )  :: x) (REncodeB i ((a :: x1)))).
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

Lemma InREncodeB : forall i L a,
      In (Bang i (atom (up  a )) ) (REncodeB i L) <-> In a L.
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

Theorem NoDinRB : forall i F L, In (atom (down  F ) ) (REncodeB i L) -> False .
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

Theorem NoUinLB : forall i F L, In (Bang i (atom (up  F )) ) (LEncode L) -> False .
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

Theorem NoDinRB' : forall i F L x, Permutation (REncodeB i L) (atom (down  F ) ::x) -> False .
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

Theorem NoUinLB' : forall i F L x, Permutation (LEncode L) (Bang i (atom (up  F )) ::x)  -> False .
Proof with sauto.  
  intros.
  eapply NoUinLB with (F:=F) (L:=L) (i:=i).
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

Theorem downLeftB : forall L L' F i,
      In (atom (down  F ) ) (LEncode L ++ REncodeB i L') ->
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

Theorem upRightD : forall i L L' F,
    In (Bang i (atom (up  F )) ) (LEncode L ++ REncodeB i L') ->
    In (Bang i (atom (up  F )) ) (REncodeB i L').
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

Theorem OLInPermutationB: forall i L F,
      In (Bang i (atom (up  F ))) (REncodeB i L) ->
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

Lemma MapREncodeEqualB: forall i L L', (REncodeB i L) = (REncodeB i L') -> L = L'.
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

Lemma UpREncodeB i P1 P2 L1 L2 :
    Permutation (Bang i (atom (up  P1 ))::REncodeB i L1) (Bang i (atom (up  P2 )):: REncodeB i L2) ->
    (
      P1 = P2 /\ Permutation (REncodeB i L1) (REncodeB i L2)
    ) \/ (
      exists L2',
        Permutation (REncodeB i L2) (Bang i (atom (up  P1 ))::REncodeB i L2') /\
        Permutation (REncodeB i L1) (Bang i (atom (up  P2 ))::REncodeB i L2')
    ).
Proof with sauto.
  intro HP.
  assert (HI:=in_eq  (Bang i (atom (up  P1 ))) (REncodeB i L1)).
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

Theorem OLInPermutationB': forall i L x F,
     Permutation (REncodeB i L) (Bang i (atom (up F )):: REncodeB i x) ->
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
     assert(Permutation (REncodeB i x) (REncodeB i (a :: x0))).
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

Theorem REncodeBPermutation: forall i L M,
     Permutation (REncodeB i L) (REncodeB i M) ->
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

Lemma onlyAtomsLinearB  M L F :
     IsPositiveAtomBFormulaL M ->
     positiveFormula F ->
     Permutation (F :: L) M -> exists A a, isOLFormula A /\ F= (Bang a (⌈ A ⌉)).
Proof with sauto;solvePolarity.
  intros HM HF HP.
  rewrite <- HP in HM.
  inversion HM...
  inversion H1... exists A, a...
Qed.

Lemma onlyAtomsClassical i (B:list (subexp*oo)) F:
     IsPositiveAtomFormulaL (second B) ->
     ~ IsPositiveAtom F ->
     In (i,F) B
 -> False.
Proof with sauto;solvePolarity.
  intros HM HF HP.
  apply InPermutation in HP...
  assert(Permutation (second B) (second ((i, F) :: x))).
  apply Permutation_map... 
  rewrite H in HM.
  simpl in HM.
  inversion HM...
  inversion H2...
Qed.

Lemma onlyAtomsClassical2 i (B:list (subexp*oo)) B' F:
     IsPositiveAtomFormulaL (second B) ->
     ~ IsPositiveAtom F ->
     Permutation ((i,F)::B') B -> False.
Proof with sauto;solvePolarity.
  intros HM HF HP.
  assert (In (i,F) B). 
   rewrite <- HP... 
eapply onlyAtomsClassical in H...
Qed.

Lemma AtomFtoAtomB M:
     IsPositiveAtomFormulaL M -> IsPositiveAtomBFormulaL M.
Proof with sauto.
  intros.
  induction H...
  inversion H...
Qed.


Lemma CEncodeApp i L1 L2 : CEncode i (L1++L2) = CEncode i L1 ++ CEncode i  L2.
Proof with sauto.
 unfold CEncode;
 rewrite map_app;auto.
Qed.


Lemma CEncodePerm i L1 L2 : Permutation L1 L2 -> Permutation (CEncode i L1) (CEncode i L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 


Lemma setUCEncode i L : u i = true -> SetU (CEncode i L).
Proof with sauto.
 induction L;simpl;intros...
 apply Forall_cons...
 apply IHL...
Qed.
 
 Lemma setK4CEncodeM4 i L : m4 i = true -> SetK4 (CEncode i L).
Proof with sauto.
 induction L;simpl;intros...
 apply Forall_cons...
 apply IHL...
 Qed.
 
 Lemma LtXCEncode i L : LtX i (CEncode i L).
Proof with sauto.
 induction L;simpl;intros...
 apply Forall_cons...
 solveSignature1.
 Qed.
     
Lemma setK4CEncode L : SetK4 (CEncode loc L) -> L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H...
 solveSignature1.
Qed.

 Lemma LtXCEncodeLoc i L : LtX i (CEncode loc L) -> i = loc \/ L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H...
 assert(i=loc).
 apply locAlone'...
 subst...
 Qed.
 
(* Lemma setKCEncode i L : SetK i (CEncode loc L) -> L=[] \/ i = loc.
 *)

Lemma setK4DCEncode i j L : md i = true -> md j = false -> LtX i (CEncode j L) -> L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H1...
 assert(md j = true).
 apply mdClosure with (x:=i)...
 rewrite H2 in H0...
Qed.

Lemma setKDCEncode i j L : md i = true -> md j = false -> LtX i (CEncode j L) -> L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H1...
 assert(md j = true).
 apply mdClosure with (x:=i)...
 rewrite H2 in H0...
Qed.

Lemma setTCEncode i L : mt i = true -> SetT (CEncode i L).
Proof with sauto.
 induction L;simpl;intros...
 apply Forall_cons...
 apply IHL...
Qed.

Lemma secCEncode i L : second (CEncode i L) = L.
Proof with auto.
 induction L...
 simpl.
 rewrite IHL...
Qed. 

 
Lemma LocCEncode L : (CEncode loc (second L)) = Loc L.
Proof with auto.
 induction L...
 simpl.
 rewrite IHL...
Qed.  
 
Lemma getUCEncode i L : u i = true -> getU (CEncode i L) = CEncode i L.
Proof with auto.
intros. 
 induction L;intros...
 simpl. 
 rewrite H...
 rewrite IHL...
Qed.

Lemma getLCEncode i L : u i = true -> getL (CEncode i L) = [].
Proof with auto.
intros. 
 induction L;intros...
 simpl. 
 rewrite H...
Qed.

Lemma getULCEncode  L : getU (CEncode loc L) = CEncode loc L.
Proof with sauto.
  apply getUCEncode...
  apply locu.
Qed.
 
 
 Lemma LocCEncodeLoc  L : Loc (CEncode loc L) = CEncode loc L.
Proof with auto.
 induction L;intros...
 simpl. 
 rewrite IHL...
Qed.  
 Theorem destructCEncode i C: forall D1 D2, Permutation (CEncode i C) (D1++D2) ->
       exists X Y, Permutation D1 (CEncode i X) /\ Permutation D2 (CEncode i Y) /\
       Permutation C (X++Y). 
Proof with sauto.
 induction C;intros...
 simpl in H...
 exists nil...
 exists nil...
 simpl in H.
 checkPermutationCases H.
 - symmetry in H1.
   eapply IHC in H1...
   exists (a::x0).
   exists x1...
   rewrite H...
   rewrite H0...
   rewrite H4...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0.
   exists (a::x1)...
   rewrite H...
   rewrite H3...
   rewrite H4...
Qed.

 Theorem destructEncode2 i j C1 C1' C2 C2': 
    Permutation (CEncode i C1 ++ CEncode j C2) (C1' ++ C2') -> 
    exists K4_1 K4_2 K4_3 K4_4, 
    Permutation C1' (CEncode i K4_1 ++ CEncode j K4_2) /\ 
    Permutation C2' (CEncode i K4_3 ++ CEncode j K4_4) /\ 
    Permutation C1 (K4_1 ++ K4_3) /\ 
    Permutation C2 (K4_2 ++ K4_4). 
  Proof with sauto.
    intros.
    revert dependent C1'.
    revert dependent C2.
    revert dependent C2'.
    induction C1;intros...
    * simpl in *... 
      apply destructCEncode in H...
      eexists []. 
      eexists x. 
      eexists []. 
      eexists x0.
      split;auto...
    *
      simpl in H.
      checkPermutationCases H.
      - symmetry in H1.  
         eapply IHC1 in H1...
         eexists (a::x0).
         eexists x1.
         eexists x2.
         eexists x3.
         split;auto...
         rewrite H.
         rewrite H0...
         rewrite <- app_comm_cons.
         rewrite H2...
      - symmetry in H1.  
         eapply IHC1 in H1...
         eexists x0.
         eexists x1.
         eexists (a::x2).
         eexists x3.
         split;auto...
         rewrite H.
         simpl.
         rewrite H3...
         rewrite H2...
 Qed.          
  
Lemma Loc_no4  X : forall j L1 L2 ,  SetK4 X ->
 Permutation (CEncode j L1 ++ CEncode loc L2) X ->
 Permutation (CEncode j L1) X /\ L2 = [].
 Proof with sauto.
 induction X;intros...
 -
 rewrite H0...
 -
 apply map_eq_nil in H1...
 -
 checkPermutationCases H0.
 + 
  rewrite Permutation_cons_append in H0.
  apply destructCEncode in H0...
  apply CEncodePerm with (i:=j) in H5.
  rewrite H5...
  rewrite CEncodeApp...
  rewrite H4.
  rewrite <- Permutation_cons_append...
  apply perm_skip...
  eapply IHX with (L2:=L2)...
  solveSE.
  rewrite <- H1...
 + 
   
  rewrite Permutation_cons_append in H0.
  apply destructCEncode in H0...
  apply map_eq_cons in H4...
  inversion H...
  solveSignature1.
 - checkPermutationCases H0.
 + 
  rewrite Permutation_cons_append in H0.
  apply destructCEncode in H0...
  eapply IHX with (L1:=x0) (j:=j)...
  solveSE.
  rewrite <- H1...
 +  
  rewrite Permutation_cons_append in H0.
  apply destructCEncode in H0...
  apply map_eq_cons in H4...
  inversion H...
  solveSignature1.   
  Qed.
  
  Lemma SetK4_Loc X : forall Y L, SetK4 X -> Permutation (CEncode loc L) (X ++ Y) -> X = [].
Proof with sauto.
 induction X;simpl;intros...
 rewrite Permutation_cons_append in H0.
 apply destructCEncode in H0...
 apply map_eq_cons in H3...
 inversion H...
 solveSignature1.
 Qed.

End OLEncodings.
End OLSyntax.

Ltac OLSolve :=   solveFoldFALL1 IsPositiveAtomFormulaL.
Ltac OLSolveB :=   solveFoldFALL1 IsPositiveAtomBFormulaL.
