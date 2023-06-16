(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export LL.Misc.Hybrid.
Require Export LL.Framework.SL.MMLL.Tactics.
Require Import Lia.
Require Import LL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export LL.Framework.SL.MMLL.InvPositivePhase.
Require Export LL.Framework.SL.MMLL.Reasoning.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section CutElimination.
Context `{OLS: OLSig}.
Context `{SI : SigMMLL}.

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (MLLN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (MLLS theory B L X) (at level 80).
 
Lemma unformUnb B C X Y Z : 
    SetU B -> SetL C -> SetU X -> SetL Y -> SetL Z -> 
    Permutation (B ++ C) (X ++ Y ++ Z) -> Permutation B X /\ Permutation C (Y++Z).
Proof with sauto.
  revert C X Y Z.
  induction B;intros. 
  - destruct X...
    +  rewrite H4 in H0.
        rewrite <- app_comm_cons in H0. 
        inversion H1. inversion H0...
    +  rewrite H4 in H0.
        rewrite <- app_comm_cons in H0. 
        inversion H1. inversion H0...
  - rewrite <- app_comm_cons in H4. 
    checkPermutationCases H4.
    rewrite H4. apply perm_skip.
    rewrite H4 in H1. 
    inversion H...
    inversion H1...
    pose proof (IHB C x Y Z H9 H0 H11 H2 H3 (symmetry H6))...
    rewrite H4 in H1. 
    inversion H...
    inversion H1...
    pose proof (IHB C x Y Z H9 H0 H11 H2 H3 (symmetry H6))...
    inversion H... 
    checkPermutationCases H4.
    rewrite H4 in H2. inversion H2...
    rewrite H4 in H3. inversion H3...
    inversion H... 
    checkPermutationCases H4.
    rewrite H4 in H2. inversion H2...
    rewrite H4 in H3. inversion H3...
Qed.

Lemma AbsorptionInC
     : forall (th : oo -> Prop) (i : subexp)
         (Gamma : list (subexp * oo)) 
         (Delta : list oo) (F : oo) (X : Arrow),
       u i = true ->
       mt i = true -> In (i,F) Gamma -> 
       MLLS th Gamma (F :: Delta) X ->
       MLLS th Gamma Delta X.
Proof with sauto.
  intros.
  apply InPermutation in H1...
  rewrite H1. 
 apply AbsorptionC'...
  LLExact H2.
Qed.


Lemma contractionK4Gen i CC D LC CC' X:
       i <> loc ->
       SetU CC' -> 
       tri_bangK4' theory (CC'++CC'++CC) i D LC X ->
       tri_bangK4' theory (CC'++CC) i D LC X.
Proof with sauto.
     revert CC.
     induction CC';intros...
     rewrite <- app_comm_cons.
    eapply contractionK4 with (F:=a)...
    inversion H0...
    LLPerm (CC'++(a::a::CC)).
    eapply IHCC'...
    inversion H0...
    LLPerm ((a :: CC') ++ (a :: CC') ++ CC)...
Qed.
  
Lemma LWeak B C L X: (exists D, SetU D /\ Permutation B (C++D)) -> 
MLLS theory C L X -> MLLS theory B L X. 
 Proof with sauto.
  intros...
  rewrite H2. apply weakeningGen_rev...
Qed.

Lemma LWeakN n B C L X: (exists D, SetU D /\ Permutation B (C++D)) -> 
MLLN theory n C L X -> MLLN theory n B L X. 
 Proof with sauto.
  intros...
  rewrite H2. apply weakeningGenN_rev...
Qed.


Ltac LLExactW H:=
  let G:= type of H in
  match G with
  | (MLLS ?T ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- MLLS ?T ?Gamma' ?Delta' ?X ] =>
      apply @exchangeLC with (LC:= Delta);[ try perm |
      apply  LWeak with (C:= Gamma);auto]
    end
  | (MLLN ?T ?n ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- MLLN ?T ?n ?Gamma' ?Delta' ?X ] =>
      apply @exchangeLCN with (LC:= Delta);[ try perm |
      apply  LWeakN with (C:= Gamma);auto]
    end
  end;auto.


Lemma CutK4BaseInit n C P a : a <> loc -> SetK4 C -> LtX a C -> n >= length C + 1 -> 
        n - length C - 1 |--- PlusT C; []; (UP [P]) ->
        S n |--- PlusT C; []; (DW (Bang (plust a)  P)).
Proof with sauto.
 intros. 
  createWorld.
  apply plust_loc_diff...
  eapply @GenK4Rel with (C4:=PlusT C) (CK:=[]) (CN:=[])...
  apply plust_loc_diff...
  apply SetK4PlusT...
  apply LtXPlusT...
  autounfold.
  rewrite map_length...
   simpl...
  rewrite PlusT_fixpoint...
 refine (HeightGeq H3 _). 
  autounfold.
  rewrite map_length...
Qed.
             
(* Hypothesis TheoryIsFormula: forall P, theory P -> isFormula P.   *)

Definition cut1 i j B C D M N L1 L2 cF:=   
           i |---  B++C; cF::M; (UP L1) -> j |--- B++D; N; (UP (dual cF::L2)) -> |-- B++C++D; M ++ N; (UP (L1++L2)). 

 Definition cut2 i j B C D M N L cF:=  
           i |---  B++C; M; (UP (cF::L)) -> j |--- B++D; N; (DW (dual cF)) -> |-- B++C++D; M ++ N; (UP L).

 Definition cut3 i j A P B C D M cF :=  forall a, S (complexity A) = complexity cF ->
           i |---  (a,A)::B++C; M; (DW P) -> j |--- B++D; []; (DW (Bang a (dual A))) -> |-- B++C++D; M; (UP [P]).

 Definition cut4 i j A B C D M L cF :=  forall a, S (complexity A) = complexity cF ->
           i |---  (a,A)::B++C; M; (UP L) -> j |--- B++D; []; (DW (Bang a (dual A))) -> |-- B++C++D; M; (UP L).

  Hypothesis WellFormed : forall L, isFormulaL L. 

   Definition CutW (w: nat) :=  
    forall i j A B C D cF P M N L L1 L2, 
    complexity cF < w ->
    SetU B -> SetL C -> SetL D -> 
    cut1 i j B C D M N L1 L2 cF /\ cut2 i j B C D M N L cF /\ cut3 i j A P B C D M cF /\ cut4 i j A B C D M L cF .

  Definition CutH (w h: nat) :=  
    forall i j A B C D cF P M N L L1 L2, 
    i + j < h ->
    complexity cF = w ->
    SetU B -> SetL C -> SetL D -> 
    cut1 i j B C D M N L1 L2  cF /\ cut2 i j B C D M N L cF /\cut3 i j A P B C D M cF /\ cut4 i j A B C D M L cF .

Ltac applyCutH := 
  match goal with
  | [ H: CutH _ _ |- cut1 _ _ _ _ _ _ _ _ _ _ ] => eapply H
  | [ H: CutH _ _ |- cut2 _ _ _ _ _ _ _ _ _ ] => eapply H
  | [ H: CutH _ _ |- cut3 _ _ _ _ _ _ _ _ _ ] => eapply H
  | [ H: CutH _ _ |- cut4 _ _ _ _ _ _ _ _ _ ] => eapply H  
| _ => idtac end;sauto.
  

Ltac applyCutW := 
  match goal with
  | [ H: CutW _ |- cut1 _ _ _ _ _ _ _ _ _ _ ] => eapply H
  | [ H: CutW _ |- cut2 _ _ _ _ _ _ _ _ _ ] => eapply H
  | [ H: CutW _ |- cut3 _ _ _ _ _ _ _ _ _ ] => eapply H
  | [ H: CutW _ |- cut4 _ _ _ _ _ _ _ _ _ ] => eapply H  
  | _ => idtac end;sauto.

Ltac cut1H P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   |  MLLN ?th ?h1 (?B++?C) (?FC::?M) (UP ?L1) => 
          match tP2 with 
          |  MLLN ?th ?h2 (?B++?D) ?N (UP (dual ?FC::?L2)) =>  
                      assert(H': cut1 h1 h2 B C D M N L1 L2 FC);applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut2H P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   |  MLLN ?th ?h1 (?B++?C) ?M (UP (?CF::?L)) => 
          match tP2 with 
          |  MLLN ?th ?h2 (?B++?D) ?N (DW (dual ?FC)) =>  
                      assert(H': cut2 h1 h2 B C D M N L FC);applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut2W P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   |  MLLN ?th ?h1 (?B++?C) ?M (UP (?CF::?L)) => 
          match tP2 with 
          |  MLLN ?th ?h2 (?B++?D) ?N (DW (dual ?FC)) =>  
                      assert(H': cut2 h1 h2 B C D M N L FC);applyCutW
           | _ => idtac "type of " P2 " is " tP2 end
end.


Theorem Cut1  a b P  L1 L2 M N B C D : 
 CutH (complexity P) (a+b) -> 
SetU B -> SetL C -> SetL D ->
  a |--- B++C; P::M; (UP L1) ->
  b |--- B++D; N; (UP (dual P :: L2)) ->
  |-- B++C++D; M ++ N; (UP (L1++L2)).
Proof with sauto;try solveLL. 
 intro CH.
 intros stB stC stD. 
 intros Ha Hb.
 inversion Ha...
 * rewrite <- app_comm_cons...
 * rewrite <- app_comm_cons...
    cut1H H3 Hb.
 * rewrite <- app_comm_cons...
    cut1H H3 Hb.
 * rewrite <- app_comm_cons...
    cut1H H0 Hb.
    cut1H H4 Hb.
 * rewrite <- app_comm_cons...
   destruct (uDec i).
   - apply weakeningN with (F:=(i,F)) in Hb. 
      rewrite app_comm_cons in Hb, H3.
      cut1H H3 Hb. simpl...
   - rewrite Permutation_middle in H3.
     cut1H H3 Hb.
     LLPerm (B++((i,F)::C)++D)...
 * rewrite <- app_comm_cons...
    rewrite perm_swap in H4.
    cut1H H4 Hb.
 * checkPermutationCases H1.
    rewrite H3 in H5.
    rewrite (dualInvolutive P) in H5.
    cut2H Hb H5.
    LLPerm (B++D++C).
    LLPerm (N++M).     
    apply OLCut... 
    rewrite H2 in H5. 
    rewrite H1. 
    inversion H5...
    { enough(C= [])...
      simpl in Hb. inversion Hb... HProof.
      assert(SetU C). 
      apply Forall_app in H6...
      refine(SETXempty C H stC). }
    { pose proof (unformUnb stB stC H6 H7 H8 H4)...
       checkPermutationCases H3.
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B0++C0; P::F0::x0; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H3...
              rewrite <- H12, H11.
              LLPerm(B++(C0++D)++D0).
              LLPerm(F0 ⊗ G :: (x0 ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensor...
              apply Forall_app...
              cut1H  H14 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 F0 (P::x0). LLExact H9. 
              rewrite H10...
              apply unRelease. rewrite H10. HProof. }
           { inversion H9;solvePolarity... 
              rewrite <- H12, H11.
              LLPerm(B++(C0++D)++D0).
              LLPerm(F0 ⊗ G :: (x0 ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensor...
              apply Forall_app...
              rewrite H3 in H19.
              cut1H  H19 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
               apply OLCut... rewrite H10...
               apply unRelease. rewrite H10. HProof. }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B0++D0; P::G::x0; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H3...
              rewrite <- H12, H11.
              LLPerm(B++C0++(D0++D)).
              LLPerm(F0 ⊗ G :: M0++(x0 ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensor...
              apply Forall_app...
              apply unRelease. rewrite H10. HProof.
              cut1H  H14 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 G (P::x0). LLExact H13. 
              rewrite H10...  }
           { inversion H13;solvePolarity... 
              rewrite <- H12, H11.
              LLPerm(B++C0++(D0++D)).
              LLPerm(F0 ⊗ G :: M0++(x0 ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensor...
              apply Forall_app...
               apply unRelease. rewrite H10. HProof.
              rewrite H3 in H19.
              cut1H  H19 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...
               apply OLCut... rewrite H10...
               } }
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B++C; P::F0::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- app_comm_cons.
              eapply InvPlus...
              cut1H  H3 Hb.
              apply UpExtension'...  }
           { inversion H7;solvePolarity... 
              rewrite <- app_comm_cons.
              eapply InvPlus...
              cut1H  H10 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...  }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B++C; P::G::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- app_comm_cons.
              eapply InvPlusComm...
              cut1H  H3 Hb.
              apply UpExtension'...  }
           { inversion H7;solvePolarity... 
              rewrite <- app_comm_cons.
              eapply InvPlusComm...
              cut1H  H10 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...  }
       -  apply posNotNeg in H0...
       -  destruct(posOrNeg (FX t)).
           { assert(S n0 |--- B++C; P::(FX t)::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- app_comm_cons.
              eapply InvEx with (t:=t)...
              cut1H  H6 Hb.
              apply UpExtension'...  }
           { inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
              rewrite <- app_comm_cons.
              eapply InvEx with (t:=t)...
              cut1H  H12 Hb. 
              eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...  }
 * apply in_app_or in H3... 
    2:{ apply InPermutation in H... rewrite H in stC. inversion stC... }
   destruct(posOrNeg F).
    2:{ inversion H7;solvePolarity...
          cut1H H10 Hb.
          eapply AbsorptionClassic' with (i:=i) (F:=F)...
         eapply EquivUpArrow2 with (L:=[F] ++ L2)... }
    eapply AbsorptionInC with (i:=i) (F:=F)...
    inversion H7...
    { enough(C= [])...
      simpl in Hb. inversion Hb... HProof.
      assert(SetU C). 
      apply Forall_app in H8...
      refine(SETXempty C H4 stC). }
    { pose proof (unformUnb stB stC H8 H9 H10 H6)...
       checkPermutationCases H5.
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B0++C0; P::F0::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H5...
              rewrite <- H14, H13.
              LLPerm(B++(C0++D)++D0).
              LLPerm(F0 ⊗ G :: (x ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensor...
              apply Forall_app...
              cut1H  H16 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 F0 (P::x). LLExact H11. 
              rewrite H12...
              apply unRelease. rewrite H12. HProof. }
           { inversion H11;solvePolarity... 
              rewrite <- H14, H13.
              LLPerm(B++(C0++D)++D0).
              LLPerm(F0 ⊗ G :: (x ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensor...
              apply Forall_app...
              rewrite H5 in H21.
              cut1H  H21 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
               apply OLCut... rewrite H12...
               apply unRelease. rewrite H12. HProof. }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B0++D0; P::G::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H5...
              rewrite <- H14, H13.
              LLPerm(B++C0++(D0++D)).
              LLPerm(F0 ⊗ G :: M0++(x ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensor...
              apply Forall_app...
              apply unRelease. rewrite H12. HProof.
              cut1H  H16 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 G (P::x). LLExact H15. 
              rewrite H12...  }
           { inversion H15;solvePolarity... 
              rewrite <- H14, H13.
              LLPerm(B++C0++(D0++D)).
              LLPerm(F0 ⊗ G :: M0++(x ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensor...
              apply Forall_app...
               apply unRelease. rewrite H12. HProof.
              rewrite H5 in H21.
              cut1H  H21 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...
               apply OLCut... rewrite H12...
               } }
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B++C; P::F0::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              eapply InvPlus...
              cut1H  H5 Hb.
              apply UpExtension'...  }
           { inversion H9;solvePolarity... 
              eapply InvPlus...
              cut1H  H12 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...  }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B++C; P::G::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              eapply InvPlusComm...
              cut1H  H5 Hb.
              apply UpExtension'...  }
           { inversion H9;solvePolarity... 
              eapply InvPlusComm...
              cut1H  H12 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...  }
       -  apply posNotNeg in H3...
       -  destruct(posOrNeg (FX t)).
           { assert(S n0 |--- B++C; P::(FX t)::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              eapply InvEx with (t:=t)...
              cut1H  H8 Hb.
              apply UpExtension'...  }
           { inversion H11;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
              eapply InvEx with (t:=t)...
              cut1H  H14 Hb. 
              eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...  }
 * checkPermutationCases H3. 
    rewrite H3 in stB. inversion stB...
   destruct(posOrNeg F).
    2:{ inversion H7;solvePolarity...
          rewrite <- H4 in H11. cut1H H11 Hb.
          rewrite H3 in stC. inversion stC... 
          eapply AbsorptionLinear with (i:=i) (F:=F) (B':=B++x++D)...
         rewrite H3...
         eapply EquivUpArrow2 with (L:=[F] ++ L2)... }
    rewrite H3.
    LLPerm ((i, F) :: B ++ x ++ D).
    eapply AbsorptionL'... 
    assert(SetL x).
    rewrite H3 in stC. inversion stC...
      inversion H7...
    { enough(x= [])...
      simpl in Hb. inversion Hb... HProof.
      assert(SetU x).
      rewrite <- H4 in H10.
      apply Forall_app in H10...
      refine(SETXempty x H6 H5). }
    { rewrite <- H4 in H9. 
       pose proof (unformUnb stB H5 H10 H11 H12 H9)...
       checkPermutationCases H8.
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B0++C0; P::F0::x0; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H8...
              rewrite <- H16, H15.
              LLPerm(B++(C0++D)++D0).
              LLPerm(F0 ⊗ G :: (x0 ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensor...
              apply Forall_app...
              cut1H  H18 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 F0 (P::x0). LLExact H13. 
              rewrite H14...
              apply unRelease. rewrite H14. HProof. }
           { inversion H13;solvePolarity... 
              rewrite <- H16, H15.
              LLPerm(B++(C0++D)++D0).
              LLPerm(F0 ⊗ G :: (x0 ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensor...
              apply Forall_app...
              rewrite H8 in H23.
              cut1H  H23 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
               apply OLCut... rewrite H14...
               apply unRelease. rewrite H14. HProof. }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B0++D0; P::G::x0; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H8...
              rewrite <- H16, H15.
              LLPerm(B++C0++(D0++D)).
              LLPerm(F0 ⊗ G :: M0++(x0 ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensor...
              apply Forall_app...
              apply unRelease. rewrite H14. HProof.
              cut1H  H18 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 G (P::x0). LLExact H17. 
              rewrite H14...  }
           { inversion H17;solvePolarity... 
              rewrite <- H16, H15.
              LLPerm(B++C0++(D0++D)).
              LLPerm(F0 ⊗ G :: M0++(x0 ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensor...
              apply Forall_app...
               apply unRelease. rewrite H14. HProof.
              rewrite H8 in H23.
              cut1H  H23 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...
               apply OLCut... rewrite H14...
               } }
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B++x; P::F0::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. rewrite H4... 
              eapply InvPlus...
              cut1H  H8 Hb.
              apply UpExtension'...  }
           { inversion H11;solvePolarity... 
              eapply InvPlus...
              rewrite <- H4 in H14... 
              cut1H  H14 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...  }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B++x; P::G::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. rewrite H4... 
              eapply InvPlusComm...
              cut1H  H8 Hb.
              apply UpExtension'...  }
           { inversion H11;solvePolarity... 
              eapply InvPlusComm...
              rewrite <- H4 in H14... 
              cut1H  H14 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...  }
       -  apply posNotNeg in H...
       -  destruct(posOrNeg (FX t)).
           { assert(S n0 |--- B++x; P::(FX t)::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. rewrite H4... 
              eapply InvEx with (t:=t)...
              cut1H  H10 Hb.
              apply UpExtension'...  }
           { inversion H13;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
              eapply InvEx with (t:=t)...
              rewrite <- H4 in H16... 
              cut1H  H16 Hb. 
              eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...  }
 * destruct(posOrNeg F).
    2:{  destruct (negAtomDec F). 
          assert(False). 
          inversion H2;solvePolarity... 
         contradiction.
         inversion H5;solvePolarity...
         cut1H H9 Hb. apply @AbsorptionTheory with (F:=F)...
        eapply EquivUpArrow2 with (L:=[F] ++ L2)... }
    inversion H5...
    { enough(C= [])...
      simpl in Hb. inversion Hb...
      apply AbsorptionPerp' with (A:=A)...
      apply UpExtension'...
      HProof.
      assert(SetU C). 
      apply Forall_app in H6...
      refine(SETXempty C H2 stC). }
    { pose proof (unformUnb stB stC H6 H7 H8 H4)...
       checkPermutationCases H3.
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B0++C0; P::F0::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H3...
              rewrite <- H12, H11.
              LLPerm(B++(C0++D)++D0).
              LLPerm((x ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensorT with (F:=F0) (G:=G)...
              apply Forall_app...
              cut1H  H14 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 F0 (P::x). LLExact H9. 
              rewrite H10...
              apply unRelease. rewrite H10. HProof. }
           { inversion H9;solvePolarity... 
              rewrite <- H12, H11.
              LLPerm(B++(C0++D)++D0).
              LLPerm((x ++ N) ++ N0).
              rewrite <- (app_nil_r L2).
              eapply InvTensorT with (F:=F0) (G:=G)...
              apply Forall_app...
              rewrite H3 in H19.
              cut1H  H19 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
               apply OLCut... rewrite H10...
               apply unRelease. rewrite H10. HProof. }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B0++D0; P::G::x; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              rewrite <- H3...
              rewrite <- H12, H11.
              LLPerm(B++C0++(D0++D)).
              LLPerm(M0++(x ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensorT with (F:=F0) (G:=G)...
              apply Forall_app...
              apply unRelease. rewrite H10. HProof.
              cut1H  H14 Hb.
              apply UpExtension'... apply OLCut...
              LLfocus1 G (P::x). LLExact H13. 
              rewrite H10...  }
           { inversion H13;solvePolarity... 
              rewrite <- H12, H11.
              LLPerm(B++C0++(D0++D)).
              LLPerm(M0++(x ++ N)).
              rewrite <- (app_nil_l L2).
              eapply InvTensorT with (F:=F0) (G:=G)...
              apply Forall_app...
               apply unRelease. rewrite H10. HProof.
              rewrite H3 in H19.
              cut1H  H19 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...
               apply OLCut... rewrite H10...
               } }
       -  destruct(posOrNeg F0).
           { assert(S n0 |--- B++C; P::F0::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              eapply InvPlusT with (F:=F0) (G:=G)...
              cut1H  H3 Hb.
              apply UpExtension'...  }
           { inversion H7;solvePolarity... 
              eapply InvPlusT with (F:=F0) (G:=G)...
              cut1H  H10 Hb. 
              eapply EquivUpArrow2 with (L:=[F0] ++ L2)...  }
       -  destruct(posOrNeg G).
           { assert(S n0 |--- B++C; P::G::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              eapply InvPlusTComm with (F:=F0) (G:=G)...
              cut1H  H3 Hb.
              apply UpExtension'...  }
           { inversion H7;solvePolarity... 
              eapply InvPlusTComm with (F:=F0) (G:=G)...
              cut1H  H10 Hb. 
              eapply EquivUpArrow2 with (L:=[G] ++ L2)...  }
       -  apply posNotNeg in H...
       -  destruct(posOrNeg (FX t)).
           { assert(S n0 |--- B++C; P::(FX t)::M; (UP [])).
              rewrite perm_swap. 
              LLfocus1. 
              eapply InvExT with (FX:=FX) (t:=t)...
              cut1H  H6 Hb.
              apply UpExtension'...  }
           { inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
              eapply InvExT with (FX:=FX) (t:=t)...
              cut1H  H12 Hb. 
              eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...  }
  * rewrite <- app_comm_cons...
     pose proof (H4 x properX).
    cut1H H Hb. 
  Qed.         
   
 Ltac cut3H P1 P2:=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   |  MLLN ?th ?h1 ((?a,?A)::?B++?C) ?M (DW ?P) => 
          match tP2 with 
          |  MLLN ?th ?h2 (?B++?D) [] (DW (Bang ?a (dual ?A))) =>  
                      assert(H': cut3 h1 h2 A P B C D M (Quest a A));applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.


Ltac cut4H P1 P2:=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   |  MLLN ?th ?h1 ((?a,?A)::?B++?C) ?M (UP ?L) => 
          match tP2 with 
          |  MLLN ?th ?h2 (?B++?D) [] (DW (Bang ?a (dual ?A))) =>  
                      assert(H': cut4 h1 h2 A B C D M L (Quest a A));applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.

 Theorem Cut2 a b P L M N B C D : 
  CutH (complexity P) (a+b) -> CutW (complexity P) -> 
 SetU B -> SetL C -> SetL D ->
  a |--- B++C; M; (UP (P::L)) ->
  b |--- B++D; N; (DW (dual P)) ->
  |-- B++C++D; M ++ N; (UP L).
Proof with sauto;try solveLL.   
 intros CH CW.
 intros stB stC stD.
 intros Ha Hb.
 inversion Ha;subst. 
 * inversion Hb...
   CleanContext.
 * inversion Hb; CleanContext...
   enough (D=[])... HProof. 
   apply Forall_app in H...
   refine(SETXempty D H1 stD).
 * inversion Hb; CleanContext...
    pose proof (unformUnb stB stD H4 H5 H6 H2)...
   cut2W H3 H10. simpl...
   assert(|-- B0 ++  C ++ C0; M ++ M0; (UP (G :: L))).
   apply OLCut... rewrite <-H0...
    apply MLLStoSeqN in H...
   cut2W H H11. simpl...
   apply Forall_app...
   rewrite H0, H7, H1.
   LLPerm((M ++ M0) ++ N0). 
   LLPerm(B0++(C ++ C0)++D0)...
 * inversion Hb; CleanContext...
    cut2W H4 H3. simpl...
    cut2W H5 H3. simpl...
 * assert(N=[]).
   inversion Hb... inversion H0.
   subst. simpl in Hb.
   cut4H H3 Hb. 
   eapply OLCut with (a:=i)... 
 * apply posLDestruct in H4...
   apply posDualNeg in H.
     inversion Hb;subst; try match goal with
       [ H: _= dual ?C , H2: negFormula (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
    cut1H H5 H6.
   rewrite <- (app_nil_r L).
    apply OLCut...
   inversion H...
   simpl in Hb.
   inversion Hb...
   enough (D=[])... inversion Ha... HProof.
   apply Forall_app in H4...
   refine (SETXempty D H1 stD).
  checkPermutationCases H7.
   eapply AbsorptionInC with (i:=i) (F:=atom A)...
   rewrite H3 in stB. inversion stB...
   rewrite H3... rewrite <- app_comm_cons...
     enough (D=[])... HProof.
   rewrite <- H4 in H1.
   apply Forall_app in H1...
   refine (SETXempty D H6 stD).
   rewrite H3.
   LLPerm( (i, atom A) :: B++C++x).
   apply AbsorptionL'...
     enough (x=[])... HProof.
    rewrite H3 in stD. inversion stD...
   rewrite <- H4 in H1.
   apply Forall_app in H1...
   refine (SETXempty x H6 H8).
   inversion H1.
  * inversion Hb;CleanContext...
     pose proof (H5 t H1).
    cut2W H H7. simpl...
    remember (VAR con 0%nat).
    assert(proper e).
    rewrite Heqe.  
    constructor.
    erewrite ComplexityUniformEq with (y:=e)...
Qed. 
     
Ltac cut1W P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   |  MLLN ?th ?h1 (?B++?C) (?FC::?M) (UP ?L1) => 
          match tP2 with 
          |  MLLN ?th ?h2 (?B++?D) ?N (UP (dual ?FC::?L2)) =>  
                      assert(H': cut1 h1 h2 B C D M N L1 L2 FC);applyCutW
           | _ => idtac "type of " P2 " is " tP2 end
end.

Theorem CutK4SubCase a b i q P Q L B C D :  
CutH (complexity P) (S a+b) -> CutW (complexity P) ->   
S (complexity Q) = complexity P -> i <> loc ->
  SetU B ->  SetL C -> SetL D ->
 tri_bangK4 theory a ((q, Q)::B ++ C) i [] [] (UP L) -> 
 b |--- B++D; []; (DW (Bang q (dual Q ))) -> tri_bangK4' theory (B++C++D) i [] [] (UP L).
 Proof with sauto;solveF.

 intros HC WC Hcomp Hd.
 intros stB stC stD. 
 intros Ha Hb. 
  apply InvSubExpPhase in Ha;auto. 
        destruct Ha as [C4 Ha];
        destruct Ha as [CK Ha];
        destruct Ha as [CN Ha].
        CleanContext.
  checkPermutationCases H. 
  - (* P in C4 *)
     inversion Hb...
     { rewrite H in H4...
       assert(False).
       apply locAlone in Hd.
       apply Hd... left. 
       inversion H4...  
       contradiction. }
       assert(lt i q /\ m4 q = true /\ SetK4 x /\ LtX i x).
       { rewrite H in H0, H4. inversion H0; inversion H4...  } 
       CleanContext.
       finishExponential.    
        assert(LtX i CK4).
        { eapply @SetKTrans with (i:=q)... }
  assert(Hd': S n |--- PlusT CK4; []; (DW (Bang (plust q) (Q^)))).
        { apply CutK4BaseInit...  }
      eapply contractionK4Gen...
      LLPerm ((B++C)++(B++D)).
       eapply @GenK4Rel' with (C4:=x++CK4) (CK:=CK) (CN:=CN++CN0)...
       4: rewrite H6, <- H8... 
       1-3: apply Forall_app...
        pose proof(Unb_Lin_Disj' CK4). 
        destruct H19 as [CK4_1 H19].
        destruct H19 as [CK4_2 H19]...
        pose proof(Unb_Lin_Disj' x). 
        destruct H19 as [x_1 H19].
        destruct H19 as [x_2 H19]...
        assert(Hp: cut4 (a - length (C4 ++ CK) - 1) (S n) 
                                    Q 
                                    (PlusT CK4_1++PlusT x_1++Loc (getU CK)) (PlusT x_2) (PlusT CK4_2) 
                                    []  (L ++ second (getL CK)) (Quest q Q)).
         eapply HC...
         apply Forall_app; split; [apply SetUPlusT;auto| ].
         apply Forall_app; split; [apply SetUPlusT;auto| apply SetULoc].
         1-2: apply SetLPlusT... 
         rewrite H24, H27.
         LLPerm ((PlusT CK4_1 ++ PlusT x_1 ++ Loc (getU CK)) ++ (PlusT x_2) ++ (PlusT CK4_2)).
         rewrite !PlusTApp'...
         eapply Hp with (a:=plust q)...
         LLExactW H7.
         exists (PlusT CK4_1)... apply SetUPlusT...
         rewrite H, H27; simpl. rewrite  !PlusTApp'... 
         LLExactW Hd'...
         eexists (PlusT x_1 ++ Loc (getU CK))...
          apply Forall_app; split; [apply SetUPlusT;auto| apply SetULoc].
        rewrite H24;simpl...
        rewrite !PlusTApp'...
  -  checkPermutationCases H. 
      + (* P in CK *)
        inversion Hb... 
          { rewrite H in H5. 
             assert(False).
            apply locAlone in Hd.
            apply Hd... 
            inversion H5... contradiction. }
            
         destruct (uDec q).
          { (* P in Classical CK *)
          apply InvSubExpPhaseU in H14;auto.  
          destruct H14 as [C4' H14].
          destruct H14 as [CK' H14].
          destruct H14 as [CN' H14].
          CleanContext.
          assert(lt i q /\ m4 q = false /\ SetK x0 /\ LtX i x0).
       { rewrite H in H2, H5. inversion H2; inversion H5...  }
          assert(LtX i CK').
        { eapply @SetKTrans with (i:=q)... }
          assert(LtX i C4').
        { eapply @SetKTrans with (i:=q)... }
         assert(SetU D ).
        assert(SetU (C4' ++ CK' ++ CN')).
         apply Forall_app;split;[ |apply Forall_app ]...          
         rewrite <- H6 in H23. apply Forall_app in H23...
         pose proof (SETXempty D H23 stD)...
        pose proof(Unb_Lin_Disj' C4). 
        destruct H14 as [C4_1 H14].
        destruct H14 as [C4_2 H14]...
        apply Permutation_vs_cons_inv' in H... 
         setoid_rewrite getLApp in H7. simpl in H7...
        setoid_rewrite <- getLApp in H7.
       
assert(Hd': S n |--- PlusT C4' ++ Loc CK'; []; (DW (Bang loc (Q^)))).
          { solveLL.  apply Forall_app; split; [apply SetUPlusT;auto| apply SetULoc].
            HProof.  }
        assert(Hp: cut4 (a - S (length (C4 ++ x1++x2)) - 1) (S n) 
                                    Q 
                                    (PlusT C4' ++ PlusT C4_1 ++ Loc CK' ++ Loc (getU (x1++x2))) (PlusT C4_2) [] 
                                    []  (L ++ second (getL (x1++x2))) (Quest q Q)).
         eapply HC...
         apply Forall_app;split;[ apply SetUPlusT;auto|  ].
         apply Forall_app;split;[ apply SetUPlusT;auto|  ].
         apply Forall_app;split; apply SetULoc;auto. 
         apply SetLPlusT;auto.
        eapply contractionK4Gen...
       eapply @GenK4Rel' with (C4:=C4++C4') (CK:=(x1++x2)++CK') (CN:=CN++CN')...
        1-5: apply Forall_app... 1-2: rewrite <-  H29...
         rewrite <- H8, H6, <- H9,<-  H29...
        setoid_rewrite getLApp.    rewrite (SetU_then_empty CK')...
          LLPerm((PlusT C4' ++  PlusT C4_1 ++ Loc CK' ++ Loc (getU (x1++x2))) ++ (PlusT C4_2) ++[]).
         rewrite H31. rewrite !PlusTApp'... rewrite !getUApp'.
        rewrite !locApp'. rewrite (setULocgetU CK')...
        eapply Hp with (a:=loc)...
        assert( a - length (C4 ++ x1 ++ (q, Q) :: x2) - 1 =  a - S (length (C4 ++ x1 ++  x2)) - 1).
       rewrite <- !Permutation_middle.  simpl... 
          rewrite H in H7.
         LLExactW H7.
         exists (PlusT C4'++Loc CK')...
         apply Forall_app;split;[apply SetUPlusT | apply SetULoc];auto.  
          rewrite H31...  rewrite  !PlusTApp', !getUApp'... 
         rewrite !locApp';simpl... LLExactW Hd'...
         eexists (PlusT C4_1 ++ Loc (getU (x1++x2)))...
          apply Forall_app; split; [apply SetUPlusT;auto| apply SetULoc]. }
        { (* P in Linear
 CK *)
          eapply EquivUpArrow with (L':= (Q::(L ++ second (getL x0)))) in H7... 
          2:{ apply getLPerm in H.  
                eapply Permutation_map with (f:=snd) in H...
                rewrite H;simpl... }

         apply InvSubExpPhase in H14;auto.  
          destruct H14 as [C4' H14].
          destruct H14 as [CK' H14].
          destruct H14 as [CN' H14].
          CleanContext. simpl in H19...
   assert(lt i q /\ m4 q = false /\ SetK x0 /\ LtX i x0).
       { rewrite H in H2, H5. inversion H2; inversion H5...  }
          assert(LtX i CK').
        { eapply @SetKTrans with (i:=q)... }
          assert(LtX i C4').
        { eapply @SetKTrans with (i:=q)... }
       
       eapply contractionK4Gen...

      LLPerm ((B++C)++(B++D)).
       eapply @GenK4Rel' with (C4:=C4++C4') (CK:=x0++CK') (CN:=CN++CN')...
       1-5: apply Forall_app... 
        rewrite H6, <- H8, <- H9...

      pose proof(Unb_Lin_Disj' C4). 
        destruct H14 as [C4_1 H14].
        destruct H14 as [C4_2 H14]...
      pose proof(Unb_Lin_Disj' C4'). 
        destruct H14 as [C4'_1 H14].
        destruct H14 as [C4'_2 H14]...

      destruct(posOrNeg Q).
      inversion H7...
       assert(|-- (PlusT C4_1 ++ PlusT C4'_1 ++ Loc (getU CK) ++ Loc (getU CK')) ++ PlusT C4_2; [Q];
                         UP (L ++ second (getL x0))).
       LLExactW H36.
       exists (PlusT C4'_1 ++ Loc (getU CK'))...
       apply Forall_app;split;[apply SetUPlusT | apply SetULoc];auto.  
         rewrite H28.
        rewrite PlusTApp'...
assert(|-- (PlusT C4_1 ++ PlusT C4'_1 ++ Loc (getU CK) ++ Loc (getU CK')) ++ PlusT C4'_2; [ ];
                         UP (Q ^ :: second (getL CK'))).
        apply MLLNtoSeq in H19.
       LLExactW H19.
       exists (PlusT C4_1 ++ Loc (getU CK))...
       apply Forall_app;split;[apply SetUPlusT | apply SetULoc];auto.  
         rewrite H31.
        rewrite PlusTApp'...
        apply MLLStoSeqN in H29, H32...
        cut1W H29 H32.
apply Forall_app;split;[ apply SetUPlusT;auto|  ].
         apply Forall_app;split;[ apply SetUPlusT;auto|  ].
         apply Forall_app;split; apply SetULoc;auto. 
         1-2: apply SetLPlusT;auto.
       pose proof (OLCut H29 H32).
setoid_rewrite getLApp. setoid_rewrite secondApp. rewrite app_assoc.
       LLExactW H33... exists nil...
         rewrite H28, H31, H. simpl.
       rewrite !PlusTApp'... rewrite getUApp'... rewrite locApp'...

      apply negDualPos in H14. 

inversion H19;subst;
               try match goal with 
               [ H1: posFormula (dual ?Q),
                 H2: _ = dual ?Q |- _] => rewrite <- H2 in H1
                end... 
              
       assert(|-- (PlusT C4_1 ++ PlusT C4'_1 ++ Loc (getU CK) ++ Loc (getU CK')) ++ PlusT C4'_2; [dual Q];
                         UP (second (getL CK'))).
       apply MLLNtoSeq in H37. LLExactW H37.
       exists (PlusT C4_1 ++ Loc (getU CK))...
       apply Forall_app;split;[apply SetUPlusT | apply SetULoc];auto.  
         rewrite H31.
        rewrite PlusTApp'...
assert(|-- (PlusT C4_1 ++ PlusT C4'_1 ++ Loc (getU CK) ++ Loc (getU CK')) ++ PlusT C4_2; [ ];
                         UP (Q  :: (L ++ second (getL x0)))).
       LLExactW H7.
       exists (PlusT C4'_1 ++ Loc (getU CK'))...
       apply Forall_app;split;[apply SetUPlusT | apply SetULoc];auto.  
         rewrite H28.
        rewrite PlusTApp'...
        apply MLLStoSeqN in H32, H33...
        rewrite (dualInvolutive Q) in H33.
        cut1W H32 H33. rewrite <- dualComplexity... 
apply Forall_app;split;[ apply SetUPlusT;auto|  ].
         apply Forall_app;split;[ apply SetUPlusT;auto|  ].
         apply Forall_app;split; apply SetULoc;auto. 
         1-2: apply SetLPlusT;auto.
       pose proof (OLCut H32 H33).
eapply EquivUpArrow2 with (L:=(second (getL CK') ++ L ++ second (getL x0)))...
2:{ setoid_rewrite getLApp. setoid_rewrite secondApp...  }
       LLExactW H34... exists nil...
         rewrite H28, H31, H. simpl.
       rewrite !PlusTApp'... rewrite getUApp'... rewrite locApp'...  } 
 + (* P in CN *)
     assert(SetU x0 /\ u q = true ).
       rewrite H in H3. split;solveSE. CleanContext.
      pose proof(BangUnb H11 Hb)...
      assert(SetU D). apply Forall_app in H6... 
      pose proof(SETXempty D H12 stD)...
       
        eapply @GenK4Rel' with (C4:=C4) (CK:=CK) (CN:= x0)...
        rewrite <- H8. rewrite <- H9... HProof.
Qed.
             
Lemma InvBangTN i j B P : mt i = true -> u i = true ->
           j |--- B; []; (DW (Bang i  P)) -> (j-1) |--- B; []; (UP [P]).
  Proof with sauto.
  intros Hm Hu Hj.
  inversion Hj...
  inversion H0.
  eapply InvSubExpPhaseUT in H4;auto. 
  destruct H4 as [C4 H4].
  destruct H4 as [CK H4].
  destruct H4 as [CN H4]...
  rewrite H.
  rewrite app_assoc. 
  apply weakeningGenN_rev;auto.
  rewrite Permutation_app_comm.
  apply ContractionL...
  LLPerm ((C4 ++ Loc CK) ++ CK).
  apply weakeningGenN_rev;auto.
  eapply @HeightGeq with (n:=n - length (C4 ++ CK) - 1)...
 Qed. 

 Lemma InvBangTNLoc i j A B P : mt i = true -> u i = true -> m4 i = true ->
       j |--- (loc,A)::B; []; (DW (Bang i P)) -> 
       (exists C4 CN, Permutation B (C4++CN) /\ (j - length C4 - 2) |--- C4; []; (UP [P]) /\ SetK4 C4 /\ SetT C4 /\ LtX i C4 ).
  Proof with sauto.
  intros HmT Hm4 Hu Hj.
  assert(i <> loc).
  solveSignature1.
  inversion Hj;subst;auto.
  inversion H1. 
  assert(False).
  apply H... sauto.
  eapply InvSubExpPhaseUTK4 in H5;auto. 
  destruct H5 as [C4 H5].
  destruct H5 as [CN H5]...
  checkPermutationCases H0.
  rewrite H0 in H2.
  inversion H2... solveSignature1.
  exists C4.
  exists x.
  split;sauto. 
  eapply @HeightGeq with (n:=n - length C4 - 1)...
  rewrite NatComp...
 Qed. 
 
  Lemma InvBangT i j B P : mt i = true -> u i = true ->
           j |--- B; []; (DW (Bang i P)) -> |-- B; []; (UP [P]).
  Proof with sauto.
  intros Hm Hu Hj.
  apply InvBangTN in Hj...
  apply MLLNtoSeq in Hj...
 Qed. 

Lemma BangPlusT n C P a : a <> loc -> SetK4 C -> LtX a C -> n >= length C + 1 -> 
        n - length C - 1 |--- PlusT C; []; (UP [P]) ->
        S n |--- PlusT C; []; (DW (Bang (plust a) P)).
Proof with sauto.
 intros. 
  createWorld.
  apply plust_loc_diff...
  eapply @GenK4Rel with (C4:=PlusT C) (CK:=[]) (CN:=[])...
  apply plust_loc_diff...
  apply SetK4PlusT...
  apply LtXPlusT...
  autounfold.
  rewrite map_length...
  simpl...
  simplFix...
  autounfold.
  rewrite map_length...
Qed.

Theorem UCutDwC a b q P Q F L B C D :
    CutH (complexity P) (a+b) -> CutW (complexity P) -> 
    S (complexity Q) = complexity P -> u q = true ->
    SetU B -> SetL C -> SetL D ->
    a |--- (q,Q)::B ++ C; L; (DW F) -> 
    b |--- B++D; []; (DW (Bang q (Q ^))) -> 
    |-- B++C++D; L; (UP [F]).
  Proof with sauto;solveF.
  intros HC WC Hh Hc.
   intros stB stC stD. intros Ha Hb. 
   assert(stD': SetU D).
   eapply BangUnb in Hb;auto.
   apply Forall_app in Hb...
    inversion Ha...
    * pose proof(SETXempty D stD' stD)...
      solveLL.  
       inversion H3... 
   * checkPermutationCases H5.
      { assert(stC': SetU C).
         rewrite H3 in H0.
         apply Forall_app in H0...
        pose proof(SETXempty D stD' stD)...
        pose proof(SETXempty C stC' stC)...
        apply InvBangT in Hb... }
     { checkPermutationCases H2. 
        assert(stC': SetU C).
         rewrite H3 in H0. inversion H0...
         rewrite <- H4 in H7.
         apply Forall_app in H7...
        pose proof(SETXempty D stD' stD)...
        pose proof(SETXempty C stC' stC)...
        solveLL. LLfocus1. 
        solveLL. rewrite H2 in stB. inversion stB... 
        assert(stX': SetU x0). 
         rewrite H3 in H0. inversion H0... 
         rewrite <- H4 in H7. apply Forall_app in H7... 
        assert(stX: SetL x0). 
         rewrite H2 in stC. inversion stC...
         pose proof(SETXempty D stD' stD)...
         pose proof(SETXempty x0 stX' stX)... 
         solveLL. LLfocus1. 
        solveLL.  }
     * 
      solveLL. inversion H3...
       rewrite app_assoc. apply Forall_app...
     * assert(SetU ((q, Q) :: B)).
        solveSE.
      pose proof (unformUnb H stC H2 H3 H4 H1)...
      solveLL. 
     LLPermH H9 ((q, Q):: B ++ D0).
     LLPermH H5 ((q, Q):: B ++ C0).
      cut3H H5 Hb.
      cut3H H9 Hb.
      2,3: rewrite <- H7...
        rewrite H0, H8.
      pose proof(SETXempty D stD' stD)...
               rewrite <- (app_nil_r []).
       eapply @InvTensor... 
      LLPerm (B++C0++[]).
      eapply OLCut with (a:=q)...
      LLPerm (B++D0++[]).
      eapply OLCut0 with (a:=q)...
    * cut3H H3 Hb.
         solveLL.
        apply InvPlus...
       eapply OLCut with (a:=q)...
    * cut3H H3 Hb.
         solveLL.
        apply InvPlusComm...
       eapply OLCut with (a:=q)...
    * cut4H H4 Hb.   
       eapply OLCut with (a:=q)...
   *  cut3H H5 Hb.
         solveLL.
        apply InvEx with (t:=t)...
       eapply OLCut with (a:=q)...
   *  cut4H H4 Hb. 
       1-3: exact nil.
       assert(SetU C).
      inversion H0... apply Forall_app in H3...
     pose proof(SETXempty D stD' stD)...
      pose proof(SETXempty C H stC)...
     LLstore. LLfocus1.
     solveLL. LLPerm (B++[]++[]).
       eapply OLCut with (a:=q)...
    * LLstore. LLfocus1. 
       createWorld.
       eapply @CutK4SubCase with (a:=n) (b:=b) (P:=P) (q:=q) (Q:=Q)...
  Qed. 
 
 
Lemma SetULPerm B1 B2 C1 C2: 
  SetU B1 -> SetU B2 -> SetL C1 -> SetL C2 -> Permutation (B1 ++ C1) (B2 ++ C2) -> Permutation B1 B2 /\ Permutation C1 C2.
Proof with sauto.
  revert B2 C1 C2. induction B1;intros. 
 - destruct B2...
    rewrite H3 in H1. rewrite <- app_comm_cons in H1. 
    inversion H1...
    inversion H0...
    rewrite H3 in H1. rewrite <- app_comm_cons in H1. 
    inversion H1...
    inversion H0...
 - destruct B2...
    rewrite <- H3 in H2. rewrite <- app_comm_cons in H2. 
    inversion H2...
    inversion H...
    rewrite <- H3 in H2. rewrite <- app_comm_cons in H2. 
    inversion H2...
    inversion H...
   { checkPermutationCases H3.
     inversion H... inversion H0...
     pose proof (IHB1 B2 C1 C2 H7 H9 H1 H2 H6)...
     checkPermutationCases H3. 
     rewrite H3.
     rewrite perm_swap.
     rewrite H3 in H0. rewrite perm_swap in H0. inversion H0...
    inversion H...
     rewrite <- H6 in H5.
    rewrite app_comm_cons in H5.
     pose proof (IHB1 (t::x0) C1 C2 H11 H9 H1 H2 H5)...
    rewrite  H3 in H2.
    inversion H2... inversion H... }
   { checkPermutationCases H3.
     inversion H... inversion H0...
     pose proof (IHB1 B2 C1 C2 H7 H9 H1 H2 H6)...
     checkPermutationCases H3. 
     rewrite H3 in H0. rewrite perm_swap in H0. inversion H0...
    inversion H...
     rewrite <- H6 in H5.
    rewrite app_comm_cons in H5.
     pose proof (IHB1 (t::x0) C1 C2 H11 H9 H1 H2 H5)...
    rewrite  H3 in H2.
    inversion H2... inversion H... }
Qed.

 Theorem LCutDwC  a b q P Q F L B C D :
      CutH (complexity P) (a+b) -> CutW (complexity P) -> 
    S (complexity Q) = complexity P -> u q = false ->
    SetU B -> SetL C -> SetL D ->
    a |--- (q,Q)::B ++ C; L; (DW F) -> 
    b |--- B++D; []; (DW (Bang q (Q ^))) -> 
    |-- B++C++D; L; (UP [F]).
  Proof with sauto;solveF.
  intros HC WC Hh Hc.
  intros stB stC stD. intros Ha Hb. 
  inversion Ha...
  - inversion H3... 
  - checkPermutationCases H5. 
    2:{ rewrite H3 in H0. inversion H0...  }
    assert(stC': SetU C). rewrite H3 in H0. apply Forall_app in H0... 
     inversion Hb... assert(stD': SetU D). apply Forall_app in H6...
    pose proof(SETXempty D stD' stD)...
    pose proof(SETXempty C stC' stC)... HProof.
    pose proof(SETXempty C stC' stC)... 
    apply InvSubExpPhase in H7;auto.  
     destruct H7 as [C4 H7].
     destruct H7 as [CK H7].
     destruct H7 as [CN H7]...
     CleanContext.
     assert(SetT C4). 
     { eapply (SetTKClosure q C4 H1 H9). } 
     assert(SetT CK).     
     { eapply (SetTKClosure q CK H1 H10). }
     rewrite H.
     rewrite app_assoc.
     apply weakeningGen_rev... 
     rewrite (cxtDestruct CK).
     LLPerm(getU CK ++ getL CK ++ C4).
     apply Loc_Unb'... apply getUtoSetU.
     rewrite cxtDestruct in H11. apply Forall_app in H11...
     eapply AbsorptionLinearSet with (C:=getL CK) (B':=C4 ++  Loc (getU CK) )...
     rewrite cxtDestruct in H11. apply Forall_app in H11...
     rewrite <- (SetTPlusT C4)...
     HProof. 
   - inversion H3...
  -  checkPermutationCases H1.
     rewrite H1 in H2. inversion H2...  
     checkPermutationCases H1;solveLL; rewrite H0;
     apply SetULPerm in H6...    
     2: rewrite H1 in H3; inversion H3;subst; rewrite <- H7;apply Forall_app...
     3: rewrite H1 in H4; inversion H4;subst; rewrite <- H7;apply Forall_app...
     1-2: rewrite <- H8, <- H, <- H7.
     assert(SetL x0). rewrite H1 in H3; inversion H3...
     LLPerm (B0 ++ (x0 ++ D) ++ D0).
     rewrite <- (app_nil_r []).
     apply InvTensor... apply Forall_app... 2: apply unRelease; HProof.
    LLPermH H5 ((q, Q) ::B0++x0). 2: rewrite H1...
    rewrite <- H in Hb.
     cut3H H5 Hb. apply OLCut with (a:=q)...
     assert(SetL x0). rewrite H1 in H4; inversion H4...
     LLPerm (B0 ++ C0++(x0 ++ D)).
     rewrite <- (app_nil_r []).
     apply InvTensor... apply Forall_app... 
     apply unRelease; HProof.
     LLPermH H9 ((q, Q) ::B0++x0). 2: rewrite H1...
    rewrite <- H in Hb.
     cut3H H9 Hb. apply OLCut with (a:=q)...
   - cut3H H3 Hb.
      solveLL. apply InvPlus... apply OLCut with (a:=q)...
   - cut3H H3 Hb.
      solveLL. apply InvPlusComm... apply OLCut with (a:=q)...
   - cut4H H4 Hb.
       apply OLCut with (a:=q)...
   - cut3H H5 Hb.
      solveLL. apply InvEx with (t:=t)... apply OLCut with (a:=q)...
   - inversion H0... 
   - LLstore. LLfocus1. 
       createWorld.
       eapply @CutK4SubCase with (a:=n) (b:=b) (P:=P) (q:=q) (Q:=Q)...
  Qed. 
  
 Theorem Cut3 a b q P Q F L B C D :
   CutH (complexity P) (a+b) -> CutW (complexity P) -> 
    S (complexity Q) = complexity P -> 
    SetU B -> SetL C -> SetL D ->
    a |--- (q,Q)::B ++ C; L; (DW F) -> 
    b |--- B++D; []; (DW (Bang q (Q ^))) -> 
    |-- B++C++D; L; (UP [F]).
  Proof with sauto.
  intros.
  destruct (uDec q).
  -  eapply UCutDwC with (a:=a) (b:=b) (q:=q) (P:=P) (Q:=Q) (B:=B) (C:=C) (D:=D)...
  -  eapply LCutDwC with (a:=a) (b:=b) (q:=q) (P:=P) (Q:=Q) (B:=B) (C:=C) (D:=D)...
   Qed.
 
Lemma splitUnbounds B C D E : 
  SetU E -> SetU B -> SetL C -> Permutation (B ++ C) (D ++ E) -> 
    Permutation B (getU D ++ E) /\ Permutation C (getL D).
Proof with sauto.
   intros.
   rewrite (cxtDestruct D) in H2.
   rewrite Permutation_assoc_comm in H2.
  apply SetULPerm in H2...
   apply Forall_app...
  apply getUtoSetU.
  apply getLtoSetL.
Qed.
 
Theorem Cut4  a b q P Q M L B C D :
   CutH (complexity P) (a+b) -> CutW (complexity P) -> 
    S (complexity Q) = complexity P -> 
    SetU B -> SetL C -> SetL D ->
    a |--- (q,Q)::B ++ C; M; (UP L) -> 
    b |--- B++D; []; (DW (Bang q (Q ^))) -> 
    |-- B++C++D; M; (UP L).
Proof with sauto;try solveLL.  
  intros CH CW compQ.
  intros stB stC stD. 
  intros Ha Hb.
  inversion Ha...  
  - cut4H H3 Hb.
    apply OLCut with (a:=q)...
  - cut4H H3 Hb.
    apply OLCut with (a:=q)...
  - cut4H H0 Hb.
    apply OLCut with (a:=q)...
  - cut4H H4 Hb.
    apply OLCut with (a:=q)...
  - destruct (uDec i).
    { rewrite perm_swap in H3. 
      apply weakeningN with (F:=(i,F)) in Hb...
      rewrite !app_comm_cons in H3, Hb.
     cut4H H3 Hb.
    apply OLCut with (a:=q)... }
    { LLPermH H3 ((q, Q) :: B ++ (i, F) :: C). 
      cut4H H3 Hb.
     LLPerm (B ++ (i, F) ::  C ++ D).
    apply OLCut with (a:=q)... }
  - cut4H H4 Hb.
    apply OLCut with (a:=q)... 
  - cut3H H5 Hb.
    assert(|-- B ++ C ++ D; L'; UP [F]).
    apply OLCut with (a:=q)... 
   inversion H;solvePolarity... rewrite H1 in H8...
  - inversion H3... 
    cut3H H7 Hb.
    assert(|-- B ++ C ++ D; M; UP [F]).
    apply OLCut with (a:=i)...
    assert(stD': SetU D).
    apply BangUnb in Hb... apply Forall_app in Hb...
   
          apply MLLStoSeqN in H...
          apply InvBangT in Hb...
         apply MLLStoSeqN in Hb...

            destruct(posOrNeg F).
            apply posDualNeg in H3...
             apply tri_rel in Hb...
           rewrite(SETXempty D) in H...
           cut2W H Hb. LLPerm(M++[]).
           eapply OLCut0...

             apply tri_rel in H...
           rewrite(SETXempty D) in H...
             rewrite (dualInvolutive F) in H.
           cut2W Hb H. 
                     rewrite <- dualComplexity...
           LLPerm(B++D++C). LLPerm([]++M). 
           eapply OLCut0... 
          
          apply in_app_or in H...
          2:{ apply InPermutation in H4...  rewrite H4 in stC. inversion stC... }
          cut3H H7 Hb.
    eapply @AbsorptionClassic with (i:=i) (F:=F)...
          apply OLCut with (a:=q)...
 - checkPermutationCases H3.
   + rewrite H5 in H7.  clear H5.
       inversion Hb... inversion H3. solveSignature1.
                   apply InvSubExpPhase in H8;auto. 
             destruct H8 as [C4 H8].
             destruct H8 as [CK H8].
             destruct H8 as [CN H8]... 
             assert(SetT C4).
             { eapply (SetTKClosure q C4 H1 H10). }
            assert(SetT CK).
             { eapply (SetTKClosure q CK H1 H11). }
      rewrite app_assoc in H. apply splitUnbounds in H...
          
           assert(Ha': |-- B++ (getL C4 ++ getL CK); [];
      UP ([Q ^])). 
          rewrite H14.  LLPerm (((getU C4++getL C4)++getU CK++getL CK) ++ CN).
        rewrite getUApp... rewrite <- (cxtDestruct C4).
            rewrite <- (SetTPlusT C4)... rewrite app_assoc.
          apply weakeningGen_rev...
eapply @AbsorptionLinearSet with (C:=getL CK) (B':= (PlusT C4 ++ getU CK) )...
            rewrite cxtDestruct in H12. 
           apply Forall_app in H12...
           LLPerm (getU CK++PlusT C4).
           apply ContractionL'...
           apply getUtoSetU.
           rewrite cxtDestruct in H12. 
           apply Forall_app in H12...
          LLPerm ((PlusT C4 ++ Loc (getU CK)) ++ getU CK).
          apply weakeningGen_rev...
           apply getUtoSetU.
          HProof. 
          apply MLLStoSeqN in  Ha'...       
          rewrite (dualInvolutive Q) in H7.
          cut2W Ha' H7. rewrite <- dualComplexity...
          apply Forall_app... 1-2:     apply getLtoSetL.
            rewrite H15.
           LLPerm(B ++ (getL C4 ++getL CK) ++C)...
          rewrite getLApp...
   + checkPermutationCases H3. 
       rewrite H3 in stB. inversion stB... 
       rewrite H4, <- H5 in H7.  clear H4.
       cut3H H7 Hb. rewrite H3 in stC. inversion stC...
          eapply AbsorptionLinear with (i:=i) (F:=F) (B':=B++x0++D)... 
       rewrite H3... eapply OLCut with (a:=q)...
 -  cut3H H5 Hb.  destruct (negAtomDec F).
    2:{  eapply @AbsorptionTheory with (F:=F)... apply OLCut with (a:=q)... }
     inversion H...
     eapply @AbsorptionPerp' with (A:=A). auto. 
     simpl. apply OLCut with (a:=q)... 
  - pose proof (H4 x properX). 
     cut4H H Hb. apply OLCut with (a:=q)...
  -  createWorld i.       
     eapply @CutK4SubCase with (a:=n) (b:=b) (P:=P) (q:=q) (Q:=Q)...
     intro... solveSignature1.
  Qed.
 
  Theorem CutElimination i j A B C D cF P M N L L1 L2:
  SetU B -> SetL C -> SetL D -> 
    cut1 i j B C D M N L1 L2  cF /\ 
    cut2 i j B C D M N L cF /\ 
   cut3 i j A P B C D M cF /\ 
     cut4 i j A B C D M L cF . 
 Proof with sauto.
    assert(exists w, complexity cF = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert i j A B C D cF P M N L L1 L2.
 
  induction w using lt_wf_ind; intros. 

     remember (plus i j) as h.
      revert dependent B.
    revert dependent C.
      revert dependent D.
      revert dependent L.
      revert dependent M.
      revert dependent N.
      revert dependent P.
      revert A L1 L2.
      revert dependent cF.
      revert dependent i.
      revert j.
      induction h using lt_wf_ind; intros.
      assert(CutW (complexity cF)).
   unfold CutW;intros. eapply H with (m:=complexity cF0)... 
   clear H.
 
  assert(CutH (complexity cF) (i+j)).
   unfold CutH;intros. eapply H0 with (m:=i0+j0)... 
     clear H0.
    rename H1 into compC.
        
        split;[intros | 
        split;[intros | 
        split;intros]].
        * unfold cut1. eapply Cut1...
        * unfold cut2. eapply Cut2...
        * unfold cut3; do 2 intro. eapply Cut3 with (P:=cF)...
        * unfold cut4; do 2 intro. eapply Cut4 with (P:=cF)...
Qed.
       
    
End CutElimination.
