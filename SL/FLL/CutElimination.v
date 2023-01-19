(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export LL.Misc.Hybrid.
Require Export LL.SL.FLL.Tactics.
Require Import Lia.
Require Import LL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export LL.SL.FLL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section CutElimination.
  Context `{OLS: OLSig}.
  Variable th : oo -> Prop.
  
  Theorem CutAtom B M N L C:
  seq th B M (UP (atom C::L)) -> seq th B N (DW (perp C))  ->
  seq th B (M++N) (UP L).
  Proof with sauto;solveLL.
  intros Hd1 Hd2.
  inversion Hd2...
  inversion Hd1...
  LLExact H4.
  apply InPermutation in H2...
  rewrite H2.
  LLPerm ([atom C] ++ x).
  apply AbsorptionCSet'.
  simpl... rewrite <- H2.
  inversion Hd1...
  LLExact H5.
  inversion H0.
  Qed.
  
  
    Definition CutW (w: nat) :=  
    forall i j C A P M N L B, 
    complexity C < w ->
      (seqN th i B (C::M) (UP L) -> seqN th j B N (UP [dual C]) -> seq th B (M ++ N) (UP L)) /\
      (seqN th i B M (UP (C :: L)) -> seqN th j B N (DW (dual C)) -> seq th B (M ++ N) (UP L)) /\
       (S (complexity A) = complexity C ->
       seqN th i (A::B) M (DW P) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP [P]))  /\
      (S (complexity A) = complexity C ->
       seqN th i (A::B) M (UP L) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP L)). 
    
  Definition CutH (w h: nat) :=  
    forall i j C A P M N L B, 
    i + j < h ->
    complexity C = w ->
      (seqN th i B (C::M) (UP L) -> seqN th j B N (UP [dual C]) -> seq th B (M ++ N) (UP L)) /\
      (seqN th i B M (UP (C :: L)) -> seqN th j B N (DW (dual C)) -> seq th B (M ++ N) (UP L)) /\
      (S (complexity A) = complexity C ->
       seqN th i (A::B) M (DW P) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP [P]))   /\
      (S (complexity A) = complexity C ->
       seqN th i (A::B) M (UP L) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP L)). 
          
Ltac applyCutH := 
  match goal with
  | [ H: CutH _ _ |- 
         seqN ?th ?x _ _ _ -> 
         seqN ?th ?y _ _ _ -> 
         seq ?th _ _ _ ] => eapply H
  | _ => idtac end;sauto.
  
Ltac applyCutW := 
  match goal with
  | [ H: CutW _ |- 
         seqN ?th ?x _ _ _ -> 
         seqN ?th ?y _ _ _ -> 
         seq ?th _ _ _ ] => eapply H
  | _ => idtac end;sauto.

Ltac cut1H P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 ?B (?FC::?M) (UP ?L) => 
          match tP2 with 
          | seqN ?th ?h2 ?B ?N (UP [dual ?FC]) =>  
                      assert(H': tP1 -> tP2 -> seq th B (M++N) (UP L));applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut2H P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 ?B ?M (UP (?FC::?L)) => 
          match tP2 with 
          | seqN ?th ?h2 ?B ?N (DW (dual ?FC)) =>  
                      assert(H': tP1 -> tP2 -> seq th B (M++N) (UP L));applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut3H P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 (?FC::?B) ?M (DW ?P) => 
          match tP2 with 
          | seqN ?th ?h2 ?B [] (DW (Bang (dual ?FC))) =>  
                      assert(H': tP1 -> tP2 -> seq th B M (UP [P]));applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut4H P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 (?FC::?B) ?M (UP ?L) => 
          match tP2 with 
          | seqN ?th ?h2 ?B [] (DW (Bang (dual ?FC))) =>  
                      assert(H': tP1 -> tP2 -> seq th B M (UP L));applyCutH
           | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.

Ltac cut1W P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 ?B (?FC::?M) (UP ?L) => 
          match tP2 with 
          | seqN ?th ?h2 ?B ?N (UP [dual ?FC]) =>  
                      assert(H': tP1 -> tP2 -> seq th B (M++N) (UP L));applyCutW
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut2W P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 ?B ?M (UP (?FC::?L)) => 
          match tP2 with 
          | seqN ?th ?h2 ?B ?N (DW (dual ?FC)) =>  
                      assert(H': tP1 -> tP2 -> seq th B (M++N) (UP L));applyCutW
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut3W P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 (?FC::?B) ?M (DW ?P) => 
          match tP2 with 
          | seqN ?th ?h2 ?B [] (DW (Bang (dual ?FC))) =>  
                      assert(H': tP1 -> tP2 -> seq th B M (UP [P]));applyCutW
           | _ => idtac "type of " P2 " is " tP2 end
end.

Ltac cut4W P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 (?FC::?B) ?M (UP ?L) => 
          match tP2 with 
          | seqN ?th ?h2 ?B [] (DW (Bang (dual ?FC))) =>  
                      assert(H': tP1 -> tP2 -> seq th B M (UP L));applyCutW
           | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.

Theorem Cut1  a b P L M N B : 
CutH (complexity P) (a+b) -> 
  seqN th a B (P::M) (UP L) ->
  seqN th b B N (UP [P ^]) ->
  seq th B (M ++ N) (UP L ).
Proof with sauto;solveLL.  
 intros CH Ha Hb.
 inversion Ha...
 * cut1H H0 Hb. 
 * cut1H H4 Hb. 
 * cut1H H3 Hb.
 * cut1H H3 Hb. 
 * apply weakeningN with (F:=F) in Hb.
    LLPerm (F::B). 
    cut1H H3 Hb.
 * apply H4 in properX...
    cut1H properX Hb.
 * rewrite perm_swap in H4. cut1H H4 Hb. 
 * checkPermutationCases H1.
    -  rewrite H3 in H5. 
       rewrite (ng_involutive P) in H5...
       LLPerm(N ++ M).
       cut2H Hb H5. 
    - rewrite H2 in H5. clear H2.
       inversion H5...
       + inversion Hb...
           HProof. 
       +  destruct(PositiveOrNegative F0).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                 FLLstore.
                assert( seqN th (S n0) B (P::(F0::x)) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                LFocus F0 (P::x). 
             
 }

             {   inversion H6;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                 cut1H H9 Hb. 
               }
 
  +    destruct(PositiveOrNegative G).   
       {         rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                 FLLstore. 
                assert(seqN th (S n0) B (P::(G::x)) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x ) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                 LFocus G (P::x).  }

             {   inversion H6;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                 cut1H H9 Hb.   
               }
+           checkPermutationCases H2.
    {  
              destruct(PositiveOrNegative F0).
              * (* first *) 
              assert(seqN th (S n0) B (P::(F0::x0)) (UP [])).
              LFocus F0 (P::x0)...
              HProof. 
              rewrite H1.

              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H4.
              LLPerm(G ⊗ F0::N0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
              
              apply unRelease.
              HProof.
              cut1H H6 Hb. 
             * (* second *) 
              
inversion H3;CleanContext...
              rewrite H1.
              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H4.
              LLPerm(G ⊗ F0::N0++(x0++N)).
                rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
                apply unRelease.
              HProof.
                 rewrite H2 in H12.
                 cut1H H12 Hb. }
{ 
              destruct(PositiveOrNegative G).
              * (* first *) 
              assert(seqN th (S n0) B (P::(G::x0)) (UP [])).
              LFocus G (P::x0)...
              rewrite <- H2...
              rewrite H1.
              rewrite <- H4.
              LLPerm(F0⊗ G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
              apply unRelease.
              HProof.
              cut1H H6 Hb. 
            * (* second *) 
              inversion H8;CleanContext...
              rewrite H1.
              rewrite <- H4.
              LLPerm(F0⊗ G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
                apply unRelease.
             HProof.
                 rewrite H2 in H12.
                 cut1H H12 Hb.   }   
               
   +   destruct(PositiveOrNegative (FX t)).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                 FLLstore. 
                 assert( seqN th (S n0) B (P::(FX t::x) ) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((FX t::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                 LFocus (FX t) (P::x).  }
             {   inversion H8;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                 cut1H H11 Hb.  }
       +  apply PositiveNotNegative in H0. contradiction. 
           
*  destruct(PositiveOrNegative F).


- inversion H5...
       +  apply @AbsorptionClassic' with  (F:=perp A)...
          inversion Hb...
          HProof.
  +  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusC with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'...
        assert(seqN th (S n0) B (P::(F0::M) ) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((F0::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               LFocus F0 (P::M). }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusC with (F:=F0) (G:=G) ...
                 cut1H H10 Hb. 
}
  +  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusCComm with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'...
        assert(seqN th (S n0) B (P::(G::M) ) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((G::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               LFocus G (P::M).  }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusCComm with (F:=F0) (G:=G)...
                 cut1H H10 Hb.  }

      + checkPermutationCases H3.
          {  destruct(PositiveOrNegative F0).
             * (* first *) 
               rewrite <- H6.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'...
                
                 assert(seqN th (S n0) B (P::(F0::x)) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               LFocus F0 (P::x). HProof. 
               apply unRelease.
               HProof.  
*
               rewrite <- H6.
               inversion H4;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
                 rewrite  H3 in H13.
                 cut1H H13 Hb. 

               apply unRelease.
                HProof.
              } 
          {  destruct(PositiveOrNegative G).
             * (* first *) 
               rewrite <- H6.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               apply unRelease.
                HProof.
               rewrite <- (app_nil_l [G]).
               apply UpExtension'...
                 assert(seqN th (S n0) B (P::(G::x)) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               LFocus G (P::x).  HProof.
            *   rewrite <- H6.
               inversion H9;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               apply unRelease.
                HProof.
                 rewrite H3 in H13.
                 cut1H H13 Hb. 
               }
  +  destruct(PositiveOrNegative (FX t)).   
     { eapply @InvExC with  (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'...
        assert(seqN th (S n0) B (P::(FX t::M)) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((FX t::M) ++ N) (UP [ ])) as Cut.
                eapply CH...
        LLPerm((FX t :: M) ++ N)...
        apply Cut... 
        LFocus (FX t) (P::M).  }
     {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExC with (t:=t) (FX:=FX)...
                 cut1H H12 Hb. 
}
    +  apply PositiveNotNegative in H. contradiction. 
 -  inversion H5;CleanContext... apply @AbsorptionClassic' with (F:=F)...
        cut1H H8 Hb. 
*
destruct(PositiveOrNegative F).

   - inversion H5...
    +   eapply @AbsorptionPerp' with (A:=A)...
        inversion Hb...
        HProof.
  + destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusT with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'...
        assert(seqN th (S n0) B (P::(F0::M)) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((F0::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               LFocus F0 (P::M). }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusT with (F:=F0) (G:=G) ...
                 cut1H H10 Hb. 
}
  +  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusTComm with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'...
        assert(seqN th (S n0) B (P::(G::M)) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((G::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               LFocus G (P::M).  }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
                 cut1H H10 Hb. 
 }

       + checkPermutationCases H3.
          {  destruct(PositiveOrNegative F0).
             * (* first *) 
               rewrite <- H6.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'...
                
                 assert(seqN th (S n0) B (P::(F0::x)) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               LFocus F0 (P::x). HProof. 
               apply unRelease.
               HProof. 
(* first *) 
*               rewrite <- H6.
               inversion H4;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
                 rewrite  H3 in H13.
                 cut1H H13 Hb. 

               apply unRelease.
                HProof. }
          {  destruct(PositiveOrNegative G).
             * (* first *) 
               rewrite <- H6.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               apply unRelease.
                HProof.
               rewrite <- (app_nil_l [G]).
               apply UpExtension'...
                 assert(seqN th (S n0) B (P::(G::x)) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               LFocus G (P::x).  HProof.
            * (* first *) 
               rewrite <- H6.
               inversion H9;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               apply unRelease.
                HProof.
                 rewrite H3 in H13.
                 cut1H H13 Hb. 

               } 
  +  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExT with  (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'...
        assert(seqN th (S n0) B (P::(FX t::M)) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((FX t::M) ++ N) (UP [ ])) as Cut.
                eapply CH...
       apply Cut...
       LFocus (FX t) (P::M). }
          {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExT with (t:=t) (FX:=FX)...
                 cut1H H12 Hb. 
}
                
  +  apply PositiveNotNegative in H. contradiction. 
- inversion H5;CleanContext...
        destruct (NegativeAtomDec F).
        
        assert(False). 
        inversion H;subst;solvePolarity... 
        contradiction.
        apply @AbsorptionTheory with (F:=F)...
                 cut1H H8 Hb. 

  Qed.         
  
  Theorem Cut2  a b P L M N B : 
  CutH (complexity P) (a+b) -> CutW (complexity P) ->
  seqN th a B M (UP (P::L)) ->
  seqN th b B N (DW (dual P)) ->
  seq th B (M ++ N) (UP L).
Proof with sauto;solveLL.   
 intros CH CW Ha Hb.
 inversion Ha;subst. 
 * inversion Hb...
   CleanContext.
 * inversion Hb; CleanContext...
   cut2W H4 H3.
   simpl...
   cut2W H5 H3.
   simpl...
 * inversion Hb; CleanContext...
    HProof.
 * inversion Hb; CleanContext...
    cut2W H3 H6.
    simpl...
   apply OLCut in H6;auto.
    apply seqtoSeqN in H6.
    destruct H6.
    cut2W H H7.
    simpl...
    rewrite H1.
    LLPerm((M ++ M0) ++ N0)...
 * assert(N=[]).
   inversion Hb;solvePolarity...
   subst.
   simpl in Hb.
   cut4H H3 Hb.
  * inversion Hb;CleanContext...
     pose proof (H5 _ H1).
    cut2W H H7. 

   simpl...
    remember (VAR con 0%nat).
            assert(proper e).
            rewrite Heqe.  
            constructor.
            subst.
            erewrite ComplexityUniformEq...
          
 *  apply NotAsynchronousPosAtoms in H4...
   assert(negativeFormula (P ^)).
   apply PositiveDualNegative in H...
 
     inversion Hb;subst; try match goal with
       [ H: _= dual ?C , H2: negativeFormula (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
    cut1H H5 H7.
   inversion H...
   inversion Hb...
   HProof.
   apply InPermutation in H4...
   rewrite H4 in H5.

   eapply absorptionN in H5.
   HProof.
   solvePolarity. 
 Qed.
 
 Theorem Cut3 a b P Q F L B:
    CutH (complexity P) (a+b) -> CutW  (complexity P) ->
    S (complexity Q) = complexity P ->
    seqN th a (Q::B) L (DW F) -> 
    seqN th b B [] (DW (! Q ^)) ->   
    seq th B L (UP [F]).
  Proof with sauto;solveLL.
  intros HC WC Hc' Ha Hb.
    inversion Ha...
    * apply InPermutation in H3... 
      checkPermutationCases H3.
      - simpl in Hb.
        inversion Hb;solvePolarity...
        inversion H3...
        HProof.
     -  LFocus (perp A). 
        solveLL. rewrite H1...  
      * cut3H H3 Hb. 
        apply InvPlus...
      * cut3H H3 Hb. 
        apply InvPlusComm...
      * cut3H H1 Hb. 
         cut3H H5 Hb.
         rewrite H0.
        eapply @InvTensor' with (B:=B)...
     *  cut4H H3 Hb.
        LFocus.
   *    cut3H H5 Hb.
        eapply InvEx with (t:=t)...
       * cut4H H4 Hb. 
  Qed. 

Theorem Cut4  a b P Q L M B  : 
CutH (complexity P) (a+b) -> CutW (complexity P) ->    S (complexity Q) = complexity P ->
  seqN th a (Q::B) M (UP L) ->
  seqN th b B [] (DW (! Q ^)) ->
  seq th B M (UP L).
Proof with sauto;solveLL.  
  intros CH CW Hc Ha Hb.
  inversion Ha...  
  * cut4H H0 Hb.
  * cut4H H4 Hb.
  * cut4H H3 Hb.
  * cut4H H3 Hb.
  * LLPermH H3 (Q::F::B). 
     apply weakeningN with (F:=F) in Hb.     
     cut4H H3 Hb.
     LLPerm (F::B)...
  * apply H4 in properX. cut4H properX Hb.
  * cut4H H4 Hb.
  * destruct (PositiveOrNegative F).
     cut3H H5 Hb. 
     assert( seq th B L' (UP [F]))...
     inversion H0;subst;try solve [inversion H].
     rewrite <- H1.
       HProof. 
     inversion H5;CleanContext...
     rewrite <- H1.
     LFocus...
     cut4H H8 Hb. 
  *  inversion H1...
      + cut3H H5 Hb. 
         assert(Hs: seq th B M (UP [F]))...
          apply seqtoSeqN in Hs.
          destruct Hs as [x Hs].
          inversion Hb...
            destruct(PositiveOrNegative F).
            assert(negativeFormula (F ^)).
            apply PositiveDualNegative...
            assert( seqN th x B M  (UP [F]) -> 
                    seqN th (S n0) B [] (DW (F ^)) ->
                      seq th B (M++[])  (UP [ ])) as Cut.
            eapply CW...
            CleanContext. 
           
            assert( seqN th n0 B []  (UP [F^]) -> 
                  seqN th (S x ) B M (DW ((F^)^)) ->
                      seq th B ([]++M) (UP [ ])) as Cut.
            eapply CW...
            rewrite <- DualComplexity...
            rewrite <- ng_involutive in Cut.
            CleanContext.
            solvePolarity.
    + eapply @AbsorptionClassic with  (F:=F)...
          cut3H H5 Hb. 
  
     * cut3H H5 Hb. 
        assert(Hs:seq th B M (UP [F]))...
             destruct (NegativeAtomDec F).
              2:{  eapply @AbsorptionTheory with (F:=F)... }
             inversion H...
             eapply @AbsorptionPerp' with (A:=A)...
  Qed.
  
 
  Theorem CutElimination i j C A B L M N P: 
      (seqN th i B (C::M) (UP L) -> 
      seqN th j B N (UP [dual C]) -> 
      seq th B (M ++ N) (UP L)) /\
      (seqN th i B M (UP (C :: L)) -> 
      seqN th j B N (DW (dual C)) -> 
      seq th B (M ++ N) (UP L)) /\
       (S (complexity A) = complexity C ->
       seqN th i (A::B) M (DW P) -> 
       seqN th j B [] (DW (! (dual A))) -> 
       seq th B M (UP [P]))  /\
      (S (complexity A) = complexity C ->
       seqN th i (A::B) M (UP L) -> 
       seqN th j B [] (DW (! (dual A))) -> 
       seq th B M (UP L)).
  Proof with sauto;solvePolarity;solveLL.
    assert(exists w, complexity C = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert i j C A  P B L M N.
    
    induction w using lt_wf_ind; intros. 
     
     remember (plus i j) as h.
      revert dependent B.
      revert dependent L.
      revert dependent M.
      revert dependent N.
      revert dependent P.
      revert A.
      revert dependent C.
      revert dependent i.
      revert j.
      induction h using lt_wf_ind; intros.
      rename H into CutW.
      rename H0 into CutH.
      rename H1 into compC.
        
        move B at top.
        move L at top.
        move M at top.
        move N at top.
        
        move C at top.
        move A at top.
        move P at top.
        
        subst.
        split;[intros | 
        split;[intros | 
        split;intros]].
         *
         refine (Cut1 _   H H0).
         eauto.
          unfold CutElimination.CutH; intros.
          eauto.
         * eapply (@Cut2 i j C L M)...
          unfold CutElimination.CutH; intros.
          eapply CutH with (m:=i0 + j0)...
          unfold CutElimination.CutW; intros.
          eapply CutW with (m:=complexity C0)...
    *  eapply (@Cut3 i j C A P M B)...
          unfold CutElimination.CutH; intros.
          eapply CutH with (m:=i0 + j0)...
          unfold CutElimination.CutW; intros.
          eapply CutW with (m:=complexity C0)...
    *  eapply (@Cut4 i j C A  L M B)...
          unfold CutElimination.CutH; intros.
          eapply CutH with (m:=i0 + j0)...
          unfold CutElimination.CutW; intros.
          eapply CutW with (m:=complexity C0)...
          Qed.
          
  Theorem GeneralCut i j C B L M N: 
    seqN th i B M (UP (C::L)) -> 
                   seqN th j B N (DW (dual C)) -> 
                                 seq th B (M++N ) (UP L).
  Proof with subst;auto.
    assert(exists w, complexity C = w). 
    eexists; auto.
    destruct H as [w H].
    apply CutElimination...
  Qed.
  
  Theorem GeneralCut' C B L M N:   
      seq th B M  (UP (C :: L)) ->
      seq th B N  (DW (dual C)) ->
      seq th B (M ++ N) (UP L).
  Proof.
    intros.
    apply seqtoSeqN in H.
    apply seqtoSeqN in H0...
    CleanContext.
    eapply GeneralCut with (C:= C);eauto.
  Qed.

  Theorem CutAndreoli i j C B M N: 
    seqN th i B M (DW C) -> 
                   seqN th j B N (DW (dual C)) -> 
                                 seq th B (M++N) (UP []).
  Proof with subst;auto.
    intros.
    assert(exists w, complexity C = w). 
    eexists; auto.
    destruct H1 as [w H1].
    
    destruct(PositiveOrNegative C).  
    -
      eapply PositiveDualNegative in H2;eauto.
      inversion H0;subst;
        try solve[
              match goal with
              | [H : _ = C ^ |- _] => rewrite <- H in H2;inversion H2
              end].
      eapply exchangeLC with (LC:=N++M). perm.  
      eapply GeneralCut; try assumption.
      exact H8.
      rewrite <- ng_involutive.
      exact H.
    -
      inversion H;subst; try solve [inversion H2].
      eapply GeneralCut; try assumption.
      exact H8.
    exact H0.
  Qed. 
               

End CutElimination.
