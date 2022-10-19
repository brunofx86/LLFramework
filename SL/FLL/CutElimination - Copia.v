(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.Focused.FLLTactics.
Require Import Lia.
Require Import FLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export FLL.SL.Focused.InvPositivePhase.

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
    forall i j C A M N L B, 
    complexity C < w ->
      (seqN th i B M (UP (C :: L)) -> seqN th j B N (DW (dual C)) -> seq th B (M ++ N) (UP L)) /\
      (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (UP L) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP L)). 
    
  Definition CutH (w h: nat) :=  
    forall i j C A M N L B, 
    i + j < h ->
    complexity C = w ->
      (seqN th i B M (UP (C :: L)) -> seqN th j B N (DW (dual C)) -> seq th B (M ++ N) (UP L)) /\
      (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (UP L) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP L)). 

 Lemma Derivation1 D M F : 
 seq th D M (DW F) -> seq th D M (UP [F]).
 Proof with sauto;solveLL.
 intros.
 inversion H...
 all:LFocus.
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
    HProof.
 * inversion Hb; CleanContext...
   assert( seqN th n B M (UP (F :: G :: L)) -> 
          seqN th n0 B M0 (DW (F ^)) -> 
             seq th B (M ++ M0) (UP (G :: L))) as HcutF.
    eapply CW...
    simpl...
    apply HcutF in H6;auto.
    
    apply seqtoSeqN in H6.
    destruct H6.
    
    assert( seqN th x B (M ++ M0) (UP (G :: L)) -> 
           seqN th n0 B N0 (DW (G ^)) -> 
              seq th B ((M ++ M0) ++ N0) (UP L)) as HcutG.
      eapply CW...
      simpl...
      rewrite H1.
      LLPerm((M ++ M0) ++ N0)...
 * inversion Hb; CleanContext...
   assert( seqN th n B M (UP (F :: L)) -> 
          seqN th n0 B N (DW (F ^)) -> 
             seq th B (M ++ N) (UP L)) as HcutF.
    eapply CW...
     simpl...
    apply  HcutF ... 
  assert( seqN th n B M (UP (G :: L)) -> 
          seqN th n0 B N (DW (G ^)) -> 
             seq th B (M ++ N) (UP L)) as HcutG.
    eapply CW...
     simpl...
    apply  HcutG...
 * assert(N=[]).
   inversion Hb...
   subst.
    assert( seqN th n (B ++ [F]) M  (UP L) -> 
           seqN th b B [] (DW (! F ^)) -> 
             seq th B M  (UP L)) as UCCut.
    eapply CH... 
    rewrite app_nil_r...
 *  apply NotAsynchronousPosAtoms in H4...
   assert(negativeFormula (P ^)).
   apply PositiveDualNegative in H...
 
     inversion Hb;subst; try match goal with
       [ H: _= dual ?C , H2: negativeFormula (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
  
  (** LEGO part *)

 inversion H5...
 + assert(seqN th (S n1) B (M) (UP (P::M0)) ->
          seqN th (S n0) B N (DW (dual P)) ->
            seq th B (M ++ N) (UP M0)) as Cut.
           eapply CH...
           apply Cut...
           
 + assert(seqN th (S n1) B M (UP (P::F :: G :: M0)) ->
        seqN th (S n0) B N (DW (dual P)) ->
            seq th B (M ++ N) (UP (F :: G :: M0))) as Cut.
           eapply CH...
                    
           apply Cut...                                       
 + assert(seqN th (S n1) B M (UP (P::F  :: M0)) ->
          seqN th (S n0) B N (DW (dual P)) ->
            seq th B (M ++ N) (UP (F :: M0))) as CutF.
           eapply CH...
                    
           apply CutF...             

 + assert(seqN th (S n1) B M (UP (P::G  :: M0)) ->
          seqN th (S n0) B N (DW (dual P)) ->
            seq th B (M ++ N) (UP (G :: M0))) as CutG.
           eapply CH...
                    
           apply CutG...             

 + assert(seqN th (S n1) (B ++ [(F)]) M (UP (P::M0)) ->
            seqN th (S n0) (B ++ [(F)]) N (DW (dual P)) ->
              seq th (B ++ [(F)]) (M ++ N) (UP M0)) as Cut.
           eapply CH...
           apply Cut...
           apply weakeningGenN_rev...
 + assert(seqN th (S n1) B (F::M) (UP (P::M0)) ->
        seqN th (S n0) B N (DW (dual P)) ->
            seq th B ((F::M) ++ N) (UP M0)) as Cut.
           eapply CH...
           apply Cut...
           FLLstore.
           LLExact H8.
 (** Inversion Cases *)
 + checkPermutationCases H3.
  assert(seqN th n0 B N (UP [P ^]) ->
        seqN th  n1 B L' (DW ((P ^)^)) ->
            seq th B (N++L') (UP [])) as Cut.
           eapply CH...
           rewrite <- ng_involutive in Cut.
       rewrite <- H6. 
       LLPerm(N ++ L')...    
       
       inversion H9...
            {
              inversion H4...
              inversion H7...
              HProof. }
          {     rewrite H4 in H6.
              checkPermutationCases H6.
              -
                destruct(PositiveOrNegative F0).
              { (* first *)  
              assert(seqN th (S n) B ((F0::x0)++[P]) (UP [])).
              LFocus F0 (x0++[P])...
              HProof. 
              rewrite H6...
              rewrite H3.
              rewrite <- app_comm_cons.
              
              
              apply TensorComm'.
              rewrite <- H10.
              LLPerm(G ⊗ F0::N0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
              
              apply Derivation1.
              HProof.
             
              assert(seqN th (S (S n)) B ((F0::x0)) (UP [P ]) ->
                       seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((F0::x0) ++ N) (UP [ ])) as Cut.
                eapply CH...
                FLLstore. 
                apply Cut...
              FLLstore. HProof.
               }
             { (* second *) 
              inversion H8;CleanContext...
              rewrite H3.
              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H10.
              LLPerm(G ⊗ F0::N0++(x0++N)).
                rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
                apply Derivation1.
              HProof.  
                 assert(seqN th (S n1) B x0 (UP [P;F0]) ->
                       seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x0 ++ N) (UP [F0])) as Cut.
                eapply CH... 
                apply Cut...
                FLLstore.
                HProof. } 
             - 
                destruct(PositiveOrNegative G).
              { (* first *)  
              assert(seqN th (S n) B ((G::x0)++[P]) (UP [])).
              LFocus G (x0++[P])...
              HProof. 
              rewrite H6...
              rewrite H3.
              rewrite <- app_comm_cons.
              rewrite <- H10.
              LLPerm(F0 ⊗ G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
              
              apply Derivation1.
              HProof.
             
              assert(seqN th (S (S n)) B ((G::x0)) (UP [P ]) ->
                       seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((G::x0) ++ N) (UP [ ])) as Cut.
                eapply CH...
                FLLstore. 
                apply Cut...
              FLLstore. HProof.
               }
             { (* second *) 
              inversion H13;CleanContext...
              rewrite H3.
              rewrite <- app_comm_cons.
              rewrite <- H10.
              LLPerm(F0 ⊗ G::M0++(x0++N)).
                rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
                apply Derivation1.
              HProof.  
                 assert(seqN th (S n1) B x0 (UP [P;G]) ->
                       seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x0 ++ N) (UP [G])) as Cut.
                eapply CH... 
                apply Cut...
                FLLstore.
                HProof. }  }
          -    destruct(PositiveOrNegative F0).   
       { rewrite H3. 
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                 FLLstore. 
                assert( seqN th (S (S n)) B (F0::x) (UP [P ]) ->
                    seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                apply Cut...
                FLLstore.
                 LFocus F0 (P::x). HProof.
              }
             {   inversion H11;CleanContext...  
                 rewrite H3.
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                assert(seqN th (S n1) B x (UP [P;F0]) ->
                     seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [F0])) as Cut.
                eapply CH...
               apply Cut... FLLstore. HProof.  
               } 
     -    destruct(PositiveOrNegative G).   
       { rewrite H3. 
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                 FLLstore. 
                assert( seqN th (S (S n)) B (G::x) (UP [P ]) ->
                    seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                apply Cut...
                FLLstore.
                 LFocus G (P::x). HProof.
              }
             {   inversion H11;CleanContext...  
                 rewrite H3.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                assert(seqN th (S n1) B x (UP [P;G]) ->
                     seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [G])) as Cut.
                eapply CH...
               apply Cut... FLLstore. HProof.  
               }  
     -  apply PositiveNotNegative in H1. contradiction. 
   -   destruct(PositiveOrNegative (FX t)).   
       { rewrite H3. 
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                 FLLstore. 
                 assert( seqN th (S (S n)) B (FX t::x) (UP [P]) ->
                     seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((FX t::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                FLLstore. 
                 LFocus (FX t) (P::x). HProof. }
             {   inversion H13;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
                 rewrite H3.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                assert(seqN th (S n1) B x (UP [P;FX t]) ->
                     seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [FX t])) as Cut.
                eapply CH...
               apply Cut...
                FLLstore. 
               
                HProof. }
  
  +  destruct(PositiveOrNegative F).
  
   2:{ inversion H9;CleanContext... 
   apply @AbsorptionClassic' with (F:=F)...
        assert(seqN th (S n) B M (UP [P;F]) ->
            seqN th (S n0) B N (DW (dual P)) ->
                  seq th B (M ++ N) (UP [F])) as Cut.
       eapply CH... 
       apply Cut... } 
       inversion H9...  
       -  apply @AbsorptionClassic' with  (F:=perp A)...
          inversion H7...
          HProof.
         - checkPermutationCases H6.
          {  destruct(PositiveOrNegative F0).
             { (* first *) 
               rewrite <- H10.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               FLLstore.
                
                 assert(seqN th (S (S n)) B ((F0::x)) (UP [P]) ->
                   seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               FLLstore.
               LFocus F0 (P::x). HProof. 
               apply Derivation1.
               HProof.  }
            { (* first *) 
               rewrite <- H10.
               inversion H8;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
                 assert(seqN th (S n1) B x (UP [P;F0]) ->
               seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut...
                FLLstore.
                HProof.
               apply Derivation1.
                HProof.
              } }
          {  destruct(PositiveOrNegative G).
             { (* first *) 
               rewrite <- H10.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
                FLLstore.
               
                 assert(seqN th (S (S n)) B (G::x) (UP [P]) ->
                   seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               FLLstore.
               LFocus G (P::x).  HProof.
            }
            { (* first *) 
               rewrite <- H10.
               inversion H13;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
                 assert(seqN th (S (S n1)) B x (UP [P;G]) ->
                   seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut... 
                FLLstore.
                 HProof.
               } }
  -  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusC with (F:=F0) (G:=G)...
        FLLstore.
        assert(seqN th (S (S n)) B (F0::M) (UP [P ]) ->
              seqN th (S n0) B N (DW (dual P)) ->
                    seq th B ((F0::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               FLLstore.
               LFocus F0 (P::M). }
                
     {  inversion H11;CleanContext...               
        eapply @InvPlusC with (F:=F0) (G:=G) ...
        assert( seqN th (S n1) B M (UP [P;F0]) ->
               seqN th (S n0) B N (DW (dual P)) ->
                 seq th B (M ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut... }
  -  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusCComm with (F:=F0) (G:=G)...
        FLLstore. 
        assert(seqN th (S (S n)) B (G::M) (UP [P]) ->
                seqN th (S n0) B N (DW (dual P)) ->
                    seq th B ((G::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               FLLstore.
               LFocus G (P::M). }
     {  inversion H11;CleanContext...               
        eapply @InvPlusCComm with (F:=F0) (G:=G)...
        assert( seqN th (S n1) B M (UP [P;G]) ->
               seqN th (S n0) B N (DW (dual P)) ->
                 seq th B (M ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut... }
  -  apply PositiveNotNegative in H0. contradiction. 
  -  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExC with  (t:=t) (FX:=FX)...
        FLLstore.
        assert(seqN th (S (S n)) B (FX t::M) (UP [P]) ->
                seqN th (S n0) B N (DW (dual P)) ->
                    seq th B ((FX t::M) ++ N) (UP [ ])) as Cut.
                eapply CH...
        LLPerm((FX t :: M) ++ N)...
        apply Cut...
        FLLstore. 
        LFocus (FX t) (P::M).  }
     {  inversion H13;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExC with (t:=t) (FX:=FX)...
        assert( seqN th (S n1) B M (UP [P;FX t]) ->
                seqN th (S n0) B N (DW (dual P)) ->
                 seq th B (M ++ N) (UP [FX t])) as Cut.
                eapply CH...
                apply Cut... }
+
destruct(PositiveOrNegative F).
    2:{ inversion H9;CleanContext...
        destruct (NegativeAtomDec F).
        assert(False). 
        inversion H6;subst... 
        contradiction.
        apply @AbsorptionTheory with (F:=F)...
        assert(seqN th (S n) B M (UP [P;F]) ->
                 seqN th (S n0) B N (DW (dual P)) ->
                    seq th B (M ++ N) (UP [F])) as Cut.
                         
                eapply CH...
                 
                apply Cut... }
    inversion H9...
    -   eapply @AbsorptionPerp' with (A:=A)...
        inversion H7...
        HProof.
          - checkPermutationCases H6.
          {  destruct(PositiveOrNegative F0).
             { (* first *) 
               rewrite <- H10.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               FLLstore.
                
                 assert(seqN th (S (S n)) B (F0::x) (UP [P]) ->
                      seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               FLLstore. 
               LFocus F0 (P::x). HProof. 
               apply Derivation1.
               HProof.  }
            { (* first *) 
               rewrite <- H10.
               inversion H8;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
                 assert(seqN th (S n1) B x (UP [P;F0]) ->
                      seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut...
                FLLstore.
                HProof.
               apply Derivation1.
                HProof.
              } }
          {  destruct(PositiveOrNegative G).
             { (* first *) 
               rewrite <- H10.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
                FLLstore.
                 assert(seqN th (S (S n)) B (G::x) (UP [P]) ->
                    seqN th (S n0) B N (DW (dual P)) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               FLLstore.
               LFocus G (P::x).  HProof.
            }
            { (* first *) 
               rewrite <- H10.
               inversion H13;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
                 assert(seqN th (S n1) B x (UP [P;G]) ->
                   seqN th (S n0) B N (DW (dual P)) ->
                         seq th B (x ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut... 
                FLLstore.
                 HProof.
               } }
  -  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusT with (F:=F0) (G:=G)...
     FLLstore.
        assert(seqN th (S (S n)) B (F0::M) (UP [P]) ->
                 seqN th (S n0) B N (DW (dual P)) ->
                    seq th B ((F0::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               FLLstore.
               LFocus F0 (P::M). }
                
     {  inversion H11;CleanContext...               
        eapply @InvPlusT with (F:=F0) (G:=G) ...
        assert( seqN th (S n1) B M (UP [P;F0]) ->
            seqN th (S n0) B N (DW (dual P)) ->
                 seq th B (M ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut... }
  -  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusTComm with (F:=F0) (G:=G)...
     FLLstore.
        assert(seqN th (S (S n)) B (G::M) (UP [P]) ->
                seqN th (S n0) B N (DW (dual P)) ->
                    seq th B ((G::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               FLLstore.
               LFocus G (P::M).  }
                
     {  inversion H11;CleanContext...               
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
        assert( seqN th (S n1) B M (UP [P;G]) ->
          seqN th (S n0) B N (DW (dual P)) ->
                 seq th B (M ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut... }

  -  apply PositiveNotNegative in H0. contradiction. 
  -  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExT with  (t:=t) (FX:=FX)...
     FLLstore.
        assert(seqN th (S (S n)) B (FX t::M) (UP [P]) ->
              seqN th (S n0) B N (DW (dual P)) ->
                    seq th B ((FX t::M) ++ N) (UP [ ])) as Cut.
                eapply CH...
       rewrite app_comm_cons...
       apply Cut...
       FLLstore.
       LFocus (FX t) (P::M). }
          {  inversion H13;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExT with (t:=t) (FX:=FX)...
        assert( seqN th (S n1) B M(UP [P;FX t]) ->
               seqN th (S n0) B N (DW (dual P)) ->
                 seq th B (M ++ N) (UP [FX t])) as Cut.
                eapply CH...
                apply Cut... }
                
  +  assert(seqN th (S n1) B M (UP (P::FX x :: M0)) ->
         seqN th (S n0) B N (DW (dual P)) ->
             seq th B (M ++ N) (UP (FX x :: M0))) as Cut.
           eapply CH...
              
           apply H8 in properX...
    +       
     inversion H...
   inversion Hb;CleanContext...
   HProof.
   apply InPermutation in H4...
   rewrite H4 in H5.
   eapply AbsorptionC in H5.
   rewrite <- H4 in H5.
   HProof.
   
  (** End LEGO part *)
  
  * inversion Hb;CleanContext...
   assert( seqN th n B M (UP (FX t :: L)) -> 
           seqN th n0 B N (DW ((FX t) ^)) -> 
              seq th B (M++N) (UP L)) as HCut.
   eapply CW...
   simpl...
    remember (VAR con 0%nat).
            assert(proper e).
            rewrite Heqe.  
            constructor.
            subst.
            erewrite ComplexityUniformEq...
            
            apply HCut... 
 Qed.
 

Theorem Cut4  a b P Q L M B  : 
CutH (complexity P) (a+b) -> CutW (complexity P) ->    S (complexity Q) = complexity P ->
  seqN th a (B++[Q]) M (UP L) ->
  seqN th b B [] (DW (! Q ^)) ->
  seq th B M (UP L).
Proof with sauto;solveLL.  
  intros CH CW Hc Ha Hb.
  inversion Ha...  
  --  assert( seqN th n (B++[Q]) M (UP M0) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP M0)) as Cut.
              eapply CH...
              apply Cut... 
  --  assert( seqN th n (B++[Q]) M (UP (F :: G :: M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (F :: G ::M0))) as Cut.
              eapply CH...  
              apply Cut...
  --  assert( seqN th n (B++[Q]) M (UP (F :: M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (F :: M0))) as Cut.
              eapply CH... 
              apply Cut... 
  --  assert( seqN th n (B++[Q]) M (UP (G :: M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (G ::M0))) as Cut.
              eapply CH... 
              apply Cut...
  --  assert( seqN th n ((B ++ [F]) ++ [Q]) M (UP M0) ->
              seqN th b (B ++ [F]) [] (DW (! Q ^)) -> seq th (B ++ [F]) M (UP M0)) as Cut.
              eapply CH... 
              LLPerm(B  ++ [F])...
              apply Cut...
              LLExact H3.
              apply weakeningGenN_rev...
  --  assert( seqN th n (B++[Q]) (F::M)  (UP M0) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B (F::M) (UP M0)) as Cut.
              eapply CH... 
              apply Cut...
  --
  (** LEGO part *)

  inversion H5...
  + rewrite <- H1... 
  + apply in_app_or in H6...
     LFocus.
     inversion H...
       inversion Hb...
  2:{ inversion H1. }
     inversion H3... HProof.
   +  
          
       assert(CutF: seqN th (S n0) (B++[Q]) (F0::M0) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (F0::M0) (UP [])).
        eapply CH... 
      
          
       assert(CutF': seqN th n0 (B++[Q]) M0 (UP [F0]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M0 (UP [F0])).
        eapply CH... 
        
         assert(CutG: seqN th (S n0) (B++[Q]) (G::N) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (G::N) (UP [])).
        eapply CH...
        
        
         assert(CutG': seqN th n0 (B++[Q]) N (UP [G]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B N (UP [G])).
        eapply CH...
        
        destruct(PositiveOrNegative F0);destruct(PositiveOrNegative G).   
      { 
       rewrite <- H1.   
       rewrite H2.
       rewrite <- (app_nil_l []).  
       eapply @InvTensor with (B:=B)...
       FLLstore. 
        apply CutF...
        LFocus F0.
       FLLstore. 
        apply CutG...
        LFocus G. }
       { 
       rewrite <- H1.   
       rewrite H2.
       rewrite <- (app_nil_l []).  
       eapply @InvTensor with (B:=B)...
       FLLstore. 
        apply CutF...
        LFocus F0.
        apply CutG'...
        inversion H8;CleanContext...
        HProof. }
       { 
       rewrite <- H1.   
       rewrite H2.
       rewrite <- (app_nil_l []).  
       eapply @InvTensor with (B:=B)...
        apply CutF'...
        inversion H3;CleanContext...
        HProof.
        FLLstore. 
        apply CutG...
        LFocus G. }  
       { 
       rewrite <- H1.   
       rewrite H2.
       rewrite <- (app_nil_l []).  
       eapply @InvTensor with (B:=B)...
        apply CutF'...
        inversion H3;CleanContext...
        HProof.
        apply CutG'...
        inversion H8;CleanContext...
        HProof. }
    +     
      assert(CutF: seqN th (S n0) (B++[Q]) (F0::L') (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (F0::L') (UP [])).
        eapply CH... 
          
       assert(CutF': seqN th n0 (B++[Q]) L' (UP [F0]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B L' (UP [F0])).
        eapply CH...
        
        destruct(PositiveOrNegative F0).
       { 
       rewrite <- H1.   
       rewrite <- (app_nil_l []).  
       eapply @InvPlus...
       FLLstore. 
        apply CutF...
        LFocus F0. }
       { 
       rewrite <- H1.   
       rewrite <- (app_nil_l []).  
       eapply @InvPlus...
        apply CutF'...
        inversion H6;CleanContext...
        HProof. }
       +     
       
      assert(CutG: seqN th (S n0) (B++[Q]) (G::L') (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (G::L') (UP [])).
        eapply CH... 
          
       assert(CutG': seqN th n0 (B++[Q]) L' (UP [G]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B L' (UP [G])).
        eapply CH...
        
        destruct(PositiveOrNegative G).
       { 
       rewrite <- H1.   
       rewrite <- (app_nil_l []).  
       eapply @InvPlusComm...
       FLLstore. 
        apply CutG...
        LFocus G. }
       { 
       rewrite <- H1.   
       rewrite <- (app_nil_l []).  
       eapply @InvPlusComm...
        apply CutG'...
        inversion H6;CleanContext...
        HProof. }
        +     
        LFocus.
          solveLL.
         assert(CutF0: seqN th n0 (B++[Q]) [] (UP [F0]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B [] (UP [F0])).
        eapply CH... 
     apply CutF0...
      +
       rewrite <- H1. LFocus.
          solveLL.
         assert(CutF: seqN th n0 (B++[Q]) L' (UP [F]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B L' (UP [F])).
        eapply CH... 
     apply CutF...
      +
      assert(CutFX: seqN th (S n0) (B++[Q]) (FX t::L') (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (FX t::L') (UP [])).
        eapply CH... 
          
       assert(CutFX': seqN th n0 (B++[Q]) L' (UP [FX t]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B L' (UP [FX t])).
        eapply CH...
        
        destruct(PositiveOrNegative (FX t)).
       { 
       rewrite <- H1.   
       rewrite <- (app_nil_l []).  
       eapply @InvEx with (t:=t)...
       FLLstore. 
        apply CutFX...
        LFocus.  }
       { 
       rewrite <- H1.   
       rewrite <- (app_nil_l []).  
        eapply @InvEx with (t:=t)...
        apply CutFX'...
         inversion H8;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.
        HProof. }
    --   apply in_app_or in H1...
     {
      destruct(PositiveOrNegative F).
      inversion H5...
       +  CFocus (perp A).
       + apply in_app_or in H7...
           CFocus (perp A).
           inversion H2...
           apply InPermutation in H...
           rewrite H in Hb.
           inversion Hb...
           2:{ inversion H3. }
           inversion H6... 
           apply AbsorptionC in H10.
           rewrite <- H in H10.
           HProof.
       + CFocus One.
       +      
       assert(CutF: seqN th (S n0) (B++[Q]) (F0::M0) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (F0::M0) (UP [])).
        eapply CH... 
      
          
       assert(CutF': seqN th n0 (B++[Q]) M0 (UP [F0]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M0 (UP [F0])).
        eapply CH... 
        
         assert(CutG: seqN th (S n0) (B++[Q]) (G::N) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (G::N) (UP [])).
        eapply CH...
        
        
         assert(CutG': seqN th n0 (B++[Q]) N (UP [G]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B N (UP [G])).
        eapply CH...
        
        destruct(PositiveOrNegative F0);destruct(PositiveOrNegative G).   
      { 
       rewrite H3.
       rewrite <- (app_nil_l []).  
       eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
       FLLstore. 
        apply CutF...
        LFocus F0.
       FLLstore. 
        apply CutG...
        LFocus G. }
       { 
       rewrite H3.
       rewrite <- (app_nil_l []).
       eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
       FLLstore. 
        apply CutF...
        LFocus F0.
        apply CutG'...
        inversion H9;CleanContext...
        HProof. }
       { 
       rewrite H3.
       rewrite <- (app_nil_l []).
       eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
        apply CutF'...
        inversion H4;CleanContext...
        HProof.
        FLLstore. 
        apply CutG...
        LFocus G. }  
       { 
       rewrite H3.
       rewrite <- (app_nil_l []).
       eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
        apply CutF'...
        inversion H4;CleanContext...
        HProof.
        apply CutG'...
        inversion H9;CleanContext...
        HProof. }
    +     
      assert(CutF: seqN th (S n0) (B++[Q]) (F0::M) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B  (F0::M) (UP [])).
        eapply CH... 
          
       assert(CutF': seqN th n0 (B++[Q]) M (UP [F0]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M (UP [F0])).
        eapply CH...
        
        destruct(PositiveOrNegative F0).
       { 
       rewrite <- (app_nil_l []).  
       eapply @InvPlusC with (F:=F0) (G:=G)...
       FLLstore.
        
        apply CutF...
        LFocus F0. }
       { 
       rewrite <- (app_nil_l []).  
        eapply @InvPlusC with (F:=F0) (G:=G)...
        apply CutF'...
        inversion H7;CleanContext...
        HProof. }
    +     
      assert(CutG: seqN th (S n0) (B++[Q]) (G::M) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B  (G::M) (UP [])).
        eapply CH... 
          
       assert(CutG': seqN th n0 (B++[Q]) M (UP [G]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M (UP [G])).
        eapply CH...
        
        destruct(PositiveOrNegative G).
       { 
       rewrite <- (app_nil_l []).  
       eapply @InvPlusCComm with (F:=F0) (G:=G)...
       FLLstore.
        
        apply CutG...
        LFocus G. }
       { 
       rewrite <- (app_nil_l []).  
        eapply @InvPlusCComm with (F:=F0) (G:=G)...
        apply CutG'...
        inversion H7;CleanContext...
        HProof. }
        +
        CFocus (! F0).
          solveLL.
         assert(CutF0: seqN th n0 (B++[Q]) [] (UP [F0]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B [] (UP [F0])).
        eapply CH... 
     apply CutF0...
      +
       CFocus F.
          solveLL.
         assert(CutF: seqN th n0 (B++[Q]) M (UP [F]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M (UP [F])).
        eapply CH... 
     apply CutF...
      +
      assert(CutFX: seqN th (S n0) (B++[Q]) (FX t::M) (UP []) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B (FX t::M) (UP [])).
        eapply CH... 
          
       assert(CutFX': seqN th n0 (B++[Q]) M (UP [FX t]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M (UP [FX t])).
        eapply CH...
        
        destruct(PositiveOrNegative (FX t)).
       { 
       rewrite <- (app_nil_l []).  
       eapply @InvExC with (t:=t) (FX:=FX)...
       FLLstore. 
        apply CutFX...
        LFocus.  }
       { 
       rewrite <- (app_nil_l []).  
        eapply @InvExC with (t:=t) (FX:=FX)...
        apply CutFX'...
         inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.
        HProof. }
     +
       CFocus F.
          solveLL.
         assert(CutF: seqN th n (B++[Q]) M (UP [F]) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M (UP [F])).
        eapply CH...
        inversion H5;CleanContext...
         
     apply CutF...
     HProof. }
     
     inversion H...
     
     
     destruct(PositiveOrNegative F).
     2:{ inversion H5;CleanContext...
           inversion Hb...
          assert(CutF1: seqN th n0 (B++[F]) M (UP [F]) ->
             seqN th (S n) B [] (DW (! F ^)) ->
             seq th B M (UP [F])).
        eapply CH...

         assert(seq th B M (UP [F])).
        apply CutF1...
        apply seqtoSeqN in H...
         assert(CutF2: seqN th n B [] (UP [F^]) ->
             seqN th (S x) B M (DW ((F^)^)) ->
             seq th B ([]++M) (UP [])).
        eapply CW...
        rewrite <- (DualComplexity F)...
        rewrite <- (app_nil_l M).
        apply CutF2...
        rewrite <- ng_involutive.
        
        HProof.
        inversion H1. }
        
     Check AbsorptionC.
     Check AbsorptionL.
     Check 
     Check AbsorptionPerp.
     
        (* Case LEGO ? *)
      
      
      
      inversion H5...  
        - 
           inversion Hb...
           inversion H4...
           HProof.
           inversion H2...
        - apply in_app_or in H6...
           apply InPermutation in H1...
            inversion Hb...
             inversion H6...
             rewrite H1 in H10.
             apply AbsorptionC in H10.
           rewrite <- H1 in H10...  
           HProof.
           inversion H3. 
           inversion H1...
        -    inversion Hb...
             inversion H4...
             HProof.
             inversion H8.
             inversion H2.
        -  inversion Hb...
        2:{ inversion H4. }
             inversion H7...
        2:{ inversion H11. }
             
             HProof.
             inversion H8.
             inversion H2.    
             rewrite H1 in H10.
           
          assert(CutF1: seqN th n0 (B++[F]) M (UP [F]) ->
             seqN th (S n) B [] (DW (! F ^)) ->
             seq th B M (UP [F])).
        eapply CH...

         assert(seq th B M (UP [F])).
        apply CutF1...
        apply seqtoSeqN in H...
         assert(CutF2: seqN th n B [] (UP [F^]) ->
             seqN th (S x) B M (DW ((F^)^)) ->
             seq th B ([]++M) (UP [])).
        eapply CW...
        rewrite <- (DualComplexity F)...
        rewrite <- (app_nil_l M).
        apply CutF2...
        rewrite <- ng_involutive.
        
        HProof.
        inversion H1. }    
        
        
        
        
        apply
        
             assert( seqN th n (B++[Q]) M (DW F) ->
          seqN th b B [] (DW (! Q ^)) -> seq th B M (UP [F])) as Cut.
          eapply CH...
          eapply @AbsorptionClassic with  (F:=F)...
        
      +   assert( seqN th n (B++[Q]) M (DW F) ->
          seqN th b B [] (DW (! Q ^)) -> seq th B M (UP [F])) as Cut.
          eapply CH...
          eapply @AbsorptionClassic with  (F:=F)...
      + inversion H...
        assert( seqN th n (B ++ [F]) M (DW F) ->
          seqN th b B [] (DW  (! F ^)) -> seq th B M (UP [F])) as Cut.
          eapply CH... 
          assert(Hs: seq th B M (UP [F]))...
          clear Cut.
          
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
            solveF.
     -- assert(seqN th n (B ++ [Q]) M (DW F) ->
                    seqN th b B [] (DW (! Q ^)) -> 
                     seq th B M (UP [F])) as Cut.
            eapply CH... 
           assert(Hs:seq th B M (UP [F])).
           apply Cut... 
             destruct (NegativeAtomDec F).
              2:{  eapply @AbsorptionTheory with (F:=F)... }
             inversion H...
             eapply @AbsorptionPerp' with (A:=A)...
 
  --  assert( seqN th n (B++[Q]) M (UP (FX x ::  M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (FX x :: M0))) as Cut.
              eapply CH... 
              apply Cut...
  Qed.
  
 
  Theorem CutElimination i j C A B L M N P: 
      (seqN th i B (M ++ [C]) (UP L) -> 
      seqN th j B N (UP [dual C]) -> 
      seq th B (M ++ N) (UP L)) /\
      (seqN th i B M (UP (C :: L)) -> 
      seqN th j B N (DW (dual C)) -> 
      seq th B (M ++ N) (UP L)) /\
       (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (DW P) -> 
       seqN th j B [] (DW (! (dual A))) -> 
       seq th B M (UP [P]))  /\
      (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (UP L) -> 
       seqN th j B [] (DW (! (dual A))) -> 
       seq th B M (UP L)).
  Proof with sauto;solveF;solveLL.
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
         * eapply (@Cut1 i j C L M)...
          unfold CutElimination.CutH; intros.
          eapply CutH with (m:=i0 + j0)...
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
