(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export LL.Misc.Hybrid.
Require Export LL.SL.Focused.FLLTactics.
Require Import Lia.
Require Import LL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export LL.SL.Focused.InvPositivePhase.

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
      (seqN th i B (M ++ [C]) (UP L) -> seqN th j B N (UP [dual C]) -> seq th B (M ++ N) (UP L)) /\
      (seqN th i B M (UP (C :: L)) -> seqN th j B N (DW (dual C)) -> seq th B (M ++ N) (UP L)) /\
       (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (DW P) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP [P]))  /\
      (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (UP L) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP L)). 
    
  Definition CutH (w h: nat) :=  
    forall i j C A P M N L B, 
    i + j < h ->
    complexity C = w ->
      (seqN th i B (M ++ [C]) (UP L) -> seqN th j B N (UP [dual C]) -> seq th B (M ++ N) (UP L)) /\
      (seqN th i B M (UP (C :: L)) -> seqN th j B N (DW (dual C)) -> seq th B (M ++ N) (UP L)) /\
      (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (DW P) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP [P]))   /\
      (S (complexity A) = complexity C ->
       seqN th i (B ++ [A]) M (UP L) -> seqN th j B [] (DW (! (dual A))) -> seq th B M (UP L)). 

 Lemma Derivation1 D M F : 
 seq th D M (DW F) -> seq th D M (UP [F]).
 Proof with sauto;solveLL.
 intros.
 inversion H...
 all:LFocus.
Qed.
 
          
Theorem Cut1  a b P L M N B : 
CutH (complexity P) (a+b) -> 
  seqN th a B (M ++ [P]) (UP L) ->
  seqN th b B N (UP [P ^]) ->
  seq th B (M ++ N) (UP L ).
Proof with sauto;solveLL.  
 intros CH Ha Hb.
 inversion Ha...
 * assert(seqN th n B (M ++ [P]) (UP (F  :: M0)) ->
          seqN th b B N (UP [dual P]) ->
            seq th B (M ++ N) (UP (F :: M0))) as CutF.
           eapply CH...
                    
           apply CutF...             

 * assert(seqN th n B (M ++ [P]) (UP (G  :: M0)) ->
          seqN th b B N (UP [dual P]) ->
            seq th B (M ++ N) (UP (G :: M0))) as CutG.
           eapply CH...
                    
           apply CutG...           
 
 * assert(seqN th n B (M ++ [P]) (UP M0) ->
          seqN th b B N (UP [dual P]) ->
            seq th B (M ++ N) (UP M0)) as Cut.
           eapply CH...
                    
           apply Cut...
 * assert(seqN th n B (M ++ [P]) (UP (F :: G :: M0)) ->
          seqN th b B N (UP [dual P]) ->
            seq th B (M ++ N) (UP (F :: G :: M0))) as Cut.
           eapply CH...
                    
           apply Cut...                                       
  

 * assert(seqN th n (B ++ [(F)]) (M ++ [P]) (UP M0) ->
            seqN th b (B ++ [(F)]) N (UP [dual P]) ->
              seq th (B ++ [(F)]) (M ++ N) (UP M0)) as Cut.
           eapply CH...
           apply Cut...
           apply weakeningGenN_rev...
  *  assert(seqN th n B (M ++ [P]) (UP (FX x :: M0)) ->
           seqN th b B N (UP [dual P]) ->
             seq th B (M ++ N) (UP (FX x :: M0))) as Cut.
           eapply CH...
              
           apply H4 in properX...

 * assert(seqN th n B ((M ++ [F]) ++ [P]) (UP M0) ->
          seqN th b B N (UP [dual P]) ->
            seq th B ((M ++ [F]) ++ N) (UP M0)) as Cut.
           eapply CH...
                    
           LLPerm((M ++ [F]) ++ N).
           apply Cut...
           LLExact H4.
 
 
 * checkPermutationCases H1.
   2:{ inversion H1...
       rewrite H2.
       assert(seqN th b B N (UP [dual P]) ->
              seqN th n B L' (DW (dual (dual P))) ->
                seq th B (N++L') (UP [])) as Cut.
       eapply CH...
       rewrite <- ng_involutive in Cut...
       LLPerm(N ++ L')... }
       
       inversion H5...
            1:{ 
              inversion Hb...
              HProof. }
               
            3:{ rewrite H3 in H2.
              checkPermutationCases H2.
              - 
              destruct(PositiveOrNegative F0).
              { (* first *) 
              assert(seqN th (S n0) B ((F0::x0)++[P]) (UP [])).
              LFocus F0 (x0++[P])...
              HProof. 
              rewrite H1.
              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H6.
              LLPerm(G ⊗ F0::N0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
              
              apply Derivation1.
              HProof.
             
              assert(seqN th (S n0) B ((F0::x0) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x0) ++ N) (UP [ ])) as Cut.
                eapply CH... 
                rewrite <- (app_nil_l [F0]).
               apply UpExtension'...
               }
             { (* second *) 
              inversion H4;CleanContext...
              rewrite H1.
              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H6.
              LLPerm(G ⊗ F0::N0++(x0++N)).
                rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
                apply Derivation1.
              HProof.  
                 assert(seqN th n B (x0 ++ [P]) (UP [F0]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x0 ++ N) (UP [F0])) as Cut.
                eapply CH... 
                apply Cut...
                HProof. } 
             - 
              destruct(PositiveOrNegative G).
              { (* first *) 
              assert(seqN th (S n0) B ((G::x0)++[P]) (UP [])).
              LFocus G (x0++[P])...
              rewrite <- H2...
              rewrite H1.
              rewrite <- H6.
              LLPerm(F0⊗ G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
              apply Derivation1.
              HProof.
              assert(seqN th (S n0) B ((G::x0) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x0) ++ N) (UP [ ])) as Cut.
                eapply CH...
                  rewrite <- (app_nil_l [G]).
               
               apply UpExtension'...
             }
             { (* second *) 
              inversion H9;CleanContext...
              rewrite H1.
              rewrite <- H6.
              LLPerm(F0⊗ G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor...
                apply Derivation1.
             HProof.   
              assert(seqN th n B (x0++ [P]) (UP [G ]) ->
                          seqN th b B N (UP [dual P]) ->
                         seq th B (x0 ++ N) (UP [G])) as Cut.
                 eapply CH... 
                
                apply Cut... HProof.  }   
                }
    -   destruct(PositiveOrNegative F0).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                 FLLstore. 
                assert( seqN th (S n0) B ((F0::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 LFocus F0. HProof.
              }
             {   inversion H7;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                assert(seqN th n B (x ++ [P]) (UP [F0]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [F0])) as Cut.
                eapply CH...
               apply Cut... HProof.  
               } 
  -    destruct(PositiveOrNegative G).   
       {         rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                 FLLstore. 
                
                assert(seqN th (S n0) B ((G::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x ) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 LFocus G. HProof. }
             {   inversion H7;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                assert(seqN th n B (x ++ [P]) (UP [G]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [G])) as Cut.
                eapply CH...
               apply Cut... HProof.  
               }
   -   destruct(PositiveOrNegative (FX t)).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                 FLLstore. 
                 assert( seqN th (S n0) B ((FX t::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((FX t::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 LFocus (FX t). HProof. }
             {   inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                assert(seqN th n B (x ++ [P]) (UP [FX t]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [FX t])) as Cut.
                eapply CH...
               apply Cut... HProof. }
       -  apply PositiveNotNegative in H0. contradiction. 
           
*  destruct(PositiveOrNegative F).
   2:{ inversion H5;CleanContext... apply @AbsorptionClassic' with (F:=F)...
        assert(seqN th n0 B (M ++ [P]) (UP [F]) ->
                seqN th b B N (UP [dual P]) ->
                  seq th B (M ++ N) (UP [F])) as Cut.
       eapply CH... 
       apply Cut... } 
       inversion H5...
       -  apply @AbsorptionClassic' with  (F:=perp A)...
          inversion Hb...
          HProof.
  -  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusC with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'...
        assert(seqN th (S n0) B ((F0::M) ++ [P]) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((F0::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0. }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusC with (F:=F0) (G:=G) ...
        assert( seqN th n B (M ++ [P]) (UP [F0]) ->
                seqN th b B N (UP [dual P]) ->
                 seq th B (M ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut... }
  -  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusCComm with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'...
        assert(seqN th (S n0) B ((G::M) ++ [P]) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((G::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus G.  }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusCComm with (F:=F0) (G:=G)...
        assert( seqN th n B (M ++ [P]) (UP [G]) ->
                seqN th b B N (UP [dual P]) ->
                 seq th B (M ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut... }

          
       - checkPermutationCases H3.
          {  destruct(PositiveOrNegative F0).
             { (* first *) 
               rewrite <- H6.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'...
                
                 assert(seqN th (S n0) B ((F0::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0. HProof. 
               apply Derivation1.
               HProof.  }
            { (* first *) 
               rewrite <- H6.
               inversion H4;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
                 assert(seqN th n B (x ++ [P]) (UP [F0]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut...
                HProof.
               apply Derivation1.
                HProof.
              } }
          {  destruct(PositiveOrNegative G).
             { (* first *) 
               rewrite <- H6.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
               rewrite <- (app_nil_l [G]).
               apply UpExtension'...
                 assert(seqN th (S n0) B ((G::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus G.  HProof.
            }
            { (* first *) 
               rewrite <- H6.
               inversion H9;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
                 assert(seqN th n B (x ++ [P]) (UP [G]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut...  HProof.
               } }
  -  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExC with  (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'...
        assert(seqN th (S n0) B ((FX t::M) ++ [P]) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((FX t::M) ++ N) (UP [ ])) as Cut.
                eapply CH...
        LLPerm((FX t :: M) ++ N)...
        apply Cut... 
        rewrite <- app_comm_cons.
        LFocus (FX t).  }
     {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExC with (t:=t) (FX:=FX)...
        assert( seqN th n B (M ++ [P]) (UP [FX t]) ->
                seqN th b B N (UP [dual P]) ->
                 seq th B (M ++ N) (UP [FX t])) as Cut.
                eapply CH...
                apply Cut... }
    -  apply PositiveNotNegative in H. contradiction. 
              
*
destruct(PositiveOrNegative F).
    2:{ inversion H5;CleanContext...
        destruct (NegativeAtomDec F).
        
        assert(False). 
        inversion H;subst;solvePolarity... 
        contradiction.
        apply @AbsorptionTheory with (F:=F)...
        assert(seqN th n0 B (M ++ [P]) (UP [F]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B (M ++ N) (UP [F])) as Cut.
                         
                eapply CH...
                 
                apply Cut... }
    inversion H5...
    -   eapply @AbsorptionPerp' with (A:=A)...
        inversion Hb...
        HProof.
  -  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusT with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'...
        assert(seqN th (S n0) B ((F0::M) ++ [P]) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((F0::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0. }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusT with (F:=F0) (G:=G) ...
        assert( seqN th n B (M ++ [P]) (UP [F0]) ->
                seqN th b B N (UP [dual P]) ->
                 seq th B (M ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut... }
  -  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusTComm with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'...
        assert(seqN th (S n0) B ((G::M) ++ [P]) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((G::M) ++ N) (UP [ ])) as Cut.
                eapply CH... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus G.  }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
        assert( seqN th n B (M ++ [P]) (UP [G]) ->
                seqN th b B N (UP [dual P]) ->
                 seq th B (M ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut... }

        
          - checkPermutationCases H3.
          {  destruct(PositiveOrNegative F0).
             { (* first *) 
               rewrite <- H6.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'...
                
                 assert(seqN th (S n0) B ((F0::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((F0::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0. HProof. 
               apply Derivation1.
               HProof.  }
            { (* first *) 
               rewrite <- H6.
               inversion H4;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
                 assert(seqN th n B (x ++ [P]) (UP [F0]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [F0])) as Cut.
                eapply CH...
                apply Cut...
                HProof.
               apply Derivation1.
                HProof.
              } }
          {  destruct(PositiveOrNegative G).
             { (* first *) 
               rewrite <- H6.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
               rewrite <- (app_nil_l [G]).
               apply UpExtension'...
                 assert(seqN th (S n0) B ((G::x) ++ [P]) (UP [ ]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B ((G::x) ++ N) (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus G.  HProof.
            }
            { (* first *) 
               rewrite <- H6.
               inversion H9;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B)...
               apply Derivation1.
                HProof.
                 assert(seqN th n B (x ++ [P]) (UP [G]) ->
                       seqN th b B N (UP [dual P]) ->
                         seq th B (x ++ N) (UP [G])) as Cut.
                eapply CH...
                apply Cut...  HProof.
               } }
  -  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExT with  (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'...
        assert(seqN th (S n0) B ((FX t::M) ++ [P]) (UP [ ]) ->
                  seqN th b B N (UP [dual P]) ->
                    seq th B ((FX t::M) ++ N) (UP [ ])) as Cut.
                eapply CH...
       rewrite app_comm_cons...
       apply Cut...
       rewrite <- app_comm_cons...
       LFocus (FX t). }
          {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExT with (t:=t) (FX:=FX)...
        assert( seqN th n B (M ++ [P]) (UP [FX t]) ->
                seqN th b B N (UP [dual P]) ->
                 seq th B (M ++ N) (UP [FX t])) as Cut.
                eapply CH...
                apply Cut... }
                
  -  apply PositiveNotNegative in H. contradiction. 

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
 * assert(N=[]).
   inversion Hb;solvePolarity...
   subst.
    assert( seqN th n (B ++ [F]) M  (UP L) -> 
           seqN th b B [] (DW (! F ^)) -> 
             seq th B M  (UP L)) as UCCut.
    eapply CH... 
    rewrite app_nil_r...
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
    
 *  apply NotAsynchronousPosAtoms in H4...
   assert(negativeFormula (P ^)).
   apply PositiveDualNegative in H...
 
     inversion Hb;subst; try match goal with
       [ H: _= dual ?C , H2: negativeFormula (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
  
    assert( seqN th n B (M ++ [P]) (UP L) -> 
            seqN th n0 B N (UP [dual P]) -> 
             seq th B (M ++ N) (UP L)) as ULCut.
   eapply CH... 
   apply ULCut...
   LLExact H5.
   inversion H...
   inversion Hb...
   HProof.
   apply InPermutation in H4...
   rewrite H4 in H5.

   eapply AbsorptionC in H5.
   HProof.
   solvePolarity. 
 Qed.
 
 Theorem Cut3 a b P Q F L B:
    CutH (complexity P) (a+b) -> CutW  (complexity P) ->
    S (complexity Q) = complexity P ->
    seqN th a (B ++ [Q]) L (DW F) -> 
    seqN th b B [] (DW (! Q ^)) ->   
    seq th B L (UP [F]).
  Proof with sauto;solveLL.
  intros HC WC Hc' Ha Hb.
    inversion Ha...
    * apply InPermutation in H3... 
      checkPermutationCases H3.
      { solveLL. LFocus (perp A). 
        solveLL. rewrite H0... } 
      { inversion H0...
        simpl in Hb.
        inversion Hb;solvePolarity...
        inversion H3...
        HProof. } 
      *   assert(seqN th n (B ++ [Q]) L (DW F0) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B  L (UP [F0])).
        eapply HC...
        apply InvPlus...
    *   assert(seqN th n (B ++ [Q]) L (DW G) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B  L (UP [G])).
        eapply HC...
        apply InvPlusComm...
   *  assert(CutF: seqN th n (B ++ [Q]) M (DW F0) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B M (UP [F0])).
        eapply HC... 
        
      assert(CutG: seqN th n (B ++ [Q]) N (DW G) ->
             seqN th b B [] (DW (! Q ^)) ->
             seq th B  N (UP [G])).
        eapply HC... 
      rewrite H0.
      rewrite <- (app_nil_l []).  
        eapply @InvTensor with (B:=B)...
    *   assert(
              seqN th n (B ++ [Q]) [] (UP [F0]) ->
             seqN th b B [] (DW (!  Q ^)) -> 
               seq th B [] (UP [F0])).
                                       
        eapply HC...
        solveLL.
        LFocus.
   *    
   assert(Hc:
              seqN th n (B ++ [Q]) L (DW (FX t)) ->
             seqN th b B [] (DW (! Q ^)) -> 
               seq th B L (UP [FX t])).
                                       
        eapply HC... 
        apply Hc in H5...
        eapply InvEx with (t:=t)...
       *   assert(Hc:
              seqN th n (B ++ [Q]) L (UP [F]) ->
             seqN th b B [] (DW (!  Q ^)) -> 
               seq th B L (UP [F])).
                                       
        eapply HC...
        apply Hc... 
  Qed. 

Theorem Cut4  a b P Q L M B  : 
CutH (complexity P) (a+b) -> CutW (complexity P) ->    S (complexity Q) = complexity P ->
  seqN th a (B++[Q]) M (UP L) ->
  seqN th b B [] (DW (! Q ^)) ->
  seq th B M (UP L).
Proof with sauto;solveLL.  
  intros CH CW Hc Ha Hb.
  inversion Ha...  
  --  assert( seqN th n (B++[Q]) M (UP (F :: M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (F :: M0))) as Cut.
              eapply CH... 
              apply Cut... 
  --  assert( seqN th n (B++[Q]) M (UP (G :: M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (G ::M0))) as Cut.
              eapply CH... 
              apply Cut... 
  --  assert( seqN th n (B++[Q]) M (UP M0) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP M0)) as Cut.
              eapply CH...
              apply Cut... 
  --  assert( seqN th n (B++[Q]) M (UP (F :: G :: M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (F :: G ::M0))) as Cut.
              eapply CH...  
              apply Cut...

  --  assert( seqN th n ((B ++ [F]) ++ [Q]) M (UP M0) ->
              seqN th b (B ++ [F]) [] (DW (! Q ^)) -> seq th (B ++ [F]) M (UP M0)) as Cut.
              eapply CH... 
              LLPerm(B  ++ [F])...
              apply Cut...
              LLExact H3.
              apply weakeningGenN_rev...
  --  assert( seqN th n (B++[Q]) M (UP (FX x ::  M0)) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B M (UP (FX x :: M0))) as Cut.
              eapply CH... 
              apply Cut...  
--  assert( seqN th n (B++[Q]) (F::M)  (UP M0) ->
              seqN th b B [] (DW (! Q ^)) -> seq th B (F::M) (UP M0)) as Cut.
              eapply CH... 
              apply Cut...
  --
   destruct (PositiveOrNegative F).
     assert( seqN th n (B++[Q]) L' (DW F) ->
             seqN th b B [] (DW (! Q ^)) -> seq th B L' (UP [F])) as Cut.
     eapply CH...
     assert( seq th B L' (UP [F])).
     apply Cut...
     inversion H2;subst;try solve [inversion H].
     rewrite <- H1.
       HProof. 
     inversion H5;CleanContext...
     rewrite <- H1.
     LFocus...
     assert( seqN th n0 (B++[Q]) L' (UP [F]) ->
             seqN th b B [] (DW (! Q ^)) -> seq th B L' (UP [F])) as Cut.
     eapply CH...
     apply Cut...
  --  apply in_app_or in H1...
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
            solvePolarity.
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
