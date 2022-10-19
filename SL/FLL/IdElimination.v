(** This file shows that, for any formula [F], the sequent 
[|-- [] ; []; UP([F, F ^ ])] is provable *)
Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLL.Tactics.
Require Import Lia.
Require Import Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export FLL.SL.FLL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section FLLTheory.
  Context `{OLS: OLSig}.
  Section FLLTheory.
    Section AdmissibleRules.

      Theorem InitGeneral th: 
        forall P B, isFormula P -> isFormula (dual P) -> isFormulaL B ->
             seq th B [] (UP [P;dual P]) /\ seq th ((dual P)::B) [] (UP [P]).
      Proof with subst;auto;solveLL.
        induction P;intros;split;intros;
          match goal with
          | [ H: isFormulaL ?B |- _ ] => 
            rename H into isFB   
          end;simpl...  
        * CFocus.
        * LFocus... 
        * CFocus.
        * CFocus.
        * inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.

          assert(|-- B; []; (> [P1 ^ op P2 ^;P1 & P2]))...
          eapply InvPlus with (M:=[])...
          eapply InvPlus with (M:=[])...
          change ([P1 ^; P1]) with ([P1 ^]++[P1]).
          
          apply seqtoSeqN in H1...
          destruct H1.
          eapply EquivUpArrow.
          2:{ exact H1. }
          change ([P1 ^; P1]) with ([P1 ^]++[P1]).
          eapply ForallApp...
          perm.
          eapply InvPlusComm with (M:=[])...
          change ([P2 ^; P2]) with ([P2 ^]++[P2]).
          
          apply seqtoSeqN in H2...
          destruct H2.
          eapply EquivUpArrow.
          2:{ exact H2. }
          change ([P2 ^; P2]) with ([P2 ^]++[P2]).
          eapply ForallApp...
          perm.
          
          apply seqtoSeqN in H7...
          destruct H7.
          eapply EquivUpArrow.
          2:{ exact H7. }
          change ([P1 & P2; P1 ^ op P2 ^]) with ([P1 & P2]++[P1 ^ op P2 ^]).
          eapply ForallApp...
          perm.
        * simpl.  
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.
          eapply tri_with'.
          
          eapply AbsorptionClassic with (F:=P1 ^ op P2 ^)...
          apply in_or_app...
          
          change ([P1 ^ op P2 ^; P1]) with ([P1 ^ op P2 ^]++[P1]).

          eapply tri_store'...
          
          eapply InvPlus with (M:=[])...
          change ([P1 ^;P1]) with ([P1 ^]++[P1]).

          eapply exchangeCC with (CC:=[P1 ^ op P2 ^]++B);try perm.
          eapply weakeningGen.
          
          apply seqtoSeqN in H1...
          destruct H1.
          eapply EquivUpArrow.
          2:{ exact H1. }
          change ([P1 ^ ; P1]) with ([P1 ^]++[P1]).
          eapply ForallApp...
          perm.
          
          eapply AbsorptionClassic with (F:=P1 ^ op P2 ^)...
          apply in_or_app...
          change ([P1 ^ op P2 ^; P2]) with ([P1 ^ op P2 ^]++[P2]).
          eapply tri_store'...
          
          eapply InvPlusComm with (M:=[])...
          change ([P2 ^ ; P2]) with ([P2 ^]++[P2]).
          
          eapply exchangeCC with (CC:=[P1 ^ op P2 ^]++B);try perm.
          eapply weakeningGen.
          
          apply seqtoSeqN in H2...
          destruct H2.
          eapply EquivUpArrow.
          2:{ exact H2. }
          change ([P2 ^ ; P2]) with ([P2 ^]++[P2]).
          eapply ForallApp...
          perm.    
        * 
          
          simpl.  
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.
          
          eapply tri_store'...
          eapply tri_par'...

          eapply InvTensor with (M:=[]) (M':=[]) (L:=[P1 ^]) (L':=[P2 ^])...
        * 
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.

          eapply tri_store'...
          eapply tri_dec2' with (F:=P1 -o P2 ^)...
          apply in_or_app...
          
          eapply tri_rel'...
          eapply tri_par'.
          eapply InvTensor with (M:=[]) (M':=[]) (L:=[P1^]) (L':=[P2^])...
          eapply ForallApp...
          eapply exchangeCC with (CC:=[P1 -o P2 ^]++B);try perm.
          eapply weakeningGen...

          eapply exchangeCC with (CC:=[P1 -o P2 ^]++B);try perm.
          eapply weakeningGen...
        * simpl.  
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.
          
          eapply tri_store'...
          eapply tri_with'.

          eapply InvPlus with (M:=[])...
          change ([P1  ; P1^]) with ([P1 ]++[P1 ^]).
          
          eapply InvPlusComm with (M:=[])...
        * simpl.  
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.
          
          eapply tri_store'...
          eapply tri_dec2' with (F:=P1 ^ & P2 ^)...
          apply in_or_app...
          
          eapply tri_rel'...
          eapply tri_with'...
          
          eapply InvPlus with (M:=[])...
          
          change ([P1  ; P1^]) with ([P1 ]++[P1 ^]).
          
          eapply exchangeCC with (CC:=[P1 ^ & P2 ^]++B);try perm.
          eapply weakeningGen...
          
          eapply InvPlusComm with (M:=[])...
          change ([P2  ; P2^]) with ([P2 ]++[P2 ^]).
          
          eapply exchangeCC with (CC:=[P1 ^ & P2 ^]++B);try perm.
          eapply weakeningGen...
        * simpl.
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.
          
          assert(|-- B; []; (> [ P1 ^ ** P2 ^;P1 $ P2])).
          
          eapply tri_store'...
          eapply tri_par'.
          eapply InvTensor with (M:=[]) (M':=[]) (L:=[P1]) (L':=[P2])...
          
          apply seqtoSeqN in H1...
          destruct H1.
          eapply EquivUpArrow.
          2:{ exact H1. }
          change ([P1^  ; P1]) with ([P1^ ]++[P1 ]).
          eapply ForallApp...
          perm.   
          
          apply seqtoSeqN in H2...
          destruct H2.
          eapply EquivUpArrow.
          2:{ exact H2. }
          change ([P2^  ; P2]) with ([P2^ ]++[P2 ]).
          eapply ForallApp...
          perm.   
          
          
          apply seqtoSeqN in H7...
          destruct H7.
          eapply EquivUpArrow.
          2:{ exact H7. }
          
          change ([P1 $ P2; P1 ^ ** P2 ^]) with ([P1 $ P2]++[P1 ^ ** P2 ^]).
          eapply ForallApp...
          perm.     
        * simpl.
          inversion H...
          inversion H0...
          generalize(IHP1 B H3 H5 isFB);intros.
          generalize(IHP2 B H4 H6 isFB);intros.
          
          eapply tri_par'...
          eapply AbsorptionClassic with (F:=P1 ^ ** P2 ^)...
          apply in_or_app...
          change ([P1 ^ ** P2 ^; P1;P2]) with ([P1 ^ ** P2 ^]++[P1]++[P2]).
          
          
          eapply tri_store'...
          eapply InvTensor with (M:=[]) (M':=[]) (L:=[P1]) (L':=[P2])...

          eapply ForallApp...
          eapply exchangeCC with (CC:=[P1 ^ ** P2 ^]++B);try perm.
          eapply weakeningGen...
          
          apply seqtoSeqN in H1...
          destruct H1.
          eapply EquivUpArrow.
          2:{ exact H1. }
          change ([P1^  ; P1]) with ([P1^ ]++[P1 ]).
          eapply ForallApp...
          perm.
          
          
          eapply exchangeCC with (CC:=[P1 ^ ** P2 ^]++B);try perm.
          eapply weakeningGen...
          
          apply seqtoSeqN in H2...
          destruct H2.
          eapply EquivUpArrow.
          2:{ exact H2. }
          change ([P2^  ; P2]) with ([P2^ ]++[P2 ]).
          eapply ForallApp...
          perm.   
        * simpl.
          inversion H...
          inversion H0...
          generalize(IHP B H2 H3 isFB);intros.
          
          eapply tri_store'...    
          eapply tri_quest'...
          eapply tri_dec1' with (F:=! P)...
          eapply tri_bang'...
        * simpl.
          inversion H...
          inversion H0...
          generalize(IHP B H2 H3 isFB);intros.
          
          eapply tri_store'...    
          eapply tri_dec2' with (F:=? P^)...
          apply in_or_app...
          eapply tri_rel'...
          eapply tri_quest'...
          eapply tri_dec1' with (F:=! P)...
          eapply tri_bang'...   
          apply exchangeCC with (CC:=[? P ^] ++ (B ++ [P ^]));try perm.
          eapply weakeningGen...
        * simpl.
          inversion H...
          inversion H0...
          generalize(IHP B H2 H3 isFB);intros.
          
          eapply tri_quest'...
          eapply tri_store'...
          eapply tri_dec1' with (F:=! P^)...
          eapply tri_bang'.
          
          eapply AbsorptionClassic with (F:=P)...
          apply in_or_app...
          change ([P ; P^]) with ([P ]++[P^]).
          eapply exchangeCC with (CC:=[P]++B);try perm.
          eapply weakeningGen...
        * simpl.
          inversion H...
          inversion H0...
          generalize(IHP B H2 H3 isFB);intros.
          
          eapply tri_quest'...
          eapply tri_dec2' with (F:=! P^)...
          apply in_or_app. left. apply in_or_app...
          eapply tri_bang'.
          
          eapply AbsorptionClassic with (F:=P)...
          
          apply in_or_app...
          change ([P ; P^]) with ([P ]++[P^]).
          
          
          eapply exchangeCC with (CC:=([P]++[! P ^]) ++ B);try perm.
          eapply weakeningGen...   
        *
          inversion H0...
          inversion H1...

          assert(|-- B; []; (> [(F{ o}) ^;F{ o}])).
          eapply tri_store'...
          eapply tri_fx';intros...
          
          generalize(H4 x);intros. 
          generalize(H6 x);intros.
          
          generalize(H x B H7 H8 isFB);intros.
          
          eapply InvEx with (M:=[]) (t:=x)...
          
          change ([(o x)^ ; (o x)]) with ([(o x)^  ]++[(o x)]).
          apply seqtoSeqN in H9...
          destruct H9.
          eapply EquivUpArrow.
          2:{ exact H9. }
          
          change ([(o x)^ ; (o x)]) with ([(o x)^  ]++[(o x)]).
          eapply ForallApp...
          perm.
          
          apply seqtoSeqN in H2...
          destruct H2.
          eapply EquivUpArrow.
          2:{ exact H2. }
          change ([F{ o} ; E{ fun x0 : expr con => (o x0) ^}]) with ([F{ o} ]++[E{ fun x0 : expr con => (o x0) ^}]).
          eapply ForallApp...
          
          simpl.
          perm.
        *
          inversion H0...
          inversion H1...

          assert(|-- B++[F{ o} ^]; []; (> [F{ o}])).
          eapply tri_fx';intros...
          
          generalize(H4 x);intros. 
          generalize(H6 x);intros.
          
          generalize(H x B H7 H8 isFB);intros.
          eapply AbsorptionClassic with (F:=E{ fun x0 : expr con => (o x0) ^})...
          apply in_or_app...
          change ([E{ fun x0 : expr con => (o x0) ^}; o x]) with ([E{ fun x0 : expr con => (o x0) ^}]++[(o x)]).
          eapply tri_store'...
          
          eapply InvEx with (M:=[]) (t:=x)...
          change ([(o x)^ ; (o x)]) with ([(o x)^  ]++[(o x)]).
          
          
          eapply exchangeCC with (CC:=[E{ fun x0 : expr con => (o x0) ^}]++B);try perm.
          eapply weakeningGen...
          
          apply seqtoSeqN in H9...
          destruct H9.
          eapply EquivUpArrow.
          2:{ exact H9. }
          change ([(o x)^ ; (o x)]) with ([(o x)^  ]++[(o x)]).
          eapply ForallApp...
          perm.
          
          exact H2.
        *
          inversion H0...
          inversion H1...

          eapply tri_store'...
          eapply tri_fx';intros...
          
          generalize(H4 x);intros. 
          generalize(H6 x);intros.
          
          generalize(H x B H7 H8 isFB);intros.
          
          eapply InvEx with (M:=[]) (t:=x)...
          
        *
          inversion H0...
          inversion H1...

          eapply tri_store'...
          eapply AbsorptionClassic with (F:=F{ fun x : expr con => (o x) ^})...
          apply in_or_app; right.
          firstorder.
          
          eapply Forall_forall;intros x Hx;
            inversion Hx...
          intro. inversion H7.
          eapply tri_fx';intros...

          generalize(H4 x);intros. 
          generalize(H6 x);intros.
          
          generalize(H x B H7 H8 isFB);intros.
          
          eapply InvEx with (M:=[]) (t:=x)...
          change ([(o x) ; (o x^)]) with ([(o x)  ]++[(o x)^]).
          
          
          eapply exchangeCC with (CC:=[F{ fun x0 : expr con => (o x0) ^}]++B);try perm.
          eapply weakeningGen...
      Qed.  

      Theorem FLLGeneralInit: 
        forall P B, isFormula P -> isFormula (dual P) -> isFormulaL B -> |-- B; [] ; UP [P;dual P].
      Proof.
        intros.
        apply InitGeneral;auto. 
      Qed.
      
      Theorem FLLGeneralInit1: 
        forall P B, isFormula P -> isFormula (dual P) -> isFormulaL B -> isNotAsyncL [dual P] -> 
                    |-- B; [dual P] ; DW P.
      Proof.
        intros.
        destruct (PositiveOrRelease P).
        * 
          apply PositiveDualRelease in H3.
          inversion H2;subst;auto.
          inversion H3;subst;
            try solve [match goal with
                       | [ H: ?A = (?P ^), H': Notasynchronous  (?P ^) |- _ ] => 
                         assert (asynchronous A) by constructor;
                         rewrite <- H in H'; contradiction
                       end].
          assert(P = perp A).
          rewrite ng_involutive.
          assert((perp A) ^ =atom A) by auto.
          rewrite H4.
          rewrite H5.
          rewrite <- ng_involutive;auto.
          subst.
          eapply tri_init1'.

        *
          inversion H2;subst;auto. 
          eapply tri_rel';auto.
          assert (|-- B; [] ; UP [P;dual P]).
          apply FLLGeneralInit;auto.
          eapply EquivUpArrow2 with (L':=[P^; P]) in H4; try perm.
          
          apply ReleaseDualPositive in H3.
          inversion H4;subst;
            
            try solve [match goal with
                       | [ H: _ = (?P ^), H':positiveFormula (?P ^) |- _ ] => 
                         rewrite <- H in H'; inversion H'
                       end].
          simpl in H11;auto.
          
          change ([P ^; P]) with ([P ^]++[P]).
          eapply ForallApp;subst;auto...
      Qed.
      
      
      
      Theorem FLLEquiv : forall F, isFormula F -> isFormula (dual F) -> |-- []; []; (> [F == F]).
      Proof with subst;auto;solveF.
        intros. 
        apply tri_with'; eapply tri_par';
          eapply EquivUpArrow2 with (L:=[F;F^]).
        change ([F ^; F]) with ([F ^]++ [F]).
        apply ForallApp...
        apply FLLGeneralInit...
        perm.
        change ([F ^; F]) with ([F ^]++ [F]).
        apply ForallApp...
        apply FLLGeneralInit...
        perm.
      Qed.
      
      
      Theorem FLLEquiv' : forall F B, isFormulaL B -> isFormula F -> isFormula (dual F) -> 
                                      |-- B; []; (> [F == F]).
      Proof with subst;auto;solveF.
        intros. 
        apply tri_with'; eapply tri_par';
          eapply EquivUpArrow2 with (L:=[F;F^]).
        change ([F ^; F]) with ([F ^]++ [F]).
        apply ForallApp...
        apply FLLGeneralInit...
        perm.
        change ([F ^; F]) with ([F ^]++ [F]).
        apply ForallApp...
        apply FLLGeneralInit...
        perm.
      Qed.

    End AdmissibleRules.
  End FLLTheory.
End FLLTheory.