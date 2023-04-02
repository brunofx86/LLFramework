(** This file shows that, for any formula [F], the sequent 
[|-- [] ; []; UP([F, F ^ ])] is provable *)
Require Export LL.Framework.SL.FLL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section FLLTheory.
  Context `{OLS: OLSig}.
    Section AdmissibleRules.


Ltac LLPermA M :=
    match goal with
    | [ |- flls _ _ _ ?X ] =>
     eapply @EquivUpArrow2 with (L:=M);[| | perm]  
  end;auto.

 Theorem InvTensorS th: forall B PF PG F G,
        flls th B [] (UP [PF;F]) -> 
        flls th B [] (UP [PG;G]) -> 
        flls th B [F ⊗ G] (UP [PF;PG]) .
    Proof with sauto;solvePolarity;solveLL.
      intros.
      change [F ⊗ G] with (F ⊗ G::[]++[]).
       change [PF ;PG] with ([PF]++[PG]).
      eapply  InvTensor...   
Qed.

Theorem InvTensorCS th: forall B PF PG F G,
        flls th B [] (UP [PF;F]) -> 
        flls th B [] (UP [PG;G]) -> 
        flls th (F ⊗ G::B) [] (UP [PF;PG]) .
    Proof with sauto;solvePolarity;solveLL.
      intros. 
      change (flls th (F ⊗ G :: B) [] (UP [PF; PG])) with 
                   (flls th (F ⊗ G :: B) ([]++[]) (UP ([PF] ++ [PG]))).
      eapply  InvTensorC with (F:=F) (G:=G)...
     1-2: apply weakening...   
Qed.

      Theorem InitGeneral th: 
        forall P B, isFormula P -> isFormula (dual P) -> isFormulaL B ->
             flls th B [] (UP [P;dual P]) .
      Proof with sauto;solveLL.
        induction P;intros;intros;
          match goal with
          | [ H: isFormulaL ?B |- _ ] => 
            rename H into isFB   
          end;simpl...
       -   
          inversion H...
          inversion H0...
          pose proof (IHP1 B H3 H5 isFB);sauto.
          LLPermA [P1 ^ ⊕ P2 ^;P1]...
          eapply InvPlus with (M:=[])...
       -   
          inversion H...
          inversion H0...
          pose proof (IHP2 B H4 H6 isFB);sauto.
          LLPermA [P1 ^ ⊕ P2 ^;P2]...
          eapply InvPlusComm with (M:=[])...
       -   
          inversion H...
          inversion H0...
          pose proof (IHP1 B H3 H5 isFB);sauto.
          pose proof (IHP2 B H4 H6 isFB);sauto.
          eapply InvTensorS. 
          LLPermA [P1; P1 ^]...
          LLPermA [P2; P2 ^]...
       -   
          inversion H...
          inversion H0...
          pose proof (IHP1 B H3 H5 isFB);sauto.
          eapply InvPlus with (M:=[])...
         simpl. LLPermA [P1; P1 ^]...
       -   
          inversion H...
          inversion H0...
          pose proof (IHP2 B H4 H6 isFB);sauto.
          eapply InvPlusComm with (M:=[])...
         simpl. LLPermA [P2; P2 ^]...
       -   
          inversion H...
          inversion H0...
          LLPermA [P1 ^ ⊗ P2 ^; P1;P2]...
          pose proof (IHP1 B H3 H5 isFB);sauto.
          pose proof (IHP2 B H4 H6 isFB);sauto.
          eapply InvTensorS... 
       -   
          inversion H...
          inversion H0...
          pose proof (IHP B H2 H3 isFB);sauto.
          LFocus...
         eapply AbsorptionClassic with (F:=P ^)...
         eapply weakeningGen_rev...
       -   
          inversion H...
          inversion H0...
          pose proof (IHP B H2 H3 isFB);sauto.
          LFocus...
         eapply AbsorptionClassic with (F:=P)...
         eapply weakeningGen_rev...
         LLPermA [P  ; P^]...
        apply Forall_app...
       - 
          inversion H0...
          inversion H1...
          pose proof (H4 x). pose proof (H6 x). clear H4 H6.
          pose proof (H x B H2 H7 isFB);sauto.
         LLPermA [∃{ fun x0 : expr con => (o x0) ^}; o x ]...
          eapply InvEx with (M:=[]) (t:=x)...
       - 
          inversion H0...
          inversion H1...
          pose proof (H4 x). pose proof (H6 x). clear H4 H6.
          pose proof (H x B H2 H7 isFB);sauto.
          eapply InvEx with (M:=[]) (t:=x)...
          LLPermA [o x; dual ( o x) ]...
          apply Forall_app...
Qed.
       
     Theorem FLLGeneralInit1 th: 
        forall P B, isFormula P -> isFormula (dual P) -> isFormulaL B -> positiveLFormula P -> 
                  flls th  B [P] (DW (dual P)).
      Proof with sauto;solvePolarity.
        intros.
assert(flls th  B [] (UP [P; dual P])). 
apply InitGeneral...
inversion H3...
  destruct (PositiveOrNegative P)...
 FLLrelease... 
  apply PositiveDualNegative in H2...
inversion H2...

simpl...
Qed.

(* 
      Theorem FLLEquiv th : forall F, isFormula F -> isFormula (dual F) -> flls th [] []  (UP [F == F]).
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
 *)
    End AdmissibleRules.
  End FLLTheory. 