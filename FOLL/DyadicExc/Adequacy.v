Require Import LL.FOLL.Dyadic.Tactics.
Require Import LL.FOLL.DyadicExc.Tactics.


Section LLAdequacy.
  Context `{OLS: OLSig}.
  
Import DyadicExcTactics.

Theorem LL2N_to_LL3S n B L : LL2N n B L -> LL3S B L.
Proof with sauto.
  intros.
  revert dependent B.
  revert L.
  induction n;intros...
  + inversion H...
    rewrite H0...
    rewrite H0...
  + inversion H...
    all: try match goal with
      | H: Permutation ?L _ |- LL3 |-- ?B; ?L => rewrite H;sauto
     end.
    - LLexists t.
    - LLcopy F.        
 Qed.   

Import DyadicTactics.

   Theorem LL3N_to_LL2 n B L : LL3N n B L -> LL2S B L.
Proof with sauto.
  intros.
  revert dependent B.
  revert L.
  induction n;intros...
  + inversion H...
    LLinit A.
    LLtop M.
  + inversion H...
    LLleft F G M.
    LLright F G M.
    LLwith F G M.
    LLbot M.
    LLpar F G M.
    LLtensor F G M N.
    LLstore F M. 
    LLexists t FX M.
    LLforall FX M.
    LLcopy F.
    rewrite <- H1...    
  Qed.  
    
End LLAdequacy.

