Require Import LL.FOLL.DyadicExc.Tactics.
Require Import LL.FOLL.Dyadic.Tactics.

Section LLAdequacy.
  Context `{OLS: OLSig}.
  
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
    - LL3exist t.
    - LL3copy F.        
 Qed.   

   Theorem LL3N_to_LL2 n B L : LL3N n B L -> LL2S B L.
Proof with sauto.
  intros.
  revert dependent B.
  revert L.
  induction n;intros...
  + inversion H...
    LL2init A.
    LL2top M.
  + inversion H...
    LL2plus1 F G M.
    LL2plus2 F G M.
    LL2with F G M.
    LL2bot M.
    LL2par F G M.
    LL2tensor F G M N.
    LL2store F M. 
    LL2exist t FX M.
    LL2forall FX M.
    LL2copy F.
    rewrite <- H1...    
  Qed.  
    
End LLAdequacy.
