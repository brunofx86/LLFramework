Require Import LL.FOLL.Dyadic.CutElimination.
Require Import LL.FOLL.Dyadic.Tactics.

Import DyadicTactics.
Set Implicit Arguments.

Section InvRules.

  Context `{OLS: OLSig}.

(******************************************************)
(*                    INVERTIBILITY: RULE BOT                     *)
(******************************************************)

Lemma invertibility_bot : forall B M, LL2S B  (Bot::M) -> LL2S B  M.
Proof with simpl;auto.
  intros.
  eapply CutLL2' with (C:=One) (M:=[]) (N:=M)...
Qed.

(*******************************************************)
(*                    INVERTIBILITY: RULE PAR                      *)
(*******************************************************)

Lemma invertibility_par : forall B M F G, 
isFormula F -> isFormula (dual F) ->
isFormula G -> isFormula (dual G) ->
                            LL2S B  (F ⅋ G::M) -> LL2S B  (F::G::M).
Proof with simpl;auto.
  intros.
  assert(LL2 |-- B; M ++ [F; G]).
  eapply CutLL2' with (C:=F ⅋ G) (M:=M) (N:=[F;G])...
  LLtensor (dual F) (dual G) [F] [G].
  1-2: rewrite perm_takeit_8.
  1-2: apply LLinitGen...
rewrite Permutation_app_comm in H4...
Qed.

(********************************************************)
(*                    INVERTIBILITY: RULE QUEST                    *)
(********************************************************)

Lemma invertibility_store : forall B M F,
isFormula F -> isFormula (dual F) ->
                            LL2S B  (? F::M) -> LL2S (F::B)  M.
Proof with simpl;auto.
  intros. 
  eapply CutLL2' with (C:=! (dual F)) (M:=[]) (N:=M)...
  constructor.
  LLcopy F...
  apply LLinitGen...
  rewrite <- ng_involutive.
  apply LL2weakening... 
Qed.
  
(********************************************************)
(*                    INVERTIBILITY: RULE WITH                     *)
(********************************************************)

Lemma invertibility_with : forall B M F G, 
      isFormula F -> isFormula (dual F) ->
      isFormula G -> isFormula (dual G) ->
     LL2S B (F & G::M) -> LL2S B (F::M) /\ LL2S B (G::M).
Proof with simpl;sauto.
  intros...
  - assert(LL2 |-- B; M ++ [F]).
    eapply CutLL2' with (C:=F & G) (M:=M) (N:=[F])...
   LLleft (dual F) (dual G) [F].
   rewrite perm_takeit_8.
   apply LLinitGen...
   rewrite Permutation_app_comm in H4...
  - assert(LL2 |-- B; M ++ [G]).
    eapply CutLL2' with (C:=F & G) (M:=M) (N:=[G])...
   LLright (dual F) (dual G) [G].
   rewrite perm_takeit_8.
   apply LLinitGen...
   rewrite Permutation_app_comm in H4...
Qed.

(********************************************************)
(*                    INVERTIBILITY: RULE FORALL                  *)
(********************************************************)


Lemma invertibility_forall : forall B FX M, 
       isFormula (∀{ FX}) -> isFormula (dual (∀{ FX})) -> 
     LL2S B (∀{ FX}::M) -> (forall x : expr con, proper x -> LL2S B (FX x :: M)).
Proof with simpl;sauto.
  intros...
 inversion H... inversion H0...
  pose proof (H5 x). pose proof (H7 x).
  clear H5 H7. 
  assert(LL2S B [FX x; dual (FX x)]).
  apply LLinitGen...
  assert(LL2 |-- B; M ++ [FX x]).
  eapply CutLL2' with (C:= ∀{ FX}) (M:=M) (N:=[FX x])...
  eapply ll2_ex' with (t:=x) (M:=[FX x]) (FX:=fun x0 : expr con => (FX x0) ^)... 
   rewrite perm_takeit_8...  
   rewrite Permutation_app_comm in H7...
Qed.


(********************************************************)
(*                    INVERTIBILITY: RULE BANG                     *)
(********************************************************)

Lemma invertibility_bang : forall B F, 
      isFormula F -> isFormula (dual F) ->
     LL2S B [! F] -> LL2S B [F].
Proof with simpl;sauto.
  intros...
  - assert(LL2 |-- B; [] ++ [F]).
    eapply CutLL2' with (C:= ! F) (M:=[]) (N:=[F])... 
    LLstore (dual F) [F].
    LLcopy (dual F)...
   rewrite perm_takeit_8.
   apply LLinitGen...
   rewrite Permutation_app_comm in H2...
Qed.
 
End InvRules.
