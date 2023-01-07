  (** ** Aditional results on Forall/map *)
  
  Require Import Coq.Lists.List.
  Require Import Permutation.

  Import ListNotations.

Ltac solveForall :=  
try
  match goal with
   | [  |- Forall _ nil] => apply Forall_nil
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M ?N |- Forall ?f ?N  ] => rewrite <- H2; auto
   | [ H1 : Forall ?f ?M, H2 : Permutation ?N ?M |- Forall ?f ?N  ] => rewrite H2; auto
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?L) |- Forall ?f ?N  ] => rewrite H2 in H1; simpl in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?L) ?M |- Forall ?f ?N  ] => rewrite <- H2 in H1; simpl in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?L) |- Forall ?f ?L  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?L) ?M |- Forall ?f ?L  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?F::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?F::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?F::?L) |- Forall ?f ?L  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?F::?L) ?M |- Forall ?f ?L  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?F::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?F::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?F::?L) |- Forall ?f [?F]  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?F::?L) ?M |- Forall ?f [?F]  ] => rewrite <- H2 in H1; solveForall
 
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++(_ ?F _)::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++(_ _ ?F)::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
  
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++(_ ?F _)::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++(_ _ ?F)::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   

   | [ H : Forall ?f (?F :: ?M) |- ?f ?F ] => eapply @Forall_inv with (l:=M) (a:=F);auto
   | [ H : Forall ?f ((_ ?F _) :: ?M) |- ?f ?F ] => eapply @Forall_inv with (l:=M) (a:=F);auto
   | [ H : Forall ?f ((_ _ ?F) :: ?M) |- ?f ?F ] => eapply @Forall_inv with (l:=M) (a:=F);auto
  
   | [ H : Forall ?f (?F :: ?M) |- Forall ?f ?M ] => apply Forall_inv_tail in H;auto 
   | [ H1 : Forall ?f ?M, H2 : Forall ?f ?N |- Forall ?f (?M++?N) ] => apply Forall_app;split;auto 
   | [ H: Forall ?f (?M++?N) |-  Forall ?f ?M  /\ Forall ?f ?N ] => apply Forall_app;auto 
   | [ H: Forall ?f (?M++?N) |-  Forall ?f ?M ] => apply Forall_app in H; destruct H;auto
   | [ H: Forall ?f (?M++?N) |-  Forall ?f ?N ] => apply Forall_app in H; destruct H;auto 
   | [ H: Forall ?f (?M++?N++?L) |-  Forall ?f ?L ] => rewrite app_assoc in H;solveForall
   | [ H: Forall ?f (?M++?N++?L) |-  Forall ?f ?N ] => rewrite Permutation_app_swap_app in H;solveForall
   | [ H: Forall ?f (?M++?F::?L) |-  ?f ?F ] => apply Forall_elt in H;auto
   | [ H: Forall ?f (?M++?F::?L) |-  Forall ?f [?F] ] => apply Forall_elt in H;auto
   | [ H: Forall ?f (?M++?F::?L) |-  Forall ?f ?L ] => rewrite Permutation_cons_append in H;solveForall

  
   | H: Forall ?f ?M  |- Forall ?f (_ :: ?M) => apply Forall_cons; auto  
   | H: Forall ?f ?M  |- Forall ?f (?M++[_]) => apply Forall_app;split;auto 
   | [ |- Forall ?f (?M++_) ] => apply Forall_app;split;solveForall
   |  |- Forall ?f (_ :: ?M) => apply Forall_cons; solveForall 
   
    end;auto.
    

(* Definition plusT L := map (fun x => 2+x) L.

Lemma asas M N: plusT (M++N) = plusT M ++ plusT N.
rewrite map_app. *)


  

 Ltac solveFoldFALL1 isP :=  
try
  match goal with
   | [  |- ?isPL nil] => autounfold 
   | [H: ?isPL (?K1++?K2++_) |- ?isPL (?K1++?K2)] => autounfold; rewrite app_assoc in H;autounfold in H
   | [H: ?isPL (?K1++_++?K2) |- ?isPL (?K1++?K2)] => autounfold; autounfold in H;rewrite Permutation_app_rot in H


   | [ H : ?isPL (?F :: ?M) |- isP ?F ] => autounfold in H
   | [ H : ?isPL (?F :: ?M) |- ?isPL ?M ] => autounfold;autounfold in H 
   | [ H1 : ?isPL ?M, H2 : ?isPL ?N |- ?isPL (?M++?N) ] => autounfold;autounfold in H1;autounfold in H2 
   | [ H: ?isPL (?M++?N) |-  ?isPL ?M  /\ ?isPL ?N ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?N) |-  ?isPL ?M ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?N) |-  ?isPL ?N ] => autounfold;autounfold in H 
   | [ H: ?isPL (?M++?N++?L) |-  ?isPL ?L ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?N++?L) |-  ?isPL ?N ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?F::?L) |-  isP ?F ] => autounfold in H
   | [ H: ?isPL (?M++?F::?L) |-  ?isPL [?F] ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?F::?L) |-  ?isPL ?L ] => autounfold;autounfold in H

  
   | H: ?isPL ?M  |- ?isPL (_ :: ?M) => autounfold;autounfold in H
   | H: ?isPL ?M  |- ?isPL (?M++_) => autounfold;autounfold in H 
   | H: ?isPL ?M  |- ?isPL (_++?M) => autounfold;autounfold in H 
   | [ H1 : ?isPL ?M, H2 : Permutation ?M ?N |- ?isPL ?N  ] => autounfold;autounfold in H1 
   | [ H1 : ?isPL ?M, H2 : Permutation ?N ?M |- ?isPL ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?L) |- ?isPL ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?L) ?M |- ?isPL ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?L) |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?L) ?M |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?F::?L) |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?F::?L) ?M |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?F::?L) |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?F::?L) ?M |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?F::?L) |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?F::?L) ?M |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?F::?L) |- ?isPL [?F]  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?F::?L) ?M |- ?isPL [?F]  ] => autounfold;autounfold in H1

   | [ |- ?isPL (?M++_) ] => autounfold
   |  |- ?isPL (_ :: ?M) => autounfold 
   
    end;solveForall.
  
        
