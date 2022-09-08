Require Export LL.SL.DyadicExc.StructuralRules.

Export LLNotations.
Set Implicit Arguments.

   Global Instance LL3N_morphism {OLS : OLSig} n:
      Proper ((@Permutation oo) ==> eq ==> iff)
             (LL3N n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (LL3exchangeNC H _);auto.
      + apply Permutation_sym in H.
        refine (LL3exchangeNC H _);auto.
    Qed.
  
  Global Instance LL3S_morphism {OLS : OLSig}:
      Proper ((@Permutation oo) ==> (@Permutation oo) ==> iff)
             (LL3S).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      + refine (LL3exchangeC H _);auto.
        LL3exchangeL x0.
      + apply Permutation_sym in H.
        refine (LL3exchangeC H _);auto.
        apply Permutation_sym in H0.
         LL3exchangeL y0. 
    Qed.

Ltac solvell3 :=
 try
 match goal with
 | [ H: LL3N _ ?B ?L |- LL3S ?B ?L] => apply LL3NtoLL3S in H;auto
 end. 
   
Ltac llExact H :=
  let G:= type of H in
  match G with
  | (LL3N ?x ?Gamma ?Delta) => 
    match goal with
    | [ |- LL3N ?x ?Gamma' ?Delta'] => 
      eapply @LL3exchangeNC with (CC:=Gamma);  try perm
    end 
  end;auto.
 
 Ltac llExac H :=
  match type of H with
  | (LL3N ?x ?Gamma ?Delta) => 
    match goal with
    | [ |- LL3N x ?Gamma' Delta] => 
      eapply @LL3exchangeNC with (CC:=Gamma);  try perm
    | _ => idtac "The conclusion is not a sequent." 
    end   
  | _ => idtac H "is not a sequent." 
  end;auto.
  
Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (LL3S ?Gamma ?Delta) =>
    match goal with
    | [ |- LL3S ?Gamma' ?Delta] =>
      eapply @LL3exchangeC with (CC:=Gamma);try perm
    | [ |- LL3S ?Gamma ?Delta'] =>
       LL3exchangeL Delta
    end 
  end;auto.


Ltac LLExact H := 
  match (type of H) with
  | LL3S _ _  =>  llExact' H
  | LL3N _ _ _ => llExact H
  end.

Definition CutW {OL:OLSig} (w: nat) :=  
  forall i j C A M N O B, 
  complexity C < w ->
  (LL3 i |-- B; C::M -> LL3 j |-- B; N++(dual C)::O -> LL3 |-- B; M ++ N ++ O) /\
  (S (complexity A) = complexity C -> LL3 i |-- A::B ; M -> LL3 j |-- B; N ++ (! dual A)::O -> LL3 |-- B; M++N++O). 

Definition CutH {OL:OLSig} (w h: nat) :=  
  forall i j C A M N O B, 
  i + j < h ->
  complexity C = w ->
  (LL3 i |-- B; C::M -> LL3 j |-- B; N++(dual C)::O -> LL3 |-- B; M ++ N ++ O) /\
  (S (complexity A) = complexity C -> 
  LL3 i |-- A::B ; M -> LL3 j |-- B; N ++ (! dual A)::O -> LL3 |-- B; M++N++O). 

Ltac dualSimpl :=
 match goal with
 | H: ?F = ?C^ |- _ => 
    apply dualSubst in H;subst
 | H: ?C^ = ?F |- _ => 
   symmetry in H; apply dualSubst in H;subst    
 | H: context [((?C)^)^] |- _ => 
    rewrite <- ng_involutive in H  
end;auto.    

 Ltac applyCutH := 
  match goal with
  | [ H: CutH _ _ |- LL3N ?x (?FF::?BX) _ -> 
         LL3N ?y ?BX _ -> 
         LL3S _ _ ] => eapply H
  | [ H: CutH _ _ |- LL3N ?x _ _ -> 
         LL3N ?y _ _ -> 
         LL3S _ _ ] => eapply H
  | _ => idtac end.


Ltac applyCutW :=
  match goal with
 | [ H: CutW _ |- LL3N ?x (?FF::?BX) _ -> 
         LL3N ?y ?BX _ -> 
         LL3S _ _ ] => eapply H
 
  | [ H: CutW _ |- LL3N _ _ (?CF::_) -> 
         LL3N _ _ _ -> 
         LL3S _ _ ] => eapply H
  | _ => idtac end.
  
Ltac putFirst H :=
match type of H with
| LL3N _ _ (?FF::?TT::?XX) => 
    change (FF::TT::XX) with ([FF]++TT::XX) in H
 | LL3N _ _ [?XX] => 
    change XX with ([ ]++XX::[]) in H    
 | LL3N _ _ (?FF::?XX) => 
    change (FF::XX) with ([ ]++FF::XX) in H

end.
  
Tactic Notation "cutLH" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "HCUT" in
   match tP1 with
   | LL3N ?x ?BX (?CF::?CX) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL3N ?y ?BX (?CY1++_::?CY2) =>  
                           assert(H': tP1 -> tP2 -> LL3S BX (CX++CY1++CY2));
                           applyCutH            
                    | _ => idtac "l: type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.
  
Tactic Notation "cutLW" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "WCUT" in
   match tP1 with
   | LL3N ?x ?BX (?CF::?CX) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL3N ?y ?BX (?CY1++_::?CY2) =>  
                           assert(H': tP1 -> tP2 -> LL3S BX (CX++CY1++CY2));
                           applyCutW     
                    | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.

Tactic Notation "cutCH" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "HCUT" in
   match tP1 with
   | LL3N ?x (?CF::?BX) (?CX) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL3N ?y ?BX (?CY1++_::?CY2) =>  
                           assert(H': tP1 -> tP2 -> LL3S BX (CX++CY1++CY2));
                           applyCutH         end   
                  
   | _ => idtac "type of " P1 " is " tP1 end;sauto.
  
Tactic Notation "cutCW" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "WCUT" in
   match tP1 with
   | LL3N ?x (?CF::?BX) ?CX => let tP2 := type of P2 in
                    match tP2 with 
                    | LL3N ?y ?BX (?CY1++_::?CY2) =>  
                           assert(H': tP1 -> tP2 -> LL3S BX (CX++CY1++CY2));
                           applyCutW
                    | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.    


     
