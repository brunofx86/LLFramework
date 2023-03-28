Require Export LL.PLL.StructuralRules.

Export LLNotations.
Set Implicit Arguments.

Ltac solvell2 :=
 try
 match goal with
 | [ H: LL2N _ ?B ?L |- LL2S ?B ?L] => apply LL2NtoLL2S in H;auto
 end. 
   
Ltac llExact H :=
  let G:= type of H in
  match G with
  | (LL2N ?x ?Gamma ?Delta) =>
    match goal with
    | [ |- LL2N ?x ?Gamma' ?Delta'] =>
      eapply @LL2N_compat with (B1:=Gamma) (L1:=Delta); try perm
    end 
  end;auto.
 
Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (LL2S ?Gamma ?Delta) =>
    match goal with
    | [ |- LL2S ?Gamma' ?Delta'] =>
      eapply @LL2S_compat with (B1:=Gamma) (L1:=Delta); try perm
    end 
  end;auto.


Ltac LLExact H := 
  match (type of H) with
  | LL2S _ _  =>  llExact' H
  | LL2N _ _ _ => llExact H
  end.

  Definition CutW (w: nat) :=  
    forall i j C A M N B, 
    complexity C  < w ->
      (LL2 i |-- B; C::M -> LL2 j |-- B; (dual C)::N -> LL2 |-- B; M ++ N) /\
      (S (complexity A) = complexity C ->
       LL2 i |-- A::B ; M -> LL2 j |-- B; (! dual A)::N -> LL2 |-- B; M++N). 

  Definition CutH (w m: nat) :=  
    forall i j C A M N B, 
   i + j < m ->
    complexity C = w ->
      (LL2 i |-- B; C::M -> LL2 j |-- B; (dual C)::N -> LL2 |-- B; M ++ N) /\
      (S (complexity A) = complexity C ->
      LL2 i |-- A::B ; M -> LL2 j |-- B; (! dual A)::N -> LL2 |-- B; M++N). 


Ltac dualSimpl :=
 match goal with
 | H: ?F = ?C^ |- _ => 
    apply dualSubst in H;subst
 | H: ?C^ = ?F |- _ => 
   symmetry in H; apply dualSubst in H;subst    
 | H: context [((?C)^)^] |- _ => 
    rewrite <- ng_involutive in H  
end;auto.    


Ltac putFirst H TT :=
match type of H with
| LL2N ?x ?BB (?FF::TT::?XX) => 
    eapply LL2N_compat with 
     (B2:=BB) (L2:= TT::FF::XX) in H;try perm
 | LL2N ?x ?BB (?FF::?GG::TT::?XX) => 
   eapply LL2N_compat with 
     (B2:=BB) (L2:= TT::FF::GG::XX) in H;try perm
end.

 Ltac applyCutH := 
  match goal with
  | [ H: CutH _ _ |- LL2N ?x (?FF::?BX) _ -> 
         LL2N ?y ?BX _ -> 
         LL2S _ _ ] => eapply H with (m := x + y) (C:=Quest FF);sauto
  | [ H: CutH _ _ |- LL2N ?x _ _ -> 
         LL2N ?y _ _ -> 
         LL2S _ _ ] => eapply H ;sauto
  | _ => idtac end.


Ltac applyCutW := 
  match goal with
 | [ H: CutW _ |- LL2N ?x (?FF::?BX) _ -> 
         LL2N ?y ?BX _ -> 
         LL2S _ _ ] => eapply @H with (m := x + y) (C:=Quest FF);sauto
 
  | [ H: CutW _ |- LL2N _ _ (?CF::_) -> 
         LL2N _ _ _ -> 
         LL2S _ _ ] => eapply H ;sauto
  | _ => idtac end.
  
Tactic Notation "cutH" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "HCUT" in
   match tP1 with
   | LL2N ?x ?BX (?CF::?CX) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL2N ?y ?BX (_::?CY) =>  
                           assert(H': tP1 -> tP2 -> LL2S BX (CX++CY));
                           applyCutH; try rewrite app_nil_r in H' 
                    | _ => idtac "type of " P2 " is " tP2 end
   | LL2N ?x ?BX (?NF::?CF::?CX2) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL2N ?y ?BX (_::?CY) =>  
                           assert(LL2N x BX (CF::(NF++CX2)) -> tP2 -> LL2S BX ((NF::CX2)++CY));
                           applyCutH; try rewrite app_nil_r in H' 
                    | _ => idtac "type of " P2 " is " tP2 end

   | _ => idtac "type of " P1 " is " tP1 end.
  
Tactic Notation "cutW" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "WCUT" in
   match tP1 with
   | LL2N ?x ?BX (?CF::?CX) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL2N ?y ?BX (_::?CY) =>  
                           assert(H': tP1 -> tP2 -> LL2S BX (CX++CY));
                           applyCutW; try rewrite app_nil_r in H'
                    | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end.

Tactic Notation "cutH'" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "HCUT" in
   match tP1 with
   | LL2N ?x (?CF::?BX) (?CX) => let tP2 := type of P2 in
                    match tP2 with 
                    | LL2N ?y ?BX (_::?CY) =>  
                           assert(H': tP1 -> tP2 -> LL2S BX (CX++CY));
                           applyCutH; try rewrite app_nil_r in H'
                    | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end.
  
Tactic Notation "cutW'" constr(P1) constr(P2) :=
   let tP1 := type of P1 in
   let H' := fresh "WCUT" in
   match tP1 with
   | LL2N ?x (?CF::?BX) ?CX => let tP2 := type of P2 in
                    match tP2 with 
                    | LL2N ?y ?BX (_::?CY) =>  
                           assert(H': tP1 -> tP2 -> LL2S BX (CX++CY));
                           applyCutW; try rewrite app_nil_r in H'
                    | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end.    


     
