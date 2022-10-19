Require Export SL.SELLF.Syntax.
Require Export SL.SELLF.Signature.

Section SubExpSets.
  Context `{SI : Signature}.
  Context `{OLS : OLSig}.
 
 Definition SetX  (x:  subexp -> bool) (b:bool) (K : list TypedFormula):= Forall (fun k => x (fst k) = b) K.
 
 Definition LtX  i (K : list TypedFormula) := Forall (fun k => lt i (fst k)) K.
  
 Global Instance perm_SetX A b :
      Proper (@Permutation TypedFormula ==>  Basics.impl)
             (SetX A b).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetX.
      rewrite <- H;auto.
    Qed.

Global Instance perm_LtX a :
      Proper (@Permutation TypedFormula ==>  Basics.impl)
             (LtX a).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold LtX.
      rewrite <- H;auto.
    Qed.


   Fixpoint getU  (l : list TypedFormula) :=
  match l with
  | [] => []
  | (x,F) :: l0 => if u x then (x,F) :: (getU l0) else getU l0
  end.
  
 Fixpoint getL (l : list TypedFormula) :=
  match l with
  | [] => []
  | (x,F) :: l0 => if u x then getL l0 else (x,F) :: (getL l0) 
  end.
   
End SubExpSets.

 Global Hint Unfold SetX LtX first second: core.  

 
Tactic Notation "srewrite" constr(H) := autounfold;
 let Hs := type of H in 
 match Hs with
| Permutation _ _ => try rewrite H
                     
end.

Tactic Notation "srewrite_reverse" constr(H) := autounfold;
 let Hs := type of H in 
 match Hs with
| Permutation _ _ => symmetry in H;try rewrite H
                     
end.


Tactic Notation "srewrite" constr(H1) "in" constr(H2) := 
autounfold in H2;
 let Hs := type of H1 in 
 match Hs with
| Permutation _ _ => try rewrite H1 in H2
                     
end.

Tactic Notation "srewrite_reverse" constr(H1) "in" constr(H2) := 
autounfold in H2;
 let Hs := type of H1 in 
 match Hs with
| Permutation _ _ => symmetry in H1; try rewrite H1 in H2
                     
end.

 Ltac simplSignature1 := 
  repeat 
    multimatch goal with
  (* Basic simplifcation *)
  | [  |- context[_ []] ] => simpl
  | [ H: context[_ []]  |- _ ] => simpl in H
 
  | [ H1: u (fst ?F) = _, H2: context[_(?F :: _)] |- _ ] => 
     destruct F;simpl in H1;simpl in H2; try rewrite H1 in H2 
  | [ H: u (fst ?F) = _ |- context[_ (?F :: _)] ] => 
     destruct F;simpl;simpl in H; try rewrite H 
 | [ H1: ?s ?a = _, H2: context[if ?s ?a then _ else _] |- _ ] => rewrite H1 in H2 
 | [ H: ?s ?a = _|- context[if ?s ?a then _ else _] ] => rewrite H 

(* About second *)
 | [ H: context[second(_++_)] |- _ ] => rewrite secondApp in H 
 | [ |- context[second(_++_)] ] => rewrite secondApp
 
 | [  |- context[_ (_::_)] ] => simpl
  | [ H: context[_ (_::_)] |- _ ] => simpl in H 

  end.

 
 Ltac solveSignature1 := try
  match goal with
  | [ H: UnbSignature |- u ?i = true ] => apply allU 
 
  | [ |- lt ?i ?i] => apply @PreOrder_Reflexive; exact lt_pre
 
   | [H: SetX ?a ?b (?F::?K) |- ?a (fst ?F) = ?b] => inversion H;subst;auto
   | [H: SetX ?a ?b ((?s, _)::?K) |- ?a ?s = ?b] => inversion H;subst;auto
  
   | [H: _ ?i (?F::?K) |- lt ?i (fst ?F) ] => inversion H;subst;intuition
   | [H: _ ?i ((?s, _)::?K) |- lt ?i ?s ] => inversion H;subst;intuition
   
  end.
  
 Ltac solveLocation :=simplSignature1; try solve [solveSignature1]; autounfold in *;solveForall.
 

Section Properties.
  Context `{SI : Signature}.
  Context `{OLS : OLSig}.
       
  Lemma locSetK1 sub a b F: sub a = b -> SetX sub b [(a, F)].
  Proof with solveLocation.
  constructor... 
  Qed.

  
   Lemma SetU_then_empty K : SetX u true K -> getL K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 
  
    
   Lemma SetL_then_empty K : SetX u false K -> getU K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 

     
   Lemma SetKRef a F: LtX a [(a, F)].
  Proof with sauto.
  apply Forall_cons... 
  apply @PreOrder_Reflexive.
  exact lt_pre.
  Qed.

   Lemma SetKTrans i a K : LtX i K -> lt a i -> LtX a K.
  Proof with sauto.
  induction K;simpl;intros...
  inversion H...
  apply Forall_cons... 
  apply @PreOrder_Transitive with (R:=lt) (y:=i);auto.
  exact lt_pre.
  apply IHK...
  Qed.

  Global Instance trans_SetK :
       Proper (lt ==> @Permutation TypedFormula ==> Basics.flip Basics.impl)
             (LtX ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.flip; unfold Basics.impl .
      intros;subst.
      rewrite H0.
      eapply (SetKTrans _ _ _ H1);auto. 
    Qed.
  
  Lemma SetUL_then_empty' i K : SetX u false K -> LtX i K -> u i = true -> K=[].
  Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  assert(u p = true).
  {
  eapply uClosure.
  exact H1. inversion H0...  }
  sauto.
  Qed.
  
  
    Lemma SetTKClosure i sub K  : (forall x y : subexp,
       sub x = true -> lt x y -> sub y = true) -> sub i = true -> LtX i K -> SetX sub true K. 
  Proof with sauto.
  intros.
  induction K;intros... 
  inversion H1...
  apply Forall_cons...
  eapply H. 
  exact H0. exact H4.
  apply IHK...
  Qed.
  
(*   Check SetTKClosure _ u _ uClosure . *)
  Lemma SetUKClosure i K  : u i = true -> LtX i K -> SetX u true K. 
  Proof with sauto.
  intros.
  apply SetTKClosure with (i:=i)...
  exact uClosure.
  Qed.

 Lemma SetK4In sub a K: SetX sub true K -> In a K -> sub (fst a) = true.
  Proof with sauto.
  intros.
  eapply @ForallIn with (F:=a) in H...
  Qed.
 
 
  Lemma SetKK4_then_empty sub K : SetX sub true K -> SetX sub false K -> K=[].
   Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  inversion H0...
  Qed. 
  
  Theorem cxtDestruct K: Permutation K (getU K++getL K).
 Proof with subst;auto.
 induction K;auto.
 destruct a as [a F].
 destruct (uDec a); simpl; rewrite e.
 constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.
 
  Theorem cxtDestructSecond K: Permutation (second K) (second (getU K++getL K)).
 Proof with subst;auto.
 induction K;auto.
 destruct a as [a F].
 destruct (uDec a); simpl; rewrite e.
 constructor;auto.
 rewrite secondApp.
 simpl.
 apply Permutation_cons_app;auto.
 rewrite <- secondApp;auto.
 Qed.

 Theorem cxtDestruct' K: exists K1 K2, Permutation K (getU K++getL K1 ++ getL K2) /\ Permutation (getL K) (getL K1 ++ getL K2).
 Proof with sauto.
 induction K...
 exists [].
 exists [].
 simpl;auto.
 destruct a as [a F].
 destruct (uDec a); simpl;
 rewrite e;simpl.
 exists x. exists x0.
 constructor;auto.
 exists ((a,F)::x).
  exists x0.
  simpl; rewrite e;simpl.
  constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.
 
 Lemma getUPerm K1 K2 : Permutation K1 K2 -> Permutation (getU K1) (getU K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];
   destruct (uDec x);
   simpl;rewrite e...
 * destruct x as [x F];
   destruct y as [y G];
   destruct (uDec x);
   destruct (uDec y);
   simpl;rewrite e;rewrite e0...  
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.
 
  Lemma getLPerm K1 K2 : Permutation K1 K2 -> Permutation (getL K1) (getL K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];
   destruct (uDec x);
   simpl;rewrite e...
 * destruct x as [x F];
   destruct y as [y G];
   destruct (uDec x);
   destruct (uDec y);
   simpl;rewrite e;rewrite e0...  
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.

  Global Instance getU_morph :
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getU ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getUPerm;auto.
    Qed. 
  
    Global Instance getL_morph :
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getL ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getLPerm;auto.
    Qed. 
    
     
  Lemma getU_fixpoint K : getU(getU K) =  getU K.
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.
  
    Lemma getL_fixpoint K : getL(getL K) =  getL K.
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.  
 
  Lemma getUgetL K : getU(getL K) =  [].
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.
  
  Lemma getLgetU K : getL(getU K) =  [].
  Proof.
   induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
  Qed.

 
  Lemma getUApp K1 K2 : getU (K1 ++ K2) =  getU K1 ++ getU K2.
  Proof.
    induction K1;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl.
  rewrite IHK1; auto.
   Qed.
 
 
 Lemma getUApp' K1 K2 : Permutation (getU (K1 ++ K2)) (getU K1 ++ getU K2).
  Proof.
  rewrite getUApp;auto.
  Qed. 
 
 Lemma uIngetU i F B :  u i = true -> In (i, F) B -> In (i, F) (getU B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *.
  rewrite e in *...  firstorder. 
  rewrite e in *...
  inversion H0...
 Qed.
 
  Lemma getLApp K1 K2 : getL (K1 ++ K2) =  getL K1 ++ getL K2.
  Proof.
  induction K1;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto.
  simpl. 
  rewrite IHK1. auto.
 Qed.
  
 Lemma getLApp' K1 K2 : Permutation (getL (K1 ++ K2)) (getL K1 ++ getL K2).
  Proof.
  rewrite getLApp;auto.
  Qed. 

Lemma lIngetL i F B :  u i = false -> In (i, F) B -> In (i, F) (getL B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
 Qed.

Lemma lIngetU i F B :  u i = true -> In (i, F) B -> In (i, F) (getU B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
  inversion H0...
 Qed.


  Theorem getUtoSetU K: SetX u true (getU K).
 Proof with subst;auto.
 induction K...  
 apply Forall_nil.
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
   Theorem getLtoSetU K: SetX u true (getL K) -> getL K =[].
 Proof with sauto.
 induction K;intros. 
 * auto.
 * destruct a as [a F].
   destruct (uDec a); simpl in *;
  rewrite e in *...
  inversion H...
 Qed.
 
 
 Lemma getUPerm_SetU K X : Permutation (getU K) X -> SetX u true X.
  Proof.
  intros.
  symmetry in H.
  srewrite  H.
  apply getUtoSetU.
 Qed. 
 

 
  Theorem getLtoSetL K: SetX u false (getL K).
 Proof with subst;auto.
 induction K...
 apply Forall_nil.
 
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
  Lemma getLPerm_SetL K X : Permutation (getL K) X -> SetX u false X.
  Proof.
  intros.
  symmetry in H.
  srewrite H.
  apply getLtoSetL.
 Qed. 
 
  Theorem setUtoGetU K: SetX u true K -> getU K = K.
 Proof with subst;auto.
 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.

  Theorem setLtoGetL K: SetX u false K -> getL K = K.
 Proof with subst;auto.

 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.
 
   Lemma getUPermU K1 K2 : Permutation (getU K1) K2 -> Permutation (getU K1) (getU K2).
Proof with sauto.
 intros.
 rewrite H.
 apply getUPerm_SetU in H.
 rewrite cxtDestruct...
 rewrite (SetU_then_empty _ H)...
 rewrite setUtoGetU...
 rewrite setUtoGetU...
 Qed.
 
 Theorem Unb_Lin_Disj' K: exists K1 K2, SetX u true K1 /\ SetX u false K2 /\ Permutation K (K1++K2).
 Proof with subst;solveLocation;auto .
 induction K;auto.
 do 2 eexists [];simpl...
 destruct IHK.
 destruct H.
 decompose [and] H ;clear H.
 destruct a as [a F].
 destruct (uDec a).
 eexists ((a,F)::x).
 eexists x0.
 split... 
 eexists x.
 eexists ((a,F)::x0).
 split... 
 split...  
 rewrite H3... apply Permutation_middle.
 Qed.
 
  Lemma SetUDec sub K :  {SetX sub true K} + {~ SetX sub true K}.
  Proof with sauto.
    induction K;simpl;auto.
    destruct IHK.
    - destruct a as [p F]... 
      destruct (subDec sub p). 
      left.  apply Forall_cons...
      right. intro.
      inversion H...
    - destruct a as [p F]. 
      destruct (subDec sub p).
      right. intro. inversion H... 
      right. intro.
      inversion H... 
 Qed.
 
 
 
  Lemma isFormulaL_getU B :  
      isFormulaL (second B) -> isFormulaL  (second (getU B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - 
      simpl in *.
      inversion H;sauto.
      rewrite e.
      apply Forall_cons;sauto.
    -
      simpl in *.
      inversion H;sauto.
      rewrite e;sauto...
  Qed.    
    
    Lemma isFormulaL_getL  B :  
      isFormulaL  (second B) -> isFormulaL  (second (getL B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - simpl in *.
    rewrite e.
      inversion H;sauto.
   -  simpl in *.
   rewrite e.
      inversion H;sauto.
      apply Forall_cons;sauto.
  Qed.
  
  Lemma isFormulaLSplitUL  B :  
      isFormulaL  (second (getU B)) ->  isFormulaL  (second (getL B)) -> isFormulaL  (second B). 
  Proof.
    intros.
    rewrite cxtDestructSecond.
    rewrite secondApp.
    apply Forall_app;auto.
  Qed.   
  
      
     Lemma isFormulaLSecond  B D X Y:  
     Permutation (getL B) (getL D ++ X) -> 
     Permutation (getU B) (getU D ++ Y) ->
     isFormulaL  (second B) -> isFormulaL  (second D). 
  Proof.
    autounfold;unfold second;intros.
    rewrite cxtDestruct in H1.
    rewrite H in H1.
    rewrite H0 in H1.
    fold (second ((getU D ++ Y) ++ getL D ++ X)) in H1.
    repeat rewrite secondApp in H1.
    apply Forall_app in H1.
    destruct H1.
    apply Forall_app in H1.
    apply Forall_app in H2.
    sauto.
    rewrite cxtDestruct.
    fold (second (getU D ++ getL D)). 
    repeat rewrite secondApp.
    apply Forall_app;auto.
    Qed.
    
 
 Lemma getUS F t D L: getU D = (t, F)::L -> u t = true.
 Proof with sauto.
 induction D;intros...
 destruct a.
 destruct (uDec s).
 inversion H...
 rewrite e in H1... 
 inversion H1...
 inversion H...
 rewrite e in H1... 
 Qed.
 

  Lemma linearEmpty K : getL K = [] -> getL K = [] /\ Permutation (getU K) K /\ SetX u true K.
  Proof with auto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    apply IHK in H. 
    split;sauto. 
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
Qed.

Lemma unboundedEmpty K : getU K = [] -> getU K = [] /\ Permutation (getL K) K /\ SetX u false K.
  Proof with auto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
     apply IHK in H. 
    split;sauto. 
 Qed.
 
  Lemma SetK4Destruct sub b K : SetX sub b K -> SetX sub b (getU K) /\ SetX sub b (getL K).
  Proof with sauto.
  intros.
  rewrite cxtDestruct in H;split;
  apply Forall_app in H...
  Qed.
  
   Lemma linearInUnb a A K : u a = false -> SetX u true K -> In (a, A) K -> False.
  Proof with sauto.
  induction K;intros...
  destruct a0.
  inversion H1...
  inversion H0...
  apply IHK...
  inversion H0... 
  Qed. 
  
  
 Lemma InContext1 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F B ->  In F BD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.

 Lemma InSecond1 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F (second B) ->  In F (second BD).
  Proof with sauto.
  intros.
  unfold second.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  rewrite map_app.
  apply in_or_app;auto.
  Qed.
  
  
  
 Lemma InContext2 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F D ->  In F BD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.
  
  Lemma InSecond2 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F (second D) ->  In F (second BD).
  Proof with sauto.
  intros.
  unfold second.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  rewrite map_app.
  apply in_or_app;auto.
  Qed.  
 

  Lemma isFormulaSecond1  BD X Y B Z U:
  isFormulaL  (second (X++getU BD++Y)) -> 
  Permutation (X++getU BD++Y) (Z++B++U) ->
  isFormulaL  (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL  (second (Z ++ B ++ U))).
   symmetry in H0.
   srewrite H0...
   rewrite !secondApp in H1.
   apply Forall_app in H1...
   apply Forall_app in H3...
 Qed.  

 Lemma isFormulaSecond2  BD X Y B Z U:
  isFormulaL  (second (X++getL BD++Y)) -> 
  Permutation (X++getL BD++Y) (Z++B++U) ->
  isFormulaL  (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL  (second (Z ++ B ++ U))).
   symmetry in H0.
   srewrite H0...
   rewrite !secondApp in H1.
   apply Forall_app in H1...
   apply Forall_app in H3...
 Qed.
 


  Lemma isFormulaSecondSplit1  BD X Y B D:
  isFormulaL  (second (BD++X++Y)) -> 
  Permutation (getU BD++X) (getU B) ->
  Permutation (getL BD++Y) (getL B ++ getL D) -> isFormulaL  (second B).
   Proof with sauto.
  intros.
   rewrite !secondApp in H.
  assert(isFormulaL  (second BD)).
  apply Forall_app in H...
  assert(isFormulaL  (second X)).
  apply Forall_app in H...
  apply Forall_app in H4...
  assert(isFormulaL  (second Y)).
  apply Forall_app in H...
  apply Forall_app in H5...
  assert(Permutation ([] ++ getU BD ++ X) ([] ++getU B ++ [])).
  sauto.
  eapply isFormulaSecond1  in H5...
  assert(Permutation ([] ++ getL BD ++ Y) ([] ++getL B ++ getL D)).
  sauto.
  eapply isFormulaSecond2  in H6...
  apply isFormulaLSplitUL...
  
  rewrite !secondApp...
  apply Forall_app...
  apply isFormulaL_getL...
  rewrite !secondApp...
  apply Forall_app...
  apply isFormulaL_getU...
 Qed. 
 
  Lemma isFormulaSecondSplit2  BD X Y B D:
  isFormulaL  (second (BD++X++Y)) -> 
  Permutation (getU BD++X) (getU D) ->
  Permutation (getL BD++Y) (getL B ++ getL D) -> isFormulaL  (second D).
   Proof with sauto.
  intros.
  eapply isFormulaSecondSplit1 with (X:=X) (Y:=Y) (BD:=BD) (D:=B);auto.
  rewrite H1...
  Qed.
 
 
  Lemma simplUnb BD B D:          
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetX u true B -> Permutation BD D.
  Proof.   
  intros.
  rewrite (SetU_then_empty _ H1) in H0.
  rewrite (cxtDestruct BD).
  rewrite H0.
  rewrite H.
  simpl. 
  rewrite <- cxtDestruct;auto.
  Qed.
  
  Lemma simplUnb' BD B D:          
  Permutation (getU BD) (getU B) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetX u true D -> Permutation BD B.
  Proof.   
  intros.
  rewrite (SetU_then_empty _ H1) in H0.
  rewrite (cxtDestruct BD).
  rewrite H.
  rewrite H0;sauto.
  rewrite <- cxtDestruct;auto.
  Qed.
  
 Definition SetU K := SetX  u true K. 
 Definition SetL K := SetX  u false K.

End Properties.

 Global Hint Unfold SetU SetL:core. 

Global Hint Resolve SetUKClosure   getUtoSetU getLtoSetL: core.


Global Hint Extern 1 (LtX ?a ?K) =>
  match goal with
  | H: LtX ?i ?K,  H1: lt ?a ?i |- _ =>  apply (SetKTrans _ _ _ H H1)
  end : core.

Global Hint Resolve linearInUnb: core.

Ltac solveLT :=  
try
 match goal with
   | [H: _ ?i (?F::?K) |- lt ?i (fst ?F) ] => inversion H;subst;intuition
   | [H: _ ?i ((?s, _)::?K) |- lt ?i ?s ] => inversion H;subst;intuition
   | [H: _ ?i (_::?K) |- LtX ?i ?K ] => inversion H;subst;intuition
   
   
   | [H: lt ?x ?y, H2: LtX ?y ?K |- LtX ?x ?K ] => rewrite H;auto
   | [H: Permutation ?K ?K', H2: LtX ?x ?K' |- LtX ?x ?K ] => rewrite H;auto
    | [H: Permutation ?K ?K', H2: LtX ?x ?K |- LtX ?x ?K' ] => rewrite <- H;auto  
 
  end;auto.

Ltac solveSE :=  
try
 match goal with
  | [H: SetU ((?s, _)::_) |- u ?s = true] => inversion H;subst;auto      
    | [H: SetL ((?s, _)::_) |- u ?s = false] => inversion H;subst;auto

  | [H: SetU (?s::_) |- u (fst ?s) = true] => inversion H;subst;intuition
    | [H: SetL (?s::_) |- u (fst ?s) = false] => inversion H;subst;intuition

     
    | [H: SetU (_::?K) |- SetU ?K] => inversion H;subst;auto
   | [H: SetL (_::?K) |- SetL ?K] => inversion H;subst;auto
 end.
 
 
 Ltac simplEmpty := 
 repeat    
  multimatch goal with

 
  | [H: SetU ?K, H1: SetL ?K |- _  ] =>  assert(K=[]) by apply (SetKK4_then_empty _ _ H H1);clear H H1 
 
  | [H: SetL ?K, H0: LtX ?i ?K, H1:  u ?i = true |- _  ] =>  assert(K=[]) by apply (SetUL_then_empty' _ _ H H0 H1);clear H 

  | [  |- context[getL(getU _)] ] => rewrite getLgetU 
  | [ H: context[getL(getU _)] |- _  ] => rewrite getLgetU in H
  | [  |- context[getU(getL _)] ] => rewrite getUgetL 
  | [ H: context[getU(getL _)] |- _  ] => rewrite getUgetL in H
 
  | [ H: SetU ?K |- context[getL ?K] ] => rewrite (SetU_then_empty _ H)
  | [ H1: SetU ?K, H2: context[getL ?K] |- _ ] => rewrite (SetU_then_empty _ H1) in H2

  | [ H: SetL ?K |- context[getU ?K] ] => rewrite (SetL_then_empty _ H)
  | [ H1: SetL ?K, H2: context[getU ?K] |- _ ] => rewrite (SetL_then_empty _ H1) in H2
  
   
 | [ H: SetU (getL ?K)  |- context[getL ?K] ] => rewrite (getLtoSetU _ H)
  | [H0: SetU (getL ?K), H: context[getL ?K] |- _  ] => rewrite (getLtoSetU _ H0) in H

 | [H: SetU (getL ?K) |- context[getL ?K]  ] => rewrite (getLtoSetU _ H)
 
  | [H: SetU (getL ?K), H1: context[getL ?K] |- _  ] => rewrite (getLtoSetU _ H) in H1
end.


Ltac simplFix := 
 repeat    
  multimatch goal with

 | [  |- context[getU (getU _)] ] => rewrite getU_fixpoint
 | [H:  context[getU (getU _)]  |- _ ]  => rewrite getU_fixpoint in H

 | [  |- context[getL (getL _)] ] => rewrite getL_fixpoint
 | [H:  context[getL (getL _)]  |- _ ]  => rewrite getL_fixpoint in H

 | [H: SetU ?K  |- context[getU ?K] ] => rewrite (setUtoGetU _ H)
 | [H: SetU ?K, H1: context[getU ?K]  |- _ ]  => rewrite (setUtoGetU _ H) in H1

 | [H: SetL ?K  |- context[getL ?K] ] => rewrite (setLtoGetL _ H)
 | [H: SetL ?K, H1: context[getL ?K]  |- _ ]  => rewrite (setLtoGetL _ H) in H1

end.




Ltac simplCtx :=
 multimatch goal with
 
 | [  |- context[getU(_++_)] ] => setoid_rewrite getUApp
 | [  |- context[getL(_++_)] ] => setoid_rewrite getLApp
 | [ H: context[getU(_++_)] |- _ ] => setoid_rewrite getUApp in H
 | [ H: context[getL(_++_)] |- _ ] => setoid_rewrite getLApp in H
  | [  |- context[(second (getU ?K++getL ?K))] ] => rewrite <- cxtDestructSecond
 | [ H:context[(second (getU ?K++getL ?K))] |- _ ] => rewrite <- cxtDestructSecond in H 
end. 

 
Ltac solveSignature2 :=
 match goal with
  | [ H: SetX ?s ?b ?K |- SetX ?s ?b (getU ?K)] => apply SetK4Destruct in H;sauto
  | [ H: SetX ?s ?b ?K |- SetX ?s ?b (getL ?K)] => apply SetK4Destruct in H;sauto

| [ H: SetX ?s ?b ?K, H2: Permutation (getU ?K) (?K2 ++ _) |- SetX ?s ?b ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2
 | [ H: SetX ?s ?b ?K, H2: Permutation (getU ?K) (_ ++ ?K2) |- SetX ?s ?b ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2

  | [H: Permutation (getU ?CN) (_ ++ ?M) |- SetU ?N] =>  apply getUPerm_SetU in H;solveSignature2
  | [H: Permutation (getU ?CN) (?M ++ _) |- SetU ?M] =>  apply getUPerm_SetU in H;solveSignature2

 | [ H1: u ?i = false, H2: In (?i, ?F) ?B  |- In (?i, ?F) (getL ?B) ] => apply lIngetL;auto

end.
 