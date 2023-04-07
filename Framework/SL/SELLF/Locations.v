Require Export LL.Framework.SL.SELLF.Syntax.
Require Export LL.Framework.SL.SELLF.Signature.
Require Import LL.Misc.UtilsForall.

Ltac simplSignature := 
  repeat 
    multimatch goal with
  (* Basic simplifcation *)
  | [  |- context[fst (_,_)] ] => simpl
  | [ H: context[fst (_,_)]  |- _ ] => simpl in H
 
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

 
  Ltac solveSignature :=
  match goal with
   | [H: _ ?a ?b (?F::?K) |- ?a (fst ?F) = ?b] => inversion H;subst;auto
   | [H: _ ?a ?b ((?s, _)::?K) |- ?a ?s = ?b] => inversion H;subst;auto
  
   | [H: _ ?i (?F::?K) |- lt ?i (fst ?F) ] => inversion H;subst;intuition
   | [H: _ ?i ((?s, _)::?K) |- lt ?i ?s ] => inversion H;subst;intuition
  end.
   
   
  
 Ltac solveLocation :=simplSignature; try solve [solveSignature]; autounfold in *;solveForall.
 
Section SubExpSets.

  Context `{SI : SigSELL}.
  Context `{OLS : OLSig}.

        
 Definition SetU (K : list TypedFormula):= 
        Forall (fun k => u (fst k) = true) K.
  
   Definition SetL (K : list TypedFormula):= 
        Forall (fun k => u (fst k) = false) K.
            
 Definition LtX i (K : list TypedFormula) := Forall (fun k => lt i (fst k)) K.

 Fixpoint getLtX  (a: subexp) (L: list TypedFormula) :=
  match L with
  | [] => []
  | (x,F) :: l0 => if lt_dec a x then (x,F) :: (getLtX a l0) else getLtX a l0
  end.
  
Fixpoint getNoLtX  (a: subexp) (L: list TypedFormula)  := 
  match L with
  | [] => []
  | (x, F) :: l0 => if lt_dec a x then getNoLtX a l0 else (x, F) ::  getNoLtX a l0
  end.

 Fixpoint getU  (L: list TypedFormula) :=
  match L with
  | [] => []
  | (x,F) :: l0 => if u x then (x,F) :: (getU l0) else getU l0
  end.
 
  Fixpoint getL  (L: list TypedFormula) :=
  match L with
  | [] => []
  | (x,F) :: l0 => if u x then (getL l0) else (x,F) :: getL l0
  end.
  
(*    Lemma filter_In : forall x l, In x (first (getU l)) <-> In x (first l) /\ sub x = true.   
Proof. 
      intros *. 
      induction l; intros. 
      - simpl; tauto.
      - destruct a. destruct (subDec s). 
         all: simpl; rewrite e;simpl.
         all: intuition congruence.
    Qed. *)
   
      
Section Properties.
  Hint Unfold LtX getLtX SetU SetL:core.
  
    
  Lemma USetU (SE: USigSELL) K: SetU K.
  Proof with solveLocation.
  induction K...
  Qed.
  
  
  
  Lemma SetUFirst a F: u a = true -> SetU [(a, F)].
  Proof with solveLocation.
  auto.
  Qed.
  
  Lemma SetLFirst a F: u a = false -> SetL [(a, F)].
  Proof with solveLocation.
  auto.
  Qed.
  
  
  Lemma LtXRefl a F: LtX a [(a, F)].
  Proof with solveLocation.
  simpl... 
  reflexivity.
  Qed.
 
  
  Lemma LtXTrans i a K : LtX i K -> lt a i -> LtX a K.
  Proof with solveLocation.
  induction K;simpl;intros...
  inversion H;subst.
  transitivity i;auto.
  inversion H;subst.
  apply IHK...
  Qed.
  
Lemma SETXLTEmpty i K: 
       SetL K -> LtX i K -> u i = true -> K=[].
  Proof with solveLocation.
  destruct K;intros...
  destruct t as [p F].
  inversion H0;subst.
  assert(u p = true).
  { eapply uClosure.  
     exact H1. simpl in H4... }
     inversion H...
  sauto.
  Qed.
  
  
    Lemma SETXClosure i K  : 
       u i = true -> LtX i K -> SetU K. 
  Proof with solveLocation.
  intros.
  induction K;intros...
  inversion H0;subst.
  eapply uClosure.
  exact H. exact H3.
  apply IHK...
  Qed.
  
 
 Lemma SETUIn a K: SetU K -> In a K -> u (fst a) = true.
  Proof with sauto.
  intros.
  eapply @ForallIn with (F:=a) in H...
  Qed.
 
 Lemma SETLIn a K: SetL K -> In a K -> u (fst a) = false.
  Proof with sauto.
  intros.
  eapply @ForallIn with (F:=a) in H...
  Qed.
 
  Lemma SETXempty K : SetU K -> SetL K -> K=[].
   Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  inversion H0...
  Qed.
  
   Lemma SETUNotIn a F K : u a = true -> SetL K -> In (a, F) K -> False.
  Proof with sauto.
  induction K;intros...
  destruct a0.
  inversion H1...
  inversion H0...
  apply IHK...
  inversion H0... 
  Qed.
   
   Lemma SETLNotIn a F K : u a = false -> SetU K -> In (a, F) K -> False.
  Proof with sauto.
  induction K;intros...
  destruct a0.
  inversion H1...
  inversion H0...
  apply IHK...
  inversion H0... 
  Qed.
   
   
  Lemma SETUDec K :  {SetU K} + {~ SetU K}.
  Proof with sauto.
  apply Forall_dec; intros.
  destruct (uDec (fst x))... 
  Qed.

  Lemma SETLDec K :  {SetL K} + {~ SetL K}.
  Proof with sauto.
  apply Forall_dec; intros.
  destruct (uDec (fst x))...
  right. intro...
  Qed.
 
   Global Instance perm_SetU :
      Proper (@Permutation TypedFormula ==>  Basics.impl)
             (SetU ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetU.
      rewrite <- H;auto.
    Qed.
    
 Global Instance perm_SetL :
      Proper (@Permutation TypedFormula ==>  Basics.impl)
             (SetL ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetL.
      rewrite <- H;auto.
    Qed.

Global Instance perm_LtX a :
      Proper (@Permutation TypedFormula  ==>  Basics.impl)
             (LtX a).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold LtX.
      rewrite <- H;auto.
    Qed. 
   
Lemma SetU_then_empty K : SetU K -> getL K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 
  
    
   Lemma SetL_then_empty K : SetL  K -> getU K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed.
  
 Global Instance trans_SetK :
       Proper (lt ==> @Permutation TypedFormula ==> Basics.flip Basics.impl)
             (LtX ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.flip; unfold Basics.impl .
      intros;subst.
      rewrite H0.
      eapply (LtXTrans _ _ _ H1);auto. 
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
 exists [], [].
 simpl;auto.
 destruct a as [a F].
 destruct (uDec a); simpl;
 rewrite e;simpl.
 exists x, x0.
 constructor;auto.
 exists ((a,F)::x), x0.
  simpl; rewrite e;simpl.
  constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.

  Theorem cxtDestructLtX i K: SetU K -> exists K', Permutation K (getLtX i K++getU K').
 Proof with sauto.
 induction K;intros...
 * exists nil...
 * destruct a as [a F].
    simpl in *.
    destruct (lt_dec i a)...
    inversion H...
    apply IHK in H3...
    exists x...
    rewrite <- app_comm_cons.
    rewrite <- H3...
    inversion H...
    apply IHK in H3...
    exists ((a,F)::x)...
    rewrite Permutation_app_comm.
    simpl...
    rewrite <- app_comm_cons.
    rewrite Permutation_app_comm.
    rewrite <- H3...
    Qed.

  Theorem cxtDestructNoLtX i K:Permutation K (getLtX i K++getNoLtX i K).
 Proof with sauto.
 induction K;intros...
 destruct a as [a F].
    simpl in *.
    destruct (lt_dec i a)...
    rewrite <- app_comm_cons.
    apply perm_skip...
   rewrite <- Permutation_middle.
   apply perm_skip...
Qed.

  Theorem cxtDestructNoLtX' i K: LtX i (getL K) -> SetU (getNoLtX i K).
 Proof with sauto.
 induction K;intros... 
 simpl...
 destruct a as [a F].
 simpl in *.
  destruct (uDec a)...
-
    destruct (lt_dec i a)...
apply Forall_cons...
   simpl...
apply IHK...
-
    destruct (lt_dec i a)...
 apply IHK...
inversion H...
inversion H...
Qed. 
        
 Lemma getLtXPerm a K1 K2 : Permutation K1 K2 -> Permutation (getLtX a K1) (getLtX a K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];simpl.
   destruct (lt_dec a x)... 
 * destruct x as [x F];
   destruct y as [y G];simpl.
   destruct (lt_dec a x);
   destruct (lt_dec a y)...   
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.
 
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

  Global Instance getLtX_morph a:
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getLtX a ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getLtXPerm;auto.
    Qed. 
    
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
     
      Lemma getLtX_fixpoint a K : getLtX a (getLtX a K) =  getLtX a K.
  Proof.
  induction K;auto.
  destruct a0;simpl;auto.
  destruct (lt_dec a s).
  simpl... 
  destruct (lt_dec a s).
  rewrite IHK; auto.
  contradiction.
  rewrite IHK; auto.
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
 
   Lemma getLtXApp a K1 K2 : getLtX a (K1 ++ K2) =  getLtX a  K1 ++ getLtX a  K2.
  Proof.
    induction K1;auto.
  destruct a0;simpl;auto.
  destruct (lt_dec a s).
  simpl. 
  rewrite IHK1;auto.
  rewrite IHK1;auto.
   Qed.
 
 Lemma getUApp' K1 K2 : Permutation (getU (K1 ++ K2)) (getU K1 ++ getU K2).
  Proof.
  rewrite getUApp;auto.
  Qed. 
 
 Lemma uIngetU i F K :  u i = true -> In (i, F) K -> In (i, F) (getU K).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction K...
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

Lemma lIngetL i F K :  u i = false -> In (i, F) K -> In (i, F) (getL K).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction K...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
 Qed.

Lemma lIngetU i F K :  u i = true -> In (i, F) K -> In (i, F) (getU K).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction K...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
  inversion H0...
 Qed.


  Theorem getUtoSetU K: SetU (getU K).
 Proof with subst;auto.
 induction K...  
 apply Forall_nil.
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
   Theorem getLtoSetU K: SetU (getL K) -> getL K =[].
 Proof with sauto.
 induction K;intros. 
 * auto.
 * destruct a as [a F].
   destruct (uDec a); simpl in *;
  rewrite e in *...
  inversion H...
 Qed.
 
 
 Lemma getUPerm_SetU K X : Permutation (getU K) X -> SetU X.
  Proof.
  intros.
  symmetry in H.
  rewrite  H.
  apply getUtoSetU.
 Qed. 
 
  Theorem getLtoSetL K: SetL (getL K).
 Proof with subst;auto.
 induction K...
 apply Forall_nil.
 
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
  Lemma getLPerm_SetL K X : Permutation (getL K) X -> SetL X.
  Proof.
  intros.
  symmetry in H.
  rewrite H.
  apply getLtoSetL.
 Qed. 
 
  Theorem setUtoGetU K: SetU K -> getU K = K.
 Proof with subst;auto.
 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.

  Theorem getUtoSetU' K:  getU K = K -> SetU K.
 Proof with sauto.
 induction K; intros...
 destruct a as [a F].
 simpl in H.
 destruct (uDec a)...
 apply Forall_cons...
 apply IHK...
 inversion H...
  rewrite H1...
  assert(SetU (getU K)) by apply getUtoSetU.
  rewrite H in H0.
  inversion H0...
 Qed.
 
  Theorem setLtoGetL K: SetL K -> getL K = K.
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
 
 Theorem Unb_Lin_Disj' K: exists K1 K2, SetU K1 /\ SetL K2 /\ Permutation K (K1++K2).
 Proof with sauto .
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
 rewrite H3...
  
 eexists x.
 eexists ((a,F)::x0).
 split...
 rewrite H3... 
  Qed.
 
 Lemma getUS F t D L: getU D = (t, F)::L -> u t = true.
 Proof with sauto.
 induction D;intros...
 destruct a.
 destruct (uDec s).
 inversion H...
 inversion H1...
 inversion H...
 Qed.
 
 Lemma ltConv a b K: lt a b -> exists K', Permutation (getLtX a K) (getLtX b K ++ K').
  Proof with sauto.
  revert dependent a. 
  revert dependent b. 
  revert dependent K. 
  
  induction K;intros...
  exists nil...
  destruct a.
  simpl...
  destruct (lt_dec b s)...
  destruct (lt_dec a0 s)...
  -
  apply IHK in H...
  exists x.
  rewrite H...
  - assert(lt a0 s).
     transitivity b;auto.
     contradiction.
 -
   destruct (lt_dec a0 s)...
   apply IHK in H...
   
   exists ((s, o) ::x).
  rewrite  H...
  Qed.

 Lemma ltConv' a b K: lt a b -> LtX b (getL K) -> exists K', Permutation (getLtX a K) (getLtX b K ++ getU K').
  Proof with sauto.
  revert dependent a. 
  revert dependent b. 
  revert dependent K. 
  
  induction K;intros...
  exists nil...
  destruct a.
  destruct (uDec s).
  * simpl in *...
  destruct (lt_dec b s)...
  destruct (lt_dec a0 s)...
  -
  apply IHK in H...
  exists x.
  rewrite H...
  - assert(lt a0 s).
     transitivity b;auto.
     contradiction.
 -
   destruct (lt_dec a0 s)...
   apply IHK in H...
   simpl in H0.
   exists ((s, o) ::x).
  rewrite  H...
  simpl...
  *
  simpl in *...
  destruct (lt_dec b s)...
  destruct (lt_dec a0 s)...
  -
  apply IHK in H...
  exists x.
  rewrite H...
  inversion H0...
  - assert(lt a0 s).
     transitivity b;auto.
     contradiction.
 -
   destruct (lt_dec a0 s)...
   inversion H0...
   inversion H0...
 Qed.  
  
  Lemma linearEmpty K : getL K = [] -> getL K = [] /\ Permutation (getU K) K /\ SetU K.
  Proof with sauto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  2:{
   destruct a as [p F].
  destruct (uDec p).
  simpl in H. rewrite e in H.
  apply Forall_cons...
  apply IHK...
  simpl in H. rewrite e in H.
  apply Forall_cons... }
  
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    apply IHK in H... 
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
Qed.
   
   Lemma bangUnb i K : u i = true -> LtX i (getL K) -> K = getU K.
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  simpl in H0.
  destruct (uDec p)...
  simpl...
  rewrite IHK...
  rewrite getU_fixpoint...
  inversion H0... 
  assert(u p = true).
  eauto.
  sauto.
Qed.


Lemma unboundedEmpty K : getU K = [] -> getU K = [] /\ Permutation (getL K) K /\ SetL K.
  Proof with sauto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
   2:{
   destruct a as [p F].
  destruct (uDec p).
  simpl in H. rewrite e in H.
  apply Forall_cons...
  simpl in H. rewrite e in H.
  apply Forall_cons... 
  apply IHK...
  }
 
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
     apply IHK in H... 
 Qed.
 
  Lemma SetK4Destruct  K : SetU K -> SetU (getU K) /\ SetU (getL K).
  Proof with sauto.
  intros.
  rewrite cxtDestruct in H;split;
  apply Forall_app in H...
  Qed.

  Lemma SetK4DestructL  K : SetL K -> SetL (getU K) /\ SetL (getL K).
  Proof with sauto.
  intros.
  rewrite cxtDestruct in H;split;
  apply Forall_app in H...
  Qed.
 
 Lemma InContext1 F CD C D:
  Permutation (getU CD) (getU C) ->
  Permutation (getU CD) (getU D) ->
  Permutation (getL CD) (getL C ++ getL D) ->
  In F C ->  In F CD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.

 Lemma InSecond1 F CD C D:
  Permutation (getU CD) (getU C) ->
  Permutation (getU CD) (getU D) ->
  Permutation (getL CD) (getL C ++ getL D) ->
  In F (second C) ->  In F (second CD).
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
  
  
  
 Lemma InContext2 F CD C D:
  Permutation (getU CD) (getU C) ->
  Permutation (getU CD) (getU D) ->
  Permutation (getL CD) (getL C ++ getL D) ->
  In F D ->  In F CD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.
  
  Lemma InSecond2 F CD C D:
  Permutation (getU CD) (getU C) ->
  Permutation (getU CD) (getU D) ->
  Permutation (getL CD) (getL C ++ getL D) ->
  In F (second D) ->  In F (second CD).
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
 
   Lemma simplUnb CD C D:          
  Permutation (getU CD) (getU D) ->
  Permutation (getL CD) (getL C ++ getL D) ->
  SetU C -> Permutation CD D.
  Proof.   
  intros.
  rewrite (SetU_then_empty _ H1) in H0.
  rewrite (cxtDestruct CD).
  rewrite H0.
  rewrite H.
  simpl. 
  rewrite <- cxtDestruct;auto.
  Qed.
  
  Lemma simplUnb' CD C D:          
  Permutation (getU CD) (getU C) ->
  Permutation (getL CD) (getL C ++ getL D) ->
  SetU D -> Permutation CD C.
  Proof.   
  intros.
  rewrite (SetU_then_empty _ H1) in H0.
  rewrite (cxtDestruct CD).
  rewrite H.
  rewrite H0;sauto.
  rewrite <- cxtDestruct;auto.
  Qed.
 
  Lemma isFormulaL_getU K :  
      isFormulaL (second K) -> isFormulaL  (second (getU K)). 
  Proof.
    induction K;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - 
      simpl in *.
      inversion H;sauto.
      apply Forall_cons;sauto.
    -
      simpl in *.
      inversion H;sauto.
  Qed.    
    
    Lemma isFormulaL_getL  B :  
      isFormulaL  (second B) -> isFormulaL  (second (getL B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - simpl in *.
      inversion H;sauto.
   -  simpl in *.
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
    
 
  
 
  Lemma isFormulaSecond1  BD X Y B Z U:
  isFormulaL  (second (X++getU BD++Y)) -> 
  Permutation (X++getU BD++Y) (Z++B++U) ->
  isFormulaL  (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL  (second (Z ++ B ++ U))).
   symmetry in H0.
   autounfold.
   unfold second.
   rewrite H0...
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
   autounfold.
   unfold second.
   rewrite H0...
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
 
 End Properties.
 
  End SubExpSets.

 Global Hint Resolve USetU getUtoSetU: core.

(* Global Hint Resolve LtXRefl: core. *)

Global Hint Extern 1 (LtX ?a ?K) =>
  match goal with
  | H: LtX ?i ?K,  H1: lt ?a ?i |- _ =>  apply (LtXTrans _ _ _ H H1)
  end : core.
  
  
Ltac solveLT :=  
try
 match goal with
   | [ |- lt ?x ?x ] => reflexivity
   | [H: lt ?x ?y, H2: lt ?y ?z |- lt ?x ?z ] => transitivity y;auto
   | [H: lt ?x ?y, H2: LtX ?y ?K |- LtX ?x ?K ] => rewrite H;auto
   | [H: Permutation ?K ?K', H2: LtX ?x ?K' |- LtX ?x ?K ] => rewrite H;auto
    | [H: Permutation ?K ?K', H2: LtX ?x ?K |- LtX ?x ?K' ] => rewrite <- H;auto  
 
  end;auto.
  
(*   Lemma asasa (OLS : OLSig)  (SI : SigSELL) x y K: lt y x -> lt x K -> lt y K. *)
  
  
  
(* Forall_nil: Forall P []
Forall_inv: Forall P (a :: l) -> P a
ForallIn: Forall f L -> In F L -> f F
Forall_inv_tail: Forall P (a :: l) -> Forall P l
Forall_cons: P x -> Forall P l -> Forall P (x :: l)
Forall_forall: Forall P l <-> (forall x : A, In x l -> P x)

PermuteMap: Forall f L -> Permutation L L' -> Forall f L'

Forall_impl:
  (forall a : A, P a -> Q a) ->
  forall l : list A, Forall P l -> Forall Q l

Permutation_Forall:
  forall [A : Type] [P : A -> Prop],
  Proper (Permutation (A:=A) ==> Basics.impl) (Forall P)

Forall_elt: Forall P (l1 ++ a :: l2) -> P a

ForallInP: Forall f L -> Permutation L (F :: L') -> f F

Forall_cons_iff: Forall P (a :: l) <-> P a /\ Forall P l
Forall_and: Forall P l -> Forall Q l -> Forall (fun x : A => P x /\ Q x) l

Forall_dec:
  (forall x : A, {P x} + {~ P x}) ->
  forall l : list A, {Forall P l} + {~ Forall P l}

Forall_and_inv:
  Forall (fun x : A => P x /\ Q x) l ->
  Forall P l /\ Forall Q l

exists_Forall:
  (exists k : A, Forall (P k) l) ->
  Forall (fun x : B => exists k : A, P k x) l

Forall_map:
  Forall P (map f l) <-> Forall (fun x : A => P (f x)) l

Forall_app:
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2

Forall_flat_map:
Forall P (flat_map f ls) <->
 Forall (fun d : A => Forall P (f d)) ls

map_ext_Forall:
  forall [A B : Type] (f g : A -> B) [l : list A],
  Forall (fun x : A => f x = g x) l -> map f l = map g l

Forall_rect:
  forall [A : Type] [P : A -> Prop] (Q : list A -> Type),
  Q [] ->
  (forall (b : A) (l : list A), P b -> Q (b :: l)) ->
  forall l : list A, Forall P l -> Q l

getUtoSetU getLtoSetL
uIngetU lIngetL lIngetU *)

  
  Section Locations.
  Context `{SI : SigSELL}.
  Context `{OLS : OLSig}.
  
   Lemma asasa i K : u  i = true -> LtX i (getL K) -> K = getU K.
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  simpl in H0.
  destruct (uDec p)...
  simpl...
  rewrite IHK...
  rewrite getU_fixpoint...
  inversion H0... 
  assert(u p = true).
  eauto.
  sauto.
Qed.

  End Locations.
  
Global Hint Resolve getUtoSetU : ExBase.
Global Hint Unfold  SetU SetL getU getL: core.

(* 
 Global Hint Unfold SetU SetL:core. 
Global Hint Resolve  USetU: core.
Global Hint Resolve SetUKClosure   getUtoSetU getLtoSetL: core. *)

(* Global Hint Resolve linearInUnb: core.
 *)


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

 
  | [H: SetU ?K, H1: SetL ?K |- _  ] =>  assert(K=[]) by apply (SETXempty _ _ H H1);clear H H1 
 
  | [H: SetL ?K, H0: LtX ?i ?K, H1:  u ?i = true |- _  ] =>  assert(K=[]) by apply (SETXLTEmpty _ _ H H0 H1);clear H 

  | [  |- context[getL(getU _)] ] => setoid_rewrite getLgetU 
  | [ H: context[getL(getU _)] |- _  ] => setoid_rewrite getLgetU in H
  | [  |- context[getU(getL _)] ] => setoid_rewrite getUgetL 
  | [ H: context[getU(getL _)] |- _  ] => setoid_rewrite getUgetL in H
 
  | [ H: SetU ?K |- context[getL ?K] ] => setoid_rewrite (SetU_then_empty _ H)
  | [ H1: SetU ?K, H2: context[getL ?K] |- _ ] => setoid_rewrite (SetU_then_empty _ H1) in H2

  | [ H: SetL ?K |- context[getU ?K] ] => setoid_rewrite (SetL_then_empty _ H)
  | [ H1: SetL ?K, H2: context[getU ?K] |- _ ] => setoid_rewrite (SetL_then_empty _ H1) in H2
  
   
 | [ H: SetU (getL ?K)  |- context[getL ?K] ] => setoid_rewrite (getLtoSetU _ H)
  | [H0: SetU (getL ?K), H: context[getL ?K] |- _  ] => setoid_rewrite (getLtoSetU _ H0) in H

 | [H: SetU (getL ?K) |- context[getL ?K]  ] => setoid_rewrite (getLtoSetU _ H)
 
  | [H: SetU (getL ?K), H1: context[getL ?K] |- _  ] => setoid_rewrite (getLtoSetU _ H) in H1
end.


Ltac simplFix := 
 repeat    
  multimatch goal with

 | [  |- context[getU (getU _)] ] => setoid_rewrite getU_fixpoint
 | [H:  context[getU (getU _)]  |- _ ]  => setoid_rewrite getU_fixpoint in H

 | [  |- context[getL (getL _)] ] => setoid_rewrite getL_fixpoint
 | [H:  context[getL (getL _)]  |- _ ]  => setoid_rewrite getL_fixpoint in H

 | [H: SetU ?K  |- context[getU ?K] ] => setoid_rewrite (setUtoGetU _ H)
 | [H: SetU ?K, H1: context[getU ?K]  |- _ ]  => setoid_rewrite (setUtoGetU _ H) in H1

 | [H: SetL ?K  |- context[getL ?K] ] => setoid_rewrite (setLtoGetL _ H)
 | [H: SetL ?K, H1: context[getL ?K]  |- _ ]  => setoid_rewrite (setLtoGetL _ H) in H1

end.




Ltac simplCtx :=
 multimatch goal with
 
 | [  |- context[getU(_++_)] ] => setoid_rewrite getUApp
 | [  |- context[getL(_++_)] ] => setoid_rewrite getLApp
 | [ H: context[getU(_++_)] |- _ ] => setoid_rewrite getUApp in H
 | [ H: context[getL(_++_)] |- _ ] => setoid_rewrite getLApp in H
  | [  |- context[(second (getU ?K++getL ?K))] ] => setoid_rewrite <- cxtDestructSecond
 | [ H:context[(second (getU ?K++getL ?K))] |- _ ] => setoid_rewrite <- cxtDestructSecond in H 
end. 

 
(* Ltac solveSignature2 :=
 match goal with
  | [ H: SetU ?K |- SetU (getU ?K)] => apply SetK4Destruct in H;sauto
  | [ H: SetL ?K |- SetL (getL ?K)] => apply SetK4Destruct in H;sauto

| [ H: SetU ?K, H2: Permutation (getU ?K) (?K2 ++ _) |- SetU ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2
 | [ H: SETX ?s ?b ?K, H2: Permutation (getU ?K) (_ ++ ?K2) |- SETX ?s ?b ?K2] => 
   let H' := fresh "H" in
          apply SetK4Destruct in H; destruct H as [H H'];rewrite H2 in H;solveSignature2

  | [H: Permutation (getU ?CN) (_ ++ ?M) |- SetU ?N] =>  apply getUPerm_SetU in H;solveSignature2
  | [H: Permutation (getU ?CN) (?M ++ _) |- SetU ?M] =>  apply getUPerm_SetU in H;solveSignature2

 | [ H1: u ?i = false, H2: In (?i, ?F) ?B  |- In (?i, ?F) (getL ?B) ] => apply lIngetL;auto

end.
 *)   
   
 
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
