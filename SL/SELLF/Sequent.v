Require Export LL.SL.SELLF.Locations.

Export ListNotations.
Set Implicit Arguments.

Section LLSequent.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.

  
  Reserved Notation " '|-f-' B ';' L ';' X " (at level 80).

  (** The same system without the height of the derivation *)
  Inductive seq:  list TypedFormula -> list oo -> Arrow -> Prop :=
  | tri_init1' : forall B A ,  SetU B ->  |-f- B ; [atom A] ; DW (perp A)
  | tri_init2' : forall B C A i, SetU C ->  Permutation ((i, atom A)::C) B -> |-f- B ; [] ; DW (perp A)
  
  | tri_one' : forall B, SetU B -> |-f- B ; [] ; DW One
  | tri_tensor' : forall M N MN B D BD F G, Permutation MN (M++N) -> 
                                      Permutation (getU BD) (getU B) ->
                                      Permutation (getU BD) (getU D) ->
                                      Permutation (getL BD) (getL B ++ getL D) ->
                                       |-f- B ; M ; DW F ->
                                        |-f- D ; N ; DW G ->
                                        |-f- BD ; MN ; DW (MAnd F G)
  | tri_plus1' : forall B M F G ,
      |-f- B ; M ; DW F -> |-f- B ; M ; DW (AOr F G)
  | tri_plus2' : forall B M F G,
      |-f- B ; M ; DW G -> |-f- B ; M ; DW (AOr F G)
  | tri_rel' : forall B F L,
      negativeFormula F -> |-f- B ; L ; UP [F] ->  |-f- B ; L ; DW F
  | tri_top' : forall B L M,
      |-f- B ; L ; UP (Top :: M)
  | tri_bot' : forall B L M,
      |-f- B ; L ; UP M -> |-f- B ; L ; UP (Bot :: M)
  | tri_par' : forall B L M F G,
      |-f- B ; L ; UP (F::G::M) -> |-f- B ; L ; UP((MOr F G) :: M)
  | tri_with' : forall B L M F G,
      |-f- B ; L ; UP (F :: M) ->
      |-f- B ; L ; UP (G :: M) -> |-f- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest' : forall B L M F i,
      |-f- (i,F)::B ; L ; UP M -> |-f- B ; L ; UP ((Quest i F) :: M)         
  | tri_store' : forall B L M F,
      positiveLFormula  F-> |-f- B ; F::L; UP M -> |-f- B ; L ; UP (F::M)
  | tri_dec1' : forall B L L' F,
      positiveFormula F -> Permutation (F::L') L -> |-f- B ; L' ; DW F -> |-f- B ; L ; UP []
  | tri_dec2u' : forall B L F i,
     u i = true ->  ~IsPositiveAtom F -> In (i,F) B -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_dec2l' : forall B B' L F i,
     u i = false -> ~IsPositiveAtom F -> Permutation ((i,F)::B') B -> |-f- B' ; L ; DW F -> |-f- B ; L ; UP []

  | tri_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-f- B; M ; DW (FX t) -> |-f- B; M ; DW (Some  FX)
  | tri_fx'  : forall B L FX M ,
      uniform_oo FX -> (forall x, proper x -> |-f- B ; L ; UP( (FX x) ::  M)) ->
      |-f- B ; L ; UP ((All FX) :: M) 
 | tri_bangL' : forall B F a,
    SetU B -> |-f- B ; [] ; (UP [F]) -> |-f- B ; [] ; DW (Bang a F)
                                                                                     
  where "'|-f-' B ';' L ';' X " := (seq B L X).

Variable eqS : subexp -> subexp -> bool.
Variable addF : list TypedFormula -> subexp -> oo -> list TypedFormula.

Definition TForm := prod subexp (list oo).
Fixpoint getLocation (K: list TypedFormula) a :=
match K with
| nil => nil
| (b, B)::L => if eqS b a then [B]++getLocation L a else getLocation L a

end.

Fixpoint addLocation (K: list TForm) a F :=
match K with
| nil => nil
| (b, B)::L => if eqS b a then (a,F::B)::L else 
                       (b,B)::(addLocation L a F)

end.

 
Variable a b c : subexp.
Variable A B C : oo.

  Theorem exchangeLC LC CC: forall CC' LC'  (X: Arrow),
        Permutation LC LC' -> Permutation CC CC' ->
        ( |-f- CC ; LC ; X) -> |-f- CC' ; LC' ; X.
      Admitted.  
 
    Global Instance seq_morphism  :
      Proper ((@Permutation TypedFormula) ==> (@Permutation oo) ==> eq ==> iff)
             (seq ).
    Proof.
    
     Admitted.


  Inductive isIndex : subexp -> list TypedFormula -> Prop :=
  | isInd1: forall a F L, isIndex a ((a,F)::L)
  | isInd2: forall a a' F L,  isIndex a L -> isIndex a ((a',F)::L).
  

  Inductive leIndex : subexp -> list TypedFormula ->  list TypedFormula -> Prop :=
  | leInd1: forall a, leIndex a nil nil
  | leInd2: forall a a' F G L1 L2, 
  lt a a' -> leIndex a L1 L2 -> leIndex a ((a',F)::L1) ((a',G)::L2).
  
  

Eval compute in split [(a,A);(b,B);(c,C)].


Lemma leIndexEx : lt a a -> lt a c -> lt b a -> leIndex a [(a,A);(b,B);(c,C)] [(a,A);(c,C)].
Proof with sauto.
intros.
constructor... 
constructor... 


admit.


simpl.
split;intros.
    
Lemma isIndexEx k K: isIndex k K <-> In k (first K).
Proof with sauto.
split;intros.
-
induction H... 
all:simpl...
-
induction K...
inversion H.
destruct a0.
simpl...
inversion H... 

all:constructor...
Qed.  
  
  
Inductive isIndex x (K: list TypedFormula) :=
| isInd1 : forall F:oo, isIndex x ((x, F)::K) .
| isInd2 : forall b F, isIndex a K -> isIndex a ((b,F)::K).
          
Lemma aasasas (d:subexp) L X (D1 D2 D:list oo): Permutation D (D1++D2) -> seq [(d,D)] L X -> seq [(d,D1);(d,D2)] L X.
intros.


intros Ha Hc.
simpl.
rewrite Hc, Ha.


Definition eqSS := eqS a a = true.

Lemma aasasas : eqS a a = true -> eqS c a = false -> addLocation ([(a,[A]);(c,[B]);(a,[C])]) a B = [].
intros Ha Hc.
simpl.
rewrite Hc, Ha.


auto.

Eval compute in getLocation a ([(a,A);(a,B);(c,C)]).


Print TypedFormula.

Lemma asas B L a F: seq B L (UP [Quest a F]) -> False.
Proof with sauto.
intros.
inversion H...
2: inversion H4.

inversion SI...
Abort.
  
End LLSequent .

Lemma asas: PreOrder le.
Admitted.

Variable ub : nat -> bool.
Lemma asas1 : forall x y : nat, ub x = true -> x <= y -> ub y = true.
Admitted.

Search "PreOrder" "le".
#[local]Instance SimpleSignagture : Signature:=
  {|
    subexp := nat;
    lt_pre := asas; 
    lt_dec := Compare_dec.le_dec;
    u := ub;
    uClosure := asas1
  |}.

Lemma asasasa: u 0 = true.
Admitted.

Lemma Test {OLS: OLSig} B L a F: seq B L (UP [Quest a F]) -> False.
Proof with sauto.
intros.
inversion H...
2: inversion H4.
assert (u 1 = true).
eapply uClosure with (x:=0)...
apply asasasa.
simpl. 
auto.
assert(In 0 (first B)).
destruct B.
all:simpl...
2:{ destruct t. 
simpl in *...
destruct s. 
2:{ ..


destruct a.
2:{


Module FLLNotations .

Notation "n ⊢ B ';' L ⇕ X " := (seqN _ n B L X)  (at level 80).
Notation "n ⊢ B ';' L ⇓ F " := (seqN _ n B L (DW F))  (at level 80).
Notation "n ⊢ B ';' L ⇑ F " := (seqN _ n B L (UP F))  (at level 80).
Notation "⊢ B ';' L ⇕ X " := (seq _ B L X)  (at level 80).
Notation "⊢ B ';' L ⇓ F " := (seq _ B L (DW F))  (at level 80).
Notation "⊢ B ';' L ⇑ F " := (seq _ B L (UP F))  (at level 80).

End FLLNotations .

Global Hint Constructors seqN seq: core .
