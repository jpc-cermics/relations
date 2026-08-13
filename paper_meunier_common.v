(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & datest) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".
From RL Require Import  seq1 seq2 rel.

From RL Require Import  paper_monochromatic_f. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "A [<=] B" (at level 4, no associativity). 
(* set order derived from strict porder on elements *)
Reserved Notation "A [<= U ] B" (at level 4, no associativity). 
(* strict set order derived from set order *)
Reserved Notation "A [<< U ] B" (at level 4, no associativity).

Definition leSet T U: relation (set T) := 
  [set AB |forall (a:T), (a \in AB.1) -> exists b, b \in AB.2 /\ ( a = b \/ U (a,b)) ].

Notation "A [<= U ] B" := (leSet U (A,B)).
Notation "[<= U ]%O" := (leSet U).
Notation "A [<< U ] B" := ((('Δ).^c `&` (leSet U)) (A,B)). 
Notation "[<< U ]%O" := (('Δ).^c `&` (leSet U)).

Definition pre_absorbant {T: Type} (U M: relation T) (S:set T) := S:#U `<=` M#S.

Definition absorbant {T: Type} (M: relation T) := 
  [set S: set T| forall y, ~ (y \in S) -> (y \in M#S)].

Definition preKernel {T: Type} (O U M: relation T) :=
  [set S| RelIndep O S /\ (pre_absorbant U M S) /\ S != set0 ].

Definition Kernel {T: Type} (U: relation T) :=
  [set S| RelIndep U S /\ absorbant U S].

Definition leSet' T U: relation (set T) := [set AB | AB.1 `<=` ('Δ  `|` U)#AB.2]%classic. 

Section preKernel.

  Context {T : choiceType} (U: relation T).
  
  Lemma absorbant_not_empty (S: set T): 
    (nonempty [set: T]) -> absorbant U S -> ~ (S = set0).
  Proof.
    move => [t _] + Hne; rewrite {}Hne /absorbant => /(_ t) /=.
    have ->: t \in set0 = false by rewrite [t \in set0]inE;apply/asboolP.
    move => H1.
    have: t \in U#set0 by apply: H1.
    by rewrite inE => -[y [_ ?]].
  Qed.

End preKernel.

Section CheckAsym. 
  (** * Import main result from paper_monochromatic_f *)
  Context {T : choiceType} (U: relation T).
  Hypothesis A1: (nonempty [set: T]).

  Import Asyminf2Inf(Asym2P5', allL_rc_asym).

  (* begin snippet infasym:: no-out *) 
  Lemma iic_asym_to_iic_inj:  (iic (Asym U.+)) -> (iic_inj U). 
  (* end snippet infasym *)  
  Proof. by apply: (@Asym2P5' T U A1). Qed.

  Lemma not_iic_inj_to_not_iic_asym: ~ (iic_inj U) -> ~ (iic (Asym U.+)).
  Proof. by move => ? /iic_asym_to_iic_inj ?. Qed.

End  CheckAsym. 

Module iic_asym.
  Section iic_asym. 
  (** * iic_asym_injective:  iic (Asym R.+) -> iic_inj (Asym R.+) *) 
    Context {T : Type}.
    Implicit Types (T : Type) (U: relation T) (A B: set T).
    
    #[local] Lemma iic_asym_L1 (f : nat -> T) U:
      (forall n, (Asym U.+) ((f n),(f n.+1))) -> 
      forall p n, 0 < p -> (Asym U.+) (f n, f (n + p)). 
    Proof.
      move => Hi. 
      elim => [// | p Hr n' _].
      case H2: (p == 0); first by move: H2 => /eqP ->;rewrite addn1;apply: Hi. 
      move: H2 =>  /neq0_lt0n /(Hr n') H2.
      have H4: transitive (Asym U.+) by apply: Asym_preserve_transitivity;apply: TclosT.
      have H5: Asym U.+ (f (n' + p), f (n' + p).+1) by apply: Hi.
      rewrite /transitive in H4.
      move: (H4 (f n') (f (n' + p)) (f (n'+p).+1) H2 H5).
      by rewrite -addn1 -[p.+1]addn1 addnA.
    Qed.
    
    #[local] Lemma iic_asym_L2 (f : nat -> T) U:
      (forall n, (Asym U.+) ((f n),(f n.+1))) -> 
      forall p n, 0 < p -> ~ (f n) = f (n + p). 
    Proof.
      by move => + p n H1 => /iic_asym_L1 /(_ p n H1) + H2;rewrite -H2; apply: Asym_irreflexive.
    Qed.
    
    #[local] Lemma iic_asym_L3 (f : nat -> T) U:
      (forall n, (Asym U.+) ((f n),(f n.+1))) -> injective f.
    Proof.
      have H0 n m: m < n -> exists p, p> 0 /\ n = m + p by move => H1;exists (n-m); lia.
      move => /iic_asym_L2 Hi p q;apply contraPP => H1.
      have [H2|H2]: (p < q \/ q < p) by lia.
      by move: (H0 q p H2) => [p' [H3 ->]];apply: Hi.
      by move: (H0 p q H2) => [p' [H3 ->]];move: (Hi p' q H3);symmetry.
    Qed.
    
    Lemma iic_asym_injective U: iic (Asym U.+) -> iic_inj (Asym U.+).
    Proof. by move => [f /[dup] ? /iic_asym_L3  ?];exists f. Qed.

    Lemma sporder_iic_injective U: (sporder U) -> iic U -> iic_inj U.
    Proof. by move => /sporderEq <-;apply: iic_asym_injective. Qed.
    
    End iic_asym.
End iic_asym.

Export iic_asym(iic_asym_injective,  sporder_iic_injective).

Module iic_paths.
  Section iic_paths.
    (** * Assumptions on infinite paths *)
    (* should be move on rel.v *)
    Context {T : Type}.
    Implicit Types (U V: relation T) (X: set T).

  Lemma notiic_rloop_sub_L1 X (U: relation X):
    (nonempty [set: X]) -> ~ (iic (Asym U)) -> (Rloop U).
  Proof. 
    by move => Hne Hniic;apply: (notiic_rloop Hne Hniic).
  Qed.
  
  Lemma notiic_rloop_sub_L2 X V:
    (nonempty [set: X]) -> ~ (iic (Asym V)) -> (Rloop (@Restrict' T X V)).
  Proof.
    have H3:  ~ (iic (Asym V)) -> ~ (iic (@Restrict' T X (Asym V)))
      by contra;move => [f // ?];exists (fun n => (sval (f n))). 
    move => Hne /H3 Hiic.
    by apply/(@notiic_rloop_sub_L1 X (@Restrict' T X V) Hne).
  Qed.
  
  (* notiic_rloop for a subset X *)
  Lemma notiic_rloop_sub X V:
    (nonempty [set: X]) -> ~ (iic (Asym V))
    -> (exists (v:T), v \in X /\ forall w, w \in X -> V (v,w) -> V (w,v)).
  Proof.
    move => H0 Ninf.
    move: (notiic_rloop_sub_L2 H0 Ninf) => [v H1];exists (sval v).
    split=> [| w H2];first by rewrite inE;apply: set_valP.
    have [w' <-]: exists (w': X), (sval w') = w by (exists (exist _ w H2)).
    by move => ?;apply: H1.
  Qed.
  
  End iic_paths.
End iic_paths.

Export iic_paths(notiic_rloop_sub).

Section set_relation. 
  (** * A relation on sets induced by a relation on elements *)

  Context {T : eqType}.
  Implicit Types (T : eqType) (U S: relation T) (A B: set T).
  
  Lemma lesetE U: leSet U = leSet' U. 
  Proof.
    rewrite predeqE => -[A B];split. 
    - move => H1 a /mem_set/H1 [b [/set_mem H2 [->| H3]]]; first by (exists b);split;[left|].
      by (exists b);split;[right|].
    - rewrite /leSet' /mkset /= -FsetUl Fset_D.
      move => H1 a /set_mem/H1 [/mem_set H2 | [b [H2 /mem_set H3]]].
      by (exists a); split;[ | left].
      by exists b; split;[ | right].
  Qed.
  
  (* begin snippet lesetI:: no-out *)   
  Lemma Ile U A B: A `<=` B -> A [<= U] B.
  (* end snippet lesetI *)
  Proof. by move => H1 /= a /set_mem/H1 ?;exists a;split;[rewrite inE|left]. Qed.

  Lemma leI U S: S `<=` U -> ([<= S]%O)  `<=` ([<= U]%O).
  Proof.
    move => H1;rewrite 2!lesetE => [[A B]] H2.
    by apply: subset_trans H2 _;apply: Fset_inc; apply: setUS.
  Qed.
  
End set_relation.

Section Set_order. 
  (** * the previous relation [<= U] is an order relation on U-independent sets *)

  Context (T: eqType).
  Implicit Types (U S: relation T) (A B: set T).
  
  Axiom proof_irrelevance: forall (P : Prop) (p q : P), p = q.
  
  Section Util.
    (** ingredients *)
    Lemma le_trans_if_tr U: transitive U -> transitive ([<= U]%O).
    Proof.
      rewrite lesetE => /Tclos_iff H0 A B C /= H1 H2.
      have : ('Δ  `|` U)#B `<=` ('Δ  `|` U)#(('Δ  `|` U)#C) by apply: Fset_inc1.
      rewrite Fset_comp H0 DuT_eq_Tstar compose_rt_rt -DuT_eq_Tstar -H0 => H3.
      by apply: subset_trans H1 H3.
    Qed.

    Lemma le_refl  U: reflexive (leSet U).
    Proof. by move => A r H1;exists r;split;[| left]. Qed.
    
    Lemma le_antisym_if_sp' U: 
      sporder U -> forall A B, (RelIndep U A) -> A [<= U] B -> B  [<= U] A -> A `<=` B.
    Proof.
      move => /[dup] -[_ Htr] /sporder_asym/AsymEq Asy A B H1 + +  a H4.
      rewrite -Asy => H2 H3.
      move: (H4) => /mem_set /H2 [b [/set_mem /= H5 [-> // | [H6 H6']]]]. 
      move: (H5) => /mem_set /H3 /= [c [/set_mem H8 H9]].
      case H10: (a == b ); first by move: H10 => /eqP ->.
      move: H10 => /eqP H10.
      case H12: (b == c).
      - move: H12 H8 => /eqP <- H8.
        by have: False by move: H4 H8 => /mem_set H4 /mem_set H8;apply: (H1 a b). 
      - move: H12 H9 => /eqP H12 [H9 // | [H9 H9']].
        case H13: (a == c); first by move: H13 H9' => /eqP <- H9'.
        pose proof Htr.
        have H14: U (a,c) by apply: Htr H6 H9.
        by have: False by move: H13 H4 H8 => /eqP H13 /mem_set H4 /mem_set H8; apply: (H1 a c). 
    Qed.
    
    Lemma le_antisym_if_sp U: 
      sporder U ->
      forall A B, (RelIndep U A) -> (RelIndep U B) 
             -> A [<= U] B -> B  [<= U] A -> A = B.
    Proof.
      move => Hsp A B H1 H2 H3 H4.
      by move: (le_antisym_if_sp' Hsp H1 H3 H4)
                 (le_antisym_if_sp' Hsp H2 H4 H3);rewrite eqEsubset.
    Qed.
  
  End Util.
  
  (* begin snippet lesetporder:: no-out *)   
  Lemma leSet2_porder U: 
    sporder U -> 
    @porder {S: set T| RelIndep U S} [set AB | (sval AB.1) [<= U] (sval AB.2)].
  (* end snippet lesetporder  *)   
  Proof.
    move => H_sp.
    split => [ [A ?] | [A Ha] [B Hb] H1 H2 | [A ?] [B ?] [C ?]].
    + (* reflexive *) by apply/le_refl.
    + (* antisymmetric *) 
      move: (le_antisym_if_sp H_sp Ha Hb H1 H2) => H5.
      subst A;apply: f_equal;apply: proof_irrelevance.
    + (* transitive *) by move: H_sp => [_ ?];apply/le_trans_if_tr.
  Qed.
  
End Set_order. 


Section Assumptions. 

  (*  abstract version *)
  Context (T: Type). 
  Implicit Types (R B O M: relation T).
  
  Definition Assumption1:= (nonempty [set: T]).
  Definition Assumption2 R:= ~ (iic (Asym R)).
  Definition Assumption3 O:= ~ (iic O).
  Definition Assumption4 O:= sporder O.
  Definition Assumption5 O M := O  `<=` M `|` M^-1.
  Definition Assumption6 B M O:= 
    (forall x y, B (x,y) /\ ~ (M (y, x)) -> O (x,y)).
  
  Definition Assumption7 R B M:= 
    (forall x x' y y', ~(x' = x) 
                  -> R (x,y') -> M (y', x')
                  -> (B (x',y)) -> ~ (B (x, y)) 
                  -> ~ (R (x',y)) /\ ~(M (y,x')) 
                  -> ~(R (x,y)) /\ ~(M (y,x)) 
                  -> ~ (M (x,x')) -> ~ (M (x',x))
                  -> ~ (y = y') -> ~ (y' = x) -> ~ (y' = x') -> ~ (y = x ) -> ~ (y = x' )
                  -> ~ (M (y',x))
                  -> (M (y',y))).
  
  Definition Assumption8 R B M:=
    (forall x' y y', ~ (y' = x') -> ~ (y = y') -> ~ (y = x') 
                -> R (y,y') -> M (y',x') -> B (x',y) 
                -> ~ (R (x',y)) /\ ~ M (y, x')
                -> (M (y',y))).
  
  Definition Assumption9 R B O M:= 
    (forall x y x' y' , ~ (x = y) -> ~ (x = x') -> ~ (x = y')
                   -> ~ (y = x') -> ~ (x' = y') -> ~ (y' = y) 
                   -> R (x,y) -> M (y,x') -> O (x',y') -> ~(M (y,x)) 
                   -> ~ ((M `|` M^-1) (x',x))
                   ->  ~ ((M `|` M^-1) (y',x))
                   -> M (y,y')).

End Assumptions. 

Module Extend_non_absorbant_preKernel.
  (** * if X is in preKernel but not a kernel there exists X' such that *)
  (** * X <= X' (X != X') and X' is also in preKernel *)
  Section Extend_non_absorbant_preKernel.
    
    Context {T:choiceType} (R B O: relation T).
  
    Notation M := (B `|` R).

    Lemma preKernelProp: forall S S1,
        RelIndep M S -> S1 `<=` S -> (S1:#(R) `<=` M#S <-> forall y, ~ (y \in S) -> y \in S1:#(R) -> y \in M#S).
    Proof.
    move => S S1 H1 H1';split => [H2 y _ /set_mem/H2/mem_set H4 //| H2 y H3].
    case H5: (y \in S);last first.
    + apply/set_mem/H2. by rewrite H5. by apply/mem_set.
    + move: H3. rewrite /Aset => -[y' [H6 H7]].      
      rewrite /RelIndep in H1.
      case H8: (y == y').
      ++ move: H8 => /eqP H8; have H9: M (y,y) by rewrite -H8 in H6;rewrite /M;right.
         by move: H7 => /H1' H7;(exists y);rewrite -H8 in H7.
      ++ move: H8 H7 => /eqP H8 /mem_set H7.
         have H9:  y' <> y by move => H10;rewrite H10 in H8.
         move: H7 => /set_mem/H1'/mem_set H7.
         move: (H1 y' y H7 H5 H9) => H10.
         by have H11: M (y', y) by rewrite /M;right.
  Qed.
  
  Lemma preKernelProp1: forall S,
      RelIndep M S -> (S:#(R) `<=` M#S <-> forall y, ~ (y \in S) -> y \in S:#(R) -> y \in  M#S).
  Proof. move => S H1; apply: (preKernelProp H1 (@subset_refl T S)).  Qed.
  
  Variable (X: set T).
    
  (* begin snippet Sx:: no-out *)    
  Definition Y:= [set y | ~ (y \in X) /\ ~ (y \in M#X)].
  (* end snippet Sx *)       
  
  Lemma not_absorbant_iff: 
    ~ (absorbant M X) <-> exists y, y \in Y. 
  Proof.
    split;last by move => [y +] Hma;rewrite inE => [[/Hma ? ?]].
    contra => + y Hy => /(_ y). 
    by rewrite (@notin_setE T Y y) /Y /=  not_andE => -[? // |/contrapT ?].
  Qed.
  
  (** * C'est l'ensemble X_y de la nouvelle preuve *)
  (* begin snippet Tm:: no-out *)    
  Definition Xy y:= [set x | x \in X /\ (B (x,y))].
  (* end snippet Tm *)       
  
    (* begin snippet TmI:: no-out *)    
    Lemma XyI: forall y, Xy y `<=` X.
    (* end snippet TmI *)       
    Proof. by move => x y [/set_mem H2 _]. Qed.
    
    Lemma Xpart: forall y, ( X `\` (Xy y)) `|` (Xy y) = X.
    Proof. move => y;apply: (@setDKU T (Xy y) X);apply: XyI. Qed.
    
    (* begin snippet Sxm:: no-out *)    
    Definition SeP y := forall y', y' \in Y -> R(y,y') -> R(y',y).
    (* end snippet Sxm*)       
    
    (* A consequence of A2 *)
    (* begin snippet Sxone:: no-out *)    
    Lemma Sx_1 (A2: Assumption2 R):
      nonempty [set: Y] -> (exists (y:T), y \in Y /\ SeP y).
    (* end snippet Sxone*)       
    Proof.  by move => H1; move: (notiic_rloop_sub H1 A2) => H2.  Qed.
    
    (* begin snippet Sbunp:: no-out *)    
    Lemma fact0: forall x y, x \in X `\` (Xy y) -> ~ B (x,y).
    (* end snippet Sbunp*)       
    Proof. 
      move => x y /set_mem [H3 H4].
      rewrite -inE in H3.
      rewrite -[X in ~X]inE in H4.
      have H0: x \in X -> ~(x \in (Xy y)) -> ~ B (x,y).
      by move => H3';rewrite inE not_andE => [[? // | /contrapT ? //]].
      by apply: (H0 H3 H4). 
    Qed.
    
    Lemma fact4: (X:#(R) `<=` M#X) -> forall x y, x \in X -> y \in Y -> (~ (R (x,y))) /\ (~ (M (y,x))).
    Proof.
      move => H0 x y /set_mem H1 /set_mem [H2 H3].
      move: H3; rewrite inE/Aset/Fset/mkset => H3.
      rewrite -not_orP => -[ H4 | H4]. 
      + have /H0 H5:  X:#R y by rewrite /Aset/Fset/mkset;(exists x).
        by have H3n: (exists y0 : T, M (y, y0) /\ X y0) by [].
      + by have H3n: (exists y0 : T, M (y, y0) /\ X y0) by (exists x).
    Qed.
    
    Lemma fact3: forall x, forall y, x \in X `\` Xy y -> x \in X. 
    Proof. by move => x y /set_mem/(@subDsetl T X (Xy y))/mem_set. Qed.
    
    
    (** the case one:  ~ ( y \in X:#(B) ) and candidate  (X `|` [set y]) *)

    Lemma case1_nonempty: forall y,
        preKernel M R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> (X `|` [set y]) != set0.
    Proof.
      by move => y [_ [_ +]] _ _ _;rewrite 2!set0P => -[x Hx];exists x;left. 
    Qed.
    
    Lemma case1_indep: forall y, 
        preKernel M R M  X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> RelIndep M (X `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /set_mem [H1 H2] H3 H4.
      have H5: ~ y \in X:#(R) by move => /set_mem/H0'/mem_set ?. 
      have H6: ~ y \in X:#(M) by rewrite /M /Aset inverseU -FsetUl => /set_mem [/mem_set ? |/mem_set ?].
      by apply: RelIndep_U.
    Qed.
    
    Lemma case1_RMprop: forall y, 
        preKernel M R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) ->
        forall y', ~ (y' \in (X `|` [set y])) -> y' \in (X `|` [set y]):#(R) -> y' \in M#(X `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /set_mem [H1 H2] H3 H4 y' H5.
      rewrite /Aset FsetUr => /set_mem [/H0' H6 | /Fset_s H6].
      + by rewrite FsetUr inE;left.
      + (* two subcases *)
        case H7: ( y' \in M#(X));first by rewrite FsetUr inE;left;rewrite -inE.
        have H8: y' \in Y. rewrite /Y inE;split.
        move => H9.
        by have H10: y' \in X `|` [set y] by rewrite inE;left;rewrite -inE.
        by rewrite H7.
        (* end of H8 *)
        move: (H3 y' H8 H6) => H11.
        have H12: y' \in M#([set y]). rewrite inE. exists y.
        split. rewrite /M. by right. by [].
        by rewrite FsetUr inE;right; by rewrite -inE.
    Qed.

    Lemma case1_RMprop1: forall y, 
        preKernel M R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> (X `|` [set y]):#(R) `<=` M#(X `|` [set y]).
    Proof.
      move => y H1 H2 H3 H4.
      pose proof (case1_RMprop H1 H2 H3 H4) as H5.
      pose proof (case1_indep  H1 H2 H3 H4) as H6.
      pose proof (preKernelProp1 H6) as H7.
      by rewrite H7.
    Qed.
    
    Lemma case1_Cprop: forall y,
      preKernel M R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> X [<= O] (X `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /set_mem [H1 H2] H3 H4 y' /= H5.
      by exists y';split;[rewrite inE;left; rewrite -inE |left].
    Qed.
    
    Lemma case1_notequal: forall y,
      preKernel M R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) ->
      (exists x' : T, x' \in X `|` [set y] /\ ~ x' \in X).
    Proof.
      by move => y _ /set_mem [H1 _]; exists y;split;[rewrite inE;right|].
    Qed.
    
    Lemma set_not_equal (X': set T): (exists x' : T, x' \in X' /\ ~ (x' \in X)) -> ~ (X = X').
    Proof. by move => [x' [HinX' HnotinX]] He;rewrite He in HnotinX. Qed.
    
    Lemma case1: forall y,
        preKernel M R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) )
        -> preKernel M R M (X `|` [set y]) /\  X [<< O] (X `|` [set y]).
    Proof.
      move => y H1 H2 H3 H4. 
      pose proof (case1_nonempty H1 H2 H3 H4).
      pose proof (case1_indep H1 H2 H3 H4).
      pose proof (case1_RMprop1 H1 H2 H3 H4).
      pose proof (case1_Cprop H1 H2 H3 H4).
      move: (case1_notequal H1 H2 H3 H4) => /set_not_equal H7.
      by split;[| split;[rewrite DeltaCP|]].
    Qed.
    
    (** the case one:  ( y \in X:#(B) ) and candidate  ((X `\` (Xy y)) `|` [set y]) *)

    Lemma case2_nonempty: forall y,
        preKernel M R M X -> y \in Y -> (SeP y) -> y \in X:#(B) -> ((X `\` (Xy y)) `|` [set y]) != set0.
    Proof. by move => y _ _ _ _;rewrite set0P;exists y;right. Qed.
    
    Lemma case2_indep: forall y, 
        preKernel M R M X -> y \in Y -> (SeP y) -> y \in X:#(B) -> RelIndep M ((X `\` (Xy y)) `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /set_mem [H1 H2] H3 H4.
      have H5: X `\` Xy y `<=` X by apply: subDsetl.
      pose proof (@RelIndep_Ir T M (X `\` Xy y) X H5 H0) as H6.
      pose proof fact0 as H7.
      have H8: ~ y \in X:#(R) by move => /set_mem/H0'/mem_set ?. 

      have H9:  forall x : T, x \in X `\` Xy y -> ~ M (x, y).
      move => x H10. rewrite /M => -[ H11 | H11].
      by have H12: ~ B(x,y) by apply: H7.
      have H12:  X `\` Xy y `<=` X by apply: subDsetl.
      move: H10 => /set_mem/H12 H10.
      move: H8. rewrite inE /Aset/Fset /mkset => H13.
      have H14: (exists x : T, R^-1 (y, x) /\ X x).
      by (exists x). by [].
      (** fin de H9 *)
      
      have H10:  forall x : T, x \in X `\` Xy y -> ~ M (y, x).
      move => x H11.
      move: H2. rewrite inE /Aset/Fset /mkset => H12.
      have H13:  X `\` Xy y `<=` X by apply: subDsetl.
      move: H11 => /set_mem/H13 H11.
      move => H14.
      by have H15: (exists y0 : T, M (y, y0) /\ X y0) by (exists x).
      
      have H11: ~ y \in M#(X `\` Xy y).
      by rewrite inE /Aset/Fset /mkset => -[x [H12 /mem_set/H10 H13]].

      have H12: ~ y \in (X `\` Xy y):#M.
      by rewrite inE /Aset/Fset /mkset => -[x [H12 /mem_set/H9 H13]].

      by apply: RelIndep_U.
    Qed.
      
    Lemma case2_RMprop (A7:Assumption7 R B M) (A8:Assumption8 R B M): forall y, 
        preKernel M R M X -> y \in Y -> (SeP y) -> y \in X:#(B) 
        -> ( forall y', ~ (y' \in ((X `\` (Xy y)) `|` [set y]))
                  -> y' \in ((X `\` (Xy y)) `|` [set y]):#(R) -> y' \in M#((X `\` (Xy y)) `|` [set y])).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /set_mem [H1 H2] H3 H4 y' H4'.
      (** on a necessairement ~ (y = y') **)
      have P0: ~ (y = y')
        by move => I1;(have I2: y \in  X `\` Xy y `|` [set y] by rewrite inE;right);rewrite -I1 in H4'.
      rewrite inE/Aset/Fset/mkset => -[x [H5 [/mem_set H6 | H6]]];rewrite inE/Aset/Fset/mkset.
      + (** x \in X\X_y *)
        move: (H6) => /fact3/set_mem H6'.
        have P0': ~ (y' = x)
          by move => I1;(have I2: x \in  X `\` Xy y `|` [set y] by rewrite inE;left;rewrite -inE);
                    rewrite -I1 in I2.
        have H7: y' \in  X:#R by rewrite inE /Aset/Fset /mkset;(exists x).
        have H8: y' \in  M#X by move: H7 => /set_mem/H0'/mem_set.
        move: H8 => /set_mem [x' [H8 H9]].
        move: H9;rewrite -{1}(Xpart y) => -[H9 | H9];first  by (exists x');split;[by [] | left].
        (** x' \in Xy *)
        move: (EM (M (y',x))) => [H10 | H10].
        ++ by (exists x);split;[ | left;apply/set_mem]. 
        ++ (* we will use A7 to conclude that M(y',y) *)
           exists y; split; last by right. 
           have P1: ~ (x' = x) by move => H11;move: H6 H9;move: H11 => -> /set_mem [_ ?] ?. 
           have P2: R (x,y') by apply: H5.
           have P3: M (y',x')  by apply: H8.
           have P4: B (x',y) by move: H9;rewrite /Xy => -[H9 H9'].
           have P5: ~ (B (x,y)) by apply: fact0. 
           have P6: ~ (R (x',y)) /\ ~ (M (y,x')) 
             by apply: (fact4 H0');rewrite inE;move: (@XyI y) => H11;move: H9 => /H11. 
           have P7: ~ (R (x,y)) /\ ~ (M (y,x)) 
             by apply: (fact4 H0');rewrite inE.
           have P8:  ~ (M (x,x'))
             by apply: H0;[by rewrite inE
                     | by rewrite inE;move: (@XyI y) => H11;move: H9 => /H11
                     | by move => H11; rewrite H11 in P1].
           have P9:  ~ (M (x',x))
             by apply: H0;[rewrite inE;move: (@XyI y) => H11;move: H9 => /H11 
                          | rewrite inE | move => H11;rewrite H11 in P1].
           have P10: ~ (y = y') by apply: P0.
           have P11: ~ (y' = x) by apply: P0'.
           have P12: ~ (y' = x')
             by move => I1;(have I2: M(x, x') by right ; rewrite -I1).
           have P13: ~ (y = x ) by move => I1;rewrite -I1 -inE in H6'.
           have P14: ~ (y = x' )
             by move => I1;(have: M (x',y) by left);move: P6;rewrite I1 => -[_ I3] I4.
           have P15: ~ (M (y',x)) by exact.
           by move: (A7 x x' y y' P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15).
        ++ have H7: x = y. by [].
           have H8: R (y,y') by rewrite H7 in H5.
           case H9: (y' \in M#(X)); last first.
           +++ case H10: (y' \in (Xy y)).
               ++++ move: H10;rewrite /Xy => /set_mem [H11 H12].
                    exists y. split. by rewrite /M;left. by right.
               ++++ have H11: y' \in Y. 
                    rewrite inE/Y. split.
                    rewrite -{1}(Xpart y) inE => -[H12| H12]. 
                    by have H13: y' \in X `\` Xy y `|` [set y] by rewrite inE; left.
                    by rewrite -inE H10 in H12.
                    by rewrite H9. 
                    (** * end H11 *)
                    have H12: M (y', y)  by rewrite /M;right;apply: (H3 y' H11 H8).
                    by (exists y);split;[ | right].
           +++ move: H9;rewrite -{1}(Xpart y) => /set_mem [x' [H9 [[H10 H10'] | H10]]].
               ++++ by (exists x');split;[ | left].
               ++++ move: (EM (y' = x')) => [H9'| H9'].
                    by (have H11: M (y',y) by left;rewrite H9';move: H10 => [_ H10]);
                    (exists y);split;[|  right].
                    
                    have H11: x' \in X by move: H10;rewrite /Xy => -[? _]. 
                    have H12: y \in Y by rewrite inE/Y.
                    
                    have B0: ~ (y' = x') by apply: H9'.
                    have B0': ~ (y = y') by apply: P0.
                    have B0'': ~ (y = x') 
                      by move: H12 => /set_mem [H12 _] H13;rewrite H13 in H12.
                    
                    have B1: R (y,y') by apply: H8.
                    have B2: M (y',x') by apply: H9.
                    have B3: B (x',y) by move: H10;rewrite /Xy => -[_ ?]. 
                    have B4: ~ (R (x',y)) /\ ~ M (y, x') by apply: (fact4 H0' H11 H12). 
                    
                    move: (A8 x' y y' B0 B0' B0'' B1 B2 B3 B4) => B5.
                    by (exists y);split;[ | right].
    Qed.
    
    Lemma case2_RMprop1 (A7:Assumption7 R B M) (A8:Assumption8 R B M):
      forall y, preKernel M R M X -> y \in Y -> (SeP y) -> y \in X:#(B) 
           -> ((X `\` (Xy y)) `|` [set y]):#(R) `<=` M#((X `\` (Xy y)) `|` [set y]).
    Proof.
      move => y H1 H2 H3 H4.
      pose proof (case2_RMprop A7 A8 H1 H2 H3 H4) as H7.
      pose proof (case2_indep  H1 H2 H3 H4) as H8.
      pose proof (preKernelProp1 H8) as H9.
      by rewrite H9.
    Qed.
    
    Lemma case2_Cprop (A6: Assumption6 B M O): forall y,
      preKernel M R M X -> y \in Y -> (SeP y) -> ( y \in X:#(B) )
      -> X [<= O] ((X`\` (Xy y)) `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /set_mem [H1 H2] H3 H4 x /=.
      rewrite -{1}(Xpart y) inE => -[ H5 | H5].
      + (* x \in  X `\` Xy *) by (exists x);split;[rewrite inE;left | left].
      + (* x \in Xy y *) exists y;split;first by rewrite inE;right. 
        have H6: B (x,y) by move: H5 => [_ ?].
        move: H2;rewrite inE/Fset/mkset => H2.
        have H7: X x  by rewrite -{1}(Xpart y);right.
        have H8: ~ (M (y, x))
          by move => H8;have H9: (exists y0 : T, M (y, y0) /\ X y0) by (exists x).
        by right; apply: A6.
    Qed.
    
    Lemma case2_notequal: forall y,
      preKernel M R M X -> y \in Y -> (SeP y) -> ( y \in X:#(B) ) ->
      (exists x' : T, x' \in ((X`\` (Xy y)) `|` [set y]) /\ ~ x' \in X).
    Proof.
      by move => y _ /set_mem [H1 _]; exists y;split;[rewrite inE;right|].
    Qed.

    Lemma case2 (A6: Assumption6 B M O)(A7: Assumption7 R B M)(A8: Assumption8 R B M) : forall y,
        preKernel M R M X -> y \in Y -> (SeP y) -> ( y \in X:#(B) )
        -> preKernel M R M ((X`\` (Xy y)) `|` [set y]) /\ X [<< O] ((X`\` (Xy y)) `|` [set y]).
    Proof.
      move => y H1 H2 H3 H4. 
      pose proof (case2_nonempty H1 H2 H3 H4).
      pose proof (case2_indep H1 H2 H3 H4).
      pose proof (case2_RMprop1 A7 A8 H1 H2 H3 H4).
      pose proof (case2_Cprop A6 H1 H2 H3 H4).
      move: (case2_notequal H1 H2 H3 H4) => /set_not_equal H7.
      by split;[|split;[rewrite DeltaCP|]].
    Qed.

    (** * main result *)
    Lemma extend (A2: Assumption2 R) (A6: Assumption6 B M O)
      (A7: Assumption7 R B M) (A8: Assumption8 R B M):
      preKernel M R M X -> ~ (absorbant M X) 
      -> exists X', preKernel M R M X' /\ (X [<< O] X'). 
    Proof.
      have Hne: [set: Y] !=set0 <-> exists x, x \in Y.
      {
        split => [[x _] |[x Hx]];last by (exists (exist _ x Hx)).
        by exists (sval x);rewrite inE; apply/set_valP.
      }
      have Hna: (nonempty [set: Y]) -> exists y, y \in Y /\ (SeP y)
            by move => H0;pose proof (Sx_1 A2 H0). 
      move => H1 /not_absorbant_iff/Hne/Hna [y [H2 H3]]. 
      have H4: y \in (X:#(B) `|` (X:#(B)).^c) by rewrite (setUv X:#(B)) inE.
      move: H4 => /set_mem [ H4 | H4];rewrite -inE in H4.
      by move: (case2 A6 A7 A8 H1 H2 H3 H4) => H5;exists (X `\` Xy y `|` [set y]).
      move: H4;rewrite in_setC notin_setE -[X in ~ X]inE => H4.
      by move: (case1 H1 H2 H3 H4) => H5;exists (X `|` [set y]).
    Qed.
    
    End Extend_non_absorbant_preKernel.
End Extend_non_absorbant_preKernel.

Export Extend_non_absorbant_preKernel (extend).

Module Maximal_with_Zorn.
  Section Maximal_with_Zorn.
    (** * Existence of a Maximal in the infinite case with Zorn Lemma *)
    (** * we need [<= O] to be a porder *)

    Variables (T:choiceType) (R B O: relation T).
    
    Notation M := (B `|` R).
    
    Definition Scal := preKernel M R M. 

    (* begin snippet IsMaximal:: no-out *)  
    Definition IsMaximal (S: set T):= 
      S \in Scal /\ forall T, T \in Scal -> S [<= O] T -> T = S.
    (* end snippet IsMaximal:: no-out *)  
    
    Definition SType := {S | preKernel M R M S}.

    Definition Elt (C: set SType) := {x : T |exists (S: SType), S \in C /\ x \in (sval S)}.
    
    Lemma S2Scal: forall (S: SType), (sval S) \in Scal.
    Proof. by move => [S [H1 [H2 H3]]];rewrite inE. Qed.

    Lemma Scal2S: forall S, S \in Scal -> exists (S': SType), (sval S') = S.
    Proof. by move => S /set_mem H1; exists (exist _ S H1). Qed.

    (* begin snippet Scalnotempty:: no-out *) 
    Lemma Scal_not_empty (A1: Assumption1 T) (A2: Assumption2 R):
      exists v, Scal [set v].
    (* end snippet Scalnotempty *)
    Proof.
      have: Rloop R by apply: notiic_rloop.
      move => [v H1]; exists v.
      have H2':  R `<=` M by rewrite /M;apply: subsetUr.
      split;first by rewrite /RelIndep;move => x y /set_mem /= -> /set_mem /= ->.
      split;first by move => t [y [/= H3 H4]];move: H3; rewrite H4 /= => /H1/H2' H3;exists v.
      by rewrite set0P;(exists v).
    Qed.
    
    Lemma SType_not_empty (A1: Assumption1 T) (A2: Assumption2 R):
      (@setT SType) != set0.
    Proof.
      rewrite set0P;move: (Scal_not_empty A1 A2) => [v H2].
      by exists (exist _ [set v] H2).
    Qed.
    
    (** * The relation on sets restricted to Stype subsets *)
    Definition leSet1 (AB: SType*SType) :=
      leSet O ((sval AB.1), (sval AB.2)).
    Notation "A [<=] B" := (leSet1 (A,B)).
    
    Section Scal_order. 
      
      Lemma leSet1_transitive: sporder O -> @transitive SType leSet1.
      Proof. by move => [? ?] [X ?] [Y ?] [Z ?];apply/le_trans_if_tr. Qed.
      
      Lemma leSet1_reflexive: @reflexive _ leSet1.
      Proof. by move => [A ?];apply: le_refl. Qed.
      
      Lemma le_antisym_l1: forall A B, 
          sporder O -> O  `<=` M `|` M^-1 ->  (RelIndep M A) -> (RelIndep M B)
          -> A [<= O] B -> B  [<= O] A -> A = B.
      Proof.
        move => X Y H1 H3 /RelIndep_Is H4 /RelIndep_Is H5. 
        apply/le_antisym_if_sp. exact.
        by apply/(@RelIndep_I T O (M `|` M^-1) X H3 H4).
        by apply/(@RelIndep_I T O (M `|` M^-1) Y H3 H5).
      Qed.
      
      Lemma leSet1_antisymmetric: sporder O -> O `<=` M `|` M^-1 -> @antisymmetric _ leSet1.
      Proof. 
        move => H1 H2 [X [Hx Hx']] [Y [Hy Hy']] H3 H4.
        move: (le_antisym_l1 H1 H2 Hx Hy H3 H4) => H5.
        subst X. (** why I cannot use rewrite *)
        apply: f_equal.
        apply: proof_irrelevance.
      Qed.
      
      Lemma leSet1_porder: sporder O -> O  `<=`  M `|` M^-1 -> @porder _ leSet1. 
      Proof.
        move => ? ?; split. 
        + by apply/leSet1_reflexive.
        + by apply/leSet1_antisymmetric.
        + by apply/leSet1_transitive. 
      Qed.
      
    End Scal_order.

    Section Sinf_set.
      (** * Sinf C for (C: set SType) and C != set0 *)
      
      Variables  (C: set SType).
      Hypothesis Hne: C != set0.
      
      (* Set Sinf associated to a chain C *)
      (* begin snippet Sinf:: no-out *)   
      Definition Sinf := 
        [ set v: T | 
          exists S, (S \in C) /\ (v \in (sval S)) /\
                 (forall T, T \in C -> S [<=] T -> v \in (sval T))].
      (* end snippet Sinf *)   

      (* A relation on the set Elt C, all the elements
       of T which are elements of a set in C *)
      (* begin snippet RC:: no-out *)   
      Definition RC:= [set xy: (Elt C)*(Elt C) |
                        ((sval xy.1) \in Sinf /\ xy.2 = xy.1)
                        \/ (~ ((sval xy.1) \in Sinf) /\
                             O (sval xy.1, sval xy.2))].
      (* end snippet RC*)   
      
      Lemma transitive_RC:  sporder O -> transitive RC. 
      Proof.
        move => [_ H3].
        by move => x y z [/= [H0 ->]| [H1 H1']] [ /= [H0' /= ->]| /= [H2 H2']]; 
                  [left | right | right |right;split;[ | apply H3 with (sval y)]].
      Qed.

      (** * Elt C  is not empty *)
      (* begin snippet Eltnotempty:: no-out *)   
      Lemma Elt_not_empty: exists _ : Elt C, True.
      (* end snippet Eltnotempty *)   
      Proof.
        have: exists (S: SType), S \in C /\ (exists x, x \in (sval S)).
        { 
          move: Hne;rewrite set0P => -[S /mem_set H2];exists S;split;first by []. 
          move: S H2 => [S' [H3 [H4 H5]] /=] _.
          move: H5;rewrite set0P => -[x /mem_set Hx].
          by exists x.
        }
        move => [S [? [x ?]]].
        have H4: exists (S: SType), S \in C /\ x \in (sval S) by (exists S).
        by exists (exist _ x H4).
      Qed.
      
      Section total_RC. 
        (** *  the main result here is total_RC *) 

        Lemma total_RC_L1: forall (S: SType) (s:T), 
            (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
            -> exists S1, S1 \in C /\ S [<=] S1 /\ ~ (s \in (sval S1)).
        Proof.
          move => S s H2 H3. 
          apply contraPP;rewrite not_existsP 2!not_notE inE /Sinf => H4;exists S.
          split => [// | ];split => [// |A ? ?].
          by move: H4 => /(_ A) /not_andP [? //|/not_andP [// | /contrapT ?]].
        Qed.
        
        Lemma total_RC_L2: forall (S: SType) (s:T), 
            (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
            -> exists S1, exists s1, S1 \in C /\ s1 \in (sval S1) /\ O (s,s1).
        Proof.
          move => S s H2 H3 H4.
          move: (total_RC_L1 H2 H3 H4) => [S1 [H5 [H6 H7]]].
          by move: ((H6 s) H3) => [s1 [H8 [H9 | H9]]];exists S1, s1;[rewrite -H9 in H8|].
        Qed.
        
        Lemma total_RC_L3: forall (s: Elt C), 
            ~ ((sval s) \in Sinf) -> exists (s1: Elt C), O (sval s,sval s1).
        Proof.
          move => [s [S [H1 H2]]] H3.
          move: (total_RC_L2 H1 H2 H3) => [S1 [s1 [H4 [H5 H6]]]].
          have H7: exists (S: SType), S \in C /\ s1 \in (sval S) by (exists S1).
          by exists (exist _ s1 H7).
        Qed.
        
        (* begin snippet totalRC:: no-out *)    
        Lemma total_RC: total_rel RC. 
        (* end snippet totalRC *)    
        Proof.
          move => s.
          case H3: ((sval s) \in Sinf); first by (exists s); left.
          have H4: ~ ((sval s) \in Sinf) by move => H5;rewrite H5 in H3.
          move: (total_RC_L3 H4) => [s1 H5].
          by exists s1; right.
        Qed.

        Lemma iic_RC: (iic RC).
        Proof.
          apply DC; last by apply: total_RC.
          by move: Elt_not_empty => [x _];exists x.
        Qed.
        
      End total_RC. 
      
      Lemma Elt_not_empty_witness: Elt C.
      Proof. by apply: inhabited_witness; rewrite inhabitedE; apply: Elt_not_empty. Qed.
      
      Section total_RC_to_iic.
        (** consequence of the fact that RC is total *)

        Implicit Type (f: nat -> Elt C) (s: Elt C).
        
        Lemma total_RC_P1 s f: 
          f 0=s /\ (forall n, RC ((f n),(f (S n)))) 
          -> (forall n, ~ (sval (f n)) \in Sinf) -> iic O. 
        Proof. 
          move => H1 H2;exists (fun n => (sval (f n))) => n.
          by move: H1 H2 => [H0 /(_ n) [/=[H1 H1'] | /= [H1 H1']]] /(_ n) H2.
        Qed.
        
        Lemma total_RC_P2:
          ~ (iic O)
          -> forall s, exists f, (f 0=s /\ (forall n, RC ((f n),(f (S n)))))
                      /\ exists n, (sval (f n)) \in Sinf.
        Proof. 
          move: total_RC => /total_rel_iff /total_rel'_to_total_rel'' H1.
          move: H1 => + H2 s => /(_ s) [f H3].
          exists f;split;[exact | apply/not_existsP]. 
          by move: H3 => /total_RC_P1 H3;move => /H3 H4.
        Qed.
        
        Lemma transitiveN_RC f:  
          sporder O -> (forall n, RC ((f n),(f (S n))))   -> (forall n, n > 1 -> RC (f 0, f n)).
        Proof.
          move => H0 H1;elim => [// | n Hn H2 ].
          case H3: (1 < n). 
          + have H4: RC (f 0, f n) by apply: Hn;rewrite H3.
            by move : (transitive_RC H0 H4 (H1 n)).
          + case H5: (n == 0); first by move: H5 => /eqP ->;apply: H1.
            case H6: (n == 1); first by move: H6 => /eqP ->;move: (transitive_RC H0 (H1 0) (H1 1)).
            have H7: ~ (n <= 1) by rewrite leq_eqVlt H6 ltnS leqn0 H5.  
            by rewrite leqNgt H3 in H7.
        Qed.
        
        (* begin snippet totalRCPTr:: no-out *)    
        Lemma total_RC_P3:
          sporder O ->  ~ (iic O) ->
          forall s, exists f, f 0=s /\ (exists n, (sval (f n)) \in Sinf /\ RC ((f 0), (f n))).
        (* end snippet totalRCPTr *)
        Proof.
          move => H0 H1; move: (total_RC_P2 H1) => + s => /(_ s) [f [[H2 H3] [n H4]]].
          exists f;split;first exact.
          case H5: (sval (f 0) \in Sinf);first by (exists 0);split;[ | left].
          have H6: ~ (n = 0) by move => H7;rewrite H7 H5 in H4. 
          case H7: (sval (f 1) \in Sinf);first by (exists 1).
          exists n. 
          have H8: ~ (n = 1) by move => H8;rewrite H8 H7 in H4.
          have H9: n > 1 by lia. 
          move: (transitiveN_RC H0 H3) => /(_ n) H10.
          by split;[| apply: H10].
        Qed.

        (* begin snippet ChooseRCCi:: no-out *)    
        Lemma ChooseRC5:sporder O -> ~ (iic O)
                        -> forall (s: Elt C), (sval s \in Sinf) \/ 
                                          exists (s':T), (s' \in Sinf) /\ O (sval s, s').
        (* end snippet ChooseRCCi *)    
        Proof. 
          move => H0 H1; move: (total_RC_P3 H0 H1) => + s => /(_ s) [f [H2 [n [H3 H3']]]].
          case H4: (sval (f 0) \in Sinf); first by left;rewrite -H2 H4.
          right;exists (sval (f n));split;first exact. 
          rewrite -H2. 
          by move: H3' => [/= [H3' _] | /= [H5 H6]//];rewrite H4 in H3'.
        Qed.

        (* begin snippet ChooseRCSi:: no-out *)    
        Lemma ChooseRC6:sporder O -> ~ (iic O)
                        -> forall (S: SType), (S \in C) -> (sval S) [<= O] Sinf.
        (* end snippet ChooseRCSi *) 
        Proof. 
          move => H0 H1 S H2 s /= H3.
          have H4: exists (S: SType), S \in C /\ s \in (sval S) by (exists S).
          move: (ChooseRC5 H0 H1 (exist _ s H4)) => /= [H5 | [s' [H5 H6]]].
          by (exists s);split;[|left].
          by (exists s');split;[|right].
        Qed.
        
      End total_RC_to_iic.
      
    End Sinf_set.
    
    Section SType_chains.
      (** * set (C: set SType) which are in Chains *)
      
      Implicit Type (C: set SType).
      
      (* begin snippet Chains:: no-out *)    
      Definition ChainsB := @Chains SType leSet1. 
      (* end snippet Chains *)    
      
      Lemma Chains_is_total C: C \in ChainsB <-> total_on C (curry leSet1).
      Proof. split => [/set_mem H2 c1 c2 ? ?| H1];first by apply: H2. 
             by apply/mem_set => c1 c2 ? ?;apply: H1.
      Qed.
      
      Lemma Chains_Scal C S: C \in ChainsB -> S \in C -> Scal (sval S).
      Proof. by move: S => [S [H1 [H2 H3]]] /set_mem H4 /set_mem H5. Qed.
      
    End SType_chains.
    
    Section Sinf_chains.
      (** * Sinf when C is a non empty Chain *)
      
      Variables  (C: set SType).
      Hypothesis Hc: C \in ChainsB. 
      Hypothesis Hne: C != set0.
      
      (* Sinf is a Mono-independent set when C is a chain *)
      Lemma Sinf_indep: RelIndep M (Sinf C).
      Proof.
        move: Hc => /set_mem H1 x y /set_mem H2 /set_mem H3 H4 /= H5.
        move: H2 H3 =>[S [/[dup] H6 /set_mem P6 [/= H7 H8]]]
                       [U [/[dup] H6' /set_mem P6' [/= H7' H8']]].
        move: H8 H8' => /((_ U) H6') H8 /((_ S) H6) H8'.
        have [H9|H9]: S [<=] U \/ U [<=] S by apply: H1.
        - move: H9 H1 => /H8 H9 /mem_set H1.
          move: (Chains_Scal H1 H6') => [/(_ x y) H10 _].
          by apply: (H10 H9 H7' H4 H5).
        - move: H9 H1 => /H8' H9 /mem_set H1.
          move: (Chains_Scal H1 H6) => [/(_ x y) H10 _].
          by apply: (H10 H7 H9 H4 H5).
      Qed.
      
      Lemma Sinf_not_empty (A3: Assumption3 O) (A4: Assumption4 O):
        (Sinf C) != set0.
      Proof.
        move: (@Elt_not_empty C Hne) => [s _];rewrite set0P.
        by move: (@ChooseRC5 C Hne A4 A3 s) => [/set_mem H1 | [s' [/set_mem H1 _]]];
                                              [exists (sval s) | exists s'].
      Qed.
      
      (* begin snippet SinfScalP:: no-out *)    
      Lemma Sinf_ScalP (A2: Assumption2 R) (A3: Assumption3 O) 
        (A4: Assumption4 O) (A5:Assumption5 O M) (A9: Assumption9 R B O M):
        (Sinf C):#(R) `<=` M#(Sinf C).
      (* end snippet SinfScalP *)
      Proof.
        move: Hc => H1 y [x [B1 H3]].
        move: (H3) => [X [H4 [H5 H6]]].
        move: (Chains_Scal H1 H4) => [H7 [H8 H9]].
        move: (EM (y \in (Sinf C))) => [ H9' | H9'].
        + (* we eliminate the case y \in Sinf C *)
          move: H3 => /mem_set H3. 
          move: (Sinf_indep H3 H9') => H10.
          move: (EM (x = y)) H3 => [H11 | H11] /set_mem H3.
          by (exists x);(have H12: M(y,x) by right;move: B1;rewrite H11).
          by move: H11 => /H10 H11;(have H12: M(x,y) by right).
        + (* now  ~ y \in Sinf C *)
          have B2: ~ (x = y) by move => I1;rewrite -I1 inE in H9'.
          move: (EM (M (y,x))) => [? | B3];first by (exists x).
          have H10: (sval X):#R y by (exists x);split;[ |rewrite -inE].
          move: H10 => /H8 [x' [B4 /mem_set H11]].
          
          move: (EM (x' \in (Sinf C))) => [/set_mem ? | B5];first by (exists x').
          (* now x' not in Sinf C *)
          have B6: ~ (x = x') by move => I1; move: H3;rewrite I1 => /mem_set H3. 
          have B3': ~ (y = x')
            by move => I1;rewrite I1 in B1;
                      (have I3: M (x,x') by right);move: (H7 x x' H5 H11 B6).
          
          have H12: (sval X) [<= O] (Sinf C)  by apply: ChooseRC6. 
          move: (H11) => /H12 [y' [/= B7 [H21 | B8]]].  
          by rewrite -H21 in B7.
          
          move: (EM (x' = y')) B4 => [-> | B3''] B4.
          by (exists y'); rewrite inE in B7. 
          
          have P11': ~ ((M `|` M^-1) (x',x))
            by pose proof (@RelIndep_E _ x x' M _ H5 H11 B6 H7).
          
          move: (EM (x = y')) B8 => [<- /A5 B10 //| B9 /[dup] B8 /A5 B10].
          
          have P1: ~ (x = y) by apply: B2.
          have P2: ~ (x = x') by apply: B6. 
          have P3: ~ (x = y') by apply: B9.
          have P4: ~ (y = x') by apply: B3'.
          have P5: ~ (x' = y') by apply: B3''.
          have P6: ~ (y' = y) by  move => I1; by rewrite I1 in B7.
          have P7: R (x, y) by apply: B1.
          have P8: M (y, x') by apply: B4.
          have P9: O (x',y') by apply: B8.
          have P10: ~ M (y, x) by apply: B3.
          have P11: ~ ((M `|` M^-1) (x',x)) by apply: P11'.
          have P12: ~ ((M `|` M^-1) (y',x))
            by move: H3 => /mem_set H3;
                          pose proof (@RelIndep_E _ x y' M _ H3 B7 P3 (Sinf_indep)).
          
          exists y'. split. by apply: (A9 x y x' y' P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12). by rewrite -inE.
      Qed.
      
      (* begin snippet SinfScal:: no-out *)    
      Lemma Sinf_Scal (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
        (A5:Assumption5 O M) (A9: Assumption9 R B O M):
        (Sinf C) \in Scal. 
      (* end snippet SinfScal *)
      Proof.
        by rewrite inE;split;[apply: Sinf_indep|split;[apply: Sinf_ScalP|apply: Sinf_not_empty]].
      Qed.
      
      Lemma Sinf_final (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)   (A5:Assumption5 O M) (A9: Assumption9 R B O M):
        exists Si, forall (S: SType), C S -> S [<=] Si.
      Proof.
        move: (Sinf_Scal A2 A3 A4 A5 A9) => /set_mem H2;exists (exist _ (Sinf C) H2);move => S /mem_set H3. 
        by apply: ChooseRC6.
      Qed.

    End Sinf_chains.
    
    (** * existence of Smax with Zorn Lemma for type SType *)
    (* begin snippet SmaxSType:: no-out *)    
    Lemma Maximal_SType
      (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O) (A5: Assumption5 O M)
      (A9: Assumption9 R B O M):
      exists Sm, forall S, Sm [<=] S -> S = Sm.
    (* end snippet SmaxSType *)
    Proof.
      apply: (@Zorn_relation SType leSet1 (leSet1_porder A4 A5)) => C.
      move: (@Sinf_final C) => H2 /mem_set H3.
      move: H3 => {}/H2 H3.
      case H4: ( C != set0 ); first by apply: (H3 H4 A2 A3 A4 A5 A9).
      move: H4 => /negP/contrapT/eqP H4. 
      
      move: (SType_not_empty A1 A2);rewrite set0P => -[Sm Ht].
      by exists Sm; move => S; rewrite H4 -inE in_set0. 
    Qed.
    
    (** * back to Maximal set in preKernels *)
    (* begin snippet Smax:: no-out *)    
    Lemma Maximal_Zorn (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
      (A5: Assumption5 O M) (A9: Assumption9 R B O M):
      exists Sm, IsMaximal Sm.
    (* end snippet Smax *)    
    Proof. 
      move: (Maximal_SType A1 A2 A3 A4 A5 A9) => [Sm H1];exists (sval Sm); split; first by  apply: S2Scal.
      by move => S /Scal2S [S' <-] H3; f_equal;by apply H1.
    Qed.

  End Maximal_with_Zorn.
End Maximal_with_Zorn.

Export Maximal_with_Zorn(Maximal_Zorn).

