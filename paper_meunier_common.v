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

Definition NotEmpty (T: Type) := (exists (v0:T), (v0 \in setT)).

Reserved Notation "A [<=] B" (at level 4, no associativity). 
Reserved Notation "A [<= R ] S" (at level 4, no associativity). 

Definition leSet T R: relation (set T) := 
  [set AB |forall (a:T), (a \in AB.1) -> exists b, b \in AB.2 /\ ( a = b \/ R (a,b)) ].

Notation "A [<= R ] B" := (leSet R (A,B)).

Definition setRM (T: Type) (R M: relation T) (S:set T) := S:#R `<=` M#S.

Definition preKernel (T: Type) (R M: relation T) :=
  [set S| RelIndep M S /\ (setRM R M S) /\ S != set0 ].

Section CheckAsym. 
  (** * Import main result from paper_monochromatic_f *)
  Context (T : choiceType) (R: relation T).
  Hypothesis A1: (NotEmpty T).

  Import Asyminf2Inf(Asym2P5', allL_rc_asym).

  (* begin snippet infasym:: no-out *) 
  Lemma iic_asym_to_iic_inj:  (iic (Asym R.+)) -> (iic_inj R). 
  (* end snippet infasym *)  
  Proof. by apply: (@Asym2P5' T R A1). Qed.

  Lemma not_iic_inj_to_not_iic_asym: ~ (iic_inj R) -> ~ (iic (Asym R.+)).
  Proof. by move => ? /iic_asym_to_iic_inj ?. Qed.

End  CheckAsym. 

Module Infinite_paths.
  (** * iic_asym_injective:  iic (Asym R.+) -> iic_inj (Asym R.+) *) 

  Section iic_asym. 

    Variable (T : Type).
    Implicit Types (T : Type) (R: relation T) (A B: set T).
    
    #[local] Lemma iic_asym_L1 (f : nat -> T) R:
      (forall n, (Asym R.+) ((f n),(f (S n)))) -> 
      forall p n, 0 < p -> (Asym R.+) (f n, f (n + p)). 
    Proof.
      move => Hi. 
      elim => [// | p Hr n' _].
      case H2: (p == 0); first by move: H2 => /eqP ->;rewrite addn1;apply: Hi. 
      move: H2 =>  /neq0_lt0n /(Hr n') H2.
      have H4: transitive (Asym R.+) by apply: Asym_preserve_transitivity;apply: TclosT.
      have H5: Asym R.+ (f (n' + p), f (n' + p).+1) by apply: Hi.
      rewrite /transitive in H4.
      move: (H4 (f n') (f (n' + p)) (f (n'+p).+1) H2 H5).
      by rewrite -addn1 -[p.+1]addn1 addnA.
    Qed.
    
    #[local] Lemma iic_asym_L2 (f : nat -> T) R:
      (forall n, (Asym R.+) ((f n),(f (S n)))) -> 
      forall p n, 0 < p -> ~ (f n) = f (n + p). 
    Proof.
      by move => + p n H1 => /iic_asym_L1 /(_ p n H1) + H2;rewrite -H2; apply: Asym_irreflexive.
    Qed.
    
    #[local] Lemma iic_asym_L3 (f : nat -> T) R:
      (forall n, (Asym R.+) ((f n),(f (S n)))) -> injective f.
    Proof.
      have H0 n m: m < n -> exists p, p> 0 /\ n = m + p by move => H1;exists (n-m); lia.
      move => /iic_asym_L2 Hi p q;apply contraPP => H1.
      have [H2|H2]: (p < q \/ q < p) by lia.
      by pose proof (H0 q p H2) as [p' [H3 ->]]; apply: Hi.
      by move: (H0 p q H2) => [p' [H3 ->]];move: (Hi p' q H3);symmetry.
    Qed.
    
    Lemma iic_asym_injective R: iic (Asym R.+) -> iic_inj (Asym R.+).
    Proof. by move => [f /[dup] ? /iic_asym_L3  ?];exists f. Qed.

    Lemma sporder_iic_injective R: (sporder R) -> iic R -> iic_inj R.
    Proof. by move => /sporderEq <-;apply: iic_asym_injective. Qed.
    
    End iic_asym.
  
End Infinite_paths. 

Export Infinite_paths.
Arguments iic_asym_injective {T}.
Arguments sporder_iic_injective {T}.

Section Infinite_paths_X.
  (** * Assumptions on infinite paths *)
  (* should be move on rel.v *)

  Context (T : Type).
  Implicit Types (R: relation T) (X: set T).

  Lemma notiic_rloop_sub_L1 X (S: relation X):
    (exists (v0:T), (v0 \in X)) -> ~ (iic (Asym S)) -> (Rloop S).
  Proof. 
    have setTypeP: (exists x : X, x \in [set: X]) <-> (exists (t:T), (t \in X))
      by split => [[v ?] |[v H0]];[exists (sval v) | exists (exist _ v H0)];
                 rewrite inP;[apply: set_valP|].
    by move => /setTypeP H0; apply: notiic_rloop. 
  Qed. 
  
  Lemma notiic_rloop_sub_L2 X R:
    ~ (iic (Asym R)) -> (exists (v0:T), (v0 \in X)) -> (Rloop (@Restrict' T X R)).
  Proof.
    move => H1 H0.
    have H2: (iic (@Restrict' T X (Asym R))) -> (iic (Asym R))
      by move => [f // ?];exists (fun n => (sval (f n))). 
    have H3:  ~ (iic (Asym R)) -> ~ (iic (@Restrict' T X (Asym R)))
      by contra => -[f H4];apply: H2; by (exists f).
    by apply/(notiic_rloop_sub_L1 H0)/H3.
  Qed.
  
  (* notiic_rloop for a subset X *)
  Lemma notiic_rloop_sub X R:
    ~ (iic (Asym R)) ->(exists (v0:T), (v0 \in X))
    -> (exists (v:T), v \in X /\ forall w, w \in X -> R (v,w) -> R (w,v)).
  Proof.
    move => Ninf H0.
    move: (notiic_rloop_sub_L2 Ninf H0) => [v H1];exists (sval v).
    split=> [| w H2];first by rewrite inP;apply: set_valP.
    have [w' <-]: exists (w': X), (sval w') = w by (exists (exist _ w H2)).
    by move => ?;apply: H1.
  Qed.
  
End Infinite_paths_X.

Definition leSet' T R: relation (set T) := [set AB | AB.1 `<=` ('Δ  `|` R)#AB.2]. 

Section Set_relation. 
  (** * A relation on sets induced by a relation on elements *)

  Context (T : eqType).
  Implicit Types (T : eqType) (R S: relation T) (A B: set T).
  
  Lemma lesetE R: leSet R = leSet' R. 
  Proof.
    rewrite predeqE => -[A B];split. 
    - move => H1 a /inP/H1 [b [/inP H2 [->| H3]]]; first by (exists b);split;[left|].
      by (exists b);split;[right|].
    - rewrite /leSet' /mkset /= -FsetUl Fset_D.
      move => H1 a /inP/H1 [/inP H2 | [b [H2 /inP H3]]].
      by (exists a); split;[ | left].
      by exists b; split;[ | right].
  Qed.

  (* begin snippet lesetI:: no-out *)   
  Lemma Ile R A B: A `<=` B -> A [<= R] B.
  (* end snippet lesetI *)
  Proof. by move => H1 /= a /inP/H1 ?;exists a;split;[rewrite inP|left]. Qed.

  Lemma leI R S: S `<=` R -> (leSet S)  `<=` (leSet R).
  Proof.
    move => H1;rewrite 2!lesetE => [[A B]] H2.
    by apply: subset_trans H2 _;apply: Fset_inc; apply: setUS.
  Qed.
  
End Set_relation.


Section Set_order. 
  (** * the previous relation [<= R] is an order relation on R-independent sets *)

  Context (T : eqType).
  Implicit Types (R S: relation T) (A B: set T).
  
  Axiom proof_irrelevance: forall (P : Prop) (p q : P), p = q.
  
  Section Util.
    (** ingredients *)
    Lemma le_trans_if_tr R: transitive R -> transitive (leSet R).
    Proof.
      rewrite lesetE => /Tclos_iff H0 A B C /= H1 H2.
      have : ('Δ  `|` R)#B `<=` ('Δ  `|` R)#(('Δ  `|` R)#C) by apply: Fset_inc1.
      rewrite Fset_comp H0 DuT_eq_Tstar compose_rt_rt -DuT_eq_Tstar -H0 => H3.
      by apply: subset_trans H1 H3.
    Qed.

    Lemma le_refl  R: reflexive (leSet R).
    Proof. by move => A r H1;exists r;split;[| left]. Qed.
    
    Lemma le_antisym_if_sp' R: 
      sporder R -> forall A B, (RelIndep R A) -> A [<= R] B -> B  [<= R] A -> A `<=` B.
    Proof.
      move => /[dup] -[_ Htr] /sporder_asym/AsymEq Asy A B H1 + +  a H4.
      rewrite -Asy => H2 H3.
      move: (H4) => /inP /H2 [b [/inP /= H5 [-> // | [H6 H6']]]]. 
      move: (H5) => /inP /H3 /= [c [/inP H8 H9]].
      case H10: (a == b ); first by move: H10 => /eqP ->.
      move: H10 => /eqP H10.
      case H12: (b == c).
      - move: H12 H8 => /eqP <- H8.
        by have: False by move: H4 H8 => /inP H4 /inP H8;apply: (H1 a b). 
      - move: H12 H9 => /eqP H12 [H9 // | [H9 H9']].
        case H13: (a == c); first by move: H13 H9' => /eqP <- H9'.
        pose proof Htr.
        have H14: R (a,c) by apply: Htr H6 H9.
        by have: False by move: H13 H4 H8 => /eqP H13 /inP H4 /inP H8; apply: (H1 a c). 
    Qed.
    
    Lemma le_antisym_if_sp R: 
      sporder R ->
      forall A B, (RelIndep R A) -> (RelIndep R B) 
             -> A [<= R] B -> B  [<= R] A -> A = B.
    Proof.
      move => Hsp A B H1 H2 H3 H4.
      by move: (le_antisym_if_sp' Hsp H1 H3 H4)
                 (le_antisym_if_sp' Hsp H2 H4 H3);rewrite eqEsubset.
    Qed.
  
  End Util.
  
  (* begin snippet lesetporder:: no-out *)   
  Lemma leSet2_porder R: 
    sporder R -> 
    @porder {S: set T| RelIndep R S} [set AB | (sval AB.1) [<= R] (sval AB.2)].
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

Section Paper. 
  (*  abstract version *)
  Variables (T:choiceType) (R B D: relation T).

  Definition M := B `|` R.

  Definition Assumption1:= (NotEmpty T).
  Definition Assumption2:= ~ (iic (Asym R)).
  Definition Assumption3:= ~ (iic D).
  Definition Assumption4:= sporder D.
  Definition Assumption5:= D  `<=` M `|` M^-1.
  Definition Assumption6:= 
    (forall x y, B (x,y) /\ ~ (M (y, x)) -> D (x,y)).
  
  Definition Assumption7:= 
    (forall x x' y y', ~(x' = x) 
                  -> R (x,y') -> M (y', x')
                  -> (B (x',y)) -> ~ (B (x, y)) 
                  -> ~ (R (x',y)) /\ ~(M (y,x')) 
                  -> ~(R (x,y)) /\ ~(M (y,x)) 
                  -> ~ (M (x,x')) -> ~ (M (x',x))
                  -> ~ (y = y') -> ~ (y' = x) -> ~ (y' = x') -> ~ (y = x ) -> ~ (y = x' )
                  -> ~ (M (y',x))
                  -> (M (y',y))).
  
  Definition Assumption8:=
    (forall x' y y', ~ (y' = x') -> ~ (y = y') -> ~ (y = x') 
                -> R (y,y') -> M (y',x') -> B (x',y) 
                -> ~ (R (x',y)) /\ ~ M (y, x')
                -> (M (y',y))).
  
  Definition Assumption9:= 
    (forall x y x' y' , ~ (x = y) -> ~ (x = x') -> ~ (x = y')
                   -> ~ (y = x') -> ~ (x' = y') -> ~ (y' = y) 
                   -> R (x,y) -> M (y,x') -> D (x',y') -> ~(M (y,x)) 
                   -> ~ ((M `|` M^-1) (x',x))
                   ->  ~ ((M `|` M^-1) (y',x))
                   -> M (y,y')).

  
  Lemma preKernelProp: forall S S1,
      RelIndep M S -> S1 `<=` S -> (S1:#(R) `<=` M#S <-> forall y, ~ (y \in S) -> y \in S1:#(R) -> y \in  M#S).
  Proof.
    move => S S1 H1 H1';split => [H2 y _ /inP/H2/inP H4 //| H2 y H3].
    case H5: (y \in S);last first.
    + apply/inP/H2. by rewrite H5. by apply/inP.
    + move: H3. rewrite /Aset => -[y' [H6 H7]].      
      rewrite /RelIndep in H1.
      case H8: (y == y').
      ++ move: H8 => /eqP H8; have H9: M(y,y) by rewrite -H8 in H6;rewrite /M;right.
         by move: H7 => /H1' H7;(exists y);rewrite -H8 in H7.
      ++ move: H8 H7 => /eqP H8 /inP H7.
         have H9:  y' <> y by move => H10;rewrite H10 in H8.
         move: H7 => /inP/H1'/inP H7.
         move: (H1 y' y H7 H5 H9) => H10.
         by have H11: M (y', y) by rewrite /M;right.
  Qed.

  Lemma preKernelProp1: forall S,
      RelIndep M S -> (S:#(R) `<=` M#S <-> forall y, ~ (y \in S) -> y \in S:#(R) -> y \in  M#S).
  Proof. move => S H1; apply: (preKernelProp H1 (@subset_refl T S)).  Qed.
  
  Section Extend.
    
    (** * if X is in preKernel but not a kernel there exists X' such that *)
    (** * X <= X' (X != X') and X' is also in preKernel *)
    
    Variable (X: set T).

    (* begin snippet Sx:: no-out *)    
    Definition Y:= [set y | ~ (y \in X) /\ ~ (y \in M#X)].
    (* end snippet Sx *)       

    Definition Mabsorbant := forall y, ~ (y \in X) -> (y \in M#X).

    Definition Non_Mabsorbant := exists y, y \in Y.

    (** * C'est l'ensemble X_y de la nouvelle preuve *)

    (* begin snippet Tm:: no-out *)    
    Definition Xy y:= [set x | x \in X /\ (B (x,y))].
    (* end snippet Tm *)       
    
    (* begin snippet TmI:: no-out *)    
    Lemma XyI: forall y, Xy y `<=` X.
    (* end snippet TmI *)       
    Proof. by move => x y [/inP H2 _]. Qed.
    
    Lemma Xpart: forall y, ( X `\` (Xy y)) `|` (Xy y) = X.
    Proof. move => y;apply: (@setDKU T (Xy y) X);apply: XyI. Qed.
    
    (* begin snippet Sxm:: no-out *)    
    Definition SeP y := forall y', y' \in Y -> R(y,y') -> R(y',y).
    (* end snippet Sxm*)       
    
    (* A consequence of A2 *)
    (* begin snippet Sxone:: no-out *)    
    Lemma Sx_1 (A2: Assumption2):
      (exists y, (y \in Y)) -> (exists (y:T), y \in Y /\ SeP y).
    (* end snippet Sxone*)       
    Proof.  by move => H1; move: (notiic_rloop_sub A2 H1) => H2.  Qed.

    Lemma NonMabsorbant (A2: Assumption2):
      Non_Mabsorbant -> exists y, y \in Y /\ (SeP y).
    Proof. by move => H0;pose proof (Sx_1 A2 H0). Qed.
    
    (* begin snippet Sbunp:: no-out *)    
    Lemma fact0: forall x y, x \in X `\` (Xy y) -> ~ B (x,y).
    (* end snippet Sbunp*)       
    Proof. 
      move => x y /inP [/inP H3 /inP H4].
      have H0: x \in X -> ~(x \in (Xy y)) -> ~ B (x,y).
      by move => H3';rewrite inP not_andE => [[? // | /contrapT ? //]].
      by apply: (H0 H3 H4). 
    Qed.
    
    Lemma fact4: (X:#(R) `<=` M#X) -> forall x y, x \in X -> y \in Y -> (~ (R (x,y))) /\ (~ (M (y,x))).
    Proof.
      move => H0 x y /inP H1 /inP [H2 H3].
      move: H3; rewrite inP/Aset/Fset/mkset => H3.
      rewrite -not_orP => -[ H4 | H4]. 
      + have /H0 H5:  X:#R y by rewrite /Aset/Fset/mkset;(exists x).
        by have H3n: (exists y0 : T, M (y, y0) /\ X y0) by [].
      + by have H3n: (exists y0 : T, M (y, y0) /\ X y0) by (exists x).
    Qed.
    
    Lemma fact3: forall x, forall y, x \in X `\` Xy y -> x \in X. 
    Proof. by move => x y /inP/(@subDsetl T X (Xy y))/inP. Qed.
    
    
    (** the case one:  ~ ( y \in X:#(B) ) and candidate  (X `|` [set y]) *)

    Lemma case1_nonempty: forall y,
        preKernel R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> (X `|` [set y]) != set0.
    Proof.
      by move => y [_ [_ /notempty_iff H0]] _ _ _;rewrite -notempty_iff setU_eq0 => -[? _].
    Qed.

    Lemma case1_indep: forall y, 
        preKernel R M  X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> RelIndep M (X `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /inP [H1 H2] H3 H4.
      have H5: ~ y \in X:#(R) by move => /inP/H0'/inP ?. 
      have H6: ~ y \in X:#(M) by rewrite /M /Aset inverseU -FsetUl => /inP [/inP ? |/inP ?].
      by apply: RelIndep_U.
    Qed.
    
    Lemma case1_RMprop: forall y, 
        preKernel R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) ->
        forall y', ~ (y' \in (X `|` [set y])) -> y' \in (X `|` [set y]):#(R) -> y' \in M#(X `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /inP [H1 H2] H3 H4 y' H5.
      rewrite /Aset FsetUr => /inP [/H0' H6 | /Fset_s H6].
      + by rewrite FsetUr inP;left.
      + (* two subcases *)
        case H7: ( y' \in M#(X));first by rewrite FsetUr inP;left;rewrite -inP.
        have H8: y' \in Y. rewrite /Y inP;split.
        move => H9.
        by have H10: y' \in X `|` [set y] by rewrite inP;left;rewrite -inP.
        by rewrite H7.
        (* end of H8 *)
        move: (H3 y' H8 H6) => H11.
        have H12: y' \in M#([set y]). rewrite inP. exists y.
        split. rewrite /M. by right. by [].
        by rewrite FsetUr inP;right; by rewrite -inP.
    Qed.

    Lemma case1_RMprop1: forall y, 
        preKernel  R M X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> (X `|` [set y]):#(R) `<=` M#(X `|` [set y]).
    Proof.
      move => y H1 H2 H3 H4.
      pose proof (case1_RMprop H1 H2 H3 H4) as H5.
      pose proof (case1_indep  H1 H2 H3 H4) as H6.
      pose proof (preKernelProp1 H6) as H7.
      by rewrite H7.
    Qed.
    
    Lemma case1_Cprop: forall y,
      preKernel R M  X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) -> X [<= D] (X `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /inP [H1 H2] H3 H4 y' /= H5.
      by exists y';split;[rewrite inP;left; rewrite -inP |left].
    Qed.
    
    Lemma case1_notequal: forall y,
      preKernel R M  X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) ) ->
      (exists x' : T, x' \in X `|` [set y] /\ ~ x' \in X).
    Proof.
      by move => y _ /inP [H1 _]; exists y;split;[rewrite inP;right|].
    Qed.
    
    Lemma case1: forall y,
        preKernel R M  X -> y \in Y -> (SeP y) -> ~ ( y \in X:#(B) )
        -> preKernel  R M (X `|` [set y]) /\  X [<= D] (X `|` [set y]) 
          /\ (exists x' : T, x' \in X `|` [set y] /\ ~ x' \in X).
    Proof.
      move => y H1 H2 H3 H4. 
      pose proof (case1_nonempty H1 H2 H3 H4).
      pose proof (case1_indep H1 H2 H3 H4).
      pose proof (case1_RMprop1 H1 H2 H3 H4).
      pose proof (case1_Cprop H1 H2 H3 H4).
      pose proof (case1_notequal H1 H2 H3 H4).
      exact.
    Qed.

    (** the case one:  ( y \in X:#(B) ) and candidate  ((X `\` (Xy y)) `|` [set y]) *)

    Lemma case2_nonempty: forall y,
        preKernel R M  X -> y \in Y -> (SeP y) -> y \in X:#(B) -> ((X `\` (Xy y)) `|` [set y]) != set0.
    Proof.
      move => y [_ [_ /notempty_iff H0]] _ _ _;rewrite -notempty_iff setU_eq0 => -[_ H1].
      have: y \in [set y] by rewrite inP. 
      by rewrite H1 in_set0. 
    Qed.
    
    Lemma case2_indep: forall y, 
        preKernel R M  X -> y \in Y -> (SeP y) -> y \in X:#(B) -> RelIndep M ((X `\` (Xy y)) `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /inP [H1 H2] H3 H4.
      have H5: X `\` Xy y `<=` X by apply: subDsetl.
      pose proof (@RelIndep_Ir T M (X `\` Xy y) X H5 H0) as H6.
      pose proof fact0 as H7.
      have H8: ~ y \in X:#(R) by move => /inP/H0'/inP ?. 

      have H9:  forall x : T, x \in X `\` Xy y -> ~ M (x, y).
      move => x H10. rewrite /M => -[ H11 | H11].
      by have H12: ~ B(x,y) by apply: H7.
      have H12:  X `\` Xy y `<=` X by apply: subDsetl.
      move: H10 => /inP/H12 H10.
      move: H8. rewrite inP /Aset/Fset /mkset => H13.
      have H14: (exists x : T, R^-1 (y, x) /\ X x).
      by (exists x). by [].
      (** fin de H9 *)
      
      have H10:  forall x : T, x \in X `\` Xy y -> ~ M (y, x).
      move => x H11.
      move: H2. rewrite inP /Aset/Fset /mkset => H12.
      have H13:  X `\` Xy y `<=` X by apply: subDsetl.
      move: H11 => /inP/H13 H11.
      move => H14.
      by have H15: (exists y0 : T, M (y, y0) /\ X y0) by (exists x).
      
      have H11: ~ y \in M#(X `\` Xy y).
      by rewrite inP /Aset/Fset /mkset => -[x [H12 /inP/H10 H13]].

      have H12: ~ y \in (X `\` Xy y):#M.
      by rewrite inP /Aset/Fset /mkset => -[x [H12 /inP/H9 H13]].

      by apply: RelIndep_U.
    Qed.
      
    Lemma case2_RMprop (A7:Assumption7) (A8:Assumption8): forall y, 
        preKernel  R M X -> y \in Y -> (SeP y) -> y \in X:#(B) 
        -> ( forall y', ~ (y' \in ((X `\` (Xy y)) `|` [set y]))
                  -> y' \in ((X `\` (Xy y)) `|` [set y]):#(R) -> y' \in M#((X `\` (Xy y)) `|` [set y])).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /inP [H1 H2] H3 H4 y' H4'.
      (** on a necessairement ~ (y = y') **)
      have P0: ~ (y = y')
        by move => I1;(have I2: y \in  X `\` Xy y `|` [set y] by rewrite inP;right);rewrite -I1 in H4'.
      rewrite inP/Aset/Fset/mkset => -[x [H5 [/inP H6 | H6]]];rewrite inP/Aset/Fset/mkset.
      + (** x \in X\X_y *)
        move: (H6) => /fact3/inP H6'.
        have P0': ~ (y' = x)
          by move => I1;(have I2: x \in  X `\` Xy y `|` [set y] by rewrite inP;left;rewrite -inP);
                    rewrite -I1 in I2.
        have H7: y' \in  X:#R by rewrite inP /Aset/Fset /mkset;(exists x).
        have H8: y' \in  M#X by move: H7 => /inP/H0'/inP.
        move: H8 => /inP [x' [H8 H9]].
        move: H9;rewrite -{1}(Xpart y) => -[H9 | H9];first  by (exists x');split;[by [] | left].
        (** x' \in Xy *)
        move: (EM (M (y',x))) => [H10 | H10].
        ++ by (exists x);split;[ | left;apply/inP]. 
        ++ (* we will use A7 to conclude that M(y',y) *)
           exists y; split; last by right. 
           have P1: ~ (x' = x) by move => H11;move: H6 H9;move: H11 => -> /inP [_ ?] ?. 
           have P2: R (x,y') by apply: H5.
           have P3: M (y',x')  by apply: H8.
           have P4: B (x',y) by move: H9;rewrite /Xy => -[H9 H9'].
           have P5: ~ (B (x,y)) by apply: fact0. 
           have P6: ~ (R (x',y)) /\ ~ (M (y,x')) 
             by apply: (fact4 H0');rewrite inP;move: (@XyI y) => H11;move: H9 => /H11. 
           have P7: ~ (R (x,y)) /\ ~ (M (y,x)) 
             by apply: (fact4 H0');rewrite inP.
           have P8:  ~ (M (x,x'))
             by apply: H0;[by rewrite inP
                     | by rewrite inP;move: (@XyI y) => H11;move: H9 => /H11
                     | by move => H11; rewrite H11 in P1].
           have P9:  ~ (M (x',x))
             by apply: H0;[rewrite inP;move: (@XyI y) => H11;move: H9 => /H11 
                          | rewrite inP | move => H11;rewrite H11 in P1].
           have P10: ~ (y = y') by apply: P0.
           have P11: ~ (y' = x) by apply: P0'.
           have P12: ~ (y' = x')
             by move => I1;(have I2: M(x, x') by right ; rewrite -I1).
           have P13: ~ (y = x ) by move => I1;rewrite -I1 -inP in H6'.
           have P14: ~ (y = x' )
             by move => I1;(have: M (x',y) by left);move: P6;rewrite I1 => -[_ I3] I4.
           have P15: ~ (M (y',x)) by exact.
           by move: (A7 x x' y y' P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15).
        ++ have H7: x = y. by [].
           have H8: R (y,y') by rewrite H7 in H5.
           case H9: (y' \in M#(X)); last first.
           +++ case H10: (y' \in (Xy y)).
               ++++ move: H10;rewrite /Xy => /inP [H11 H12].
                    exists y. split. by rewrite /M;left. by right.
               ++++ have H11: y' \in Y. 
                    rewrite inP/Y. split.
                    rewrite -{1}(Xpart y) inP => -[H12| /inP H12]. 
                    by have H13: y' \in X `\` Xy y `|` [set y] by rewrite inP; left.
                    by rewrite H10 in H12.
                    by rewrite H9. 
                    (** * end H11 *)
                    have H12: M (y', y)  by rewrite /M;right;apply: (H3 y' H11 H8).
                    by (exists y);split;[ | right].
           +++ move: H9;rewrite -{1}(Xpart y) => /inP [x' [H9 [[H10 H10'] | H10]]].
               ++++ by (exists x');split;[ | left].
               ++++ move: (EM (y' = x')) => [H9'| H9'].
                    by (have H11: M (y',y) by left;rewrite H9';move: H10 => [_ H10]);
                    (exists y);split;[|  right].
                    
                    have H11: x' \in X by move: H10;rewrite /Xy => -[? _]. 
                    have H12: y \in Y by rewrite inP/Y.
                    
                    have B0: ~ (y' = x') by apply: H9'.
                    have B0': ~ (y = y') by apply: P0.
                    have B0'': ~ (y = x') 
                      by move: H12 => /inP [H12 _] H13;rewrite H13 in H12.
                    
                    have B1: R (y,y') by apply: H8.
                    have B2: M (y',x') by apply: H9.
                    have B3: B (x',y) by move: H10;rewrite /Xy => -[_ ?]. 
                    have B4: ~ (R (x',y)) /\ ~ M (y, x') by apply: (fact4 H0' H11 H12). 
                    
                    move: (A8 x' y y' B0 B0' B0'' B1 B2 B3 B4) => B5.
                    by (exists y);split;[ | right].
    Qed.
    
    Lemma case2_RMprop1 (A7:Assumption7) (A8:Assumption8):
      forall y, preKernel  R M X -> y \in Y -> (SeP y) -> y \in X:#(B) 
           -> ((X `\` (Xy y)) `|` [set y]):#(R) `<=` M#((X `\` (Xy y)) `|` [set y]).
    Proof.
      move => y H1 H2 H3 H4.
      pose proof (case2_RMprop A7 A8 H1 H2 H3 H4) as H7.
      pose proof (case2_indep  H1 H2 H3 H4) as H8.
      pose proof (preKernelProp1 H8) as H9.
      by rewrite H9.
    Qed.

    Lemma case2_Cprop (A6: Assumption6): forall y,
      preKernel R M  X -> y \in Y -> (SeP y) -> ( y \in X:#(B) )
      -> X [<= D] ((X`\` (Xy y)) `|` [set y]).
    Proof.
      rewrite /SeP;move => y [H0 [H0' H0'']] /inP [H1 H2] H3 H4 x /=.
      rewrite -{1}(Xpart y) inP => -[ H5 | H5].
      + (* x \in  X `\` Xy *) by (exists x);split;[rewrite inP;left | left].
      + (* x \in Xy y *) exists y;split;first by rewrite inP;right. 
        have H6: B (x,y) by move: H5 => [_ ?].
        move: H2;rewrite inP/Fset/mkset => H2.
        have H7: X x  by rewrite -{1}(Xpart y);right.
        have H8: ~ (M (y, x))
          by move => H8;have H9: (exists y0 : T, M (y, y0) /\ X y0) by (exists x).
        by right; apply: A6.
    Qed.
    
    Lemma case2_notequal: forall y,
      preKernel  R M X -> y \in Y -> (SeP y) -> ( y \in X:#(B) ) ->
      (exists x' : T, x' \in ((X`\` (Xy y)) `|` [set y]) /\ ~ x' \in X).
    Proof.
      by move => y _ /inP [H1 _]; exists y;split;[rewrite inP;right|].
    Qed.

    Lemma case2 (A6: Assumption6)(A7: Assumption7)(A8: Assumption8) : forall y,
        preKernel  R M X -> y \in Y -> (SeP y) -> ( y \in X:#(B) )
        -> preKernel  R M ((X`\` (Xy y)) `|` [set y]) /\  X [<= D] ((X`\` (Xy y)) `|` [set y])
          /\ (exists x' : T, x' \in ((X`\` (Xy y)) `|` [set y]) /\ ~ x' \in X).
    Proof.
      move => y H1 H2 H3 H4. 
      pose proof (case2_nonempty H1 H2 H3 H4).
      pose proof (case2_indep H1 H2 H3 H4).
      pose proof (case2_RMprop1 A7 A8 H1 H2 H3 H4).
      pose proof (case2_Cprop A6 H1 H2 H3 H4).
      pose proof (case2_notequal H1 H2 H3 H4).
      exact.
    Qed.

    Lemma extend (A2: Assumption2) (A6: Assumption6) (A7: Assumption7) (A8: Assumption8):
        preKernel  R M X -> Non_Mabsorbant ->
        exists X', preKernel  R M X' /\  X [<= D] X' /\ (exists x', x' \in X' /\ ~ (x' \in X)).
    Proof.
      move => H1 /(NonMabsorbant A2) [y [H2 H3]]. 
      have H4: y \in (X:#(B) `|` (X:#(B)).^c) by rewrite (setUv X:#(B)) inP.
      move: H4 => /inP [/inP H4 | H4].
      by move: (case2 A6 A7 A8 H1 H2 H3 H4) => H5;exists (X `\` Xy y `|` [set y]).
      move: H4;rewrite -inP  in_setC notin_setE => /inP H4.
      by move: (case1 H1 H2 H3 H4) => H5;exists (X `|` [set y]).
    Qed.
    
  End Extend. 
  
End Paper.


