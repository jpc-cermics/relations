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
From mathcomp Require Import all_ssreflect seq order boolp classical_sets. 
Set Warnings "parsing coercions".

From RL Require Import  seq1 ssrel rel.

(* Require Import ClassicalChoice. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "A [<=] B" (at level 4, no associativity). 
Reserved Notation "A [<= R ] S" (at level 4, no associativity). 

Section Asym. 
  (** * Asymmetric part of a relation *) 
    
  Variables (T: Type) (R: relation T).
  
  Definition Asym (R: relation T): relation T := [set xy | R xy /\ ~ (R.-1 xy)].
  
  Lemma Asym_antisymmetric: antisymmetric  (Asym R).
  Proof. by move => x y [_ ?] [? _]. Qed.

  Lemma Asym_irreflexive: irreflexive (Asym R).
  Proof. by move => x [? ?]. Qed.

  Lemma Asym_preserve_transitivity: transitive R -> transitive (Asym R).
  Proof.
    move => H0 x y z [H1 /= H1'] [H2 /= H2'];split => [ | /= H3].
    by apply: H0 H1 H2.
    by have: R (y,x) by apply: H0 H2 H3.
  Qed.
  
  Lemma AsymE: antisymmetric R /\ irreflexive R <-> Asym R = R.
  Proof.
    split; last by move => <-;split;
                          [apply: Asym_antisymmetric | apply: Asym_irreflexive].
    move => [H1 H2].
    rewrite predeqE => [[x y]]; split => [[H3 _] // | H3]. 
    split; first by [].
    by move: H3 => /[dup] H3 /H1 H3' /H3' H4; move: H3; rewrite H4 => /H2 H3.
  Qed.

  Lemma AsymI: forall (R: relation T), Asym R `<=` R.
  Proof. by move => R' [a b] [? _]. Qed.

  Lemma AsymInvol: Asym (Asym R) = (Asym R).
  Proof.
    rewrite predeqE => [[a b]];split; first by move => [? _].
    move => H1;split; first by [].
    move => H2. 
    move: Asym_antisymmetric => /(_  a b) H3.
    move: (H1) (H2) => /H3 H1' /H1' H2'.
    by move: H1; rewrite H2'; apply: Asym_irreflexive. 
  Qed.
  
  Lemma AsymIncl: R.+ `;` Asym(R.+) `<=`  Asym(R.+).
  Proof.
    move: AsymI => /(_ R.+) H3 => [[x y] [z /= [H1 /[dup] H2 /H3 H4]]].
    split =>[| H5]; first by apply: (t_trans H1 H4).
    have H6: R.+ (y,z) by apply: (t_trans H5 H1).
    by move: H2 => [_ H2].
  Qed.
    
  Lemma AsymIncr: Asym(R.+) `;` R.+ `<=`  Asym(R.+).
  Proof.
    move: AsymI => /(_ R.+) H3 => [[x y] [z /= [/[dup] H2 /H3 H4 H1]]].
    split =>[| H5]; first by apply: (t_trans H4 H1).
    have H6: R.+ (z,x) by apply: (t_trans H1 H5).
    by move: H2 => [_ H2 ].
  Qed.
  
End Asym.

Section Independent_set.
  (** * Independence of sets with respect to a relation *)
  
  Variables (T: Type) (R: relation T).

  (* begin snippet RelIndep:: no-out *)    
  Definition RelIndep (R: relation T) (S: set T) :=
    forall (x y:T),  x \in S -> y \in S -> ~(x = y) -> ~( R (x,y)).
  (* end snippet RelIndep *)    
  
  Lemma RelIndep_I: forall (Q R: relation T) (S: set T),
      Q `<=` R -> RelIndep R S -> RelIndep Q S.
  Proof.
    move => Q R' S H1 H2 x y H3 H4 H5 /H1 H6.
    by pose proof (H2 x y) H3 H4 H5.
  Qed.
  
  Lemma RelIndep_set0: RelIndep R set0.
  Proof. by move => x y /inP H3 _ _ _. Qed.
  
  Lemma RelIndep_set1: forall (x: T), RelIndep R [set x].
  Proof. by move => x x1 x2 /inP -> /inP -> H4. Qed.
  
  Lemma RelIndep_U: forall X x,
      RelIndep R X -> ~(x \in R#X) -> ~(x \in (X:#R)) -> RelIndep R (X `|` [set x]).
  Proof.
    move => X x H2 H3 H4 x1 x2 /inP 
             [/inP H5 | /inP H5] /inP [/inP H6 |/inP H6] H7 H8.
    rewrite /RelIndep in H2.
    + by apply: ((H2 x1 x2) H5 H6 H7 H8).
    + move: H6 H4 => /inP <- H4. 
      by have H9: x2 \in X:#R by rewrite inP;exists x1; rewrite inP in H5.
    + move: H5 H3 => /inP <- H3. 
      by have H9: x1 \in R#X by rewrite inP;exists x2;rewrite inP in H6.
    + by move: H5 H6 H7 => /inP -> /inP ->. 
  Qed.
  
End Independent_set.

Section Set_relation. 
  (** * A relation on sets induced by a relation on elements *)

  Variables (T: eqType) (R: relation T).
  
  (* begin snippet leset:: no-out *)    
  Definition leSet (R: relation T): relation (set T) := 
    [set AB |forall (a:T), (a \in AB.1) -> exists b, b \in AB.2 /\ ( a = b \/ R (a,b)) ].
  
  Notation "A [<= R ] B" := (leSet R (A,B)).
  (* end snippet leset *)       
  
  Definition leSet' (R: relation T): relation (set T) :=
    [set AB | AB.1 `<=` ('Δ  `|` R)#AB.2]. 
  
  Lemma lesetE : forall (R: relation T), leSet R = leSet' R. 
  Proof.
    move => R';rewrite predeqE => -[A B];split. 
    - move => H1 a /inP/H1 [b [/inP H2 [->| H3]]]; first by (exists b);split;[left|].
      by (exists b);split;[right|].
    - rewrite /leSet' /mkset /= -Fset_union_rel Fset_D.
      move => H1 a /inP/H1 [/inP H2 | [b [H2 /inP H3]]].
      by (exists a); split;[ | left].
      by exists b; split;[ | right].
  Qed.
  
  Lemma Ile: forall (A B: set T), A `<=` B -> A [<= R] B.
  Proof. by move => A B H1 /= a /inP/H1 ?;exists a;split;[rewrite inP|left]. Qed.

  Lemma leI: forall (Q R: relation T), Q `<=` R -> (leSet Q)  `<=` (leSet R).
  Proof.
    move => R' V H1;rewrite lesetE lesetE => [[A B]] H2.
    have H3: ('Δ  `|` R')#B `<=` ('Δ  `|` V)#B by apply: Fset_inc; apply: setUS.
    by apply: subset_trans H2 H3.
  Qed.
   
End Set_relation.

(** Notation for the set order we use *)
Notation "A [<= R ] B" := (leSet R (A,B)).

Section Set_order. 
  (** * the previous relation [<= R] is an order relation on R-independent sets *)
  
  Variables (T: eqType) (R: relation T). 

  Axiom proof_irrelevance: forall (P : Prop) (p q : P), p = q.
  
  Definition isetType := {S: set T| RelIndep R S}.
  
  Definition leSet2 (AB: isetType* isetType) := (sval AB.1) [<= R] (sval AB.2).

  Section Util.
    (** ingredients *)
    Lemma le_trans (U: relation T): transitive U -> transitive (leSet U).
    Proof.
      rewrite lesetE => /clos_t_iff H0 A B C /= H1 H2.
      have : ('Δ  `|` U)#B `<=` ('Δ  `|` U)#(('Δ  `|` U)#C) by apply: Fset_inc1.
      rewrite Fset_comp H0 DuT_eq_Tstar compose_rt_rt -DuT_eq_Tstar -H0 => H3.
      by apply: subset_trans H1 H3.
    Qed.

    Lemma le_refl (U: relation T): reflexive (leSet U).
    Proof. by move => A r H1;exists r;split;[| left]. Qed.
 
    Lemma le_antisym_l1' (U: relation T): 
      transitive U -> Asym U = U ->
      forall A B, (RelIndep U A) -> A [<= U] B -> B  [<= U] A -> A `<=` B.
    Proof.
      move => H0 H0' A B H1 H2 H3 a H4.
      move: H2 H3; rewrite -H0' => H2 H3.
      move: (H4) => /inP /H2 [b [/inP /= H5 [-> // | [H6 H6']]]]. 
      move: (H5) => /inP /H3 /= [c [/inP H8 H9]].
      case H10: (a == b ); first by move: H10 => /eqP ->.
      move: H10 => /eqP H10.
      case H12: (b == c).
      - move: H12 H8 => /eqP <- H8.
        by have: False by move: H4 H8 => /inP H4 /inP H8;apply: (H1 a b). 
      - move: H12 H9 => /eqP H12 [H9 // | [H9 H9']].
        case H13: (a == c); first by move: H13 H9' => /eqP <- H9'.
        have H14: U (a,c) by apply: H0 H6 H9.
        by have: False by move: H13 H4 H8 => /eqP H13 /inP H4 /inP H8; apply: (H1 a c). 
    Qed.
  
    Lemma le_antisym (U: relation T): 
      transitive U -> Asym U = U -> 
      forall A B, (RelIndep U A) -> (RelIndep U B) 
             -> A [<= U] B -> B  [<= U] A -> A = B.
    Proof.
      move => H0 H0' A B H1 H2 H3 H4.
      by move: (le_antisym_l1' H0 H0' H1 H3 H4)
                 (le_antisym_l1' H0 H0' H2 H4 H3);rewrite eqEsubset.
    Qed.
  
  End Util.

  Lemma leSet2_transitive: transitive R -> @transitive isetType leSet2.
  Proof. by move => ? [A ?] [B ?] [C ?]; apply/le_trans. Qed.
  
  Lemma leSet2_reflexive: @reflexive isetType leSet2.
  Proof. by move => [A ?];apply: le_refl. Qed.

  Lemma leSet2_antisymmetric:
    transitive R -> Asym R = R ->  @antisymmetric isetType leSet2.
  Proof. 
    move => H_T H_As [A Ha] [B Hb] H1 H2.
    move: (le_antisym H_T H_As Ha Hb H1 H2) => H5.
    subst A;apply: f_equal;apply: proof_irrelevance.
  Qed.
  
End Set_order. 

Section Infinite_paths.
  (** * Assumptions on infinite paths *)
  Variables (T:Type).

  (* total (or left total)  *) 
  Definition total_rel (R: relation T) := forall x, exists y, R (x,y).
  
  Definition total_rel' (R: relation T) := exists f : T -> T, forall x, R (x, f x). 
  
  (* choice from boolp version for relation T *)
  Lemma choice': forall (R: relation T), total_rel R -> total_rel' R.
  Proof.
    move => S H1.
    have H2: forall x : T, exists y : T, (curry S) x y
        by move => x;move: H1 => /(_ x) [y H1];exists y.
    move: H2 => /choice [f H2].
    by exists f => x; move: H2 => /(_ x).
  Qed.
  
  Lemma total_rel_iff: forall (R: relation T),  total_rel R <-> total_rel' R.
  Proof.
    by move => R; split =>[| [f H1] x];[apply: choice' | exists (f x)].
  Qed.
  
  Definition total_rel'' (R: relation T) := 
    (forall x, exists f : nat -> T, f 0 = x /\ forall n, R ((f n),(f (S n)))).
  
  Fixpoint iter (f: T -> T) (x: T) k := 
    match k with 
    | 0 => x 
    | S m => f (iter f x m)
    end. 
  
  Lemma iterP: forall k f x, iter f x k.+1 = f (iter f x k).
  Proof. by elim. Qed.
  
  Lemma total_rel'_to_total_rel'' (R: relation T):
    total_rel' R -> total_rel'' R.
  Proof. by move => [f H1] x;exists (iter f x). Qed.
  
  Definition iic (R: relation T) := exists f : nat -> T, forall n, R ((f n),(f (S n))).  
  
  Lemma total_rel''_to_iic (R: relation T): 
    (exists (v0:T), (v0 \in setT)) ->  total_rel'' R -> iic R. 
  Proof.
    by move => -[v0 H1] /(_ v0) [f [H2 H3]]; exists f.
  Qed.
  
  (** * DC as a lemma deduced from choice *)
  Lemma DC: forall (R: relation T),
      (exists (v0:T), (v0 \in setT)) ->  total_rel R -> iic R. 
  Proof.
    by move => R H0 /total_rel_iff/total_rel'_to_total_rel''/(total_rel''_to_iic H0) H1.
  Qed.
  
  (* begin snippet Rloop:: no-out *)    
  Definition Rloop (S: relation T) := exists v, forall w,  S (v,w) -> S (w,v).
  (* end snippet Rloop *)
  
  Lemma test (S: relation T):
    (antisymmetric S /\ irreflexive S /\ Rloop S) -> (~ (total_rel S)).
  Proof.
    move => [H1 [H1' [v H2]]].
    rewrite -existsNP; exists v; rewrite -forallNE => x /[dup] H3 /H2 H4.
    have H5: x = v by apply: H1.
    by move: H3; rewrite H5 => /H1'.
  Qed.
  
  Lemma test1 (S: relation T): (~ (total_rel S)) -> exists v, (forall x : T, ~ S (v, x)).
  Proof. by rewrite -existsNP => -[v H1];exists v;move: H1; rewrite -forallNE. Qed. 

  Lemma test2 (S: relation T): (exists v, (forall x : T, ~ S (v, x)))-> Rloop S.
  Proof. by move => -[v H1];exists v => y /H1 H2. Qed. 

  Lemma test3 (S: relation T): ~ (Rloop S) -> total_rel (Asym S).
  Proof. 
    by rewrite -forallNE => H1 v;move: H1 => /(_ v)/existsNP [w /not_implyP H1];exists w.
  Qed.

  Lemma test4 (S: relation T): (Rloop S) -> Rloop (Asym S).
  Proof.
    by move => [v H1];exists v => w [H2 H3];split;[apply: H1| move: H2 => /H1 H2].
  Qed.

  Lemma test5 (S: relation T):
    (Rloop S) -> let Sa:= (Asym S) in exists v, (forall x : T, ~ (Sa (v, x))).
  Proof. by move => [v H1];exists v => w [/H1 H2 H3]. Qed.
  
  Lemma notiic_rloop: forall (S: relation T),
      (exists (v0:T), (v0 \in setT)) -> ~ (iic (Asym S)) -> (Rloop S).
  Proof. 
    by move => S H0; apply contraPP => /test3/(DC H0) H1.
  Qed.

End Infinite_paths.

Section Infinite_paths_X.
  (** * Assumptions on infinite paths *)
  Variables (T:Type).

  (** (* this is mem_setT *)
  Lemma test90 (X: set T): forall (x: X), x\in [set: X].
  Proof. by move => x; apply: mem_setT. Qed.
      (* this is set_valP *)
  Lemma test91 (X: set T): forall (x: X), (sval x) \in X. 
  Proof. by move => x; rewrite inP; apply: set_valP.  Qed.
  
  Lemma XtoT (X: set T): forall x, x \in X -> exists (x': X), (sval x') = x.
  Proof. by move => x H1;exists (exist _ x H1). Qed.
  *)
  
  Lemma setTypeP (X: set T):
    (exists v : X, v \in [set: X]) <-> (exists (v:T), (v \in X)).
  Proof.
    split => [[v H0] |[v H0]].
    by (exists (sval v));rewrite inP; apply: set_valP. 
    by (exists (exist _ v H0));rewrite inP.
  Qed.
  
  Lemma notiic_rloop_sub: forall (X: set T) (S: relation X),
      (exists (v0:T), (v0 \in X)) -> ~ (iic (Asym S)) -> (Rloop S).
  Proof. by move => X S /setTypeP H0; apply: notiic_rloop. Qed. 
  
  Definition Restrict (T:Type) (R: relation T) (X: set T) : relation X := 
    [set xy : X*X | R ((sval xy.1),(sval xy.2))].
  
  Lemma test67 : forall (X: set T) (R: relation T),
      (iic (@Restrict T (Asym R) X)) -> (iic (Asym R)).
  Proof.
    by move => X R [f // H1];exists (fun n => (sval (f n))).
  Qed.

  Lemma test68: forall (X: set T) (R: relation T),
      ~ (iic (Asym R)) -> (exists (v0:T), (v0 \in X))
      -> (Rloop (@Restrict T R X)).
  Proof.
    move => X R H1 H0.
    have H2:  ~ (iic (Asym R)) -> ~ (iic (@Restrict T (Asym R) X))
      by apply contraPP;rewrite notE notE; apply: test67.
    move: H1 => /H2 H1.
    by apply: (notiic_rloop_sub H0 H1).
  Qed.
    
  Lemma test68': forall (X: set T) (R: relation T),
       ~ (iic (Asym R)) ->(exists (v0:T), (v0 \in X))
      -> (exists (v:T), v \in X /\ forall w, w \in X -> R (v,w) -> R (w,v)).
  Proof.
    move => X R Ninf H0.
    move: (test68 Ninf H0) => [v H1].
    exists (sval v).
    split. 
    by rewrite inP; apply: set_valP.
    move => w H2.
    have [w' <-]: exists (w': X), (sval w') = w by exists (exist _ w H2). 
    move => H3.
    by apply: H1.
  Qed.
  
End Infinite_paths_X.

Section Paper. 
  (*  On Monochromatic Paths in Edge-Coulured Digraphs *)
  Variables (T:choiceType) (Eb Er: relation T).

  (** Mono (x,y): there exists a monochromatic oriented path from x to y *)
  (* begin snippet Mono:: no-out *)   
  Definition Mono :=  Eb.+ `|` Er.+.
  (* end snippet Mono *) 

  (** The after set of S (for the red-path relation) is included in the forset of S 
   *  for the monochromatic path relation *)

  (* begin snippet ScalP:: no-out *)    
  Definition ScalP (S: set T) := S:#(Er.+) `<=` Mono#S.
  (* end snippet ScalP *)    

  (* The set Scal as a subset of T *)
  (* begin snippet Scal:: no-out *) 
  Definition Scal := [ set S | RelIndep Mono S /\ ScalP S /\  S != set0 ].
  (* end snippet Scal *) 
    
  (* The set Scal as a Type *)
  Definition SType := {S: set T| RelIndep Mono S /\ ScalP S /\ S != set0}.

  Definition Elt (C: set SType) := {x : T |exists (S: SType), S \in C /\ x \in (sval S)}.
  
  Lemma S2Scal: forall (S: SType), (sval S) \in Scal.
  Proof. by move => [S [H1 [H2 H3]]];rewrite inP. Qed.

  Lemma Scal2S: forall S, S \in Scal -> exists (S': SType), (sval S') = S.
  Proof.  by move => S /inP H1; exists (exist _ S H1). Qed.
  
  Definition leSet1 (AB: SType*SType) :=
    leSet (Asym Eb.+) ((proj1_sig AB.1), (proj1_sig AB.2)).

  (** * The relation on sets restricted to Stype subsets *)
  Notation "A [<=] B" := (leSet1 (A,B)).
  
  Section Scal_order. 

    Lemma leSet1_transitive: @transitive SType leSet1.
    Proof. by move => [A ?] [B ?] [C ?]; 
                     apply/le_trans/Asym_preserve_transitivity/t_trans. Qed.
    
    Lemma leSet1_reflexive: @reflexive SType leSet1.
    Proof. by move => [A ?];apply: le_refl. Qed.
    
    Lemma le_antisym_l1: forall A B, 
        (RelIndep Mono A) -> (RelIndep Mono B)
        -> A [<= (Asym Eb.+)] B -> B  [<= (Asym Eb.+)] A -> A = B.
    Proof.
      move => A B H1 H2 H1' H2'. 
      pose proof @AsymI T (Eb.+) as H3.
      have H4: Eb.+ `<=` Mono by apply: subsetUl.
      have H5: Asym Eb.+ `<=` Mono by apply: subset_trans H3 H4.
      have H6: (RelIndep (Asym Eb.+) A) by apply: RelIndep_I H5 H1. 
      have H7: (RelIndep (Asym Eb.+) B) by apply: RelIndep_I H5 H2. 
      have H8: transitive (Asym Eb.+) 
        by apply: Asym_preserve_transitivity;apply: t_trans.
      have H9: (Asym (Asym Eb.+)) = (Asym Eb.+) by apply: AsymInvol.
      by move : (le_antisym H8 H9 H6 H7 H1' H2').
    Qed.
    
    Lemma leSet1_antisymmetric: @antisymmetric SType leSet1.
    Proof. 
      move => [A Ha] [B Hb] H1 H2.
      move: (Ha) (Hb) => [Ha' Ha''] [Hb' Hb''].
      move: (le_antisym_l1 Ha' Hb' H1 H2) => H5.
      subst A. (** why I cannot use rewrite *)
      apply: f_equal.
      apply: proof_irrelevance.
    Qed.
    
  End Scal_order.

  Section SType_chains.
    (** * Chains in Stype *)
    Definition Chains := [set C: set SType| forall (c1 c2: SType),
          c1 \in C -> c2 \in C -> c1 [<=] c2 \/ c2 [<=] c1].
    
    Lemma Chains_is_total: forall (A : set SType),
        A \in Chains <-> total_on A (curry leSet1).
    Proof. split => [/inP H2 c1 c2 /inP ? /inP ?| H1]; first by apply: H2. 
           by apply/inP => c1 c2 /inP H2 /inP H3;apply: H1.
    Qed.
  
    Lemma Chains_Scal:  forall (C: set SType) S,
        C \in Chains -> S \in C -> Scal (sval S).
    Proof. by move => C [S [H1 [H2 H3]]] /inP H4 /inP H5. Qed.
  
    Lemma Elt_not_empty: forall (C: set SType), 
        C \in Chains -> C != set0 -> exists (S: SType), (S \in C /\ (exists x, x \in (sval S))).
    Proof.
      move => C H1 /notempty_exists [S H2];exists S;split;first by []. 
      by move: S H2 => [S' [H3 [H4 /notempty_exists H5]] /=] _.
    Qed.
    
  End SType_chains.

  Section Sinf_set.
    (** * Sinf C for a non empty Chain *)
    
    Variables  (C: set SType).
    Hypothesis Hc: C \in Chains. 
    Hypothesis Hne: C != set0.
    
    Definition Ec := Elt C.

    (* Set Sinf associated to a chain *)
    Definition Sinf := 
      [ set v: T | 
        exists S, (S \in C) /\ (v \in (sval S)) /\ (forall T, T \in C -> S [<=] T -> v \in (sval T))].
    
    (* A relation on the set Elt C, all the elements
       of T which are elements of a set in the chain C *)
    Definition RC:= [set xy:Ec*Ec |
                      ((sval xy.1) \in Sinf /\ xy.2 = xy.1)
                      \/ (~ ((sval xy.1) \in Sinf) /\ (Asym Eb.+) (sval xy.1, sval xy.2))].
    
    Lemma transitive_RC: transitive RC. 
    Proof.
      have H3: transitive (Asym Eb.+) by apply/Asym_preserve_transitivity/t_trans.
      by move => x y z [/= [H0 ->]| [H1 H1']] [ /= [H0' /= ->]| /= [H2 H2']]; 
                [left | right | right |right;split;[ | apply H3 with (sval y)]].
    Qed.
    
    Lemma ChnotE: exists _ : Elt C, True.
    Proof.
      move: (Elt_not_empty Hc Hne) => [S [H2 [x H3]]].
      have H4: exists (S: SType), S \in C /\ x \in (sval S) by (exists S).
      by exists (exist _ x H4).
    Qed.
    
    Lemma ChnotE_witness: Elt C.
    Proof. by apply: inhabited_witness; rewrite inhabitedE; apply: ChnotE. Qed.
    
    (* Sinf is a Mono-independent set *)
    Lemma Sinf_indep: RelIndep Mono Sinf.
    Proof.
      move: Hc => /inP H1 x y /inP H2 /inP H3 H4 /= H5.
      move: H2 H3 =>[S [H6 [/= H7 H8]]] [U [H6' [/= H7' H8']]].
      move: H8 H8' => /((_ U) H6') H8 /((_ S) H6) H8'.
      have [H9|H9]: S [<=] U \/ U [<=] S by apply: H1.
      - move: H9 H1 => /H8 H9 /inP H1.
        move: (Chains_Scal H1 H6') => [/(_ x y) H10 _].
        by apply: (H10 H9 H7' H4 H5).
      - move: H9 H1 => /H8' H9 /inP H1.
        move: (Chains_Scal H1 H6) => [/(_ x y) H10 _].
        by apply: (H10 H7 H9 H4 H5).
    Qed.
    
    Section Ec_seq. 
      (** *  the main result here is total_RC *) 

      Lemma Ec_seq1: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, S1 \in C /\ S [<=] S1 /\ ~ (s \in (sval S1)).
      Proof.
        move: Hc => H1 S s H2 H3. 
        apply contraPP;rewrite not_existsP 2!notE inP /Sinf => H4;exists S.
        split => [// | ];split => [// |A ? ?].
        by move: H4 => /(_ A) /not_andP [? //|/not_andP [// | /contrapT ?]].
      Qed.
      
      Lemma Ec_seq2: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, exists s1, S1 \in C /\ s1 \in (sval S1) /\ (Asym Eb.+) (s,s1).
      Proof.
        move: Hc => H1 S s H2 H3 H4.
        move: (Ec_seq1 H2 H3 H4) => [S1 [H5 [H6 H7]]].
        by move: ((H6 s) H3) => [s1 [H8 [H9 | H9]]];exists S1, s1;[rewrite -H9 in H8|].
      Qed.
      
      Lemma Ec_seq3: forall (s: Ec), 
          ~ ((sval s) \in Sinf) -> exists (s1: Ec), (Asym Eb.+) (sval s,sval s1).
      Proof.
        move => [s [S [H1 H2]]] H3.
        move: (Ec_seq2 H1 H2 H3) => [S1 [s1 [H4 [H5 H6]]]].
        have H7: exists (S: SType), S \in C /\ s1 \in (sval S) by (exists S1).
        by exists (exist _ s1 H7).
      Qed.
      
      Lemma total_RC: total_rel RC. 
      Proof.
        move => s.
        case H3: ((sval s) \in Sinf); first by (exists s); left.
        have H4: ~ ((sval s) \in Sinf) by move => H5;rewrite H5 in H3.
        move: (Ec_seq3 H4) => [s1 H5].
        by exists s1; right.
      Qed.
      
    End Ec_seq.
    
    Section XXX.

      Lemma test0_iic_RC: forall s, exists f : nat -> Ec, f 0 = s /\ forall n, RC ((f n),(f (S n))).  
      Proof. 
        by move: total_RC => /total_rel_iff H1;apply: total_rel'_to_total_rel''. 
      Qed.
      
      Lemma test1_RC:forall s, forall f, f 0=s /\ (forall n, RC ((f n),(f (S n)))) 
                               -> (forall n, ~ (sval (f n)) \in Sinf)
                               -> (forall n, (Asym Eb.+) (sval (f n), sval(f (S n)))).
      Proof. 
        by move => s f + + n => [[H0 /(_ n) [/=[H1 H1'] | /= [H1 H1']]]] /(_ n) H2.
      Qed.
      
      Lemma test3_RC: ~ (iic (Asym Eb.+)) -> 
                      forall s, exists f, (f 0=s /\ (forall n, RC ((f n),(f (S n)))))
                                /\ ~ (forall n, ~ (sval (f n)) \in Sinf).
      Proof.
        move => H1; move: test0_iic_RC => + s => /(_ s) [f H2].
        exists f; split => [// | H4]. 
        have H5:  iic (Asym Eb.+)
          by exists (fun n => (sval (f n)));move: test1_RC => /(_ s f) H6;apply: H6. 
               exact.
      Qed.
      
      Lemma test4_RC: ~ (iic (Asym Eb.+)) ->
                      forall s, exists f, (f 0=s /\ (forall n, RC ((f n),(f (S n)))))
                                /\ exists n, (sval (f n)) \in Sinf.
      Proof.
        move => H1; move: (test3_RC H1) => + s => /(_ s) [f [H2 /not_existsP [n H3]]].
        exists f;split;[ exact| exists n; exact].
      Qed.

      Lemma transitiveN_RC: forall f, 
          (forall n, RC ((f n),(f (S n)))) -> (forall n, n > 1 -> RC (f 0, f n)).
      Proof.
        move => f H1;elim => [// | n Hn H2 ].
        case H3: (1 < n). 
        + have H4: RC (f 0, f n) by apply: Hn;rewrite H3.
          by move : (transitive_RC H4 (H1 n)).
        + case H5: (n == 0); first by move: H5 => /eqP ->; apply: H1.
          case H6: (n == 1); first by move: H6 => /eqP ->;move: (transitive_RC (H1 0) (H1 1)).
          have H7: ~ (n <= 1) by rewrite leq_eqVlt H6 ltnS leqn0 H5.  
          by rewrite leqNgt H3 in H7.
      Qed.
      
      Lemma Util: forall n, ~ (n = 0) /\ ~ (n = 1) ->  n > 1. 
      Proof.
        move => n [/eqP H1 /eqP H2]. 
        have: n >= 0 by []; rewrite  leq_eqVlt => /orP [/eqP H3 // | ].
        by move: H3 H1 => H3; rewrite -H3. 
        rewrite leq_eqVlt => /orP [/eqP H4 | H4 //].
        by move: H2; by rewrite -H4.
      Qed.
      
      Lemma test_yy: ~ (iic (Asym Eb.+)) ->
                     forall s, exists f, f 0=s /\ (exists n, (sval (f n)) \in Sinf /\ RC ((f 0), (f n))).
      Proof.
        move => H1; move: (test4_RC H1) => + s => /(_ s) [f [[H2 H3] [n H4]]].
        exists f. split;first by [].
        case H5: (sval (f 0) \in Sinf).
        + exists 0. split.  by []. left. by [].
        + have H6: ~ (n = 0). move => H6. rewrite H6 in H4. by rewrite H5 in H4.
          case H7: (sval (f 1) \in Sinf).
          ++ by (exists 1).
          ++ exists n. 
             have H8: ~ (n = 1). move => H8. rewrite H8 in H4. by rewrite H7 in H4.
             have H9: n > 1 by apply Util.
             move: (transitiveN_RC H3) => /(_ n) H10.
             split. by []. by apply: H10.           
      Qed.


      Lemma ChooseRC5:~ (iic (Asym Eb.+))
            -> forall (s:Ec), (sval s \in Sinf) \/ exists s',  s' \in Sinf /\ (Asym Eb.+) (sval s, s').
      Proof. 
        move => H1; move: (test_yy H1) => + s => /(_ s) [f [H2 [n [H3 H3']]]].
        case H4: (sval (f 0) \in Sinf ). by left; rewrite -H2 H4.
        right. exists (sval (f n)). split. by []. 
        rewrite -H2. 
        move: H3' => [/= [H3' _] | /= [H5 H6]].
        by rewrite H4 in H3'.
        by [].
      Qed.

      Lemma ChooseRC6:~ (iic (Asym Eb.+)) -> forall (S: SType), (S \in C) -> (sval S) [<= (Asym Eb.+)] Sinf.
      Proof. 
        move => H1 S H2 s /= H3.
        have H4: exists (S: SType), S \in C /\ s \in (sval S) by (exists S).
        move: (ChooseRC5 H1 (exist _ s H4)) => /= [H5 | [s' [H5 H6]]].
        by (exists s);split;[|left].
        by (exists s');split;[|right].
      Qed.
      
    End XXX.
    
    (** * The Assumptions we use: weaker than the original paper assumptions *)
    (* begin snippet Assumptions:: no-out *)    
    Hypothesis A1: (exists (v0:T), (v0 \in setT)).
    Hypothesis A3: ~ (iic (Asym Er.+)).
    Hypothesis A4: ~ (iic (Asym Eb.+)).
    (* end snippet Assumptions *)    
    
    (* begin snippet Scalnotempty:: no-out *) 
    Lemma Scal_not_empty: exists v, Scal [set v].
    (* end snippet Scalnotempty *)
    Proof.
      have: Rloop Er.+ by apply: notiic_rloop.
      move => [v H1]; exists v.
      have H2': Er.+ `<=` Mono by apply: subsetUr.
      split;first by rewrite /RelIndep;move => x y /inP /= -> /inP /= ->.
      split;first by move => t [y [/= H3 H4]];move: H3; rewrite H4 /= => /H1/H2' H3;exists v.
      by rewrite -notempty_exists;(exists v);rewrite inP.
    Qed.
    
    Lemma SType_not_empty: (@setT SType) != set0.
    Proof.
      rewrite -notempty_exists;move: Scal_not_empty => [v H2].
      by exists (exist _ [set v] H2);rewrite inP.
    Qed.
    
    Lemma Sinf_not_empty: Sinf != set0.
    Proof.
      move: ChnotE => [s _];rewrite -notempty_exists.
      by move: (ChooseRC5 A4 s) => [H1 | [s' [H1 _]]];[exists (sval s) | exists s'].
    Qed.
    
    Lemma Sinf_ScalP: ScalP Sinf.
    Proof.
      move: Hc => H1 y [s [ H2 H3]].
      move: (H3) => [S [H4 [H5 H6]]].
      move: (Chains_Scal H1 H4) => [H7 [H8 H9]].
      have H13: y \in Er.+.-1#(sval S)
          by rewrite inP /Fset;exists s;split;[exact | rewrite -inP].
      move: H13 => /inP/H8 [t [H13 H14]]. 
      case H15: (t \in Sinf); first by (exists t); split;[ exact | rewrite -inP].
      have H16: (s <> t) by move => H17;rewrite -inP H17 in H3;rewrite H3 in H15.
      have H17: ~ ( Er.+ (y,t)). 
      move => H18.
      have H19: Mono (s,t) by right; apply: (t_trans H2 H18).
      move: H7 => /(_ s t) H7.
      move: H14 => /inP H14.
      by move: (H7 H5 H14 H16).
      have H18: (Eb.+ (y,t)) by move: H13 => [H13 | H13]. 
      have H19: (sval S) [<= (Asym Eb.+)] Sinf by apply: ChooseRC6. 
      move: H14 => /inP/H19 [tinf [/= H20 [H21 | [H21 H22]]]].
      + by rewrite -H21 in H20;rewrite H20 in H15. 
      + by exists tinf;split;[ left;apply: (t_trans H18 H21) | rewrite -inP].
    Qed.
    
    Lemma Sinf_Scal: Sinf \in Scal. 
    Proof.
      rewrite inP;split;[apply: Sinf_indep|split;[apply: Sinf_ScalP|apply: Sinf_not_empty]].
    Qed.
    
    Lemma Sinf_final: exists Si, forall (S: SType), C S -> S [<=] Si.
    Proof.
      move: Sinf_Scal => /inP H2;exists (exist _ Sinf H2);move => S /inP H3. 
      by apply: ChooseRC6.
    Qed.

  End Sinf_set.

  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  Hypothesis A3: ~ (iic (Asym Er.+)).
  Hypothesis A4: ~ (iic (Asym Eb.+)).
  
  
  (** * we are now able to use Zorn Lemma *)
  (** Zorn lemma  in mathcomp-analysis.1.3.1 
   * has changed and requires R to be (R : rel T) as oposed to (R: T -> T -> Prop) in 
   * previous version. Thus we have to convert (curry leSet1) to rel T and adapt the proof.
   **)
    
  Lemma SmaxZ_new: exists Sm, forall S, (fun x y => `[< (curry leSet1) x y >]) Sm S -> S = Sm.
  Proof.
    apply: Zorn.
    move => t; rewrite asboolE; by apply leSet1_reflexive.
    move => r s t; rewrite 3!asboolE; by apply leSet1_transitive.
    move => s t;rewrite 2!asboolE; by apply leSet1_antisymmetric.
    move => A. 
    rewrite /total_on => H2.
    have H3: total_on A (curry leSet1). 
    move => s t H5 H6. 
    have H7:`[< curry leSet1 s t >] \/ `[< curry leSet1 t s >] by apply H2. 
    by rewrite 2!asboolE in H7.     
    case H1: (A != set0).
    pose proof Sinf_final.
    move: H3 => /Chains_is_total H3. apply Sinf_final in H3.
    move: H3 => [Si H3].
    exists Si. move => S /H3 H4. by rewrite asboolE.
    by [].
    by [].
    move: H1 => /negP/contrapT/eqP H1. 
    move: (SType_not_empty A1 A3) => /notempty_exists [Sm Ht].
    by exists Sm; move => S; rewrite H1 -inP in_set0. 
  Qed.
  
  Lemma SmaxZ: exists Sm, forall S, (curry leSet1) Sm S -> S = Sm.
  Proof.
    move: SmaxZ_new => [Sm H1];exists Sm. move => S.
    move: H1 => /(_ S) H1; by rewrite asboolE in H1.
  Qed.
  
  (** * back to set T *)
  Lemma Exists_Smax: exists Sm, Sm \in Scal /\ forall T, T \in Scal -> Sm [<= (Asym Eb.+)] T -> T = Sm.
  Proof.
    move: SmaxZ => [Sm H1];exists (sval Sm); split; first by  apply: S2Scal.
    by move => S /Scal2S [S' <-] H3; f_equal;by apply H1.
  Qed.
  
  Section Maximal. 
    (** * We show that A maximal set is a solution *)
    
    Variable (Sm: set T).
  
    Definition IsMaximal (S: set T):= 
      S \in Scal /\ forall T, T \in Scal -> S [<= (Asym Eb.+)] T -> S = T.
  
    Definition Sx:= [set y | ~ (y \in Sm) /\ ~ (y \in Mono#Sm)].

    Definition Tm x:= [set y | y \in Sm /\ ~ (Eb.+ (y,x))].

    Lemma TmI: forall x, Tm x `<=` Sm.
    Proof. by move => x y [/inP H2 _]. Qed.

    Lemma fact1: forall x y, y \in Sm -> ~(y \in (Tm x)) -> Eb.+ (y,x).
    Proof. by move => x y H3;rewrite inP not_andE => [[? // | /contrapT ? //]]. Qed.
    
    Lemma Sb1': forall x z, z \in Sm `\` (Tm x) -> Eb.+ (z,x).
    Proof. by move => x z /inP [/inP H3 /inP H4]; apply: (fact1 H3 H4). Qed.
    
    Definition Sxm x := forall y, y \in Sx -> Er.+(x,y) -> Er.+(y,x).
    
    (* A consequence of A3 *)
    Lemma Sx_1: (exists (x:T), (x \in Sx)) -> (exists (x:T), x \in Sx /\ Sxm x).
    Proof.
      by move => H1; move: (test68' A3 H1) => H2.
    Qed.
    
    Lemma fact: IsMaximal Sm -> (forall t, t\in Sm:#(Er.+) -> t \in Mono#Sm).
    Proof. by move => Smax t H3;move: Smax H3 => [/inP [_ [H8 _]] _] /inP/H8 H3;rewrite inP. Qed.
    
    Lemma fact2: IsMaximal Sm -> (forall x, RelIndep Mono (Tm x)).
    Proof.
      move => Smax x x1 x2 /inP [H3 _] /inP [H4 _] H5 H6;move: Smax => [/inP [H7 _] _].
      by move: ((H7 x1 x2) H3 H4 H5 H6).
    Qed.
    
    Lemma fact3: forall x, (x \in Sx) -> ~(x \in Mono#(Tm x)).
    Proof.
      move => x /inP [H2 H2'] H3;move: TmI => /(_ x)/Fset_inc1 => /(_ Mono) H4.
      by have: x \in Mono#Sm by move: H3;rewrite inP => /H4 -/inP H3.
    Qed.

    Lemma fact4: IsMaximal Sm -> (forall x, (x \in Sx) -> ~(x \in (Tm x):#Mono)).
    Proof.
      move => Smax x /inP [_ H2'] /inP [x1 [H5 [H3 H3']]]. 
      move: (H5) => [H5' // | /= H5'] .
      move: Smax => [/inP [_ [H6 _]] _].
      have H7: x \in Sm:#(Er.+) by rewrite inP;exists x1;rewrite inP in H3.
      by move: H7 => /inP/H6 -/inP H7.
    Qed.

    Lemma fact5: IsMaximal Sm -> (forall x, x \in Sx -> RelIndep Mono ((Tm x) `|` [set x])).
    Proof.
      by move => Smax x H2;apply:  RelIndep_U;[apply: fact2|apply: fact3|apply: fact4].
    Qed.
    
    Lemma fact6: forall x, x \in Sx -> Sm [<= (Asym Eb.+)] ((Tm x) `|` [set x]).
      move => x H2 x1 /= H3.
      case H4: (x1 \in Tm x).
      by (exists x1);split;[rewrite inP;left;rewrite -inP| left].
      exists x;split; first by rewrite inP;right. 
      right. 
      move: H2 H4 => /inP [_ H2'] /negP H4.
      
      move: (fact1 H3 H4) => H5.
      split => [// | H6].
      by have: x \in Mono#Sm by rewrite inP;(exists x1);split;[left|rewrite -inP].
    Qed.
    
    Lemma fact7: forall x, x \in Sx -> Sm = ((Tm x) `|` [set x]) -> False.
    Proof.
      by move => x /inP [H2 _] H3;have: x \in Sm by rewrite H3 inP; right.
    Qed.
    
    Lemma fact8: IsMaximal Sm -> (forall x, x \in Sx -> ~ (((Tm x) `|` [set x]) \in Scal)).
    Proof.
      move => Smax x H2 H3; move: (fact6 H2) Smax => H4 [H5 H6].
      have: Sm = ((Tm x) `|` [set x]) by apply: H6.
      by apply: (fact7 H2).
    Qed.
    
    Lemma fact9:  IsMaximal Sm -> 
                  (forall x, (x \in Sx) -> 
                      exists y, y \in (((Tm x) `|` [set x]):#(Er.+))
                               /\ ~ (y \in Mono#((Tm x) `|` [set x]))).
    Proof.
      move => Smax x H2.
      move: (fact8 Smax H2) => /inP /not_andP [H3 | /not_andP [H3 | H3]].  
      by move: (fact5 Smax H2).
      by move: H3 => /existsNP [y /not_implyP [/inP H3 /inP H4]];exists y.
      
      have H4: exists y, y \in (Tm x `|` [set x]) by (exists x);rewrite inP; right.
      have H5: Tm x `|` [set x] = set0 by rewrite -empty_iff;move => H6.
      move: H4;rewrite H5 => [[z H4]].
      by rewrite in_set0 in H4.
    Qed.
    
    Lemma FsetlU: forall x X Y (R: relation T), x \in R#X -> x \in R#(X `|` Y).
    Proof.
      move => x X Y R /inP H2.
      have H3: R#X `<=`  R#(X `|` Y) by apply: Fset_inc1; apply: subsetUl.
      by move: H2 => /H3/inP H2. 
    Qed.
    
    Lemma FsetUO: forall x X Y (R: relation T), 
        x \in R#(X `|` Y) -> x \in R#X \/ x \in R#Y.
    Proof.
      by move => x X Y R;rewrite Fset_union => /inP [ /inP H1 | /inP H1];[left | right].
    Qed.
    
    Lemma FsetDI: forall x X Y (R: relation T), 
        x \in R#(X `\` Y) -> x \in R#X.
    Proof.
      move => x X Y R /inP H2.
      have H3: R#(X `\` Y) `<=` R#(X) by apply: Fset_inc1;rewrite setDE; apply: subIsetl.
      by move: H2 => /H3 H2;rewrite inP.
    Qed.
    
    (** strangely it is not necessary to separate the two cases 
        Sm = (Tm x) or Sm <> (Tm x) *)

    Lemma fact11:  IsMaximal Sm -> (forall x, x \in Sx -> Sxm x -> Sm = (Tm x) -> False).
    Proof.
      move => Smax x H2 H2' H3.
      have H6: ~ (x \in Sm:#Mono) by move: (fact4 Smax H2); rewrite -H3.
      have H7: ~ (x \in Mono#Sm) by move: (fact3 H2); rewrite -H3.
      have [y [H8 H9]]:
        (exists y, y \in (Sm `|` [set x]):#(Er.+) /\ ~ (y \in Mono#(Sm `|` [set x])))
        by rewrite H3; apply: fact9.
      have H10: ~ (y \in Sm:#Er.+)
        by move => H11;(have H12: y \in Mono#Sm by apply: fact);
                  (have H13: y \in Mono#(Sm `|` [set x]) by apply: FsetlU).
      have H11: y \in [set x]:#Er.+.
      move: H8 => /FsetUO [H8 | H8]; last by [].
      have: y \in Mono#(Sm). 
      by rewrite -Fset_union_rel inP;right;rewrite -inP.
      have: y \in Mono#(Sm`|` [set x]) by apply: FsetlU.
      by [].
      (* end of H11 *)
      have H12: Er.+ (x,y) by move: H11; rewrite inP /Aset/Fset => [[z [H11 <-]]].
      
      have H13: ~ (y \in Sm) 
        by (move => H14;
                   (have: x \in Mono#Sm by rewrite inP;
                    exists y;split;[right| rewrite -inP])).
      have H14: y \in Sx by rewrite inP;split;[| move => /(FsetlU [set x]) H15].
      have H15: Er.+ (y,x) by apply: H2'. 
      
      have H16: y \in Mono#([set x]) 
          by rewrite -Fset_union_rel inP; right; rewrite -Fset_t0.
      have H17: y \in Mono#(Sm `|` [set x]) by rewrite setUC FsetlU.
      by [].
    Qed.

    Lemma fact12_1: forall x, (x \in Sx) -> (Tm x) `|` (Sm `\` (Tm x)) = Sm.
    Proof.
      move => x H2.
      have H3: (Sm `&` (Tm x)) = (Tm x) by rewrite setIC setIidPl;apply: TmI.
      have H4: ((Sm `&` (Tm x)) `|` (Sm `\` (Tm x)) = Sm) by rewrite setUIDK.
      by rewrite H3 in H4.
    Qed.
    
    Lemma fact12: IsMaximal Sm -> 
                  (forall x, x \in Sx -> Sxm x -> (exists z, z \in Sm /\ ~(z\in (Tm x))) -> False).
    Proof.
      move => Smax x H2 H3 [z [H4 H5]].
      move: (fact9 Smax H2) => [y [/FsetUO [H6|H6] H7]].
      - (* y \in Er.+.-1#(Tm x) *)
        have H8: y \in Er.+.-1#Sm
            by move: TmI => /(_ x)/Fset_inc1 => /(_ Er.+.-1) H9;
                                              move: H6; rewrite inP => /H9 H6;rewrite inP.
        have H9: y \in Mono#Sm by apply: fact.
        move: (fact12_1 H2) => H12.
        move: H9;rewrite -H12 => /FsetUO [H9 | H9].
        by have H13:  y \in Mono#(Tm x `|` [set x]) by apply: FsetlU.
        move: H9;rewrite -Fset_union_rel inP => [[H9 | H9]].
        + move: H9 => [t [H13 /inP H14]].
          move: H14 => /Sb1' H14.
          have H15: Eb.+ (y,x) by apply: (t_trans H13 H14).
          have H16: y \in Mono#_(x)
              by rewrite -Fset_union_rel inP;left;rewrite -Fset_t0.
          have H17: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC; apply: FsetlU.
          by [].
        + (* T -R-> y -R-> S \ (Tm x) contredit indep  *)
          move: H6 => /inP [z1 [H13 H14]].
          move: H9 => [z2 [H15 H16]].
          have H17: Er.+ (z1, z2) by apply: t_trans H13 H15.
          have H17': Mono (z1,z2) by right.
          
          (* montrer que z1 et z2 sont differents et dans Sm *)
          have H19: z1 <> z2.
          move => H20.
          have H21: ~(z2 \in (Tm x)) by apply subDsetr in H16; move => /inP H21.
          by move: H14; rewrite H20 => /inP H14.

          move: H14 => /TmI H14.
          apply subDsetl in H16.
          move: Smax => [/inP [ISm _] _].
          move: ISm => /(_ z1 z2) ISm.
          move: H16 H14 => /inP H16 /inP H14.
          have H22: ~( Mono(z1,z2)) by apply: (ISm H14 H16 H19).
          by [].
      - (* x -R-> y est contradictoire *)
        move: H6; rewrite inP -Fset_t0 /inverse /= => H6.
        have H8: ~(y \in Mono#Sm).
        rewrite -Fset_union_rel => /inP [H9 | H9].
        + (* de H9 on a aussi Eb.+#(Sm\ T) y car ~ (y -M-> T) 
         on en deduit que y -B-> x quicontredit 5 *)
          move: (fact12_1 H2) H9 => <- /inP/FsetUO [H9 | H9].
          by have H11: y \in Mono#(Tm x `|` [set x])
              by apply: FsetlU;rewrite -Fset_union_rel inP;left;rewrite -inP.
          move: H9; rewrite inP => [[z1 [H10 /inP H11]]].
          move: (Sb1' H11) => H12.
          have H13: Eb.+ (y,x) by apply: (t_trans H10 H12).
          have H14: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -Fset_union_rel inP;
            left;rewrite -Fset_t0.
          by [].
        + (* ici y-R-> S et x-R-> y => x -R-> S contredit def de x *)
          move: H9 => [z1 [H9 H10]].
          have H11: x \in Mono#Sm
              by rewrite inP;exists z1;split;[right;apply: (t_trans H6 H9) |].
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H8 *)
          have H13: ~ (y \in Sm).
          move => H14.
          have H15: x \in Mono#Sm. 
          rewrite inP.
          exists y;split. 
          by right. by rewrite -inP.
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H13 *)
          have H14: y \in Sx. by rewrite inP;split.        
          
          rewrite /Sxm in H3.
          have H15: Er.+ (y, x). apply: ((H3 y) H14 H6). 
          have H16: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -Fset_union_rel inP;
            right;rewrite -Fset_t0.
          by [].
    Qed.
    
    Lemma fact12': IsMaximal Sm -> (forall x, x \in Sx -> Sxm x -> False).
    Proof.
      move => Smax x H2 H3.
      move: (fact9 Smax H2) => [y [/FsetUO [H6|H6] H7]].
      - (* y \in Er.+.-1#(Tm x) *)
        have H8: y \in Er.+.-1#Sm
            by move: TmI => /(_ x)/Fset_inc1 
             => /(_ Er.+.-1) H9;
               move: H6; rewrite inP => /H9 H6;rewrite inP.
        have H9: y \in Mono#Sm by apply: fact.
        move: (fact12_1 H2) => H12.
        move: H9;rewrite -H12 => /FsetUO [H9 | H9].
        by have H13:  y \in Mono#(Tm x `|` [set x]) by apply: FsetlU.
        move: H9;rewrite -Fset_union_rel inP => [[H9 | H9]].
        + move: H9 => [t [H13 /inP H14]].
          move: H14 => /Sb1' H14.
          have H15: Eb.+ (y,x) by apply: (t_trans H13 H14).
          have H16: y \in Mono#_(x)
              by rewrite -Fset_union_rel inP;left;rewrite -Fset_t0.
          have H17: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC; apply: FsetlU.
          by [].
        + (* T -R-> y -R-> S \ (Tm x) contredit indep  *)
          move: H6 => /inP [z1 [H13 H14]].
          move: H9 => [z2 [H15 H16]].
          have H17: Er.+ (z1, z2) by apply: t_trans H13 H15.
          have H17': Mono (z1,z2) by right.
          
          (* montrer que z1 et z2 sont differents et dans Sm *)
          have H19: z1 <> z2.
          move => H20.
          have H21: ~(z2 \in (Tm x)) by apply subDsetr in H16; move => /inP H21.
          by move: H14; rewrite H20 => /inP H14.

          move: H14 => /TmI H14.
          apply subDsetl in H16.
          move: Smax => [/inP [ISm _] _].
          move: ISm => /(_ z1 z2) ISm.
          move: H16 H14 => /inP H16 /inP H14.
          have H22: ~( Mono(z1,z2)) by apply: (ISm H14 H16 H19).
          by [].
      - (* x -R-> y est contradictoire *)
        move: H6; rewrite inP -Fset_t0 /inverse /= => H6.
        have H8: ~(y \in Mono#Sm).
        rewrite -Fset_union_rel => /inP [H9 | H9].
        + (* de H9 on a aussi Eb.+#(Sm\ T) y car ~ (y -M-> T) 
         on en deduit que y -B-> x quicontredit 5 *)
          move: (fact12_1 H2) H9 => <- /inP/FsetUO [H9 | H9].
          by have H11: y \in Mono#(Tm x `|` [set x])
              by apply: FsetlU;rewrite -Fset_union_rel inP;left;rewrite -inP.
          move: H9; rewrite inP => [[z1 [H10 /inP H11]]].
          move: (Sb1' H11) => H12.
          have H13: Eb.+ (y,x) by apply: (t_trans H10 H12).
          have H14: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -Fset_union_rel inP;
            left;rewrite -Fset_t0.
          by [].
        + (* ici y-R-> S et x-R-> y => x -R-> S contredit def de x *)
          move: H9 => [z1 [H9 H10]].
          have H11: x \in Mono#Sm
              by rewrite inP;exists z1;split;[right;apply: (t_trans H6 H9) |].
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H8 *)
          have H13: ~ (y \in Sm).
          move => H14.
          have H15: x \in Mono#Sm. 
          rewrite inP.
          exists y;split. 
          by right. by rewrite -inP.
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H13 *)
          have H14: y \in Sx. by rewrite inP;split.        
          
          rewrite /Sxm in H3.
          have H15: Er.+ (y, x). apply: ((H3 y) H14 H6). 
          have H16: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -Fset_union_rel inP;
            right;rewrite -Fset_t0.
          by [].
    Qed.

    Lemma fact13: IsMaximal Sm -> ~(exists x, x \in Sx).
    Proof.
      by move => H0 /Sx_1 [v [H1 H2]];apply: (fact12' H0 H1 H2).
    Qed.

    Lemma fact14: IsMaximal Sm -> (forall x, ~ (x\in Sm) -> (x \in Mono#Sm)).
    Proof.
      move => Smax x H1. 
      move: (fact13 Smax) => /forallNP /(_ x) H2.
      have H3: ~ (x \in Sx) <-> (x \in Sm) \/ (x \in Mono#Sm) by rewrite inP not_andE 2!notP.
      by move: H2 => /H3 [H2 | H2].
    Qed.
    
  End Maximal. 
  
  Theorem Final: exists Sm, forall x, ~ (x\in Sm) -> (x \in Mono#Sm). 
    Proof.
      move: Exists_Smax => [Sm [H1 H2]]. 
      have H3: IsMaximal Sm 
        by split => [// |U H3 H4];have ->: U = Sm by apply: H2 H3 H4.
      by exists Sm; move => x; apply: fact14.
    Qed.
    
End Paper.

Section Seq1_plus. 
  (** * extensions of results from seq1 and rel using eqType *)

  Variables (T:eqType) (R: relation T).
  
  (** * utilities for uniq *)
  Lemma uniq_subseq: forall (st st': seq T) (x:T),
      uniq (x :: st) -> subseq st' st -> uniq (x:: st').
  Proof.
    move => st st' x; rewrite cons_uniq => /andP [H2 H3] H4.
    rewrite cons_uniq;move: (subseq_uniq H4 H3) => ->;rewrite andbT.
    move: H4 => /subseqP [m H4 H5].
    have /contra H6: x \in st' -> x \in st by rewrite H5;apply: mem_mask.
    by apply: H6.
  Qed.
  
  (** * properties of \in for eqType *)
  
  Lemma allset_in: forall (st: seq T) (x:T) (X:set T),
      x \in st -> st [\in] X -> x \in X.
  Proof.
    elim => [ x X // | y st Hr x X ].
    rewrite in_cons allset_cons.
    move => /orP [/eqP -> | H1] [/inP H2 H3];[exact | by apply: Hr].
  Qed.
    
  Lemma in_non0: forall (st:seq T) (x:T), x \in st -> size(st) > 0.
  Proof.
    move => st x H1.
    by case H3: (size st);[apply size0nil in H3;rewrite H3 in_nil in H1|].
  Qed.

  Lemma in_rev: forall (st: seq T) (x:T), 
      x \in st <-> x \in (rev st).
  Proof.
    move => st1 x. 
    have H1: forall st, (x \in st) -> (x \in (rev st)).
    move => st.
    elim: st x =>  [ x // | z st' H1 x ].
    rewrite in_cons rev_cons -cats1 mem_cat.
    move => /orP [ /eqP H2 | H2].
    by rewrite -H2 mem_seq1;have /eqP -> : x = x by [];rewrite orbT.
    by apply H1 in H2;rewrite H2 orbC orbT.
    (* main *)
    by split;[ apply H1 | move => /H1 H2; rewrite revK in H2].
  Qed.
  
  Lemma head_in: forall (st:seq T) (x y:T), size(st) > 0 -> head x (rcons st y) \in st.
  Proof.
    elim => [x y // | z st Hr x y _ /=].
    by rewrite in_cons eq_refl orbC orbT.
  Qed.
  
  Lemma in_rcons: forall (st:seq T) (x y:T), (x \in rcons st y) = (x \in st) || (x == y).
  Proof.
    elim => [x y /= | z st Hr x y]; first by rewrite mem_seq1.
    by rewrite rcons_cons 2!in_cons Hr /= orbA.
  Qed.
 
  Lemma Lift_in_FF: forall (st: seq T) (x y: T),
      (rcons st y) [L\in] R -> y \in R.+#_(x) -> st [\in] R.+#_(x).
  Proof.
    move => st x y H1 H2.
    pose proof Lift_in_F H1 as H3.
    have H4:  R.+#_(y) `<=` R.+#_(x) by apply Fset_t5. 
    by apply allset_subset with R.+#_(y). 
  Qed.
  
  Lemma Lift_in_AA: forall (st: seq T) (x y: T),
      (y::st) [L\in] R -> y \in (x)_:#R.+ -> st [\in] (x)_:#R.+.
  Proof.
    move => st x y H1 H2.
    pose proof Lift_in_A H1 as H3.
    have H4: (y)_:#R.+ `<=` (x)_:#R.+. 
    rewrite /Aset inverse_clos_t. apply: Fset_t5.
    by rewrite inP -inverse_clos_t -inP.
    by apply allset_subset with (y)_:#R.+.
  Qed.

  Lemma Lxx: forall (st: seq T) (y z: T),
      y \in st -> (rcons st z) [L\in] R -> R.+ (y, z).
  Proof.
    move => st' y z /[dup] /in_non0/seq_c [st [x ->]] H2.
    move => /(@Lift_in_F T) H4.
    by move: (allset_in H2 H4);rewrite inP -Fset_t0. 
  Qed.
  
  Lemma Lxx8: forall (st: seq T) (x y: T),
      y \in st -> (x::st) [L\in] R -> R.+ (x, y).
  Proof.
    move => st' y z /[dup] /in_non0/seq_c [st [x ->]] H2.
    move => /(@Lift_in_A T) H4.
    by move: (allset_in H2 H4); rewrite inP /Aset -Fset_t0. 
  Qed.
  
  Lemma Lxx3: forall (st: seq T) (x y z: T),
      (y \in st) -> (rcons (rcons st x) z) [L\in] R -> R.+ (y,x).
  Proof.
    move => st x y z;rewrite Lift_rcrc allset_rcons => [H1 [H2 _]].
    by pose proof Lxx H1 H2.
  Qed.

  Lemma Lxx10: forall (st: seq T) (x y:T),
      y \in rcons st x -> (rcons st x)  [L\in] R -> R (x,y) -> x \in [set y]:#(R.+).
  Proof.
    move => st x y.
    rewrite in_rcons => /orP [H1 | /eqP ->] H2 H3.
    by pose proof Lxx H1 H2 as H4;rewrite inP /mkset /=;(exists y).
    by rewrite inP /mkset /=;(exists x);split;[apply t_step|].
  Qed.

  Lemma Lxx9: forall (st: seq T) (t x y:T),
      (t \in x :: st) -> (x :: rcons st y) [L\in] R -> 
      t= (last y st) \/  R.+ (t, last y st).
  Proof.
    move => st t x y.
    rewrite in_cons => /orP [/eqP -> | H1].
    - case H2: (size st).
      + move: H2 => /size0nil -> /= => /andP [/inP H2 _].
        by right;apply t_step.
      + rewrite Lift_crc allset_cons.
        have H3: size st > 0 by rewrite H2.
        pose proof seq_rc H3 as [st' [u ->]].
        case H4: (size st').
        ++ move: H4 => /size0nil -> /= => [[H4 _]].
           by right;apply t_step.
        ++ move => [H5 H6].
           have H7: size st' > 0 by rewrite H4.
           have H8: head y (rcons st' u) \in st' by apply head_in. 
           pose proof Lxx3 H8 H6 as H9.
           rewrite last_rcons. 
           by right;apply t_trans with (head y (rcons st' u));[ apply t_step|].
    - pose proof in_non0 H1 as H2.
      pose proof seq_rc H2 as [st' [u ->]].
      rewrite last_rcons.
      move: H1;rewrite in_rcons => /orP [H1 | /eqP H1].
      by rewrite Lift_crc allset_cons => [[H3 H4]];pose proof Lxx3 H1 H4;right.
      by move => H3;left.
  Qed.
  
  Lemma Lyy: forall (st st': seq T) (v0 vn vnp1 t:T),
      (t \in v0 :: st) -> (t \in rcons st' vnp1) ->
      (v0 :: rcons st vn) [L\in] R 
      ->  (vn :: rcons st' vnp1) [L\in] R
      -> R.+ (vn, last v0 st).
  Proof.
    move => st st' v0 vn vnp1 t H1 H2 H3 H4. 
    pose proof Lxx8 H2 H4 as H5. 
    case H21: (size st).
    + move: H21 => /size0nil H21.
      by move: H1; rewrite H21 mem_seq1 /= => /eqP <-.
    + have H23: size st > 0 by rewrite H21.
      pose proof seq_rc H23 as [st1 [zz H24]].
      pose proof Lxx9 H1 H3 as [H22 | H22];
        rewrite H24 /= last_rcons in H22 *.
      by rewrite last_rcons -H22. 
      by rewrite last_rcons;apply t_trans with t.
  Qed.
  
End Seq1_plus. 

Section allL_uniq.
  (** * The aim of this section is to prove allL_uniq *)

  Variables (T:eqType) (R: relation T).
  
  Lemma allL_drop: forall (st:seq T) (x y z:T),
      z \in st -> allL R st x y -> allL R (drop ((index z st).+1) st) z y.
  Proof.
    elim => [x y z ? ? // | t st Hr x y z H1 H2].
    case H3: (t == z). 
    + rewrite /drop //= H3 -/drop drop0.
      move: H3 => /eqP H3.
      by move: H2;rewrite H3 allL_c => /andP [_ H2'].
    + rewrite /drop //= H3 -/drop.
      apply Hr with t.
      ++ move: H1; rewrite in_cons => /orP [/eqP H1| H1 //].
         by move: H3; rewrite H1 => /eqP H3.
      ++ by move: H2; rewrite allL_c => /andP [_ H2]. 
  Qed.
 
  Lemma allL_clos_tail: forall (st:seq T) (x y z:T),
      z \in (x::st) -> allL R st x y -> R.+ (z,y).
  Proof.
    move => st x y z. 
    rewrite in_cons => /orP [/eqP ->|H1] H2;first by rewrite TCP';exists st.
    move: (allL_drop H1 H2) => H3.
    by rewrite TCP';exists (drop (index z st).+1 st).
  Qed.
  
  Lemma allL_take: forall (st:seq T) (x y z:T),
      z \in st -> allL R st x y -> allL R (take (index z st) st) x z.
  Proof.
    elim => [x y z ? ? // | t st Hr x y z H1 H2].
    case H3: (t == z). 
    + rewrite /take //= H3 -/take allL0.
      move: H3 => /eqP H3.
      by move: H2;rewrite allL_c H3 => /andP [H2 _].
    + rewrite /take //= H3 -/take.
      rewrite allL_c.
      move: H2; rewrite allL_c => /andP [H2 H2']; rewrite H2 andTb.
      move: H1; rewrite in_cons => /orP [/eqP H4 | H4].
      by move: H3; rewrite H4 => /eqP H3.
      by move: (Hr t y z H4 H2').
  Qed.

  Lemma allL_clos_head: forall (st:seq T) (x y z:T),
      z \in (rcons st y) -> allL R st x y -> R.+ (x,z).
  Proof.
    move => st x y z. 
    rewrite in_rcons => /orP [H1 | /eqP ->] H2;last by rewrite TCP';exists st.
    move: (allL_take H1 H2) => H3.
    by rewrite TCP';exists (take (index z st) st).
  Qed.
  
  Lemma last0: forall(st:seq T) t, ((last t st) \in st ) = false -> st = [::].
  Proof.
    elim => [t // | t' st Hr t1 /=].
    rewrite in_cons => /orP H1. 
    move: H1. rewrite not_orE => -[H1 H2].
    have H3: st = [::]. apply: (Hr t'). case H3: (last t' st \in st).
    by rewrite H3 in H2. by [].
    by move: H1; rewrite H3 /=.
  Qed.

  Lemma allL_asym: forall st x s y,
      s \in st -> (x :: rcons st y) [L\in] R -> ~ R.+ (y, last x st) 
           -> (Asym R.+) (s, y).
  Proof.
    elim => [x y z ? ? // | t st Hr x y z ].
    rewrite in_cons  allL_c => /orP [/eqP -> | H1] /andP [H2 H3] /= H4.
    + case H5: ((last t st) \in st).
      ++ move: (Hr t (last t st) z H5 H3 H4) => [H6 H7].
         have H8: R.+ (t,z) by rewrite TCP';(exists st).
         have H9: R.+ (t, (last t st))
           by move: (allL_take H5 H3);rewrite TCP';
           exists (take (index (last t st) st) st).
         split. by [].
         move => H10.
         have H11: R.+ (z,  last t st) by apply: (t_trans H10 H9). 
         exact.
      ++ move: H4 (last0 H5) => + H6. rewrite H6 /=.
         have: R.+ (t,z) by rewrite TCP';(exists st).
         exact.
    + by apply: (Hr t y z).
  Qed.

  Lemma allL_asym': forall st x y,
      (x :: rcons st y) [L\in] R -> ~ R.+ (y, last x st) 
      -> (Asym R.+) (x, y).
  Proof.
    move => st x y H1 H2.
    case H3: ((last x st) \in st).
    + move: (allL_asym H3 H1 H2) => H4.
      split. by rewrite TCP';(exists st).
      move => H5.
  Admitted.
  
  
  Lemma drop_cons': forall (st: seq T) (x:T),
      x \in st -> x::(drop (index x st).+1 st) = (drop (index x st) st).
  Proof.
    elim => [// | y st Hr x H1].
    case H2: (y == x);
      first by move: H2 => /eqP ->; rewrite /= eq_refl drop0.
    rewrite /drop /= H2 -/drop.
    move: H1 H2; rewrite in_cons => /orP [/eqP -> H2 | H1 _].
    by rewrite eq_refl in H2. 
    by pose proof (Hr x) H1. 
  Qed.
  
  Lemma drop_notin: forall (st: seq T) (x:T),
      x \in st -> uniq st -> x \notin (drop (index x st).+1 st).
  Proof.
    elim => [// | y st Hr x H1].
    case H2: (y == x);
      first by move: H2 => /eqP ->;rewrite /= eq_refl drop0 => /andP [H3 _].
    rewrite /drop /= H2 -/drop.
    move: H1 H2; rewrite in_cons => /orP [/eqP -> H2 | H1 _].
    by rewrite eq_refl in H2. 
    move => /andP [H2 H3]; by pose proof (Hr x) H1 H3. 
  Qed.
  
  Lemma allL_uniq_tail: forall (U: relation T) (st: seq T) (x y: T),
      allL U st x y -> exists st', subseq st' st /\  ~( y \in st') /\ allL U st' x y.
  Proof.
    move => U.
    elim => [// x y H1 | a st H1 x y]; first by (exists [::]).
    case H2: (y == a).
    + move: (H2) => /eqP H2'.
      rewrite allL_c -H2' => /andP [H3 _].
      by (exists [::]); rewrite allL0.
    + rewrite allL_c => /andP [H3 /H1 [st' [ H4 [H5 H6]]]].
      exists [::a & st'].
      split. 
      by rewrite -cat1s -[a::st]cat1s; rewrite subseq_cat2l.
      rewrite in_cons H2 /=.
      split. 
      by [].
      by rewrite allL_c H3 H6.
  Qed.
  
  Lemma allL_uniq_head: forall (st: seq T) (x y: T),
      allL R st x y -> exists st', subseq st' st /\ ~( x \in st') /\ allL R st' x y.
  Proof.
    move => st x y; rewrite allL_rev => H1.
    pose proof allL_uniq_tail H1 as [st' H2].
    move: H2; rewrite  allL_rev inverse_inverse => [[H2 [H3 H4]]].
    exists (rev st');split. 
    have H5: st = (rev (rev st)) by rewrite revK.
    by rewrite H5 subseq_rev.
    by rewrite in_rev revK. 
  Qed.

  Lemma allL_uniq_internals: forall (st: seq T) (x y: T),
      allL R st x y -> exists st', subseq st' st /\  @uniq T st' /\ allL R st' x y.
  Proof.
    elim => [// x y H1 | a st H1 x y]; first by (exists [::]).
    rewrite allL_c => /andP [H3 /H1 [st' [H4 [H5 H6]]]].
    case H2: (a \in st'); last first.
    + exists [::a&st'].
      split. 
      by rewrite -cat1s -[a::st]cat1s; rewrite subseq_cat2l.
      split.
      by rewrite /uniq -/uniq H2 H5.
      by rewrite allL_c H3 H6.
    + exists (drop (index a st') st').
      split.
      have H7: subseq (drop (index a st') st') st' by apply drop_subseq.
      have H8: subseq st' (a::st') by apply subseq_cons.
      have H9: subseq (drop (index a st') st') (a :: st')
        by apply subseq_trans with st'.
      have H10: subseq (a:: st') (a::st)
        by rewrite -cat1s -[a::st]cat1s; rewrite subseq_cat2l.      
      by apply  subseq_trans with [::a &st'].
      split.
      by apply drop_uniq.
      pose proof allL_drop H2 H6 as H7.
      have H8: a::(drop (index a st').+1 st') = (drop (index a st') st').
      apply drop_cons'.
      by [].
      by rewrite -H8 allL_c H3 H7.
  Qed.

  Lemma in_subseq_1: forall (st1 st2: seq T) (x:T),
      subseq [::x & st1] st2 -> x \in st2.
  Proof.
    elim => [st2 x | y st1 Hr st2 x H1]; first by rewrite sub1seq. 
    elim: st2 H1 Hr => [// H1 _ |  z st2 Hr' H1 H2].
    case H3: (x == z).
    - move: (H3) => /eqP <-.
      by rewrite in_cons //= eq_refl orbC orbT.
    - rewrite /subseq H3 -/subseq in H1.
      apply Hr' in H1.
      by rewrite in_cons H1 orbT.
      by [].
  Qed.
  
  Lemma in_subseq': forall (st2 st1: seq T) (x:T),
      subseq st1 st2 -> (x \in st1) -> (x \in st2).
  Proof.
    elim => [st1 x | y st1 Hr st2 x H1 H2].  
    by rewrite subseq0 => /eqP -> H2.
    elim: st2 H1 H2 Hr => [// |  z st2 Hr' H1 H2 H3].
    case H4: (z == y).
    - move: H1; rewrite /subseq H4 -/subseq => H1.
      move: (H4) => /eqP <-.
      rewrite in_cons. 
      move: H2; rewrite in_cons => /orP [H2 | H2].
      by rewrite H2 orbC orbT.
      by (have ->:  x \in st1 by apply H3 with st2); rewrite orbT.
    - move: H1; rewrite /subseq H4 -/subseq => H1.
      move: H2; rewrite in_cons => /orP [/eqP H2 | H2].
      apply in_subseq_1 in H1.
      by rewrite in_cons H2 H1 orbT.
      apply cons_subseq in H1. 
      have H5: x \in st1. by apply: (H3 st2 x).
      by rewrite in_cons H5 orbT. 
  Qed.

  Lemma in_subseq: forall (st1 st2: seq T) (x:T),
      subseq st1 st2 -> ~ (x \in st2) -> ~ (x \in st1).
  Proof.
    move => st1 st2 x ?; apply contraPP => /contrapT ? ?.
    by have:  x \in st2 by apply in_subseq' with st1.  
  Qed.
  
  Lemma allL_uniq: forall (st: seq T) (x y: T),
      allL R st x y -> exists st', subseq st' st /\ ~( x \in st') /\  ~(y \in st') /\
                               @uniq T st' /\ allL R st' x y. 
  Proof.
    move => st x y H1.
    pose proof allL_uniq_tail H1 as [st2 [S2 [I2 H2]]].
    pose proof allL_uniq_head H2 as [st3 [S3 [I3 H3]]].
    have J3: ~ (y \in st3) by  apply in_subseq with st2.
    pose proof allL_uniq_internals H3 as [st4 [S4 [K4 H4]]].
    have J4: ~ (y \in st4) by apply in_subseq with st3.
    have I4: ~ (x \in st4) by apply in_subseq with st3.
    exists st4. 
    split.
    have HH1: subseq st4 st2 by apply subseq_trans with st3.
    have HH2: subseq st4 st by apply subseq_trans with st2.
    by [].
    by [].
  Qed.

  Lemma TCP_uniq: forall (x y:T), 
      R.+ (x,y)
      <-> exists st, ~( x \in st) /\ ~(y \in st) /\ @uniq T st /\ allL R st x y. 
  Proof.
    move => x y;split. 
    - rewrite TCP' /mkset => [[st H1]].
      apply allL_uniq in H1.
      by move: H1 => [st' [H1 [H2 [H3 [H4 /= H5]]]]];(exists st').
    - by move => [st [_ [_ [_ H1]]]];rewrite TCP' /mkset; exists st.
  Qed.

  Lemma TCP_uniq'': forall (x y:T), 
      R.+ (x,y) ->  ~ (x = y) 
      ->  exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y H1 H7. 
    move: (H1) => /TCP_uniq [st [H3 [H4 [H5 H6]]]].
    have H8: uniq (rcons st y)
      by move: H4 => /negP H4;rewrite rcons_uniq H4 H5. 
    have H9: x \in (rcons st y) -> False
        by rewrite -[rcons st y]cats0 cat_rcons mem_cat mem_seq1
         => /orP [ H9 | /eqP H9].
    have H10: uniq (x :: rcons st y) by rewrite /uniq -/uniq;
      move: H9 => /negP H9;rewrite H8 andbT.
    
    by exists st.
  Qed.

  Lemma TCP_uniq': forall (x y:T), 
      R.+ (x,y) 
      -> ~ ( R.+ (y,x))
      -> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y H1 H2. 
    move: (H1) => /TCP_uniq [st [H3 [H4 [H5 H6]]]].
    have H7: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    by move: (TCP_uniq'' H1 H7).
  Qed.

End allL_uniq.

Section Hn1.
  (** * some Lemmata around Axiom of choice *) 
  
  Variables (T T':choiceType) (R: relation T) (R': set ((T*T)*T')).
  
  Hypothesis Au0: (exists (v0:T'), (v0 \in [set: T'])).
  Hypothesis Au1: forall (xy: T*T), R xy -> exists z, R' (xy,z).
  
  Lemma Au1_P1: forall (xy: T*T),
    exists z, z \in [set u| (R xy /\ R' (xy,u)) \/ ~ R xy].
  Proof. 
    move => xy. 
    case H1: (xy \in R).
    + move: H1 => /inP H1;move: xy H1 => [x y] /[dup] H1 /Au1 [z H1'].
      by exists z;rewrite inP;left;split.
    + move: Au0 => [v0 Au0'].
      by exists v0; rewrite inP; right;move => /inP H2;rewrite H1 in H2.
  Qed.
  
  Definition g1 (xy : T*T) := xchoose (Au1_P1 xy).
  
  Lemma Au1_P3 (xy: T*T): R xy -> R' (xy,g1(xy)).
  Proof.
    have H0: g1(xy) \in [set u| (R xy /\ R' (xy,u)) \/ ~ R xy]
      by apply: xchooseP.
    by move: H0 => /inP [[_ ?] //| ? //].
  Qed.
  
  Lemma Au1_G: exists (g: T*T -> T'), forall xy, R xy -> R' (xy,g(xy)).
  Proof. by exists g1; apply: Au1_P3. Qed.
  
End Hn1.

Section Hn2. 
  (** * Using Hn1 combined to TCP_uniq' *) 
  Variables (T:choiceType) (R: relation T). 

  Definition R' :=[set xyz: (T*T)*(seq T)| 
                    uniq (xyz.1.1 ::(rcons xyz.2 xyz.1.2))
                    /\ (xyz.1.1 ::(rcons xyz.2 xyz.1.2)) [L\in] R].

  Lemma Au0: (exists (v0: seq T), (v0 \in [set: seq T])).
  Proof. by exists [::];rewrite inP. Qed.
  
  Lemma Au1: forall (xy:T*T), (Asym R.+) xy -> exists z, R' (xy,z).
  Proof. 
    by move => [x y] [H1 H2];move: (TCP_uniq' H1 H2) => [st H3];exists st. Qed.
  
  Lemma choose_Rseq: exists (g: T*T -> seq T), forall xy, (Asym R.+) xy -> R' (xy,g(xy)).
  Proof. by move: (Au1_G Au0 Au1) => [g H1]; exists g. Qed.

End Hn2.

Section Hn3. 
  (** * Using Hn1 *) 
  Variables (T:choiceType) (R: relation T) (Rseq: relation (seq T)) 
    (g: T*T -> seq T).           

  Definition Re1 :=
    [set xyzt:(T*T)*(T*T) |
      (xyzt.1.2 = xyzt.2.1) /\
      (Asym R.+) (xyzt.1) /\ (Asym R.+) (xyzt.2)].

  Definition Mix (xyztu: ((T*T)*(T*T))*T)
    := ((xyztu.1.1.1,xyztu.2),(xyztu.2, xyztu.1.2.2)).
  
  Definition Re2 (g: T*T -> seq T) := 
    [set xyztu:((T*T)*(T*T))*T | 
      Re1 (Mix xyztu) /\ (Rseq (g (Mix xyztu).1, g (Mix xyztu).2))].
 
  Hypothesis ARR':  (exists (v0:T), (v0 \in [set: T])).

  Lemma Au2: forall (xyzt: (T*T)*(T*T)),
      Re1 xyzt -> exists z: T, Re2 g (xyzt,z).
  Admitted.
  
  Lemma Todo1: exists (g1: (T*T)*(T*T) -> T), 
      forall xyzt, Re1 xyzt -> Re2 g (xyzt,g1(xyzt)).
  Proof. by move: (Au1_G ARR' Au2) => [g1 H1]; exists g1. Qed.

End Hn3.

Section Hn4.
  (** * some Lemmata around infinite outward R-path *) 
  
  Variables (T:choiceType) (R: relation T).
    
  (* utility lemma *)
  Lemma RedBackL: forall (st:seq T) (x y:T),
      (x::(rcons st y)) [L\in] R
      -> uniq (x::(rcons st y)) 
      -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          subseq (rcons st' y') (rcons st y) 
          /\ uniq (x::(rcons st' y'))       
          /\ st' [\in] R.+#_(x) 
          /\ (x::(rcons st' y')) [L\in] R 
          /\ ~ (R.+ (y',x))
          /\ (y = y' \/ R.+ (y',y))
          /\ ~ (R.+ (y',(last x st'))).
  Proof.
    have H0: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim.
    elim/last_ind => [x y H1 H2| st z Hr x y H1 H1' H2];
                    first by (exists [::], y);have H3: y = y \/ R.+ (y, y) by left.
    case H3: ((z,x) \in R.+).
    - exists (rcons st z); exists y.
      have H4: (rcons st z) [\in] R.+#_(x).
      move: H1; rewrite Lift_crc Lift_rcrc allset_cons allset_rcons => [[_ [H1 _]]].
      rewrite allset_rcons.
      split. 
      apply Lift_in_FF with z. by [].
      by rewrite inP -Fset_t0 -inP H3.
      by rewrite -Fset_t0 -inP H3.
      (* end of H4 *)
      have H5: y = y \/ R.+ (y, y) by left.
      move: H3 => /inP H3.
      have H6: ~ R.+ (y, last x (rcons st z))
        by rewrite last_rcons; move => H7;have H8: R.+ (y,x) by apply: t_trans H7 H3.
      by [].
    - rewrite Lift_crc Lift_rcrc allset_cons allset_rcons in H1.
      move: (H1); rewrite H0 => [[H10 [H10' H10'']]].
      have H5: (x :: rcons st z) [L\in] R by rewrite Lift_crc allset_cons.
      apply Hr in H5; last by move => /inP H6; rewrite H6 in H3.
      move: H5 => [st' [y' [H5 [H5' [H6 [H7 [H8 [H9 H9']]]]]]]].
      have H11: subseq (rcons st' y') (rcons (rcons st z) y)
        by apply subseq_trans with (rcons st z);[ | apply subseq_rcons].
      (exists st', y'); move: H9 => [H9 | H9].
      by have H12: (y = y' \/ R.+ (y', y)) by right;rewrite -H9;apply: t_step.
      by have H12: (y = y' \/ R.+ (y', y)) by right;apply t_trans with z;[ |apply: t_step].
      have H13: subseq (rcons st z) (rcons (rcons st z) y) by apply: subseq_rcons. 
      have H14: uniq (x :: rcons st z) by apply: (uniq_subseq H1' H13).
      by [].
  Qed.

  (* utility lemma *)
  Lemma RedBackR: forall (st:seq T) (y z:T),
      (y::(rcons st z)) [L\in] R
      -> uniq (y::(rcons st z)) 
      -> ~ ( R.+ (z,y))
      -> exists st', exists y',
          subseq (y'::st') (y::st) 
          /\ uniq (y'::(rcons st' z))       
          /\ st' [\in] (z)_:#R.+ 
          /\ (y'::(rcons st' z)) [L\in] R 
          /\ ~ (R.+ (z,y'))
          /\ (y = y' \/ R.+ (y,y'))
          /\ ~ (R.+ ((head z st'),y')).
  Proof.
    elim => [y z H1 H2| y1 st Hr y z H1 H1' H2];
             first by (exists [::], y);have H3: y = y \/ R.+ (y, y) by left.
    case H3: ((z,y1) \in R.+).
    - exists (y1::st); exists y.
      have H4: (y1::st) [\in] (z)_:#R.+.
      move: H1. rewrite Lift_crc Lift_rcc allset_cons allset_rcons => [[_ [H1 _]]].
      rewrite allset_cons.
      split. 
      by rewrite  /Aset -Fset_t0 /inverse /= -inP H3.
      apply Lift_in_AA with y1. by [].
      by rewrite inP /Aset -Fset_t0 /inverse /= -inP H3.
      (* end of H4 *)
      have H5: y = y \/ R.+ (y, y) by left.
      move: H3 => /inP H3.
      have H6: ~ R.+ (head z (y1 :: st), y)
        by move => /= H7;have H8: R.+ (z,y) by apply: t_trans H3 H7.
      by [].
    - rewrite Lift_crc Lift_rcc allset_cons allset_rcons in H1.
      move: (H1) => [H10 [H10' H10'']].
      have H5: (y1 :: rcons st z) [L\in] R 
        by rewrite -rcons_cons Lift_rcc allset_rcons.
      apply Hr in H5; last by move => /inP H6; rewrite H6 in H3.
      move: H5 => [st' [z' [H5 [H5' [H6 [H7 [H8 [H9 H9']]]]]]]].
      have H11: subseq (z'::st') (y::(y1::st)).
      by apply subseq_trans with (y1::st);[| apply subseq_cons].
      (exists st', z'); move: H9 => [H9 | H9].
      by have H12: (y = z' \/ R.+ (y, z')) by right; rewrite -H9; apply: t_step.
      by have H12: (y = z' \/ R.+ (y, z')) by right;apply t_trans with y1;[apply: t_step|].
      by move: H1'; rewrite cons_uniq rcons_cons => /andP [_ H1'].
  Qed.
  
  Lemma RedBackLR: forall (stl str:seq T) (x y z:T),
      (x::(rcons stl y)) [L\in] R -> uniq (x::(rcons stl y)) -> ~ ( R.+ (y,x))
      -> (y::(rcons str z)) [L\in] R -> uniq (y::(rcons str z)) -> ~ ( R.+ (z,y))
      -> exists stl', exists yl, exists str', exists yr,
          (subseq (rcons stl' yl) (rcons stl y) 
          /\ uniq (x::(rcons stl' yl))       
          /\ stl' [\in] R.+#_(x) 
          /\ (x::(rcons stl' yl)) [L\in] R 
          /\ ~ (R.+ (yl,x))
          /\ (y = yl \/ R.+ (yl,y))
          /\ ~ (R.+ (yl,(last x stl'))))
          /\
            ( subseq (yr::str') (y::str) 
              /\ uniq (yr::(rcons str' z))       
              /\ str' [\in] (z)_:#R.+ 
              /\ (yr::(rcons str' z)) [L\in] R 
              /\ ~ (R.+ (z,yr))
              /\ (y = yr \/ R.+ (y,yr))
              /\ ~ (R.+ ((head z str'),yr))).
  Proof.
    move => strl str x y z H1 H2 H3 H4 H5 H6.
    pose proof (RedBackL H1 H2 H3) as [stl' [yl H7]].
    pose proof (RedBackR H4 H5 H6) as [str' [yr H8]].
    by exists stl';exists yl;exists str';exists yr.
  Qed.

  Lemma RedBackLR1: forall (stl str:seq T) (x y z:T),
      (x::(rcons stl y)) [L\in] R -> uniq (x::(rcons stl y)) -> ~ ( R.+ (y,x))
      -> (y::(rcons str z)) [L\in] R -> uniq (y::(rcons str z)) -> ~ ( R.+ (z,y))
      -> exists stl', exists yl, exists str', exists yr, exists stlr,
          uniq (x::(rcons stl' yl)) /\ (x::(rcons stl' yl)) [L\in] R 
          /\ ~ (R.+ (yl,x))
          /\ ~ (R.+ (yl,(last x stl')))
          /\ uniq (yr::(rcons str' z)) /\ (yr::(rcons str' z)) [L\in] R 
          /\ ~ (R.+ (z,yr))
          /\ ~ (R.+ ((head z str'),yr))
          /\ ((yl = yr) \/ (uniq (yl::(rcons stlr yr)) /\ (yl::(rcons stlr yr)) [L\in] R)).  
  Proof.
    move => stl str x y z H1 H2 H3 H4 H5 H6.
    pose proof (RedBackLR H1 H2 H3 H4 H5 H6) as [stl' [yl [str' [yr H7]]]].
    move: H7 => [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]].
    move: H7 => [H7' [H8' [H9' [H10' [H11' [H12' H13']]]]]].
    exists stl';exists yl;exists str';exists yr.
    have H15: (yl = yr) \/  R.+ (yl, yr).
    move: H13 H12' => [H16 | H16] [H17 | H17].
    by left;rewrite -H16 -H17.
    by right;rewrite -H16.
    by right;rewrite -H17.
    by right; apply t_trans with y. 
    (* end H15 *)
    move: H15 => [H15 | H15].
    + exists [::].
      have H16: yl = yr \/ uniq (yl :: rcons [::] yr) /\ (yl :: rcons [::] yr) [L\in] R 
        by left.
      by [].
    + case H16: (yl == yr).
      ++ exists [::].
         have H17: (yl = yr \/ uniq (yl :: rcons [::] yr) /\ (yl :: rcons [::] yr) [L\in] R)
           by left; move: H16 => /eqP H16.
         by [].
      ++ move: H16 => /eqP H16.
         move: (TCP_uniq'' H15 H16) => [strl H17].
         exists strl.
         have H18: (yl = yr \/ uniq (yl :: rcons strl yr) /\ (yl :: rcons strl yr) [L\in] R) by right.
         by [].
  Qed.

  Lemma uniq_util1: forall x stl1 yl stlr yr str1 z,
    uniq (x :: rcons stl1 yl) -> ~ R.+ (yl, last x stl1)
    ->  uniq (yl :: rcons stlr yr) 
    ->  uniq (yr :: rcons str1 z) ->  ~ R.+ (head z str1, yr)
    ->  uniq (x :: (stl1 ++ (yl :: rcons (stlr ++ yr :: str1) z))).
  Admitted.

  Lemma uniq_util2: forall x stl1 yl stlr yr str1 z,
      uniq (x :: rcons stl1 yl) -> ~ R.+ (yl, last x stl1)
    ->  uniq (yl :: rcons stlr yr) 
    ->  uniq (yr :: rcons str1 z) ->  ~ R.+ (head z str1, yr)
    ->  uniq (yl :: rcons (stlr ++ yr :: str1) z).
  (* implique par celui au dessus *)
  Admitted.

  Lemma uniq_util0: forall x stl1 y str1 z,
      uniq (x :: rcons stl1 y) -> ~ R.+ (y, last x stl1)
      -> uniq (y :: rcons str1 z) -> ~ R.+ (head z str1, y)
      -> uniq (x :: stl1 ++ y :: rcons str1 z).
  Proof.
    move => x stl1 y str1 z H1 H2 H3 H4.
  Admitted.
  
  Lemma uniq_util0': forall x stl1 y str1 z,
      (x :: rcons stl1 y) [L\in] R ->
      uniq (x :: rcons stl1 y) -> ~ R.+ (y, last x stl1)
      -> (y :: rcons str1 z) [L\in] R
      -> uniq (y :: rcons str1 z) -> ~ R.+ (head z str1, y)
      -> uniq ((x :: stl1) ++ (y :: rcons str1 z)).
  Proof.
    move => x stl1 y str1 z H1 H2 H3 H4 H5 H6.
    have H7: uniq (x :: stl1)
      by move: H2; rewrite -rcons_cons rcons_uniq => /andP [_ ?].
    rewrite cat_uniq H5 H7 andbT andTb.
    (* XXXX apply negbT. pose proof (contra_notF False).*) 
    have: has (in_mem^~ (mem (x :: stl1))) (y :: rcons str1 z) -> False.
    move => /hasP.
  Admitted.
    
  Lemma uniq_util3: forall x stl1 yl stlr yr str1 z,
      (x :: rcons stl1 yl) [L\in] R
      -> (yl :: rcons stlr yr) [L\in] R               
      -> (yr :: rcons str1 z) [L\in] R
      -> (yl :: rcons (stlr ++ yr :: str1) z) [L\in] R.
  Proof.
  Admitted.
  
  Lemma uniq_util3': forall yl stlr yr str1 z,
      (yl :: rcons stlr yr) [L\in] R               
      -> (yr :: rcons str1 z) [L\in] R
      -> (yl :: rcons ((rcons stlr yr) ++ str1) z) [L\in] R.
  Proof.
    by move => yl stlr yr str1 z H1 H2;rewrite allL_cat;apply/andP. 
  Qed.
  
  Lemma RedBackLR2: forall (stl str:seq T) (x y z:T),
      (x::(rcons stl y)) [L\in] R -> uniq (x::(rcons stl y)) -> ~ ( R.+ (y,x))
      -> (y::(rcons str z)) [L\in] R -> uniq (y::(rcons str z)) -> ~ ( R.+ (z,y))
      -> exists stl', exists str', exists y',
          uniq (x::(rcons stl' y')) /\ (x::(rcons stl' y')) [L\in] R /\ ~ (R.+ (y',x))
          /\ uniq (y'::(rcons str' z)) /\ (y'::(rcons str' z)) [L\in] R /\ ~ (R.+ (z,y'))
          /\ uniq (x :: (stl' ++ (y' :: rcons str' z))).
  Proof.
    move => stl str x y z H1 H2 H3 H4 H5 H6.
    move: (RedBackLR1 H1 H2 H3 H4 H5 H6) => [stl1 [yl [str1 [yr [stlr H7]]]]].
    move: H7=> [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 | [H15 H16]]]]]]]]]].
    + exists stl1; exists str1; exists yr.
      rewrite H15 in H10 H9 H8 H7.
      have H17: uniq (x :: (stl1 ++ (yr :: rcons str1 z)))
        by move: (uniq_util0 H7 H10 H11 H14).
      exact. 
    + exists stl1. exists (stlr ++ (yr::str1)). exists yl.
      have H17: uniq (yl :: rcons (stlr ++ yr :: str1) z)
        by move: (uniq_util2 H7 H10 H15 H11 H14).
      have H18: (yl :: rcons (stlr ++ yr :: str1) z) [L\in] R
        by move: (uniq_util3 H8 H16 H12).
      have H19: ~ R.+ (z, yl).
      move => H20; have H21: R.+ (yl,yr) by rewrite TCP' /mkset;exists stlr.
      have H22: R.+ (z,yr) by apply: (t_trans H20 H21).
      by [].
      (** H19 *)
      move: (uniq_util1 H7 H10 H15 H11 H14) => H20.
      exact.
  Qed.
  
  Lemma Asym_uniq : forall x y z, 
      Asym R.+ (x,y) -> Asym R.+ (y,z)
      ->exists stl, exists str, exists y',
          (x::(rcons stl y')) [L\in] R /\ uniq (x::(rcons stl y'))
          /\ (y'::(rcons str z)) [L\in] R /\ uniq (y'::(rcons str z))
          /\ uniq (x :: stl ++ y' :: rcons str z). 
  Proof.
    move => x y z [H1 H2] [H3 H4].
    move: (TCP_uniq' H1 H2) (TCP_uniq' H3 H4) => [stl [H5 H6]] [str [H7 H8]].
    move: (RedBackLR2 H6 H5 H2 H8 H7 H4) 
        => [stl' [str' [y' [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]]].
    exists stl'; exists str'; exists y'.
    exact. 
  Qed.

End Hn4.

Section Unused. 
  Variables (T:choiceType) (R: relation T).


  
  Definition Sym (R: relation T): relation T := (R `&` R.-1).

  Definition R0 := (Sym R).+.

  Definition R0' := [set xy | exists st, 
                      ~ xy.1 \in st /\ ~ xy.2 \in st /\ uniq st
                                       /\ (xy.1::(rcons st xy.2)) [L\in] R
                                       /\ (xy.1::(rcons st xy.2)) [L\in] R.-1 ].
  
  Lemma R0E: R0 = R0'.
  Proof. 
    rewrite predeqE => -[x y]; split.
    by move => /TCP_uniq [st [H0 [H1 [H2 /Lift_inI [H3 H4]]]]];exists st. 
    by move => -[st H0];rewrite /R0 TCP_uniq;exists st;rewrite -Lift_inI.
  Qed.
  
  Definition R0'' := [set xy | exists st,
                       ~ xy.1 \in st /\ ~ xy.2 \in st /\ uniq st
                                              /\ (xy.1::(rcons st xy.2)) [L\in] R
                                              /\ st [\in] R.+#_(xy.1) /\ R (xy.2 ,(last xy.1 st))].
  
  
  Definition R1 := [set xy | exists st, 
                     st [\in] R.+#_(xy.1) /\ uniq (xy.1::(rcons st xy.2)) 
                     /\ (xy.1::(rcons st xy.2)) [L\in] R /\ ~ (R.+ (xy.2,(last xy.1 st)))].
  
  Definition R4 := [set xyz: (T*T)*T | 
                     Asym R.+ (xyz.1.1, xyz.1.2) /\ R1 (xyz.1.1, xyz.2) 
                     /\ (xyz.1.2= xyz.2\/ R.+(xyz.2, xyz.1.2)) ].
  
  Definition R5:= [set xyz: (T*T)*T| ~ (Asym R.+ (xyz.1.1, xyz.1.2)) \/ ( R4 xyz)].

  
  Lemma RedBackLR0: forall (yl y yr:T),
    (R.+ (yl,y)) -> (R.+ (y,yr))
    -> exists stl, exists str, exists y',
        ~( yl \in stl) /\ ~(yr \in str) 
        /\ @uniq T ( stl ++ (y'::str)) 
        /\ (yl = y' \/ (allL R stl yl y'))
        /\ (yr = y' \/ (allL R str y' yr)).
   Proof.
     move => yl y yr /TCP_uniq [stl [H1 [H2 [H3 H4]]]]
              /TCP_uniq [str [H6 [H7 [H8 H9]]]].
     move: stl y yl H1 H2 H3 H4 H6 H9.
     elim. 
     + move => y yl H1 H2 H3 H4 H6 H9.
       rewrite allL0 in H4.
       case H5: (yl \in str). 
       ++ exists [::]; exists (drop ((index yl str).+1) str); exists yl.
          have H10: subseq (drop (index yl str).+1 str) str by apply: drop_subseq.
          have H11: ~ yr \in drop (index yl str).+1 str by apply: in_subseq H10 H7.
          have H12: uniq (drop (index yl str).+1 str) by apply: subseq_uniq H10 H8.
          have H13: uniq ([::] ++ yl :: drop (index yl str).+1 str)
            by rewrite cons_uniq H12 andbT;apply: drop_notin;[rewrite H5|].
          have H14: (yl = yl \/ allL R [::] yl yl) by left.
          have H15: (yr = yl \/ allL R (drop (index yl str).+1 str) yl yr) 
                      by right;apply: (allL_drop H5 H9).
          exact.
       ++ exists [::];exists str;exists y.
          have H10: uniq ([::] ++ y :: str)
            by rewrite cons_uniq H8 andbT;case H11: (y \in str);[rewrite H11 in H6|].
          have H11: (yl = y \/ allL R [::] yl y) by right; rewrite allL0. 
          have H12: yr = y \/ allL R str y yr by right. 
          exact. 
     + move => t strl Hr y yl H1 H2 H3 H4 H6 H9.
       case H5: (yl == t);
         first by move: H1; rewrite in_cons H5 orTb => H1.
       move: H1; rewrite in_cons H5 orFb => H1.
       case H10: (y == t);
         first by move: H2; rewrite in_cons H10 orTb => H2.
       move: H2; rewrite in_cons H10 orFb => H2.
       move: H3; rewrite cons_uniq => /andP [H11 H12].
       move: H4; rewrite allL_c => /andP [H13 H14].
       have H15: ~ t \in strl.
       move => H16;case H17: (t \in strl); first by rewrite H17 in H11.
       by rewrite H17 in H16.
       pose proof (Hr y t) H15 H2 H12 H14 H6 H9 as [stl [str' [y' HHH]]].
       exists stl. exists str'. exists y'.
   Admitted.
   
   Lemma RedBackLRR1: forall (yl y yr:T),
    (y = yl \/ R.+ (yl,y)) /\ (y = yr \/ R.+ (y,yr))
    -> exists stl, exists str, exists y',
        ~( yl \in stl) /\ ~(yr \in str) 
        /\ @uniq T ( stl ++ (y'::str)) 
        /\ (yl = y' \/ allL R stl yl y') 
        /\ (yr = y' \/ allL R str y' yr).
  Proof.
    move => yl y yr [[ H1 | /[dup] H0 /TCP_uniq [stl [H1 [H2 [H3 H4]]]]]  
                      [H5 | /[dup] H0' /TCP_uniq [str [H6 [H7 [H8 H9]]]]]].
    + exists [::]; exists [::]; exists y. rewrite -H1 -H5. 
      by have H6: (y = y \/ allL R [::] y y) by left.
    + exists [::];exists str;exists y.
      rewrite -H1.
      have H10: (y = y \/ allL R [::] y y) by left.
      have H11: (yr = y \/ allL R str y yr) by right.
      have H12:  uniq ([::] ++ y :: str)
        by rewrite /=; rewrite H8 andbT; case H13: (y \in str).
      exact. 
    + exists stl; exists [::];exists y.
      rewrite -H5.
      have H10: (yl = y \/ allL R stl yl y) by right. 
      have H11: (y = y \/ allL R [::] y y) by left.
      have H12: uniq (stl ++ [:: y])
        by rewrite cats1 rcons_uniq H3 andbT;case H13: (y \in stl).
      exact. 
    + pose proof RedBackLR0 H0 H0' as [stl' [str' [y' HH]]].
      move: HH => [H10[H11 [H12 [H13 H14]]]].
      exists stl';exists str';exists y'. 
      by [].
  Qed.
  
  (** * what follows is unused *)
  
  Lemma RedBackF: forall (x y:T), Asym R.+ (x,y) -> exists z, R4 ((x,y),z).
  Proof.
    move => x y [H1 /= H2].
    pose proof TCP_uniq' H1 H2 as [st [H3 H4]]. 
    pose proof RedBackL H4 H3 H2 as [st' [y' [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]].
    by exists y';split;[ | split;[exists st' |]].
  Qed.
  
  Lemma RedBackF1:  forall (x y:T), exists z, z \in [set u| R5 ((x,y),u)].
  Proof. 
    move => x y.
    case H1: ((x,y) \in Asym R.+).
    by move: H1=> /inP H1;move: (RedBackF H1) => [z H2];exists z;rewrite inP /R5; right.
    exists x; rewrite inP /R5; left => /inP H2.
    by rewrite H2 in H1.
  Qed.
  
  Definition g (x y:T) := xchoose (RedBackF1 x y).

  Lemma gP: forall x y, (g x y) \in [set u| R5 ((x,y),u)].
  Proof. by move => x y; apply: xchooseP. Qed.
  
  Lemma gP1: forall y z t, Asym R.+(y,z) -> Asym R.+ (z,t) -> Asym R.+ (g y z, t).
  Proof.
    move => y z t H2 H3.
    move: (gP y z) => /inP [/= H4 // | [/= _ [H4 [H5 | H5]]]].
    by rewrite -H5.
    move: H3 => [H3 /= H3'].
    split; first by apply: (t_trans H5 H3). 
    move => /= H7.
    by have H: R.+ (t,z) by apply: (t_trans H7 H5). 
  Qed.
  
  Variable (f: T->T) (x0:T).
  
  Definition h (xy:T*T) := (g xy.1 xy.2, f xy.2).
  
  Fixpoint Iterh k xy:= 
    match k with 
    | 0 => xy
    | S m => h (Iterh m xy)
    end. 

  Lemma IterhP: forall k xy, Iterh k.+1 xy = h (Iterh k xy). 
  Proof. by []. Qed.

  Fixpoint Iterf k x:= 
    match k with 
    | 0 => x
    | S m => f (Iterf m x)
    end. 

  Lemma IterfP: forall k x, Iterf k.+1 x = f (Iterf k x). 
  Proof. by []. Qed.
  
  Axiom IR: forall k, Asym R.+ (Iterf k x0, Iterf k.+1 x0).
  
  Lemma IR1: forall k, let xy := (Iterh k (x0,f x0)) in 
                  R.+ xy /\ Asym R.+ (g xy.1 xy.2, f xy.2).
  Proof.
    elim. 
    rewrite /Iterh /h /=; move: (IR 0) => /= [ H1 _].
    split.  by [].
    move: (gP x0 (f x0)) => /inP [/=  H2 | H2].
    move: H2; rewrite not_andE => [[H2 | /=/contrapT H2]].
    by [].
    rewrite /(Asym R.+) /mkset /=.
  Admitted.
  
  (*

  Lemma RedBackG: forall (x y z:T) (n:nat), 
      R2 n (x,y) -> R1 (y,z) -> R2 (n.+1) (x,z).
  Proof.
    move => x y z n [st [H1 [H2 [H3 H4]]]] [st' [H5 [H6 [H7 H8]]]].
    exists ((rcons st y) ++ st'). 

    have H12: n.+1 < size (x :: rcons (rcons st y ++ st') z)
      by rewrite rcons_cat -cat_cons size_cat size_rcons -addn1; apply leq_add.
    
    have H13: (x :: rcons (rcons st y ++ st') z) [L\in] R
      by rewrite rcons_cat Lift_cat_crc allset_cat.

    have H14:  ~ R.+ (z, last x (rcons st y ++ st'))
      by rewrite last_cat last_rcons.
      
    have H15: uniq (rcons st' z)
      by (have H15': subseq (rcons st' z) (y::(rcons st' z))
           by apply subseq_cons;
          have H15'': uniq (rcons st' z));
      pose proof subseq_uniq H15' H6.
      
    have H17: forall t, (t \in [::x & st]) -> (t \in (rcons st' z)) -> R.+ (y, last x st)
        by move => t H18 H19; pose proof Lyy  H18 H19 H3 H7.

    move: (H6);rewrite cons_uniq => /andP [_ H6'].
      
    have H20: has (in_mem^~ (mem (x :: rcons st y))) (rcons st' z) -> False.
    move => /hasP [t H21 H22]. 
    move: H22;rewrite -rcons_cons in_rcons => /orP [H22 | /eqP H22].
    by pose proof (H17 t) H22 H21 as H23.
    rewrite H22 in H21; move: H6; rewrite /uniq => /andP [H6 _].
    by rewrite H21 in H6.
    
    move: H20 => /negP H20.
      
    have H23: uniq (x :: rcons (rcons st y ++ st') z)
      by rewrite rcons_cat -cat_cons cat_uniq H2 H6' andbC 2!andbT.
    by [].
  Qed.

  Lemma RedBackFn: forall (x y y' z:T) (n:nat),
      R2 n (x,y') -> (y=y' \/ R.+(y',y))  
      -> R.+ (y,z) -> ~ ( R.+ (z,y)) ->
      exists z', R2 (n.+1) (x,z') /\ (z=z' \/ R.+(z',z)).
  Proof.
    move => x y y' z n H2 H5 H6 H7.
    have H6': R.+ (y', z) by  move: H5 => [<- // | H5]; apply: t_trans H5 H6.
    have H7': ~ (R.+ (z,y')) by move: H5 => [<- // | H5];
                                           move => H8;have H9: R.+ (z,y) by apply: t_trans H8 H5.
    pose proof RedBackF H6' H7' as [z' [H8 H9]].
    pose proof RedBackG H2 H8 as H10.
    by exists z'.
  Qed.

  Lemma RedBackF0: forall (x y:T), R1 (x,y) -> R2 0 (x,y). 
  Proof.
    by move => x y [st [H1 [H2 [H3 H4]]]]; exists st.
  Qed.
  

  Definition Rp4 (x y:T) (n:nat) := 
    exists st,  size(st) = n /\ (x::(rcons st y)) [L\in] (Asym R.+).

  Definition R4 (n:nat):= [set xy | Rp4 xy.1 xy.2 n].


  Lemma Rpath: forall (n:nat) (x y:T),
      R4 n (x,y) -> exists y', R2 n (x,y') /\ (y=y' \/ R.+(y',y)).
  Proof.
    elim. 
    + move => x y.
      rewrite /R4 /Rp4 /mkset => [[st [/size0nil -> H2]]].
      move: H2; rewrite /= andbT /(Asym R.+) inP /mkset /= => [[H3 H4]].
      pose proof RedBackF H3 H4 as [y' [H5 H6]].
      by (exists y');split;[apply: RedBackF0 |].
    + move => n Hr x y [st' [/seq_rcn [st1 [z [-> H2]]] H3]].
      move: H3; rewrite -rcons_cons Lift_rcc allset_rcons => [[H3 /= H4]].
      have H5: R4 n (x, z) by (exists st1).
      move: H4; rewrite last_rcons => [[H4 /= H6]].
      move: H5 => /Hr [y' [H5 H7]].
      pose proof RedBackFn H5 H7 H4 H6 as H8.
      by [].
  Qed.
  
  Lemma Infinite_R_path0: 
      (exists v0, v0 \in (@setT T))
      -> (forall v, exists w, R.+ (v,w) /\ ~ (R.+ (w,v)))
      -> forall n, exists v0, exists v1, R4 n (v0,v1).
  Proof.
    move => [v0 _] H1. 
    elim. 
    + pose proof H1 v0 as [v1 H2].
      by exists v0,v1;exists [::]; split;[| rewrite /= andbT inP /(Asym R.+)].
    + move => n [vn [vn' [st [H3 H3']]]].
      pose proof H1 vn' as [vnp1 [H4 H5]].
      (exists vn, vnp1);exists (rcons st vn').
      by rewrite size_rcons H3 -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.
  
  Lemma Infinite_R_path1: 
    (exists v0, v0 \in (@setT T))
    -> (forall v, exists w, R.+ (v,w) /\ ~ (R.+ (w,v)))
    -> forall (n:nat), exists x, exists y, R2 n (x,y).
  Proof.
    move => H0 H1.
    pose proof Infinite_R_path0 H0 H1 as H2.
    move => n.
    move: H2 => /(_ n) [v0 [v1 H2]]. 
    pose proof Rpath H2 as [v2 [H3 _]]. 
    by exists v0, v2.
  Qed.
    
  Lemma PQ1: forall (x:T), (exists w, R.+ (x,w) /\ ~ (R.+ (w,x))) 
                      <-> not (forall w, R.+ (x,w) -> R.+ (w,x)).
  Proof.
    move => x; rewrite not_existsP;split;apply contraPP;rewrite !notE;
           first by move => H1 x0 [/H1 H2 H3].
    move => H1 w H2;pose proof (H1 w) as H3.
    by move: H3; rewrite not_andP notE => [[H3 | H3]].
  Qed.
  
  Lemma Hyp: 
    (exists v, forall w,  R.+ (v,w) -> R.+ (w,v))
    <-> ~ (forall v, exists w, R.+ (v,w) /\ ~ (R.+ (w,v))).
  Proof.
    split => [[v ?] ? |].
    by have: not (forall w, R.+ (v,w) -> R.+ (w,v)) by apply PQ1.
    by rewrite not_existsP;apply contraPP;rewrite 2!notE => [H1 v]; rewrite PQ1.
  Qed.
  *)

End Unused.

