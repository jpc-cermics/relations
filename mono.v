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

Section Asymmetric. 
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
    rewrite predeqE => [[a b]];split => [[? _] //| H1]. 
    split => [// | H2];pose proof (Asym_antisymmetric H1 H2) as H3.
    by move: H1;rewrite H3;apply: Asym_irreflexive.
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
  
End Asymmetric. 

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
  (** * Definitions around infinite paths *)
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

    (** * We show that the maximal set is the independ set we search *)
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
  
  Definition uniq_path (st: seq T) x y := (~ x \in st /\ ~ y \in st /\ uniq st).

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

  Lemma uniq_subseq': forall (str stl stl': seq T),
      uniq (stl ++ str) -> subseq stl' str -> uniq (stl ++ stl').
  Proof.
    elim/last_ind =>  [stl' str| str x Hr stl stl' H1 H2];
            first by rewrite cats0 subseq0 => H1 /eqP ->; rewrite cats0.
  Admitted.
  
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
    move => st;elim: st x =>  [ x // | z st' H1 x ].
    rewrite in_cons rev_cons -cats1 mem_cat => /orP [ /eqP H2 | H2].
    by rewrite -H2 mem_seq1;have /eqP -> : x = x by [];rewrite orbT.
    by apply H1 in H2;rewrite H2 orbC orbT.
    (* end H1 *)
    by split;[ apply H1 | move => /H1 H2; rewrite revK in H2].
  Qed.
  
  Lemma head_in: forall (st:seq T) (x y:T), size(st) > 0 -> head x (rcons st y) \in st.
  Proof.
    by elim => [x y //| z st Hr x y _ /=];rewrite in_cons eq_refl orbC orbT.
  Qed.
  
  Lemma in_rcons: forall (st:seq T) (x y:T), 
      (x \in rcons st y) = (x \in st) || (x == y).
  Proof.
    elim => [x y /= | z st Hr x y]; first by rewrite mem_seq1.
    by rewrite rcons_cons 2!in_cons Hr /= orbA.
  Qed.
  
  Lemma uniq_cat:  forall (stl str: seq T),
      uniq(stl) -> uniq(str) -> (forall s, s \in stl -> s \in str -> False) 
      -> uniq(stl ++ str).
  Proof.
    move => stl str H1 H2 H3.
    rewrite cat_uniq H1 H2 andbT andTb; apply: negbT.
    have: has (in_mem^~ (mem stl)) str -> False
      by move => /hasP [s H4 H5];pose proof (H3 s H5 H4).
    by apply: contra_notF.
  Qed.

  Lemma Lxx: forall (st: seq T) (y z: T),
      y \in st -> (rcons st z) [L\in] R -> R.+ (y, z).
  Proof.
    move => st y z H1 H2;move: (Lift_in_F H2) => H3. 
    by move: (allset_in H1 H3);rewrite inP Fset_t0.
  Qed.
  
  Lemma Lxx'': forall (st: seq T) (x y z: T),
      y \in (x::st) -> (x::(rcons st z)) [L\in] R -> R.+ (y, z).
  Proof.
    move => st x y z;rewrite in_cons => /orP [/eqP -> H1| H1 H2].
    by move: (allL_to_clos_t H1).
    by move: (Lxx H1 (allL_Lift_in_rc H2)). 
  Qed.
  
  Lemma Lxx_head: forall (st: seq T) (x y: T),
      y \in st -> (x::st) [L\in] R -> R.+ (x, y).
  Proof.
    move => st y z H1 H2;move: (Lift_in_A H2) => H3. 
    by move: (allset_in H1 H3);rewrite inP /Aset -Fset_t0.
  Qed.
  
  Lemma Lxx_head': forall (st: seq T) (x y z: T),
      y \in (rcons st z) -> (x::(rcons st z)) [L\in] R -> R.+ (x, y).
  Proof.
    move => st x y z. rewrite in_rcons => /orP [ H1 H2 | /eqP <-].
    by move: (Lxx_head H1 (allL_Lift_in_c H2)).     
    by apply:allL_to_clos_t.
  Qed.

  Lemma uniq_crc: forall (st: seq T) x y,
      uniq (x::(rcons st y)) <-> uniq_path st x y /\ ~ (x = y).
  Proof.
    move => st x y;split => [ | [[H1 [H2 H3]] H4]].
    + by rewrite cons_uniq in_rcons rcons_uniq =>
        /andP [/orP/not_orP [H1 /negP/eqP  H3] /andP [/negP H4 H5]].
    + rewrite cons_uniq;apply/andP; split. 
      by rewrite in_rcons;apply/orP/not_orP;split;[| apply/negP/eqP].
      by rewrite rcons_uniq;apply/andP;split;[apply/negP |].
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
  
  Lemma last0: forall(st:seq T) t,
      ((last t st) \in st ) = false <-> st = [::].
  Proof.
    split; last by move => -> /=.
    elim: st t => [t // | t' st Hr t1 /=].
    rewrite in_cons => /orP H1. 
    move: H1; rewrite not_orE => -[H1 H2].
    have H3: st = [::] by apply: (Hr t'); case H3: (last t' st \in st).
    by rewrite H3 in H1.
  Qed.
  
  Lemma last0': forall(st:seq T) t,
      ~ ( st = [::]) -> (last t st) \in st.
  Proof. elim/last_ind => [// | st x Hr t _ /=].
         by rewrite last_rcons in_rcons;apply/orP;right;apply:eq_refl.
  Qed.
  
  Lemma head0: forall(st:seq T) t,
      ~ ( st = [::]) -> (head t st) \in st.
  Proof.
    elim => [// | x st Hr t _ /=].
    by rewrite in_cons;apply/orP;left;apply:eq_refl.
  Qed.
  
  Lemma allL_last: forall (st:seq T) (x y:T),
      allL R st x y ->  (rcons (belast x st) (last x st)) [L\in] R.
  Proof.
    elim/last_ind => [ // | st z _ x y H2].
    rewrite belast_rcons rcons_cons. 
    by move: H2; rewrite allL_rc last_rcons => /andP [_ H2].
  Qed.
  
  Lemma in_belast: forall (st:seq T) (x z:T),
      z \in st -> ~ (z = (last x st)) -> z \in (belast x st).
  Proof.
    elim/last_ind => [x z // | st y Hr x z H1 H2].
    move: H1; rewrite in_rcons => /orP [ H1 | /eqP H1].
    by rewrite belast_rcons in_cons H1 orbT.
    by move: H2; rewrite H1 last_rcons.
  Qed.
  
  Lemma belast_head: forall (st:seq T) x,
    ~(st = [::]) -> (belast x st) = x::(drop 1 (belast x st)).
  Proof.
    elim/last_ind => [x // | st y Hr x _].
    by rewrite belast_rcons drop1 /behead.
  Qed.
  
  Lemma allL_belast: forall (st:seq T) (x s y:T),
      s \in st -> ~(s = x) -> ~ (s = (last x st)) -> allL R st x y
      -> R.+ (s, (last x st)).
  Proof.
    move => st x s y H1 H2 H3 H4.
    move: (in_belast H1 H3) => H5.
    move: (allL_last H4) => H6.
    have H7:  ~(st = [::]) by move => H8; rewrite H8 in H1.
    have H8:  (belast x st) = x::(drop 1 (belast x st)) 
      by apply: belast_head.
    move: H5; rewrite H8 in_cons => /orP [/eqP H9 // | H9].
    move: H6; rewrite H8 rcons_cons => H6.
    by pose proof (allL_to_clos_t (allL_drop H9 H6)).
  Qed.

  Lemma in_behead: forall (st:seq T) (x z:T),
      z \in st -> ~ (z = (head x st)) -> z \in (behead st).
  Proof.
    elim => [x z // | y st Hr x z H1 /= H2].
    by move: H1; rewrite in_cons => /orP [/eqP H1 //| H1 //].
  Qed.

  Lemma behead_head: forall (st:seq T) (x:T),
    ~(st = [::]) ->  st = (head x st)::(behead st).
  Proof. by elim => [// | y st Hr x _ /=]. Qed.
    
  Lemma allL_behead: forall (st:seq T) (x s y:T),
      s \in st -> ~(s = y) -> ~ (s = (head y st)) -> allL R st x y
      -> R.+ ((head y st),s).
  Proof.
    move => st x s y H1 H2 H3 H4.
    move: (in_behead H1 H3) => H5.
    have H7: ~(st = [::]) by move => H8; rewrite H8 in H1.
    have H8: st = (head y st)::(behead st) by apply: behead_head;exact.
    move: H4; rewrite H8 allL_c => /andP [_ H4].
    by pose proof (allL_to_clos_t (allL_take H5 H4)).
  Qed.
  
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
  
  Lemma in_subseq_1: forall (st2 st1: seq T) (x:T),
      subseq [::x & st1] st2 -> x \in st2.
  Proof.
    elim => [st x //| y st Hr st1 x H1].
    case H2: (x == y);first by rewrite in_cons H2 orTb.
    move: H1;rewrite /subseq H2 -/subseq => /Hr H1.
    by rewrite in_cons H1 orbT.
  Qed.

  Lemma in_subseq': forall (st2 st1: seq T) (x:T),
      subseq st1 st2 -> (x \in st1) -> (x \in st2).
  Proof.
    elim => [st1 x | y st1 Hr st2 x H1 H2].  
    by rewrite subseq0 => /eqP -> H2.
    elim: st2 H1 H2 Hr => [// |  z st2 Hr' H1 H2 H3].
    case H4: (z == y);move: H1; rewrite /subseq H4 -/subseq => H1.
    - move: (H4) => /eqP <-;rewrite in_cons. 
      move: H2; rewrite in_cons => /orP [H2 | H2].
      by rewrite H2 orbC orbT.
      by (have ->:  x \in st1 by apply H3 with st2); rewrite orbT.
    - move: H2; rewrite in_cons => /orP [/eqP H2 | H2].
      move: H1 => /in_subseq_1 H1.
      by rewrite in_cons H2 H1 orbT.
      apply cons_subseq in H1. 
      have H5: x \in st1 by apply: (H3 st2 x).
      by rewrite in_cons H5 orbT. 
  Qed.
  
  Lemma in_subseq: forall (st1 st2: seq T) (x:T),
      subseq st1 st2 -> ~ (x \in st2) -> ~ (x \in st1).
  Proof.
    move => st1 st2 x ?; apply contraPP => /contrapT ? ?.
    by have:  x \in st2 by apply in_subseq' with st1.  
  Qed.
  
  
  Lemma allL_uniq: forall (st: seq T) (x y: T),
      allL R st x y -> 
      exists st', subseq st' st /\ ~( x \in st') /\  ~(y \in st')
             /\  @uniq T st' /\ allL R st' x y. 
  Proof.
    move => st x y H1.
    pose proof allL_uniq_tail H1 as [st2 [S2 [I2 H2]]].
    pose proof allL_uniq_head H2 as [st3 [S3 [I3 H3]]].
    have J3: ~ (y \in st3) by  apply in_subseq with st2.
    pose proof allL_uniq_internals H3 as [st4 [S4 [K4 H4]]].
    have J4: ~ (y \in st4) by apply in_subseq with st3.
    have I4: ~ (x \in st4) by apply in_subseq with st3.
    by exists st4;pose proof (subseq_trans (subseq_trans S4 S3) S2).
  Qed.
  
  Lemma TCP_uniq: forall (x y:T), 
      R.+ (x,y) <-> exists st, uniq_path st x y /\ allL R st x y. 
  Proof.
    move => x y;split. 
    - rewrite TCP' /mkset => -[st /allL_uniq H1].
      by move: H1 => [st' [H1 [H2 [H3 [H4 /= H5]]]]];(exists st').
    - by move => [st [_ H1]]; move: H1;apply: allL_to_clos_t. 
  Qed.
  
  Lemma TCP_uniq'': forall (x y:T), 
      R.+ (x,y) /\ ~ (x = y) 
      <-> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y.
    split => [[H1 H7] |].
    + move: (H1) => /TCP_uniq [st [[H3 [H4 H5]] H6]].
      by (exists st);rewrite uniq_crc.
    + by move => [st [/uniq_crc [_ H1] /(@allL_to_clos_t T)  H2]].
  Qed.
  
  Lemma TCP_uniq': forall (x y:T), 
      (Asym R.+)(x,y) 
      -> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y /[dup] H0 [H1 H2]. 
    have H3: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    by rewrite -TCP_uniq''.
  Qed.

  Definition allLu (R: relation T) st x y :=
    (x::(rcons st y)) [L\in] R /\ uniq (x :: rcons st y).
  
  Lemma TCP_uniq1 (x y:T):
      (Asym R.+)(x,y) <-> (exists st, allLu R st x y) /\ ~ R.+ (y,x).
  Proof. split. 
    by move => /[dup] /TCP_uniq' [st [H1 H2]] [_ H4];split;[exists st;split |].
    by move => [[st [H1 H2]] H3];split;[apply: allL_to_clos_t; apply: H1|].
  Qed.

End allL_uniq.

Section Hn4.
  (** * some Lemmata around infinite outward R-path *) 
  
  Variables (T:choiceType) (R: relation T).
  
  Lemma allL_asym_l1: forall st x y,
      allL R st x y -> ~ R.+ (y, last x st) -> (Asym R.+) (x, y).
  Proof.
    move => st x y H1 H2.
    split;first by move: H1 => /(@allL_to_clos_t T) H1.
    move => H3. 
    case H4: (st == [::]); first by move: H4 H2 => /eqP H4;rewrite H4 /= => H5.
    move: H4 => /eqP/(@last0' T) => /(_ x) H4.
    have H5: (last x st) \in (rcons st y) by rewrite in_rcons; apply/orP; left. 
    move: (Lxx_head' H5 H1) => H6. 
    have H7: R.+ (y, last x st) by apply: t_trans H3 H6.
    exact.
  Qed.

  Lemma allL_asym_r1: forall st x y,
      allL R st x y -> ~ R.+ (head y st,x) -> (Asym R.+) (x, y).
  Proof.
    move => st x y H1 H2.
    split;first by move: H1 => /(@allL_to_clos_t T) H1.
    move => H3. 
    case H4: (st == [::]); first by move: H4 H2 => /eqP H4;rewrite H4 /= => H5.
    move: H4 => /eqP/(@head0 T) =>  /(_ y) H4.
    have H5: (head y st) \in (x::st) by rewrite in_cons; apply/orP;right.
    move: (Lxx H5 H1) => H6. 
    have H7: R.+ (head y st,x) by apply: t_trans H6 H3.
    exact.
  Qed.
  
  Lemma allL_asym_l: forall st x s y,
      s \in st -> ~(s = x) -> allL R st x y -> ~ R.+ (y, last x st) 
      -> (Asym R.+) (s, y).
  Proof.
    move => st x s y H1 H2 H4 H5.
    split; first by move: (allL_to_clos_t (allL_drop H1 H4)) => H6.
    case H3: (s == (last x st)); first by move: H3 => /eqP ->.
    have H6: ~ ( s = (last x st)). by move => H7; rewrite -H7 eq_refl in H3.
    pose proof (allL_belast H1 H2 H6 H4) as H7.
    by move => H8;have H9: R.+ (y, last x st) by apply: (t_trans H8 H7).
  Qed.
  
  Lemma allL_asym_r: forall st x s y,
      s \in st -> ~(s = y) -> allL R st x y -> ~ R.+ (head y st, x) 
      -> (Asym R.+) (x, s).
  Proof.
    move => st x s y H1 H2 H4 H5.
    split;first by move: (allL_to_clos_t (allL_take H1 H4)). 
    case H3: (s == (head y st)); first by move: H3 => /eqP ->.
    have H6: ~ ( s = (head y st)). by move => H7; rewrite -H7 eq_refl in H3.
    pose proof (allL_behead H1 H2 H6 H4) as H7.
    by move => H8;have H9: R.+ (head y st,x) by apply: (t_trans H7 H8).
  Qed.
  
  Lemma allL_asym_lr: forall st st' x s y s' z,
      s \in st -> ~(s = x) -> allL R st x y -> ~ R.+ (y, last x st) 
      -> s' \in st'  -> allL R st' y z
      -> (Asym R.+) (s, s').
  Proof.
    move => st st' x s y s' z H1 H2 H3 H4 H5 H6.
    pose proof (allL_asym_l H1 H2 H3 H4) as H7.
    have H8: s' \in (rcons st' z) by rewrite in_rcons H5 orTb. 
    pose proof (Lxx_head' H8 H6) as H9. 
    have H10: (Asym(R.+) `;` R.+) (s,s') by (exists y).
    by move: H10 => /AsymIncr H10.
  Qed.

  Lemma allL_asym_rl: forall st st' x s y s' z,
      s \in st -> allL R st x y 
      -> s' \in st' ->  ~(s' = z) -> allL R st' y z -> ~ R.+ (head z st', y) 
      -> (Asym R.+) (s, s').
  Proof.
    move => st st' x s y s' z H1 H2 H3 H4 H5 H6.
    pose proof (allL_asym_r H3 H4 H5 H6) as H7.
    have H8: s \in (x::st) by rewrite in_cons H1 orbT. 
    pose proof (Lxx'' H8 H2) as H9. 
    have H10: (R.+  `;` Asym(R.+)) (s,s') by (exists y).
    by move: H10 => /AsymIncl H10.
  Qed.
  
  Lemma allL_asym_xx: forall st x s z,
      s \in st -> ~ (z = s) -> allL R st x z -> ~ R.+ (z, s)
      -> (Asym R.+) (x,z).
  Proof.
    elim => [// | y st Hr x s z].
    rewrite in_cons => /orP [/eqP -> | H1] H2.
    + rewrite allL_c => /andP [/inP H3 H4] H5. 
      split.
      ++ pose proof (allL_to_clos_t H4) as H6.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         by pose proof t_trans H7 H6.
      ++ move => H6.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         by pose proof t_trans H6 H7.
    + rewrite allL_c => /andP [/inP H3 H4] H5. 
      split.
      ++ pose proof (allL_to_clos_t H4) as H6.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         by pose proof t_trans H7 H6.      
      ++ pose proof (Hr y s z) H1 H2 H4 H5 as [H8 H9].
         move => H10.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         have H11: R.+ (z,y) by apply: t_trans H10 H7.
         exact.
  Qed.


  Lemma uniq_asym2: forall x stl y str z,
      allLu R stl x y -> ~ R.+ (y, last x stl) -> allLu R str y z 
      -> (forall s, s \in str -> s \in stl -> False).
  Proof.
    move => x stl y str z [H1 H2] H3 [H4 H5].
    move: H2 => /uniq_crc [[K1 [K2 K3]] K4].
    move: H5 => /uniq_crc [[J1 [J2 J3]] J4].
    move => s H9 H10.
    have H11: ~(s = x) by move => H12; rewrite H12 in H10.
    pose proof allL_asym_lr H10 H11 H1 H3 H9 H4 as H12. 
    by pose proof Asym_irreflexive H12.
  Qed.
  
  Lemma allL2_fact: forall yl (stlr: seq T) yr str z,
      allLu R stlr yl yr -> allLu R str yr z 
      -> ~ R.+ (z, yr) -> ~ R.+ (head z str, yr)
      -> ~ ( z \in stlr)  /\ ~ (yl = z).
  Proof.
    move => yl stlr yr str z H1 H2 H3 H4.
    move: H1 => [H1 /uniq_crc  [[J1 [J2 _]] _]].
    move: H2 => [H2 /uniq_crc  [[K1 [K2 _]] _]].
    have H5: forall s, s \in stlr -> ~(s = yr)
        by move => s H6 H7; rewrite H7 in H6.
    split. 
    + move => /[dup] H6 /H5 H7.
      have H8: R.+ (z, yr) 
        by pose proof (allset_in H6 (Lift_in_F (allL_Lift_in_rc H1)));
        rewrite Fset_t0 -inP.
      exact.
    + (* Asym composition is Asym *) 
      by move: H1 => + H6;rewrite H6 => /(@allL_to_clos_t T) H1.
  Qed.
  
  (* utility lemma *)
  Lemma RedBackL: forall (st:seq T) (x y:T),
      (x::(rcons st y)) [L\in] R
      -> uniq (x::(rcons st y)) 
      -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          subseq st' st (* subseq (rcons st' y') (rcons st y) *)
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
      split;first by apply Lift_in_FF with z;[|rewrite inP -Fset_t0 -inP H3].
      by rewrite -Fset_t0 -inP H3.
      (* end of H4 *)
      have H5: y = y \/ R.+ (y, y) by left.
      move: H3 => /inP H3.
      have H6: ~ R.+ (y, last x (rcons st z))
        by rewrite last_rcons; move => H7;have H8: R.+ (y,x) by apply: t_trans H7 H3.
      exact. 
    - rewrite Lift_crc Lift_rcrc allset_cons allset_rcons in H1.
      move: (H1); rewrite H0 => [[H10 [H10' H10'']]].
      have H5: (x :: rcons st z) [L\in] R by rewrite Lift_crc allset_cons.
      apply Hr in H5; last by move => /inP H6; rewrite H6 in H3.
      move: H5 => [st' [y' [H5 [H5' [H6 [H7 [H8 [H9 H9']]]]]]]].
      (* have H11: subseq (rcons st' y') (rcons (rcons st z) y)
        by apply subseq_trans with (rcons st z);[ | apply subseq_rcons]. *)
      have H11: subseq st' (rcons st z). by apply/subseq_trans/subseq_rcons.
      (exists st', y'); move: H9 => [H9 | H9].
      by have H12: (y = y' \/ R.+ (y', y)) by right;rewrite -H9;apply: t_step.
      by have H12: (y = y' \/ R.+ (y', y)) by right;apply t_trans with z;[ |apply: t_step].
      have H13: subseq (rcons st z) (rcons (rcons st z) y) by apply: subseq_rcons. 
      have H14: uniq (x :: rcons st z) by apply: (uniq_subseq H1' H13).
      exact.
  Qed.
  
  (* utility lemma *)
  Lemma RedBackR: forall (st:seq T) (y z:T),
      (y::(rcons st z)) [L\in] R
      -> uniq (y::(rcons st z)) 
      -> ~ ( R.+ (z,y))
      -> exists st', exists y',
          subseq st' st (* (y'::st') (y::st)  *)
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
      move: H1;rewrite Lift_crc Lift_rcc allset_cons allset_rcons => [[_ [H1 _]]].
      rewrite allset_cons.
      split;first by rewrite  /Aset -Fset_t0 /inverse /= -inP H3.
      by apply Lift_in_AA with y1;[|rewrite inP /Aset -Fset_t0 /inverse /= -inP H3].
      (* end of H4 *)
      have H5: y = y \/ R.+ (y, y) by left.
      move: H3 => /inP H3.
      have H6: ~ R.+ (head z (y1 :: st), y)
        by move => /= H7;have H8: R.+ (z,y) by apply: t_trans H3 H7.
      exact.
    - rewrite Lift_crc Lift_rcc allset_cons allset_rcons in H1.
      move: (H1) => [H10 [H10' H10'']].
      have H5: (y1 :: rcons st z) [L\in] R 
        by rewrite -rcons_cons Lift_rcc allset_rcons.
      apply Hr in H5; last by move => /inP H6; rewrite H6 in H3.
      move: H5 => [st' [z' [H5 [H5' [H6 [H7 [H8 [H9 H9']]]]]]]].
      (*  have H11: subseq (z'::st') (y::(y1::st)).
      by apply subseq_trans with (y1::st);[| apply subseq_cons]. *)
      have H11: subseq st' (y1 :: st) by apply/subseq_trans/subseq_cons.
      (exists st', z'); move: H9 => [H9 | H9].
      by have H12: (y = z' \/ R.+ (y, z')) by right; rewrite -H9; apply: t_step.
      by have H12: (y = z' \/ R.+ (y, z')) by right;apply t_trans with y1;[apply: t_step|].
      by move: H1'; rewrite cons_uniq rcons_cons => /andP [_ H1'].
  Qed.
  
  Lemma RedBackLR: forall (x y z:T) (stl: seq T),
      allLu R stl x y -> ~ R.+ (y,x) -> 
      (Asym R.+) (y,z) 
      -> exists stl', exists yl, exists str', exists yr, exists stlr,
          ((yl = yr) \/ (allLu R stlr yl yr))
          /\ subseq stl' stl (* (rcons stl' yl) (rcons stl y)  *)
          /\ allLu R stl' x yl 
          /\ ~ (R.+ (yl,x))
          /\ ~ (R.+ (yl,(last x stl')))
          /\ allLu R str' yr z
          /\ ~ (R.+ (z,yr))
          /\ ~ (R.+ ((head z str'),yr)).
  Proof.
    move => x y z stl [H1 H2] H3 /TCP_uniq1 [[str [H4 H5]] H6].
    pose proof (RedBackL H1 H2 H3) as [stl' [yl [H7' H7]]].
    pose proof (RedBackR H4 H5 H6) as [str' [yr [_ H8]]].
    exists stl';exists yl;exists str';exists yr.
    move: H7 => [L1 [L2 [L3 [L4 [L5 L6]]]]].
    move: H8 => [M1 [M2 [M3 [M4 [M5 M6]]]]].
    
    have: (yl = yr) \/  R.+ (yl, yr).
    by move: L5 M5 => [<- | H16] [<- | H17];
                  [left | right | right | right;apply t_trans with y].
    
    move => [? | ?]; first by (exists [::]);split;[left |]. 
    case H17: (yl == yr);move: H17 => /eqP H17;first by (exists [::]);split;[ left|].
    have: R.+ (yl, yr) /\  yl <> yr by exact.
    rewrite TCP_uniq'' => -[strl [? ?]];exists strl.
    by split;[right|].
  Qed.
  
  Lemma uniq_util: forall yl stlr yr str1 z,
      uniq (yl :: rcons stlr yr) -> uniq (yr :: rcons str1 z)
      -> ( forall s : T, s <> z -> s \in stlr -> s \in str1 -> False)
      -> ~ (yl \in str1) -> ~ (z \in stlr) -> ~ (yl = z)
      -> uniq ((yl :: stlr) ++ yr :: rcons str1 z).
  Proof.
    move => yl stlr yr str z H1 H2 H3 H4' H5' H6'.
    move: (H2);rewrite cons_uniq rcons_uniq => /andP [_ /andP [/negP H4 _]].
    
    have H5: forall s, s \in str -> ~ (s = z)
        by move => s H6 H7;rewrite -H7 in H4.

    have H6: ( forall s : T, s \in stlr -> s \in str -> False)
      by move: H3 H5 => + + s H6 H7 
         => /(_ s) H3 /(_ s) H5; pose proof (H3 (H5 H7) H6 H7).

    have H7: uniq (yl :: stlr)
      by move: H1;rewrite -rcons_cons rcons_uniq => /andP [_ H1].

    move: H1 => /uniq_crc [[J1 [J2 J3]] J4].
    move: (H2) => /uniq_crc [[K1 [K2 K3]] K4].
    

    have H8: forall s, s = yr -> s = yl -> False by move => s H1 H2';rewrite -H1 -H2' in J4. 
    have H9: forall s, s \in rcons str z -> s = yl -> False
          by move => s H1 H2';move: H1;
                    rewrite in_rcons => /orP [H1 |/eqP H1];[rewrite H2' in H1|rewrite -H2' -H1 in H6'].
    have H10: forall s, s = yr -> s \in stlr -> False by move => s H1 H2';rewrite H1 in H2'.
    have H11: forall s, s \in rcons str z -> s \in stlr -> False
            by move => s H1 H2';move: H1;
                      rewrite in_rcons => /orP [H1 |/eqP H1];
                                         [pose proof (H6 s H2' H1)|rewrite H1 in H2'].
    
    have H12: forall s, s \in yl :: stlr -> s \in yr :: rcons str z -> False
            by move => s;rewrite in_cons => /orP [/eqP H13 | H13] /orP [/eqP H14 | H14];
                                          [apply: (H8 s)| apply: (H9 s)|apply: (H10 s)|apply: (H11 s)].
    
    by pose proof (uniq_cat H7 H2 H12).
  Qed.

  Lemma RedBackLR2:  forall (x y z:T) (stl: seq T),
      allLu R stl x y -> ~ R.+ (y,x) -> (Asym R.+) (y,z) 
      -> exists stl', exists yl, exists (stlr: seq T), exists yr, exists str',
          ((yl = yr /\ (forall s, s \in stl' -> s \in str' -> False)
            /\ subseq stl' stl (* subseq (rcons stl' yl) (rcons stl y)  *)
            /\ allLu R stl' x yl /\ ~ (R.+ (yl,(last x stl')))
            /\ allLu R str' yr z /\ ~ (R.+ ((head z str'),yr))
           )
           \/
             ( 
               subseq stl' stl (* subseq (rcons stl' yl) (rcons stl y)  *)
               /\allLu R stl' x yl /\ ~ (R.+ (yl,(last x stl')))
               /\ allLu R ((rcons stlr yr) ++ str') yl z
               /\ (exists s, s \in (rcons stlr yr ++ str') /\ ~ R.+ (z,s))
             )
           \/ 
             (
               subseq stl' stl (* subseq (rcons stl' yl) (rcons stl y)  *)
               /\ allLu R stl' x yl /\ ~ (R.+ (yl,(last x stl')))
               /\ allLu R (drop (index yl str').+1 str') yl z
               /\  ~ R.+ (z, yl)
               /\ uniq (stl' ++ drop (index yl str').+1 str')
             )
           ).
  Proof.
    move => x y z stl H1 H1' H2.
    move: (RedBackLR H1 H1' H2) => [stl1 [yl [str1 [yr [stlr H7]]]]].
    
    move: H7=> [[H15 | [H15 H16]] [H7' [H7 [H8 [H10 [H11 [H13 H14]]]]]]].
    + exists stl1; exists yl; exists stlr; exists yr; exists str1. 
      move: H7' H7 H8 H10; rewrite H15 => H7' H7 H8 H10.
      have H16: (forall s : T, s \in stl1 -> s \in str1 -> False) 
        by move => s H17 H18;apply/(uniq_asym2 H7 H10 H11);[apply/H18|apply/H17].
      by left. 
    + exists stl1; exists yl; exists stlr; exists yr; exists str1. 
      case H17: (yl \in str1); last first.
      (* first case *)
       ++ move: H17 => /negP K4.
          have K1: (allLu R stlr yl yr) by split.
          pose proof allL2_fact K1 H11 H13 H14 as [K2 K3].
          
          have H21: forall s : T, s <> z -> s \in stlr -> s \in str1 -> False.
          move: H11 => [H11 H11'] s H18 H19 H20.
          by pose proof (allL_asym_rl H19 H15 H20 H18 H11 H14) as [H notH]. 
      
          have H17: allL R ((rcons stlr yr) ++ str1) yl z.
          by move: H11 => [H11' H11'']; by rewrite allL_cat; apply/andP. 
      
          have H18: uniq (rcons stlr yr)
            by move: H16; rewrite cons_uniq => /andP [_ ?]. 

          have H19: uniq str1
            by move: H11 => [_ ];rewrite cons_uniq rcons_uniq => /andP [_ /andP [_ ?]].
      
          have P1: uniq ((yl :: stlr) ++ yr :: rcons str1 z)
            by move: H11 => [H11 H11'];apply: (uniq_util H16 H11' H21).
          
          have H20: uniq (yl::(rcons ((rcons stlr yr) ++ str1) z))
            by move: P1; rewrite cat_cons -rcons_cons -rcons_cat -cat_rcons. 

          have H22: allLu R ((rcons stlr yr) ++ str1) yl z
            by split.

          have H23: exists s, s \in (rcons stlr yr ++ str1) /\ ~ R.+ (z,s).
          exists yr; split; last by [].
          by rewrite mem_cat;apply/orP;left;rewrite in_rcons;apply/orP;right;apply/eqP.
          
          by right;left.
          
       ++ move: H11 => [/[dup] H11 /(@allL_to_clos_t T) H11' /uniq_crc [[J1 [J2 J3]] J4]].
          move: (H15) => /(@allL_to_clos_t T) H15'.
          have H12: ~ (yl =z) by move => H12;rewrite H12 in H15'.
      
          have H20: ~ (R.+ (z, yl)) 
            by move => H21; have H22: R.+ (z,yr) by apply: (t_trans H21 H15').
          
          pose proof allL_drop H17 H11 as H21. 
          
          have H22: subseq (drop (index yl str1).+1 str1) str1 by apply: drop_subseq.
          have H23: ~ yr \in drop (index yl str1).+1 str1 by apply: in_subseq H22 J1.
          have H24: uniq (drop (index yl str1).+1 str1) by apply: subseq_uniq H22 J3.
          have H25: uniq (yl::(drop (index yl str1).+1 str1))
            by rewrite cons_uniq H24 andbT;apply: drop_notin. 
          have H26: uniq (yl::(rcons (drop (index yl str1).+1 str1) z)).
          rewrite -rcons_cons rcons_uniq H25 andbT. 
          rewrite in_cons. apply/orP.  move => [/eqP H27 | H27];first by rewrite H27 in H12.
          by pose proof in_subseq' H22 H27. 
          
          have H27:  allLu R (drop (index yl str1).+1 str1) yl z by split.
            
          right;right.
          split. by []. split. by []. split. by []. split. by [].
          
          move: (H7) => [H7'' /uniq_crc [[K1 [K2 K3]] K4]].
      
          have H28: (forall s : T, s \in stl1 -> s \in drop (index yl str1).+1 str1 -> False).
          move => s H29 H28. 
          have H30: s \in str1 by pose proof (in_subseq' H22 H28).
          have H31: ~ (s = x) by move => H32;rewrite H32 in H29.
          have H32: (s \in (rcons stlr yr) ++ str1)
            by rewrite mem_cat; apply/orP; right.
          
          have H33: allL R ((rcons stlr yr) ++ str1) yl z
            by rewrite allL_cat; apply/andP. 
          by pose proof (allL_asym_lr H29 H31 H7'' H10 H32 H33) as [H notH].
          (* end of H28 *)
          
          by pose proof (uniq_cat K3 H24 H28).
  Qed.
  
  (** * The main Lemma of this section *)
  Lemma Asym2P: forall (x y z:T) (stl: seq T),
      allLu R stl x y -> ~ R.+ (y,x) -> (Asym R.+) (y,z) 
      -> exists stl', exists y', exists str',
          subseq stl' stl 
          /\ allLu R stl' x y' /\ ~ R.+ (y',x)
          /\ allLu R str' y' z /\ ~ R.+ (z, y')
          /\ uniq (stl' ++ str').
  Proof.
    move => x y z stl H1 H1' H2.
    move: (RedBackLR2 H1 H1' H2) => [stl1 [yl [str1 [yr [stlr H7]]]]].
    move: H7 => [[H7 [H8 [H9' [H9 [H10 [H11 H12]]]]]] | ]. 
    + exists stl1;exists yl;exists stlr.
      have H13:  uniq (stl1 ++ stlr)
        by move: H9 H11 => [_ /uniq_crc [[K1 [K2 K3]] K4]] [_ /uniq_crc [[J1 [J2 J3]] J4]];
                          pose proof (uniq_cat K3 J3 H8).
      
      have: (~ R.+ (head z stlr, yl) \/ (exists s : T, s \in stlr /\ ~ R.+ (z, s)))
        by left;rewrite H7.
      
      have H14: (Asym R.+) (x, yl)
        by move: H9 => [H9 _];move: (allL_asym_l1 H9 H10).
      
      have H16: ~ R.+ (z, yl) 
        by move: H11 => [H11 H11'];
                       pose proof allL_asym_r1 H11 H12 as [H17 H18];rewrite H7.
      
      have H17: ~ R.+ (yl,x)
        by move: H9 => [H9 _];pose proof allL_asym_l1 H9 H10 as [H18 H19].
      
      by rewrite -H7 in H11.
    + 
      move => [[H7'' [H7 [H9 ] [H11 H11']]] |].
      ++ exists stl1;exists yl;exists(rcons str1 yr ++ stlr).
         move: (H7) (H11)  => [H7' H8] [H9' H10].
         have H12: forall s, s \in stl1 -> s \in (rcons str1 yr ++ stlr) -> False.
         move => s H13 H14. 
         have H15: ~(s = x) 
           by move: H8 => /uniq_crc   [[K1 _] _] H16;rewrite -H16 in K1.
         by move: (allL_asym_lr H13 H15 H7' H9 H14 H9') => [H notH].
      
         move: H8 => /uniq_crc [[_ [_ H8]] _].
         move: H10 => /uniq_crc [[_ [_ H10]] _].
         
         have H10': uniq (stl1 ++ rcons str1 yr ++ stlr) by pose proof (uniq_cat H8 H10 H12).
         
         have H16: ~ R.+ (z, yl).
         move: H11' => [s [K1 K2]].
         move: H11 => [H11 H11''].
         move: H11'' => /uniq_crc [[_ [J2 _]] _].
         have H14: ~ (z = s) by move => H15; rewrite H15 in J2.
         pose proof allL_asym_xx K1 H14 H11 K2 as [_ H16]. 
         exact.
      
         have H15: (~ R.+ (head z (rcons str1 yr ++ stlr), yl) \/
                      (exists s : T, s \in rcons str1 yr ++ stlr /\ ~ R.+ (z, s)))
           by right.
         
         have H17: ~ R.+ (yl,x)
           by pose proof allL_asym_l1 H7' H9 as [H18 H19].
         
         exact.
      ++ move => [H7'' [H7 [H8 [H9 [H10 H11]]]]].
         exists stl1;exists yl;exists(drop (index yl stlr).+1 stlr).
         move: H7 => [H7 H7'].
         have H12: ~ R.+ (yl, x) by pose proof (allL_asym_l1 H7 H8) as [_ H'].
         exact.
  Qed.

End Hn4.

Section Hn0.
  (** * some Lemmata around Axiom of choice *) 
  
  Variables (T T':choiceType) (R: set T) (R': set (T*T')).
  
  Hypothesis Au0: (exists (v0:T'), (v0 \in [set: T'])).
  Hypothesis Au1: forall (t: T), R t -> exists z, R' (t,z).
  
  Lemma Au1_P1: forall (t: T),
    exists z, z \in [set u| (R t /\ R' (t,u)) \/ ~ R t].
  Proof. 
    move => t. 
    case H1: (t \in R).
    + move: H1 => /inP H1;move: t H1 => t /[dup] H1 /Au1 [z H1'].
      by exists z;rewrite inP;left;split.
    + move: Au0 => [v0 Au0'].
      by exists v0; rewrite inP; right;move => /inP H2;rewrite H1 in H2.
  Qed.
  
  Lemma Au1_P3 (t: T): R t -> R' (t,xchoose (Au1_P1 t)).
  Proof.
    have H0: xchoose (Au1_P1 t) \in [set u| (R t /\ R' (t,u)) \/ ~ R t]
      by apply: xchooseP.
    by move: H0 => /inP [[_ ?] //| ? //].
  Qed.
  
  Lemma Au1_G: exists (g: T -> T'), forall t, R t -> R' (t,g(t)).
  Proof. by exists (fun t => xchoose (Au1_P1 t)); apply: Au1_P3. Qed.
  
End Hn0.

Section Hn2. 
  (* apply Hn0 to allLu *)
  Variables (T:choiceType) (R: relation T). 
  
  Lemma choose_Rseq: exists (g: T*T -> seq T), forall xy, 
      (Asym R.+) xy -> allLu R (g xy) xy.1 xy.2.
  Proof.
    have Au0: (exists (v0: seq T), (v0 \in [set: seq T]))
      by (exists [::]);rewrite inP.
    pose R' :=[set xyz: (T*T)*(seq T)| allLu R xyz.2 xyz.1.1 xyz.1.2].
    have Au1: forall (xy:T*T), (Asym R.+) xy -> exists z, R' (xy,z)
          by move => [x y] /TCP_uniq1 [[st H3] _];exists st.
    by move: (Au1_G Au0 Au1) => [g H1]; exists g. 
  Qed.
  
End Hn2.

Section Infinite_path. 
  
  Variables (T:choiceType) (R: relation T). 

  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  Definition T2 : Type := (seq T)*T*(seq T)*nat.
  
  Definition Re1 (f: nat -> T) :=
    [set p: T2 | exists (stl: seq T) (x:T) (str:seq T) n,
        p = (stl,x,str,n) /\ uniq (stl ++ str) 
        /\ allLu R str x (f n.+1) /\ ~ R.+ (f n.+1,x)].
  
  Definition Re2 (f: nat -> T) := 
    [set p: T2*T2 | exists stl x str n stl' y' str' n',
      p.1 = (stl, x, str,n) /\ p.2 = (stl', y', str',n')
      /\ n' = n.+1
      /\ allLu R stl' x y' /\ ~ R.+ (y',x) 
      /\ uniq (stl' ++ str')
      /\ allLu R str' y' (f n.+2) /\ ~ R.+ (f n.+2,y')
      /\ uniq (stl ++ stl')].
  
  Lemma Re2_to_Re1: forall (f: nat -> T) (p q: T2), Re2 f (p,q) -> Re1 f q.
  Proof.
    move => f p q -[stl [x [str [n [stl' [x' [str' [n' [/= _ [-> [H1 H2]]]]]]]]]]].
    move: H2 => [H2 [H3 [H4 [H5 [H6 H7]]]]].
    exists stl'; exists x';exists str';exists n'.
    rewrite H1.
    exact. 
  Qed.
  
  Lemma ARR':exists (v: T2), (v \in [set: T2]).
  Proof. by move: A1 => [v0 _];exists ([::],v0,[::],0);rewrite inP. Qed.
  
  Lemma Asym2P1: 
    (iic (Asym R.+)) -> 
    exists f : nat -> T, exists g: T*T -> seq T, 
      (allLu R (g (f 0,f 1)) (f 0) (f 1) /\ ~ R.+ (f 1, f 0))
      /\
        forall (p : T2), Re1 f p -> exists (t: T2), Re2 f (p,t).
  Proof.
    move => [f Hn]; exists f.
    pose proof (@choose_Rseq T R) as [g H0]; exists g.
    split; first by split;[apply: H0 | move: Hn => /(_ 0) [_ Hn]].
    move => [[stl0 x0] str0] [stl [x [str [n [-> [H1 [H2 H3]]]]]]].
    move: (Hn) => /(_ n.+1) Hn'.
    pose proof (Asym2P H2 H3 Hn')  as [stl' [y' [str' [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
    have H10:  uniq (stl ++ stl') by apply: (uniq_subseq' R H1 H4).
    by exists (stl',y', str',n.+1);exists stl; exists x; exists str;exists n; exists stl'; exists y'; exists str'; exists n.+1.
  Qed.
  
  Lemma Asym2P2: 
    (iic (Asym R.+)) -> 
    exists f : nat -> T, exists g: T*T -> seq T, 
      Re1 f ([::], f 0, g (f 0,f 1),0)
    (* (allLu R (g (f 0,f 1)) (f 0) (f 1) /\ ~ R.+ (f 1, f 0)) *)
      /\ exists h: T2 -> T2, forall (p : T2), Re1 f p -> Re2 f (p,h p).
  Proof.
    move => /Asym2P1 [f [g [H0 H1]]]; exists f; exists g.
    move: H0 => [[H2' H3'] H4'].
    have H5': uniq (g (f 0,f 1))
      by move: H3';rewrite cons_uniq rcons_uniq => /andP [_ /andP [_ ] ].
    split;first by (exists [::]; exists (f 0); exists (g (f 0,f 1)); exists 0).
    pose proof (@Au1_G T2 T2 (Re1 f) (Re2 f) ARR' H1) as [h H2].
    by exists h.
  Qed.

  Lemma Asym2P3: 
    (iic (Asym R.+)) -> exists f : nat -> T, 
      (exists (p0: T2), Re1 f p0) 
      /\ exists h: T2 -> T2, forall (p : T2), Re1 f p -> Re2 f (p,h p).
  Proof.
    move => /Asym2P1 [f [g [H0 H1]]]; exists f. 
    move: H0 => [[H2' H3'] H4'].
    have H5': uniq (g (f 0,f 1))
      by move: H3';rewrite cons_uniq rcons_uniq => /andP [_ /andP [_ ] ].
    split;first by (exists ([::],f 0,g (f 0,f 1),0);exists [::]; exists (f 0); exists (g (f 0,f 1)); exists 0).
    pose proof (@Au1_G T2 T2 (Re1 f) (Re2 f) ARR' H1) as [h H2].
    by exists h.
  Qed.
  
  Fixpoint iterh (h: T2 -> T2) (p0:T2) n : T2 := 
    match n with 
    | 0 => p0
    | S n => h (iterh h p0 n)
    end.
  
  Lemma Asym2P4: 
    (iic (Asym R.+)) -> exists f : nat -> T, exists h: T2 -> T2, exists (p0: T2),
        Re1 f p0 /\ (forall n, Re2 f (iterh h p0 n, iterh h p0 n.+1)).
  Proof.
    move => /Asym2P3 [f [[p0 H0] [h H1]]]. 
    exists f. exists h. exists p0. split. by []. 
    elim; first by rewrite /iterh; apply: H1.
    move => n Hn.
    pose proof Re2_to_Re1 Hn as H2.
    by apply: H1.
  Qed.
  
  Lemma Asym2P5: 
    (iic (Asym R.+)) -> exists k: nat -> T, exists l: nat -> seq T,
        forall n, allLu R (l n) (k n) (k n.+1) /\ ~ R.+ (k n.+1, k n)
             /\ uniq ((l n) ++ (l n.+1)).
  Proof.
    move => /Asym2P4 [f [h [p0 [H0 H1]]]].  
    exists (fun n => (iterh h p0 n).1.1.2).
    exists (fun n => (iterh h p0 n.+1).1.1.1).
    move => n. move: (H1) => /(_ n) H1'.
    move: H1' => [stl [x [str [n1 [stl' [x' [str' [n1' /= [J1 [J2 [J3 HH]]]]]]]]]]]. 
    move: HH => [H4 [H5 [H6 [H7 [H8 H9]]]]].
    move: H1 => /(_ n.+1) H1.
    move: H1 => [stl1 [x1 [str1 [n11 [stl1' [x1' [str1' [n11' /= [K1 [K2 [K3 HH']]]]]]]]]]].
    move: HH' => [H4' [H5' [H6' [H7' [H8' H9']]]]].
    split. by rewrite J2 J1 /=.
    split. by rewrite J2 J1 /=.
    by rewrite K2 K1 /=.
  Qed.

End Infinite_path. 

From Equations Require Import Equations.
From Coq  Require Import Sumbool.

Notation dec x := (sumbool_of_bool x).

Section walk.

  Variables (T:choiceType) (f: nat -> T).
  
  Equations? decode_aux (i row : nat) (p : nat -> nat) : nat* nat  by wf i lt :=
    decode_aux n row p with dec  ((p row).+1 <= n) => {
      | right H0 => (row, n) ;
      | left H0 => decode_aux (n - (p row).+1) (S row) p; 
      }.
  Proof.
    have H1: 0 <= n - (p row).+1 by [].
    rewrite leq_subRL in H1. 
    + rewrite addn0 in H1.
      have H2: 1 <= (p row).+1. by [].
      have H3: 1 <= n. by apply: (leq_trans H2 H1).
      by apply/ltP;rewrite ltn_subrL;apply/andP.
    + by rewrite H0.
  Qed.

  Definition decode (g : nat -> seq T) (i : nat) : nat * nat :=
    decode_aux i 0 (fun n => size (g n)).

  Fixpoint prefix_sum  (g: nat -> seq T) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' => (prefix_sum g n' + (size (g n')).+1)
    end.

  Definition encode (g : nat -> seq T) (row col : nat) : nat :=
    (prefix_sum g row + col)%N.

  Variables (a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 :T).
  
  Definition G n := 
    match n with 
    | 0 => [:: b1 ; c1 ; d1]
    | 1 => [:: f1 ; g1]
    | _ => [:: i1]
    end.

  Definition F n := 
    match n with 
    | 0 => a1
    | 1 => e1
    | _ => h1
    end.
  
  Compute decode G 0.
  Compute decode G 1.
  Compute decode G 2.
  Compute decode G 3.
  Compute decode G 4.
  
  Definition Val n p := 
    match p with
    | 0 => F n
    | S p => nth (F 0) (G n) p
    end.
  
  Compute Val 0 0.
  Compute Val 0 1.
  Compute Val 0 2.
  Compute Val 0 3.
  Compute Val 1 0.
  Compute Val 1 1.

  Definition val n := 
    let (p,q):= decode G n in Val p q.
  
  Compute val 0.
  Compute val 1.
  Compute val 2.
  Compute val 3.
  Compute val 4.
  Compute val 5.
  Compute val 6.
  Compute val 7.
  Compute val 8.

End walk.

  
