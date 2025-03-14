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
From mathcomp Require Import all_ssreflect seq order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets order.
Set Warnings "parsing coercions".

From RL Require Import  seq1 ssrel rel.

Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "A [<=] B" (at level 4, no associativity). 
Reserved Notation "A [<= R ] S" (at level 4, no associativity). 

Section Asym. 
  (** * Antisymmetric part of a relation *) 
    
  Variables (T:Type).
  
  Definition Asym (S: relation T) :relation T := [set xy | S xy /\ ~ (S.-1 xy)].
  
  Lemma Asym_transitive: forall (S: relation T), transitive S -> transitive (Asym S).
  Proof.
    move => S H0 x y z [H1 /= H1'] [H2 /= H2'];split => [ | /= H3].
    by apply: H0 H1 H2.
    by have: S (y,x) by apply: H0 H2 H3.
  Qed.

  Lemma Asym_antisymmetric: forall (S: relation T), antisymmetric  (Asym S).
  Proof. by move => S x y [_ ?] [? _]. Qed.

  Lemma Asym_irreflexive: forall (S : relation T), 
    forall x y : T, (Asym S) (x,y) -> x = y -> False.
  Proof. by move => S x y /[swap] -> [? ?]. Qed.

End Asym.

Section Independent_set.
  (** * Independence of sets with respect to a relation *)
  
  Variables (T: Type).

  (* begin snippet RelIndep:: no-out *)    
  Definition RelIndep (U: relation T) (S: set T) :=
    forall (x y:T),  x \in S -> y \in S -> ~(x = y) -> ~( U (x,y)).
  (* end snippet RelIndep *)    

  Lemma RelIndep_I: forall (V U: relation T) (S: set T),
      V `<=` U -> RelIndep U S -> RelIndep V S.
  Proof.
    move => V U S H1; rewrite /RelIndep => H2 x y H3 H4 H5 H6.
    pose proof (H2 x y) H3 H4 H5.
    by have H7: U (x, y) by apply H1 in H6.
  Qed.
  
  Lemma RelIndep_set0 (U: relation T): RelIndep U set0.
  Proof. by move => x y /inP H3 _ _ _. Qed.
  
  Lemma RelIndep_set1 (U: relation T): forall (x: T), RelIndep U [set x].
  Proof. by move => x x1 x2 /inP -> /inP -> H4. Qed.
  
End Independent_set.

Section Set_Order. 
  (** * Order relation on sets based on a relation on elements *)

  Variables (T: choiceType).

  (* begin snippet leset:: no-out *)    
  Definition leset (U: relation T) (A B: set T):= forall (a:T),
      (a \in A) -> exists b, b \in B /\ ( a = b \/ U (a,b)). 
  
  Definition leSet (U: relation T): relation (set T) := (uncurry (leset U)). 
  
  Notation "A [<= R ] B" := (leSet R (A,B)).
  (* end snippet leset *)       

  Lemma Ile: forall (U: relation T) (A B: set T), A `<=` B -> A [<= U] B.
  Proof. by move => U A B H1 /= => [s /inP/H1 H2];exists s;split;[rewrite inP|left]. Qed.
  
  (** (leset U) is a partial order on Independent Sets  *)
  Lemma le_trans (U: relation T): transitive U -> transitive (leSet U).
  Proof.
    move => H0 A B C /= => [H1 H2]. 
    move => r /= /H1 /= [s [H3 [-> | H4]]].
    by move: H3 => /H2 /= [u [H4 [-> | H5]]];(exists u);split;[| left| |right].
    move: H3 => /H2 /= [u [H6 [H7 | H7]]].
    by (exists u);split;[|right;rewrite -H7].
    (exists u);split;first by []. 
    right. apply: H0 H4 H7.
  Qed.
  
  Lemma le_refl (U: relation T): reflexive (leSet U).
  Proof.
    by move => A;rewrite /leset /mkset /= => r /= H1;exists r;split;[| left].
  Qed.
  
  (* here we need the choiceType *)
  Lemma le_antisym_l1 (V U: relation T): 
    transitive U -> U `<=`V
    -> forall A B, (RelIndep V A) -> A [<= (Asym U)] B -> B  [<= (Asym U)] A -> A `<=` B.
  Proof.
    move => H0 H0' A B H1 H2 H3 a H4.
    move: (H4) => /inP /H2 [b [/inP H5 [-> // | [H6 H6']]]]. 
    move: (H5) => /inP /H3 /= [c [/inP H8 H9]].
    case H10: (a == b ); first by move: H10 => /eqP ->.
    move: H10 => /eqP H10.
    case H12: (b == c).
    - move: H12 H8 => /eqP <- H8.
      have H11: V (a,b) by apply H0' in H6.
      by have: False by move: H4 H8 => /inP H4 /inP H8;apply: (H1 a b). 
    - move: H12 H9 => /eqP H12 [H9 // | [H9 H9']].
      case H13: (a == c); first by move: H13 H9' => /eqP <- H9'.
      have H14: U (a,c) by apply: H0 H6 H9.
      have H15: V (a,c) by apply H0' in H14.
      by have: False by move: H13 H4 H8 => /eqP H13 /inP H4 /inP H8; apply: (H1 a c). 
  Qed.
  
  Lemma le_antisym (V U: relation T): 
    transitive U -> U `<=`V 
    -> forall A B, (RelIndep V A) -> (RelIndep V B) 
             -> A [<= (Asym U)] B -> B  [<= (Asym U)] A -> A = B.
  Proof.
    move => H0 H0' A B H1 H2 H3 H4.
    by move: (le_antisym_l1 H0 H0' H1 H3 H4)
            (le_antisym_l1 H0 H0' H2 H4 H3);rewrite eqEsubset.
  Defined.
  
End Set_Order.

(** Notation for the set order we use *)
Notation "A [<= R ] B" := (leSet R (A,B)).

Section Paper.
  (** Proofs of the results of the paper 
   *  On Monochromatic Paths in Edge-Coulured Digraphs *)
  Variables (T:choiceType) (Eb Er: relation T).

  Section Paper_Notations. 
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
  
    Fixpoint IterCh (C: set SType) (f: Elt C -> Elt C) k (x: Elt C) := 
      match k with 
      | 0 => x 
      | S m => f (IterCh f m x)
      end. 
  
  End Paper_Notations. 

  (* begin snippet Rloop:: no-out *)    
  Definition Rloop (S: relation T) := exists v, forall w,  S (v,w) -> S (w,v).
  (* end snippet Rloop *)
  (* total (or left total)  *) 
  Definition total_rel (S: relation T) := forall x, exists y, S (x,y).
  (** infinite sequence *)
  Definition iic (U: relation T) := exists f : nat -> T, forall n, U ((f n),(f (S n))).  
  
  (** * axiom of dependent choice *) 
  Axiom DC: forall (S: relation T),  total_rel S -> iic S. 
  
  (** * The Assumptions we use: weaker than the paper assumptions 
   *  ~ (iic Er.+) and ~ (iic Eb.+)
   *)
  
  (* begin snippet Assumptions:: no-out *)    
  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  Hypothesis A3: ~ (iic (Asym Er.+)). 
  Hypothesis A4: ~ (iic (Asym Eb.+)). 
  (* end snippet Assumptions *)    
  
  Lemma notiic_rloop: forall (S: relation T), ~ (iic (Asym S)) -> (Rloop S).
  Proof.
    move => S; apply contraPP => H1.
    have H2:  total_rel (Asym S)
      by move: H1;rewrite -forallNE => H1 v;move: H1 => /(_ v)/existsNP [w /not_implyP H1];exists w.
    by move: H2 => /DC H2.
  Qed.
  
  (* begin snippet RloopErp:: no-out *) 
  Lemma A2: Rloop Er.+.
  Proof. by apply: notiic_rloop. Qed.
  (* end snippet RloopErp *)    
  
  Lemma notiic_noinf: ~ (iic (Asym Eb.+)) ->
               forall (C: set SType) (f: Elt C -> Elt C ) (s: Elt C), 
                 ~ ( forall n, (Asym Eb.+) (sval (IterCh f n s),sval (IterCh f n.+1 s))). 
  Proof.
    apply: contra_notP.
    rewrite -existsNP => [[C H1]].
    move: H1; rewrite -existsNP => [[f H1]].
    move: H1; rewrite -existsNP => [[s H1]].
    move: H1 => /contrapT H1.
    by exists (fun n => (sval (IterCh f n s))).
  Qed.

  Lemma NoInf: forall (C: set SType) (f: Elt C -> Elt C ) (s: Elt C), 
      ~ ( forall n, (Asym Eb.+) (sval (IterCh f n s),sval (IterCh f n.+1 s))).
  Proof. by apply: notiic_noinf. Qed.
  
  Lemma S2Scal: forall (S: SType), (proj1_sig S) \in Scal.
  Proof. by move => [S [H1 [H2 H3]]];rewrite inP. Qed.

  Lemma Scal2S: forall S, S \in Scal -> exists (S': SType), (proj1_sig S') = S.
  Proof. by move => S /inP H1; exists (exist _ S H1). Qed.
  
  (* begin snippet Scalnotempty:: no-out *) 
  Lemma Scal_not_empty: exists v, Scal [set v].
  (* end snippet Scalnotempty *)
  Proof.
    have H2': Er.+ `<=` Mono by apply:  subsetUr.
    move: A2 => [v H1]; exists v.
    split;first by rewrite /RelIndep;move => x y /inP /= -> /inP /= ->.
    split;first by move => t [y [/= H3 H4]];move: H3; rewrite H4 /= => /H1/H2' H3;exists v.
    by rewrite -notempty_exists;(exists v);rewrite inP.
  Qed.
    
  Lemma SType_not_empty: (@setT SType) != set0.
  Proof.
    rewrite -notempty_exists;move: Scal_not_empty => [v H2].
    by exists (exist _ [set v] H2);rewrite inP.
  Qed.
  
  Definition leSet1 (AB: SType*SType) :=
    leset (Asym Eb.+) (proj1_sig AB.1) (proj1_sig AB.2).
    
  Lemma leSet1_transitive: @transitive SType leSet1.
  Proof. by move => [A ?] [B ?] [C ?]; apply/le_trans/Asym_transitive/t_trans. Qed.
  
  Lemma leSet1_reflexive: @reflexive SType leSet1.
  Proof. by move => [A ?];apply: le_refl. Qed.

  Axiom proof_irrelevance: forall (P : Prop) (p q : P), p = q.
  
  Lemma leSet1_antisymmetric: @antisymmetric SType leSet1.
  Proof. 
    move => [A Ha] [B Hb] H1 H2.
    move: (Ha) (Hb) => [Ha' Ha''] [Hb' Hb''].
    have H3: Eb.+ `<=` Mono by apply: subsetUl.
    have H4: transitive Eb.+ by apply: t_trans. 
    move: (le_antisym H4 H3 Ha' Hb' H1 H2) => H5.
    subst A. (** why I cannot use rewrite *)
    apply: f_equal.
    apply: proof_irrelevance.
  Qed.
  
  (** * The relation on sets restricted to Stype subsets *)
  Notation "A [<=] B" := (leSet1 (A,B)).
  
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
  
  Section Sinf_properties.
    (** * Properties of Sinf C for a nonempty Chain C *)
    
    Variables  (C: set SType).
    Hypothesis Hc: C \in Chains. 
    Hypothesis Hne: C != set0.
    
    Definition Ec := Elt C.

    (* Set Sinf associated to a chain *)
    Definition Sinf := 
      [ set v: T | 
        exists (S: SType), (S \in C) /\ (v \in (sval S))
                      /\ (forall (T: SType), T \in C -> S [<=] T -> v \in (sval T))].
    
    Definition RC:= [set xy:Ec*Ec |
                      ((sval xy.1) \in Sinf /\ xy.2 = xy.1)
                      \/ (~ ((sval xy.1) \in Sinf) /\ (Asym Eb.+) (sval xy.1, sval xy.2))].
    
    Lemma ChnotE: exists _ : Elt C, True.
    Proof.
      move: (Elt_not_empty Hc Hne) => [S [H2 [x H3]]].
      have H4: exists (S: SType), S \in C /\ x \in (sval S) by (exists S).
      by exists (exist _ x H4).
    Qed.
    
    Lemma ChnotE_witness: Elt C.
    Proof. by apply: inhabited_witness; rewrite inhabitedE; apply: ChnotE. Qed.
    
    (* Sinf is an independent set *)
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
      (* Ec_seq: forall (s: Ec), exists (s1: Ec), RC (s, s1) *)
      
      Lemma Ec_seq1: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, S1 \in C /\ S [<=] S1 /\ ~ (s \in (sval S1)).
      Proof.
        move: Hc => H1 S s H2 H3. 
        apply contraPP;rewrite not_existsP 2!notE => H4.
        rewrite inP /Sinf; exists S.
        have H5: forall x: SType, x \in C -> S [<=] x -> s \in (sval x)
                by move => x H5 H6;
                          move: (H4 x) => /not_andP [H7 //|/not_andP [// | H7]];
                                         rewrite notE in H7.
        exact.
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
      
      Lemma Ec_seq: forall (s: Ec), exists (s1: Ec), RC (s, s1).
      Proof.
        move => s.
        case H3: ((sval s) \in Sinf); first by (exists s); left.
        have H4: ~ ((sval s) \in Sinf) by move => H5;rewrite H5 in H3.
        move: (Ec_seq3 H4) => [s1 H5].
        by exists s1; right.
      Qed.

    End Ec_seq.
    
    Lemma ChooseRC_fact1: forall f s,
        ~ ((sval s) \in Sinf) -> RC (s, f s) -> (Asym Eb.+) (sval s, sval (f s)).
    Proof. by move => f s H2 [[H3 _]// | [_ H3]].  Qed.
    
    Lemma ChooseRC_fact2: forall f s, 
        ~ ((sval (f s)) \in Sinf) -> RC (s,f s) -> ~ ((sval s) \in Sinf).
    Proof. by move => f s H2 [/=[H3 H4]|/= [H3 [H4 H5]]];[rewrite -H4 in H3 |]. Qed.
    
    Lemma IterChP: forall k f (x:Ec), IterCh f k.+1 x = f (IterCh f k x).
    Proof. by elim. Qed.
    
    Lemma ChooseRC_fact3: forall f s, 
        (forall s, RC (s,f s)) 
        ->forall n,
          (forall k, k < n.+1 -> ~((sval (IterCh f k s)) \in Sinf))
          -> (Asym Eb.+) (sval (IterCh f 0 s),sval (IterCh f n.+1 s)).
    Proof. 
      move => f s H2.
      elim => [H3 |n Hr H3]. 
      + have H4: ~((sval (IterCh f 0 s)) \in Sinf) by apply H3.
        by move: H2 H4 => /(_ (IterCh f 0 s)) [/= [-> _] // | /= [H2 [H5 H6]]].
      + have: forall k : nat, k < n.+1 -> ~ ((sval (IterCh f k s)) \in Sinf )
            by move => k H5;apply: H3;(have H6: k < k.+1 by apply ltnSn);
                      apply: ltn_trans H6 _;
                      rewrite -addn1 addnC -[n.+2]addn1 [n.+1 + 1]addnC (ltn_add2l 1). 
        move => /Hr H4.
        have H5: ~((sval (IterCh f n.+1 s)) \in Sinf) by apply H3;apply ltnSn.
        have H6: (Asym Eb.+) ((sval (IterCh f n.+1 s),(sval (IterCh f n.+2 s))))
          by move: ChooseRC_fact1 => /(_ f) H6;apply: H6. 
        have H7: transitive (Asym Eb.+) by apply/Asym_transitive/t_trans.
        by apply: H7 H4 H6.
    Qed.
    
    Lemma ChooseRC_fact4: forall f s,
        (forall (s:Ec), RC (s,f s))
        ->forall n,
          ~((sval (IterCh f n s)) \in Sinf)
          -> (forall k, k < n.+1 -> ~ sval (IterCh f k s) \in Sinf).
    Proof.
      move => f s H2.
      elim => [H3 k H4| n Hn H3 k H4].
      + case H5: (k == 0); first by move: H5 => /eqP ->.
        move: H5 => /eqP H5.
        by move: H4 => /ltnSE H4; move: H4; rewrite leqn0 => /eqP H4.
      + case H5: (k == n.+1);first by move: H5 => /eqP ->.
        have H6: k < n.+1 by move: H4 => /ltnSE H4;rewrite leq_eqVlt H5 /= in H4.
        have H7: ~ sval (IterCh f n s) \in Sinf
            by move: H3; rewrite IterChP => /ChooseRC_fact2 H3;apply H3.
        by apply Hn.
    Qed.
    
    Lemma ChooseRC: forall f, 
        (forall s, RC (s,f s))
        -> (forall (s:Ec),
              (forall n, ~((sval (IterCh f n s)) \in Sinf))
              -> forall n, (Asym Eb.+) (sval (IterCh f n s),sval (IterCh f n.+1 s))).
    Proof.
      by move => f H2 s H3 n;rewrite IterChP;apply: ChooseRC_fact1.
    Qed.
    
    Lemma ChooseRC2: forall f, 
        (forall s, RC (s,f s))
        ->(forall (s:Ec), ~ (forall n, ~((sval (IterCh f n s)) \in Sinf))).
    Proof.
      by move => f H2 s H3;move: (ChooseRC H2 H3) (@NoInf C) => H4 /(_ f s) H5.
    Qed.

    Lemma ChooseRC3: forall f,
        (forall s, RC (s, f s))
        -> (forall (s:Ec), exists n, ((sval (IterCh f n s)) \in Sinf)).
    Proof.
      move => f H2 s. 
      move: (ChooseRC2 H2) => /(_ s) /existsNP [k /contrapT H3].
      by exists k.
    Qed.
    
    Lemma ChooseRC4: forall f,
        (forall s, RC (s,f s))
        -> (forall (s:Ec), 
            exists n, ((sval (IterCh f n s)) \in Sinf)
                 /\ (forall k, k < n -> ~((sval (IterCh f k s)) \in Sinf))).
    Proof.
      move => f H2 s.
      move: (ChooseRC3 H2) => /(_ s) [k H3].
      elim: k H3 => [H3|n Hn H3]; first by (exists 0).
      case H4: (sval (IterCh f n s) \in Sinf );
        first by move: H4 => /Hn [n1 H4];exists n1.
      by exists n.+1;split;[ | apply: ChooseRC_fact4;[| rewrite H4]].
    Qed.
    
    Lemma ChooseRC5: forall (s:Ec),
        (sval s \in Sinf) \/ exists s',  s' \in Sinf /\ (Asym Eb.+) (sval s, s').
    Proof. 
      have [f H2]:exists f: Ec -> Ec, forall (s:Ec), (curry RC) s (f s) 
          by pose proof Ec_seq;apply: choice.
      move => s.
      move: ((ChooseRC4 H2) s) => [n [H3 H4]]. 
      case H5: (n == 0); first by move: H5 H3 => /eqP ->;left.
      right. 
      move: H5;rewrite eqn0Ngt => /negP/contrapT H5.
      have H6: n.-1.+1 = n by apply: (ltn_predK H5).
      move: (((@ChooseRC_fact3 f s) H2) n.-1); rewrite H6 => H7.
      move: H4 => /H7 /= H4.
      by exists (sval (IterCh f n s)).
    Qed.
    
    Lemma ChooseRC6: forall (S: SType), (S \in C) -> (sval S) [<= (Asym Eb.+)] Sinf.
    Proof. 
      move => S H2 s /= H3.
      have H4: exists (S: SType), S \in C /\ s \in (sval S) by (exists S).
      move: (ChooseRC5 (exist _ s H4)) => /= [H5 | [s' [H5 H6]]].
      by (exists s);split;[|left].
      by (exists s');split;[|right].
    Qed.
    
    Lemma Sinf_ne: Sinf != set0.
    Proof.
      move: ChnotE => [s _];rewrite -notempty_exists.
      by move: (ChooseRC5 s) => [H1 | [s' [H1 _]]];[exists (sval s) | exists s'].
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
      + exists tinf. 
        split. 
        left.
        apply: (t_trans H18 H21).
        by rewrite -inP.
    Qed.
     
    Lemma Sinf_Scal: Sinf \in Scal. 
    Proof.
      rewrite inP;split;[apply: Sinf_indep|split;[apply: Sinf_ScalP|apply: Sinf_ne]].
    Qed.
    
    Lemma Sinf_final: exists Si, forall (S: SType), C S -> S [<=] Si.
    Proof.
      move: Sinf_Scal => /inP H2;exists (exist _ Sinf H2);move => S /inP H3. 
      by apply: ChooseRC6.
    Qed.
    
  End Sinf_properties.
  
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
    move: H3 => /Chains_is_total H3. apply Sinf_final in H3.
    move: H3 => [Si H3].
    exists Si. move => S /H3 H4. by rewrite asboolE.
    by [].
    move: H1 => /negP/contrapT/eqP H1. 
    move: SType_not_empty => /notempty_exists [Sm Ht].
    by exists Sm; move => S; rewrite H1 -inP in_set0. 
  Qed.

  Lemma SmaxZ: exists Sm, forall S, (curry leSet1) Sm S -> S = Sm.
  Proof.
    move: SmaxZ_new => [Sm H1]. 
    exists Sm. move => S.
    move: H1 => /(_ S) H1. by rewrite asboolE in H1.
  Qed.
  
  (** 
  Lemma SmaxZ: exists Sm, forall S, (fun x y => `[< (curry leSet1) x y >]) Sm S -> S = Sm.
  Proof.
    apply: Zorn.
    move => t; rewrite asboolE; by apply leSet1_reflexive.
    move => r s t; rewrite 3!asboolE; by apply leSet1_transitive.
    move => s t;rewrite 2!asboolE; by apply leSet1_antisymmetric.
    move => A.
    case H1: (A != set0); first by move => /Chains_is_total H2;apply: Sinf_final.
    move: H1 => /negP/contrapT/eqP -> => H2. 
    move: SType_not_empty => /notempty_exists [Sm Ht].
    by exists Sm; move => S; rewrite -inP in_set0. 
  Qed.
  *)
  
  (** * back to set T *)
  Lemma Exists_Smax: exists Sm, Sm \in Scal /\ forall T, T \in Scal -> Sm [<= (Asym Eb.+)] T -> T = Sm.
  Proof.
    move: SmaxZ => [Sm H1];exists (sval Sm); split; first by  apply: S2Scal.
    by move => S /Scal2S [S' <-] H3; f_equal;by apply H1.
  Qed.
  
  Section Maximal. 
    (** * We show that A maximal set is a solution *)
    
    Variable (Sm: set T).

    Definition IsMaximal (S: set T):= S \in Scal /\ forall T, T \in Scal -> S [<= (Asym Eb.+)] T -> S = T.
    
    Definition Sx:= [set y | ~ (y \in Sm) /\ ~ (y \in Mono#Sm)].
  
    Definition Tm x:= [set y | y \in Sm /\ ~ (Eb.+ (y,x))].

    Lemma TmI: forall x, Tm x `<=` Sm.
    Proof. by move => x y [/inP H2 _]. Qed.
  
    Lemma Sb: forall x z, x \in Sx -> z \in Sm -> ~ (z \in (Tm x)) -> Eb.+ (z,x).
    Proof.
      move => x z /inP [H2 H2'] H3 H4.
      have H5: z \in (Tm x) <-> z \in Sm /\ ~ (Eb.+ (z,x)) by rewrite inP. 
      move: H4; rewrite H5 not_andP => [[H4 // | /contrapT H4 //]].
    Qed.
    
    Lemma Sb1: forall x, x \in Sx -> forall z, z \in Sm `\` (Tm x) -> Eb.+ (z,x).
    Proof.
      by move => x H2 z /inP [/inP H3 H4];apply: Sb;[ | | move=> /inP H5].
    Qed.

    Definition Sxm x := forall y, y \in Sx -> Er.+(x,y) -> Er.+(y,x).
    
    Lemma fact: IsMaximal Sm -> (forall t, t\in Sm:#(Er.+) -> t \in Mono#Sm).
    Proof. by move => Smax t H3;move: Smax H3 => [/inP [_ [H8 _]] _] /inP/H8 H3;rewrite inP. Qed.
    
    Lemma fact0: IsMaximal Sm -> (forall x, x \in Sx -> ~ (x \in (Sm:#(Er.+)))).
    Proof. by move => Smax x /inP [_ ?] /(fact Smax) ?. Qed.
    
    Lemma fact1: forall x y, y \in Sm -> ~(y \in (Tm x)) -> Eb.+ (y,x).
    Proof. by move => x y H3;rewrite inP not_andE => [[? // | /contrapT ? //]]. Qed.
    
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

    Lemma fact5_1: forall X x, RelIndep Mono X -> ~(x \in Mono#X) -> ~(x \in (X:#Mono))
                          -> RelIndep Mono (X `|` [set x]).
    Proof.
      move => X x H2 H3 H4 x1 x2 /inP [/inP H5 | /inP H5] /inP [/inP H6 |/inP H6] H7 H8.
      rewrite /RelIndep in H2.
      + by apply: ((H2 x1 x2) H5 H6 H7 H8).
      + move: H6 H4 => /inP <- H4. 
        by have H9: x2 \in X:#Mono by rewrite inP;exists x1; rewrite inP in H5.
      + move: H5 H3 => /inP <- H3. 
        by have H9: x1 \in Mono#X by rewrite inP;exists x2;rewrite inP in H6.
      + by move: H5 H6 H7 => /inP -> /inP ->. 
    Qed.
    
    Lemma fact5: IsMaximal Sm -> (forall x, x \in Sx -> RelIndep Mono ((Tm x) `|` [set x])).
    Proof.
      by move => Smax x H2;apply: fact5_1;[apply: fact2|apply: fact3|apply: fact4].
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
      by move => x X Y R /inP [y [H2 [H3| H3]]];[left | right];rewrite inP;exists y.
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
          move: H14 => /(Sb1 H2) H14.
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
          move: (((Sb1 H2) z1) H11) => H12.
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
          move: H14 => /(Sb1 H2) H14.
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
          move: (((Sb1 H2) z1) H11) => H12.
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
    
    (** * an other version of no infinite paths *)
    Definition ZNoInf1:= forall x, x \in Sx -> Sxm x. 
      
    Lemma fact13: IsMaximal Sm -> ZNoInf1 -> ~ (exists x, x \in Sx).
    Proof.
      move => Smax NoInf1 [x H1].
      move: (H1) => /NoInf1 H2.
      by apply: (fact12' Smax H1).
    Qed.
    
    Lemma fact14: IsMaximal Sm -> ZNoInf1 -> (forall x, ~ (x\in Sm) -> (x \in Mono#Sm)).
    Proof.
      move => Smax NoInf1 x H1. 
      move: (fact13 Smax NoInf1) => /forallNP /(_ x) H2.
      have H3: ~ (x \in Sx) <-> (x \in Sm) \/ (x \in Mono#Sm) by rewrite inP not_andE 2!notP.
      by move: H2 => /H3 [H2 | H2].
    Qed.
      
  End Maximal. 
  
  (** XXX A justifier: doit se déduire des autres hypothèses *)
  Hypothesis NoInf1: forall S x, x \in (Sx S) -> (Sxm S) x. 
  
  Theorem Paper: exists Sm, forall x, ~ (x\in Sm) -> (x \in Mono#Sm). 
    Proof.
      move: Exists_Smax => [Sm [H1 H2]]. 
      have H3: IsMaximal Sm. 
      split => [// |U H3 H4].
      by have ->: U = Sm by apply: H2 H3 H4.
      exists Sm. move => x; apply: fact14.
      by [].
      apply: NoInf1.
    Qed.
    
End Paper.

Section Seq1_plus. 
  (** * extensions of results from seq1 and rel using eqType *)

  Variables (T:eqType) (R: relation T).

  (** * utilities for uniq *)
  Lemma uniq_subseq: forall (st st': seq T) (x:T),
      uniq (x :: st) -> subseq st' st -> uniq (x:: st').
  Proof.
    move => st st' x;rewrite /uniq -/uniq => /andP [H2 H3] H4.
    have -> : uniq st' by apply subseq_uniq with st.
    rewrite andbT.
    move: H4 => /subseqP [m H4 H5].
    have H6: x \in st' -> x \in st by rewrite H5; apply: mem_mask.
    move: H6 => /contra H6.
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
    by move: (allset_in H2 H4);rewrite inP -Fset_t0. 
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
    elim => [x y z H1 H2 // | t st Hr x y z H1 H2].
    case H3: (t == z). 
    + rewrite /drop //= H3 -/drop drop0.
      move: H3 => /eqP H3.
      by move: H2;rewrite H3 allL_c => /andP [_ H2'].
    + rewrite /drop //= H3 -/drop.
      apply Hr with t.
      - move: H1; rewrite in_cons => /orP [/eqP H1| H1].
        by move: H3; rewrite H1 => /eqP H3.
        by [].
      - by move: H2; rewrite allL_c => /andP [_ H2]. 
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
    move => st1 st2 x H1.
    apply contraPP.
    move => /contrapT H2 H3.
    have H4:  x \in st2. by apply in_subseq' with st1.  
    by [].
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
  
  Lemma TCP_uniq': forall (x y:T), 
      R.+ (x,y) 
      -> ~ ( R.+ (y,x))
      -> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y H1 H2. 
    move: (H1) => /TCP_uniq [st [H3 [H4 [H5 H6]]]].
    have H7: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    have H8: uniq (rcons st y)
      by move: H4 => /negP H4;rewrite rcons_uniq H4 H5. 
    have H9: x \in (rcons st y) -> False
        by rewrite -[rcons st y]cats0 cat_rcons mem_cat mem_seq1
         => /orP [ H9 | /eqP H9].
    have H10: uniq (x :: rcons st y) by rewrite /uniq -/uniq;
      move: H9 => /negP H9;rewrite H8 andbT.

    by exists st.
  Qed.

End allL_uniq.

Section Hn.
  (** * some Lemmata around infinite outward R-path *) 
  
  Variables (T:choiceType) (R: relation T).
    
  Definition Rp1 (x y:T) := 
    exists st, st [\in] R.+#_(x) /\ uniq (x::(rcons st y)) 
          /\ (x::(rcons st y)) [L\in] R /\ ~ (R.+ (y,(last x st))).
  
  Definition R1 := [set xy | Rp1 (fst xy) (snd xy)].
  
  Definition R3' := [set xy | R.+ xy /\ ~ (R.+ (xy.2,xy.1))].
  
  (* utility lemma *)
  Lemma RedBack: forall (st:seq T) (x y:T),
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

  Definition R4 := [set xyz: (T*T)*T | 
                     R3' (xyz.1.1, xyz.1.2) /\ R1 (xyz.1.1, xyz.2) 
                     /\ (xyz.1.2= xyz.2\/ R.+(xyz.2, xyz.1.2)) ].
  
  Lemma RedBackF: forall (x y:T), R3' (x,y) -> exists z, R4 ((x,y),z).
  Proof.
    move => x y [H1 /= H2].
    pose proof TCP_uniq' H1 H2 as [st [H3 H4]]. 
    pose proof RedBack H4 H3 H2 as [st' [y' [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]].
    by exists y';split;[ | split;[exists st' |]].
  Qed.
  
  Definition R5:= [set  xyz: (T*T)*T| ~ (R3' (xyz.1.1, xyz.1.2)) \/ ( R4 xyz)].
  
  Lemma RedBackF1:  forall (x y:T), exists z, z \in [set u| R5 ((x,y),u)].
  Proof. 
    move => x y.
    case H1: ((x,y) \in R3').
    by move: H1=> /inP H1;move: (RedBackF H1) => [z H2];exists z;rewrite inP /R5; right.
    exists x; rewrite inP /R5; left => /inP H2.
    by rewrite H2 in H1.
  Qed.
  
  Definition g (x y:T) := xchoose (RedBackF1 x y).

  Lemma gP: forall x y, (g x y) \in [set u| R5 ((x,y),u)].
  Proof. by move => x y; apply: xchooseP. Qed.
  
  Lemma gP1: forall y z t, R3'(y,z) -> R3' (z,t) -> R3' (g y z, t).
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
  
  Axiom IR: forall k, R3' (Iterf k x0, Iterf k.+1 x0).
  
  Lemma IR1: forall k, let xy := (Iterh k (x0,f x0)) in 
                  R.+ xy /\ R3' (g xy.1 xy.2, f xy.2).
  Proof.
    elim. 
    rewrite /Iterh /h /=; move: (IR 0) => /= [ H1 _].
    split.  by [].
    move: (gP x0 (f x0)) => /inP [/=  H2 | H2].
    move: H2; rewrite not_andE => [[H2 | /=/contrapT H2]].
    by [].
    rewrite /R3' /mkset /=.
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
    exists st,  size(st) = n /\ (x::(rcons st y)) [L\in] R3'.

  Definition R4 (n:nat):= [set xy | Rp4 xy.1 xy.2 n].


  Lemma Rpath: forall (n:nat) (x y:T),
      R4 n (x,y) -> exists y', R2 n (x,y') /\ (y=y' \/ R.+(y',y)).
  Proof.
    elim. 
    + move => x y.
      rewrite /R4 /Rp4 /mkset => [[st [/size0nil -> H2]]].
      move: H2; rewrite /= andbT /R3' inP /mkset /= => [[H3 H4]].
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
      by exists v0,v1;exists [::]; split;[| rewrite /= andbT inP /R3'].
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

End Hn.
