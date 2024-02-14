(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From AAC_tactics Require Import AAC.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets order.
Set Warnings "parsing coercions".

From RL Require Import  seq1 ssrel rel erel3 aacset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "R [Set<=] S" (at level 4, no associativity). 

Section Paper.

  Variables (T:Type) (Eb Er: relation T).

  Definition Bpath := [set xy | Eb.+ (xy.1, xy.2) \/ Eb.+ (xy.2,xy.1)].
  Definition Rpath := [set xy | Er.+ (xy.1, xy.2) \/ Er.+ (xy.2,xy.1)].
  Definition Mpath := [set xy | Bpath (xy.1, xy.2) \/ Rpath (xy.1, xy.2)].

  Definition Independent (S: set T):= (S`*`S) `&` Mpath = set0.

  Definition leset (S R: set T):= 
    forall (s:T), s \in S -> exists r, r \in R /\ ( s = r \/ ((Eb.+ (s,r) /\ ~(Eb.+ (r,s))))).

  Definition leSet := [set SR | (leset SR.1 SR.2)].

  Notation "S [Set<=] R" := (leSet (S,R)).
  
  Lemma Ile: forall (R S: set T), R `<=`S -> R [Set<=] S.
  Admitted.
  
  Definition IndependentSets := [set S | Independent S].

  (** * [Set<=] is a partial order on IndependentSets  *)

  Lemma le_trans: transitive leSet.
  Proof.
    move => R S U.
    rewrite /leset /mkset /= => [H1 H2].
    move => r /= /H1 /= [s [H3 [-> | [H4 H5]]]].
    by move: H3 => /H2 /= [u [H4 [-> | [H5 H6]]]];(exists u);split;[| left| |right].
    move: H3 => /H2 /= [u [H6 [H7 | [H7 H8]]]].
    by (exists u);split;[|right;rewrite -H7].
    (exists u);split;first by []. 
    right;split. 
    by (have H9: (Eb.+ `;` Eb.+) (r,u) by (exists s));apply clos_tI.
    move => H9.
    have H10: (Eb.+ `;` Eb.+) (s,r) by (exists u).
    have H11: Eb.+ (s,r) by apply clos_tI.
    by [].
  Qed.
  
  Lemma le_refl: reflexive leSet.
  Proof.
    by move => R;rewrite /leset /mkset /= => r /= H1;exists r;split;[| left].
  Qed.

  Lemma Indep_F: forall S  (s s':T),
      IndependentSets S -> S s -> S s' -> (Eb.+) (s,s') -> False.
  Proof.
    move => S s s' H1 H2 H3 H4.
    have H5: Mpath (s,s') by left;left.
    have H6: ((S`*`S) `&` Mpath) (s,s') by [].  
    have H7: exists z, z \in (S `*` S `&` Mpath) by (exists (s,s'));rewrite inP.
    rewrite /IndependentSets /Independent /mkset empty_notexists in H1.
    by [].
  Qed.
  
  Lemma le_antisym: forall R S, 
      (S \in IndependentSets) -> R [Set<=] S -> S  [Set<=] R -> S `<=` R.
  Proof.
    move => R S;rewrite inP /IndependentSets /leset /mkset /= => [H1 H2 H3 s H4].
    move: (H4) => /inP /H3 /= [r [/inP H5 [-> // | [H6 H7]]]]. 
    move: (H5) => /inP /H2 /= [s' [/inP H8 [H9 | [H9 H10]]]].
    - rewrite H9 in H6.
      by pose proof Indep_F H1 H4 H8 H6.
    - have H11: (Eb.+ `;` Eb.+) (s,s') by (exists r).
      have H12: Eb.+ (s,s') by apply clos_tI.
      by pose proof Indep_F H1 H4 H8 H12.
  Qed.
  
  Definition ScalP (S: set T) := 
    forall s, s \in S -> exists t, Er.+ (s,t) -> exists s', s' \in S /\ Mpath (t,s').
  
  Definition Scal := [ set S | Independent S /\ ScalP S].

  Lemma Scal_notempty: Scal != set0.
  Admitted.

  


End Paper.




  
    

