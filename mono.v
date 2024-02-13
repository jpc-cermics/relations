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

  Definition leset := [set RS | RS.1 `<=` (Eb.* # RS.2)].
  
  Notation "R [Set<=] S" := (leset (R,S)).
  
  Lemma Ile: forall (R S: set T), R `<=`S -> R [Set<=] S.
  Admitted.
  
  Definition IndependentSets := [set S | Independent S].

  (** * [Set<=] is a partial order on IndependentSets  *)

  Lemma letrans: transitive leset.
  Proof.
    move => R S U.
    rewrite /leset /mkset /= => [H1 H2].
    move => y /H1 [x [H3 /H2 [u [H4 H5]]]].
    have H6: (Eb.* `;` Eb.* ) (y, u) by (exists x).
    by exists u;rewrite -compose_rt_rt.
  Qed.

  Lemma lerefl: reflexive leset.
  Proof.
    move => R.
    by rewrite /leset /mkset /= -DuT_eq_Tstar -Fset_union_rel Fset_D.
  Qed.

  Lemma leasym: antisymmetric leset.
  Proof.
    move => R S.
  Admitted.

End Paper.




  
    

