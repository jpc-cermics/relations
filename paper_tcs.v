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
From mathcomp Require Import all_ssreflect order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel  aacset paper_relations paper_tcs_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Paper.
(** ****************************************************************
 * Topological Conditional Separation
 *   Jean-Philippe Chancelier, Michel De Lara, Benjamin Heymann 
 * 
 * We list here the results of the paper
 *  Topological Conditional Separation
 * following the order given in the paper.
 ******************************************************************)

  (* To be done by copying results from paper_tcs_*.v *)
  
  Theorem tcs_T5: forall (x y: T), x \in W.^c -> y \in W.^c -> (t_separated x y <-> d_separated x y).
  Proof.
    by move => x y Hx Hy; apply: T5.
  Qed.
  
  (* c'est un peu plus general que tcs_L7 car on a ici  x \in W.^c et y \in W.^c *)
  Lemma tcs_L7: forall (x y: T), 
        x \in W.^c -> y \in W.^c -> Clos_(x |E,W) `&` Clos_(y|E,W) = set0 -> Aw (x, y) -> 
        exists w_x, exists w_y, w_x \in W /\ w_y \in W /\ Cw (w_x, w_y) 
                                /\ (Clos_(x| E,W) `&`  Clos_(w_x| E,W) != set0)
                                /\ (Clos_(y| E,W) `&`  Clos_(w_y| E,W) != set0).
  Proof.
    by move => x y; apply: L7.
  Qed.

  (* Lemma 8 of tcs *)
  Lemma tcs_L8_1 : forall (W' W'': set T),
      W' `<=` W /\ W'' `<=` W /\ (forall (w' w'': T), w' \in W' /\ w'' \in W'' -> ~(Cw (w', w'')))
      -> Clos(W' | E,W) `&` Clos(W''| E,W) = set0. 
  Proof.
    by move => W' W'';  apply: L8_1.
  Qed.

  Lemma tcsh_L8_2: forall (W' W'': set T),
      (W' `<=` W) /\ (W''= W `\` W') /\ Clos(W' | E,W) `&` Clos(W'' | E,W)=set0
      -> ~ (exists (w' w'': T), w' \in W' /\ w'' \in W'' /\ Cw (w', w'')).
  Proof.
    by move => W' W'';  apply: L8_2.
  Qed.
  
End Paper.











