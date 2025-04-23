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

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel paper_relations paper_tcs_facts.

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
  
  Theorem tcs_T5: forall (x y: T),
      (x \in W.^c) -> (y \in W.^c) -> (t_separated (x,y) <-> d_separated (x,y)).
  Proof.
    by move => x y Hx Hy; apply: T5.
  Qed.
    
  (* Theorem 5, relation version *)
  Theorem tcs_T5':  (Restrict t_separated W.^c) = (Restrict d_separated W.^c).
  Proof.
    by apply: T5'.
  Qed.
  
  (** Proposition 6 *)

  Proposition tcs_P6: forall (Γ Λ: set T),
      ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0) 
      -> (
          (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ))
          <->
            (exists (W': set T), exists (W'': set T), 
                ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0)
                /\ set_split W' W'' W)
        ).
  Proof. 
    by apply: P6.
  Qed.
  
  (* Lemma 7 *)
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

  Lemma tcs_L8_2: forall (W' W'': set T),
      (W' `<=` W) /\ (W''= W `\` W') /\ Clos(W' | E,W) `&` Clos(W'' | E,W)=set0
      -> ~ (exists (w' w'': T), w' \in W' /\ w'' \in W'' /\ Cw (w', w'')).
  Proof.
    by move => W' W'';  apply: L8_2.
  Qed.

  Lemma tcsL9 :  forall (w : T) (X : set T),
      X `<=` W.^c ->
      ( w \in (Cw `;` (Bmw `|` Kw))#X
            <-> (exists w', Cw (w,w') /\ (exists z, z \in Clos_(w'|E,W) /\ z \in Clos(X|E,W)))).
  Proof.
    by apply: L9.
  Qed.
  Lemma tcs_L10_1 : forall (w1 w2: T),
      (w1 \in W /\ w2 \in W /\ w1 <> w2) ->
      Clos_(w1 | E,W) `&` Clos_(w2 | E,W) != set0 <-> Kw (w1, w2).
  Proof.
    by apply: L10_1.
  Qed.

  Lemma tcs_L10_2 : forall (w1 w2: T),
      (w1 \in W /\ w2 \in W /\ w1 <> w2) ->
      Clos_(w1 | E,W) `&` Clos_(w2 | E,W) != set0 -> Cw (w1, w2).
  Proof.
    by apply: L10_2.
  Qed.
  
  Lemma tcs_L11: forall (Θ: set T) (W': set T),
      (W' `&` (Cw `;` (Bmw `|` Kw))#Θ = set0) 
      ->  W' `<=` W
      ->  Θ `<=` W.^c
      -> ( Clos(W'| E,W) `&` Clos(Θ `|` (Cw `;` (Bmw `|` Kw))#Θ| E,W)= set0).
  Proof.
    by apply: L11.
  Qed.
  
  Lemma  tcs_L14:
    (Emw.* `;` Ew.* ) = ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw)
    /\ Cw `;` (Emw .* ) `;` (Ew .* ) = Cw `;` ('Δ `|` Bmw `;` Δ_(W.^c) `|` Kw)
    /\ (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw 
    /\ (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c)
    /\ Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
  Proof.
    by apply: L14.
  Qed. 
  
  Lemma tcs_L15: (Δ_(W.^c) `;` Smw `;`  Emw.* `;` Ew.* `;` Sw `;` Δ_(W.^c))
             = Δ_(W.^c) `;` Aw `;`  Δ_(W.^c).
  Proof.
    by apply: L15.
  Qed.

End Paper.











