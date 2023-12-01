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
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel erel3 aacset paper_relations paper_csbr_rel paper_csbr_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Paper.
(** ****************************************************************
  * Conditional Separation as a Binary Relatio 
  *   Jean-Philippe Chancelier, Michel De Lara, Benjamin Heymann 
  * 
  * We list here the results of the paper following the order given 
  * in the paper.
 ******************************************************************)

  Theorem Th4_csbr: forall (x y:A), ( x [⊥d] y | W ) <-> ~ Aw (x, y).
  Proof.
    apply Th4.
  Qed.
  
  Lemma  L7_csbr:
    (Emw.* * Ew.* ) = ('Δ `|` (Δ_(W.^c) * Bw) `|` (Bmw *Δ_(W.^c)) `|` Kw)
    /\ Cw * (Emw .* ) * (Ew .* ) = Cw * ('Δ `|` Bmw*Δ_(W.^c) `|` Kw)
    /\ (Cw * (Emw .* ) * (Ew .* )) * Cw  = Cw 
    /\ (Cw * (Emw .* ) * (Ew .* )) * Δ_(W.^c)  = Cw *(Bmw `|` Kw)  * Δ_(W.^c).
  Proof.
    apply L7.
  Qed.
  
  Lemma L8_csbr:
    Aw_s = 'Δ `|` Aw_sp `|` Aw_sm
    /\  ((Aw_sm * Δ_(W.^c) * E) `<=`  Aw_sp)
    /\  ((Aw_sp * Δ_(W_s) * Em) `<=`  Aw_sm).
  Proof.
    apply L8.
  Qed.

  Lemma L9_csbr:  Aw = Aw_s.
  Proof.
    apply L9.
  Qed.

  Lemma L10_csbr_33a: forall (x y:A),
      Bw (x, y)  -> (exists (p: seq A), Active_path W E (Lifto (x::(rcons p y)) P) x y
                               /\ All (Ew.+)#_(y) p).
  Proof.
    by apply Bwpath. 
  Qed.
  
  Lemma L10_csbr_33b: forall (x y:A),
      Bmw (x, y) -> (exists (p: seq A), Active_path W E (Lifto (x::(rcons p y)) N) x y
                               /\ All (Ew.+)#_(x) p).
  Proof.
    by apply Bmwpath. 
  Qed.

  Lemma L10_csbr_33c: forall (x y:A),
      Kw (x,y) -> (exists (p q: seq A),exists t,
                   Active_path W E 
                     ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P )) x y
                   /\ All (Ew.+)#_(x) (rcons p t) 
                   /\ All (Ew.+)#_(y) (t::q)).
  Proof.
    by apply Kwpath.
  Qed.
  
  Lemma L10_csbr_33d: forall (x y:A),
      let R:= (Δ_(W_s) * Kw * Δ_(W_s)).+
      in R (x, y)
         -> exists (p q: seq (Eo A O)), exists (x' y':A),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) 
          /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof.
    by apply Kwcomp_tc. 
  Qed.
  
  Lemma L11_csbr: forall (x y:A),
      Aw (x, y) -> exists (p : seq (Eo A O)), Active_path W E p x y.
  Proof.
    by apply L11.
  Qed.
  
  Proposition P12_csbr: forall (x y:A), Aw (x, y) -> ~ ( x [⊥d] y | W ).
  Proof.
    by apply P12.
  Qed.

  Lemma L13_csbr: forall (n: nat) (p : seq (Eo A O)) (x y:A), 
      size (p) = n.+2 
      -> Active_path W E p x y
      -> exists (q: seq (Eo A O)) (o: O) (y':A),
          p = rcons q (y',y,o) /\ (( Aw_sp (x, y) /\ o = P) \/ ( Aw_sm (x ,y) /\ o = N)).
  Proof.
    by apply L13.
  Qed.

End Paper.
