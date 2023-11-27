(* -*- Encoding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ensembles.
Require Import Setoid.
Require Import Morphisms.

From AAC_tactics Require Import AAC.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  cssrel crel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* test of AAC with relations *)

Section AAC_eq.

  (* union *)
  #[export] Instance aac_union_eq_Comm T :
    Commutative eq (@setU (T*T)).
  Proof. by move => R S; rewrite setUC. Qed.
  #[export] Instance aac_union_eq_Assoc T :
    Associative eq (@setU (T*T)).
  Proof. by move => R S U; rewrite setUA. Qed.
  #[export] Instance aac_union_eq_Idem T :
    Idempotent eq (@setU (T*T)).
  Proof. by move => R;rewrite union_RR. Qed. 
  #[export] Instance aac_deltac_union_eq_Unit T :
    Unit eq (@setU (T*T)) ('Δc).
  Proof. by split => R;[apply: DeltaC_union_ideml | apply: DeltaC_union_idemr]. Qed.
  #[export] Instance aac_union_eq_compat T :
    Proper (eq ==> eq ==> eq) (@setU (T*T)).
  Proof. by move => R S H1 U V H2; rewrite H1 H2. Qed.

  (* composition *)
  #[export] Instance aac_compose_eq_Assoc T :
    Associative eq (@compose (T * T)).
  Proof. by move => R S U; rewrite composeA. Qed.
  #[export] Instance aac_delta_compose_eq_Unit T :
    Unit eq (@compose (T * T)) ('Δ).
  Proof. by split => R;[apply: Delta_idem_l | apply: Delta_idem_r]. Qed.
  #[export] Instance aac_compose_eq_compat T :
    Proper (eq ==> eq ==> eq) (@compose (T * T)).
  Proof. by move => R S H1 U V H2; rewrite H1 H2. Qed.

  (* inverse *) 
  #[export] Instance aac_inverse_eq_compat T :
    Proper (eq ==> eq) (@inverse (T * T)).
  Proof. by move => R S ->. Qed. 
  
  (* .+ *) 
  #[export] Instance aac_clos_trans_eq_compat T :
    Proper (eq ==> eq) (@clos_trans (T * T)).
  Proof. by move => R S ->. Qed. 

  (* .* *) 
  #[export] Instance aac_clos_refl_trans_eq_compat T :
    Proper (eq ==> eq) (@clos_refl_trans (T * T)).
  Proof. by move => R S ->. Qed. 
  
  (* Comprendre comment on etend a l'inclusion *)

End AAC_eq.

Section Test.

  Variables (A: Type) (W: set A) (R S T U:relation A).
  
  Goal (R `|` S `|` 'Δc `|` U)%classic = ((R * 'Δ) `|` 'Δc `|` (U `|` S))%classic.
    by aac_reflexivity. 
  Qed.

  Goal (R `|` S `|` U)%classic = (R `|` (U `|` S))%classic.
    by aac_reflexivity. 
  Qed.

  Goal ((R `|` S).`|` `|` S `|` U )%classic = ((S`|` R).`|` `|` (U `|` S))%classic.
    by aac_reflexivity. 
  Qed.

  Goal ((R `|` S).`|` * S * U )%classic = ((S`|` R).`|` * (S * U))%classic.
    by aac_reflexivity. 
  Qed.

  Hypothesis H: Δ_(W) =  Δ_(W) * Δ_(W)%classic.
  
  Goal ((R `|` S).`|` * S * Δ_(W) * U )%classic = ((S`|` R).`|` * (S * Δ_(W) * Δ_(W) * U))%classic.
    rewrite {1}H.
    by aac_reflexivity. 
  Qed.

  (* with eq_relation equivalence *)
  Goal (R `|` S `|` U)%classic =R= (R `|` (U `|` S))%classic.
    by aac_reflexivity. 
  Qed.

End Test.

