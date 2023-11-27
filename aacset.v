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

From AAC_tactics Require Import AAC.

From mathcomp Require Import ssreflect.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* test of AAC with classical_sets *)

Section AAC_eq_setU.
  (** * union *)
  #[export] Instance aac_union_eq_Comm T :
    Commutative eq (@setU T).
  Proof. by move => R S; rewrite setUC. Qed.
  #[export] Instance aac_union_eq_Assoc T :
    Associative eq (@setU T).
  Proof. by move => R S U; rewrite setUA. Qed.
  #[export] Instance aac_union_eq_Idem T :
    Idempotent eq (@setU T).
  Proof. by move => R;rewrite setUid. Qed. 
  #[export] Instance aac_deltac_union_eq_Unit T :
    Unit eq (@setU T) set0.
  Proof. by split => R;[apply: set0U | apply: setU0]. Qed.
  #[export] Instance aac_union_eq_compat T :
    Proper (eq ==> eq ==> eq) (@setU T).
  Proof. by move => R S H1 U V H2; rewrite H1 H2. Qed.
End AAC_eq_setU.

Section AAC_eq_setI.
  (** * intersection *)
  #[export] Instance aac_intersection_eq_Comm T :
    Commutative eq (@setI T).
  Proof. by move => R S; rewrite setIC. Qed.
  #[export] Instance aac_intersection_eq_Assoc T :
    Associative eq (@setI T).
  Proof. by move => R S U; rewrite setIA. Qed.
  #[export] Instance aac_intersection_eq_Idem T :
    Idempotent eq (@setI T).
  Proof. by move => R;rewrite setIid. Qed. 
  #[export] Instance aac_deltac_intersection_eq_Unit T :
    Unit eq (@setI T) setT.
  Proof. by split => R;[apply: setTI | apply: setIT]. Qed.
  #[export] Instance aac_intersection_eq_compat T :
    Proper (eq ==> eq ==> eq) (@setI T).
  Proof. by move => R S H1 U V H2; rewrite H1 H2. Qed.
End AAC_eq_setI.

Section Test.

  Variables (A: Type) (X Y Z T: set A).
  
  Goal (X `|` Y `|` Z `|` T)%classic = (X `|` (Y `|` Z) `|` T)%classic.
    by aac_reflexivity. 
  Qed.

  Goal (X `|` Y `|` set0 `|` T)%classic = (X `|` Y `|` T)%classic.
    by aac_reflexivity. 
  Qed.

  Goal (X `&` Y `&` Z `&` T)%classic = (X `&` (Y `&` Z) `&` T)%classic.
    by aac_reflexivity. 
  Qed.

  Goal (X `&` Y `&` setT `&` T)%classic = (X `&` Y `&` T)%classic.
    by aac_reflexivity. 
  Qed.
  
End Test.

