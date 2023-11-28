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

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel aacset. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Test.

  (** * test of AAC with relations (which are sets) *)

  Variables (A: Type) (X Y Z T: relation A).
  
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


