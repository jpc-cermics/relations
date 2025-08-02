(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.

Set Warnings "-parsing -coercions".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime finfun.
From mathcomp Require Import finset order.
Set Warnings "parsing coercions".

(******************************************************************************)
(* preorder *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[key="T", primitive]
HB.mixin Record isDuallyPreorder (d : Order.disp_t) T := {
  le       : rel T;
  lt       : rel T;
  lt_def   : forall x y, lt x y = (le x y) && ~~ (le y x);
  gt_def   : forall x y, lt y x = (le y x) && ~~ (le x y);
  le_refl  : reflexive     le;
  ge_refl  : reflexive     (fun x y => le y x);
  le_trans : transitive    le;
  ge_trans : transitive    (fun x y => le y x);
}.


#[short(type="preorderType")]
HB.structure Definition Preorder (d : Order.disp_t) :=
  { T of Choice T & isDuallyPreorder d T }.

#[key="T", primitive]
HB.mixin Record hasBottom d T of Preorder d T := {
  bottom : T;
  le0x : forall x, le bottom x;
}.

#[key="T", primitive]
HB.mixin Record hasTop d T of Preorder d T := {
  top : T;
  lex1 : forall x, le x top;
}.

#[short(type="bPreorderType")]
HB.structure Definition BPreorder d := { T of hasBottom d T & Preorder d T }.
#[short(type="tPreorderType")]
HB.structure Definition TPreorder d := { T of hasTop d T & Preorder d T }.
#[short(type="tbPreorderType")]
HB.structure Definition TBPreorder d := { T of hasTop d T & BPreorder d T }.


