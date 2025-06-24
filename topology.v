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

From HB Require Import structures.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets topology.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section test1.
  Context (T: Type) (S: relation T). 
  
  (** * properties of open sets *)
  Lemma Ropen1: forall (R : relation T) (X: set T),
      R.*#X = X <-> R.*#X `<=` X.
  Proof.
    move => R X;split => [-> | H1];first by [].
    have H2: X `<=` R.*#X
      by rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D;apply: subsetUl.
    by rewrite eqEsubset.
  Qed.

  Lemma Ropen2: forall (R : relation T) (X: set T),
      R.*#X `<=` X <-> R.+#X `<=` X.
  Proof.
    move => R X;rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D.
    split => [ H1 | H1].
    - have H2: R.+#X `<=` X `|` R.+#X by apply: subsetUr.
      by apply: (subset_trans H2 H1).
    - have H2: X `<=` X by [].
      have H3: X `|` R.+#X `<=` X `|` X by apply: setUSS.
      by move: H3;rewrite setUid.
  Qed.

  Lemma Ropen3: forall (R : relation T) (X: set T),
      R#X `<=` X -> forall (n: nat), (iter R n.+1)#X `<=` X.
  Proof.
    move => R X H1 n. 
    elim: n => [ | n H2]; first by rewrite iter1_id.
    have H3: R^(n.+2)#X = (R^(n.+1) `;` R^(1))#X
      by rewrite -iter_compose addn1.
    rewrite H3 -Fset_comp iter1_id.
    have H4: R^(n.+1)#(R#X) `<=` R^(n.+1)#(X) by apply: Fset_inc1.
    by apply: (subset_trans H4 H2).
  Qed.

  Lemma Ropen4: forall (R : relation T) (X: set T),
      R.+#X `<=` X <-> R#X  `<=` X.
  Proof.
    move => R X;split => [H1 | H1 x [y [H2 H3]]].
    - have H2:  R `<=` R.+ by apply: iter1_inc_clos_trans.
      have H3: R#X  `<=` R.+#X by apply: Fset_inc.
      by apply: (subset_trans H3 H1).
    - have [n H4]: exists (n:nat), (iter R n.+1) (x,y) by apply: clos_t_iterk.
      have H5: (iter R n.+1)#X x by (exists y).
      have H6: (iter R n.+1)#X `<=` X by apply: (Ropen3 H1).
      by move: H5 => /H6 H5.
  Qed.

  (** * clopen properties *)
  Lemma Ropen6: forall (R : relation T) (X: set T),
      R#X  `<=` X -> (X.^c :#R ) `<=` X.^c.
  Proof.
    move => R X H1.
    have H2:  (X.^c :#R ) `&` X = set0.
    rewrite empty_notexists => -[z /inP [[w [H2 H3]] H4]].
    by have /H1 H5: R#X w by (exists z).
    by rewrite -disjoints_subset;apply: H2.
  Qed.
  
  (** * Closure of a set *)
  Definition T_closure (R : relation T) (Y: set T) (X: set T) 
    := Y = R.*#Y /\ X`<=` Y /\ (forall Z, Z = R.*#Z /\ X `<=` Z -> Y `<=` Z).
  
  Lemma T_closure_iff: forall (R : relation T) (Y: set T) (X: set T),
      T_closure R Y X <-> Y = R.*#X.
  Proof.
    move => R Y X.
    have H4: R.*#X = R.*#(R.*#X) by rewrite Fset_comp compose_rt_rt.
    have H5: X `<=` R.*#X by rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D;apply: subsetUl.
    split  => [ [H1 [H2 H3]] | H1].
    - have H6: Y `<=`  R.*#X by apply: H3.
      have H7: R.*#X `<=` Y by rewrite H1; apply: Fset_inc1 .
      by rewrite eqEsubset.
    - split;rewrite H1;first by[].
      split;first by [].
      move => Z [H2 H3].
      have H6:  R.*#X `<=`  R.*#Z by apply: Fset_inc1 .
      by rewrite H2.
  Qed.
  
End test1.


Section top.
  (** * Topology associated to a relation using the After sets *)
    
  Variables (T: choiceType) (S: relation T).

  Definition aset_topology {T : Type} (V: relation T) : Type := T.
  Notation W := (aset_topology S).
  
  Definition tau : set (set T) := [ set O | O:#S `<=` O]%O.
  
  Local Lemma openT : tau [set: W].
  Proof. by apply:Aset_T. Qed.
  
  Local Lemma openI : forall A B : set W, 
      tau A -> tau B -> tau (A `&` B).
  Proof. by move => A B H1 H2;apply: (Aset_stableIf H1 H2). Qed.
  
  Local Lemma open_bigU (I : Type) (f : I -> set W):
    (forall (i : I), tau (f i)) -> tau (\bigcup_i f i).
  Proof. by apply:Aset_stableU. Qed.
  
  HB.instance Definition _ := Choice.on W.
  Set Warnings "-redundant-canonical-projection".
  HB.instance Definition AsetTopology := isOpenTopological.Build W openT openI open_bigU.

End top.

Section test.
  (** * Checking the AsetTopology *)
  Variables (T: choiceType) (S: relation T) (S': relation T).

  (* recover the fact that the open sets are tau *)
  Lemma Aset_open (O: set T) : O:#S `<=` O <-> @open (aset_topology S) O.
  Proof.
    split;first by rewrite openE /interior => H1 o H2;exists O;split.
    rewrite openE /interior /mkset => H1 o [o1 [H2 /H1 H3]].
    move: H3;rewrite nbhsE /open_nbhs /open => -[B [H3 H4]] H6.
    (** H3 gives H5 *)
    have H5:  B:#S `<=` B by [].
    have H7: B:#S o by (exists o1). 
    have H8: B o by apply: H5.
    by apply: H6.
  Qed.
  
End test.


Section porder.
  (* Topology associted to a porder *) 
  (* We could use the topology associated to a relation 
     to compact the code here *) 

  Context (disp : Order.disp_t).
  Variable (T : porderType disp).
  
  Definition downset (X: set T) := [set y :T | exists x, X x /\ (y <= x)%O].
  Definition upset (X: set T) := [set y :T | exists x, X x /\ (x <= y)%O].

  Definition porder_topology : Type := T.
  Notation W := porder_topology.
  
  Definition tau_porder : set (set T) := [ set O | upset O `<=` O]%O.
  
  Local Lemma openT_porder : tau_porder [set: W].
  Proof. by []. Qed.
  
  Local Lemma openI_porder : forall A B : set W, 
      tau_porder A -> tau_porder B -> tau_porder (A `&` B).
  Proof. 
    move => A B. rewrite /tau_porder /mkset => H1 H2 ab [x [[H3 H3'] H4]]. 
    split; first by apply: H1;exists x.
    by apply: H2;exists x.
  Qed.

  Local Lemma open_bigU_porder (I : Type) (f : I -> set W):
    (forall (i : I), tau_porder (f i)) -> tau_porder (\bigcup_i f i).
  Proof.
    move => H1.
    rewrite /tau_porder /mkset => a [x  [[j H3] H4 H5]].
    have H6: tau_porder (f j) by [].
    move : H6;rewrite /tau_porder /mkset => H6.
    exists j. by []. apply: H6. by exists x.
  Qed.
  
  HB.instance Definition _ := Choice.on W.
  Set Warnings "-redundant-canonical-projection".
  HB.instance Definition PorderTopology :=
    isOpenTopological.Build W openT_porder openI_porder open_bigU_porder.
  
End porder.







