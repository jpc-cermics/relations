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
From mathcomp Require Import all_ssreflect order contra.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets topology.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Intermediate_results_closed.
  Context (T: Type) (R: relation T). 
  
  (** * properties of closed sets in topological relation *)
  Lemma Rclosed1:
      [set X | R.*#X = X ] = [set X | R.*#X `<=` X].
  Proof.
    rewrite predeqE /mkset => X.
    split => [-> // | H1].
    have H2: X `<=` R.*#X
      by rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D;apply: subsetUl.
    by rewrite eqEsubset.
  Qed.
  
  Lemma Rclosed2: 
      [set X | R.*#X `<=` X] = [set X | R.+#X `<=` X].
  Proof.
    rewrite predeqE /mkset => X.
    rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D.
    split => [ H1 | H1].
    - have H2: R.+#X `<=` X `|` R.+#X by apply: subsetUr.
      by apply: (subset_trans H2 H1).
    - have H2: X `<=` X by [].
      have H3: X `|` R.+#X `<=` X `|` X by apply: setUSS.
      by move: H3;rewrite setUid.
  Qed.

  Local Lemma Rclosed3: forall (X: set T),
      R#X `<=` X -> forall (n: nat), (iter R n.+1)#X `<=` X.
  Proof. 
    move =>X H1 n. 
    elim: n => [ | n H2]; first by rewrite iter1_id.
    have H3: R^(n.+2)#X = (R^(n.+1) `;` R^(1))#X
      by rewrite -iter_compose addn1.
    rewrite H3 -Fset_comp iter1_id.
    have H4: R^(n.+1)#(R#X) `<=` R^(n.+1)#(X) by apply: Fset_inc1.
    by apply: (subset_trans H4 H2).
  Qed.

  Lemma Rclosed4:
      [set X | R.+#X `<=` X]= [set X | R#X  `<=` X].
  Proof.
    rewrite predeqE /mkset => X.
    split => [H1 | H1 x [y [H2 H3]]].
    - have H2:  R `<=` R.+ by apply: iter1_inc_clos_trans.
      have H3: R#X  `<=` R.+#X by apply: Fset_inc.
      by apply: (subset_trans H3 H1).
    - have [n H4]: exists (n:nat), (iter R n.+1) (x,y) by apply: clos_t_iterk.
      have H5: (iter R n.+1)#X x by (exists y).
      have H6: (iter R n.+1)#X `<=` X by apply: (Rclosed3 H1).
      by move: H5 => /H6 H5.
  Qed.
  
  Lemma Rclosed:
      [set X | R.*#X = X] = [set X | R#X  `<=` X].
  Proof.
    by rewrite Rclosed1 Rclosed2 Rclosed4. 
  Qed.
  
End Intermediate_results_closed.

Section Intermediate_results_closed_open.

  Context (T: Type).

  Lemma Rclosed6: forall (R : relation T) (X: set T),
      R#X  `<=` X -> (X.^c :#R ) `<=` X.^c.
  Proof.
    move => R X H1.
    have H2:  (X.^c :#R ) `&` X = set0.
    rewrite empty_notexists => -[z /inP [[w [H2 H3]] H4]].
    by have /H1 H5: R#X w by (exists z).
    by rewrite -disjoints_subset;apply: H2.
  Qed.
  
  Lemma Rclosed7: forall (R : relation T) (X: set T),
      (X.^c :#R ) `<=` X.^c -> R#X  `<=` X. 
  Proof.
    by rewrite /Aset => R X /Rclosed6; rewrite setCK /Aset inverse_inverse.
  Qed.
  
  (* from closed sets to open set via complement *)
  Lemma Rclosed_complement_open:  forall (R : relation T) (X: set T),
      R#X  `<=` X <-> (X.^c :#R ) `<=` X.^c.
  Proof.
    split;[apply: Rclosed6| apply: Rclosed7].
  Qed.
  
  (** * Closure of a set XXXXXXXXXXX a retirer *)
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
End Intermediate_results_closed_open.  

Section Intermediate_results_open.
  Context (T: Type) (S: relation T). 
  
  (** * properties of open sets in topological relation *)
  Lemma Ropen1 (R : relation T): 
      [set X | X:#R.* = X ] = [set X | X:#R.* `<=` X].
  Proof.
    by rewrite /Aset inverse_star;apply: Rclosed1.
  Qed.
  
  Lemma Ropen2 (R : relation T):
      [set X | X:#R.* `<=` X] = [set X | X:#R.+ `<=` X].
  Proof.
    by rewrite /Aset inverse_star inverse_clos_t;apply: Rclosed2.
  Qed.

  Lemma Ropen4 (R : relation T):
      [set X | X:#R.+ `<=` X]= [set X | X:#R  `<=` X].
  Proof.
    by rewrite /Aset inverse_clos_t; apply: Rclosed4.
  Qed.
  
  Lemma Ropen (R : relation T):
      [set X | X:#R.* = X] = [set X | X:#R  `<=` X].
  Proof.
    by rewrite Ropen1 Ropen2 Ropen4. 
  Qed.
  
End Intermediate_results_open.

Section Relation_Topology.
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
  HB.instance Definition _ := isOpenTopological.Build W openT openI open_bigU.

End Relation_Topology.
 
Section Relation_Topology_props.
  (** * Checking the AsetTopology *)
  Variables (T: choiceType) (S: relation T). 
  
  (* recover the fact that the open sets are given by tau *)

  Lemma Aset_open: [ set O | O:#S `<=` O] = @open (aset_topology S).
  Proof.
    rewrite predeqE => O.
    split;first by rewrite openE /interior => H1 o H2;exists O;split.
    rewrite openE /interior /mkset => H1 o [o1 [H2 /H1 H3]].
    move: H3;rewrite nbhsE /open_nbhs /open => -[B [H3 H4]] H6.
    (** H3 gives H5 *)
    have H5: B:#S `<=` B by [].
    have H7: B:#S o by (exists o1). 
    have H8: B o by apply: H5.
    by apply: H6.
  Qed.

  Lemma Aset_open' : [ set O | O:#S.* =  O] = @open (aset_topology S).
  Proof. by rewrite -Aset_open -Ropen. Qed.
  
  (** * already in topology_structure *)
  Lemma open_closedC' (D : set T) :
    @open (aset_topology S) D -> @closed (aset_topology S) (~` D).
  Proof. by rewrite openE => Dop p clNDp /Dop /clNDp [? []]. Qed.

  (** * could be added in topology_structure *)
  Lemma closed_openC' (D : set T) :
    @closed (aset_topology S) D -> @open (aset_topology S) (~` D).
  Proof. 
    rewrite /closed openE => /subsetC H1.
    by move: H1;rewrite -interiorC /mkset => H1.
  Qed.

  Lemma Aset_closed: [ set O | S#O `<=` O] = @closed (aset_topology S).
  Proof.
    rewrite predeqE /mkset => X.
    rewrite Rclosed_complement_open.
    split. 
    - move => H1. 
      have <-: X.^c.^c = X by rewrite setCK.
      apply: open_closedC.
      pose proof Aset_open as H2.
      by move: H2; rewrite predeqE /mkset => <-.
    - move => /closed_openC' H1.
      pose proof Aset_open as H2.
      by move: H2; rewrite predeqE /mkset => ->.
  Qed.
  
  Lemma Aset_closed': [ set O | S.*#O = O] = @closed (aset_topology S).
  Proof.
    by rewrite Rclosed Aset_closed.
  Qed.

  Lemma Aset_closed1 (X: set T) : forall (B: set T),
      @closed (aset_topology S) B /\ X `<=` B -> S.*#X `<=` B.
  Proof.
    move => B. 
    pose proof Aset_closed' as H1.
    move: H1; rewrite predeqE /mkset => <-.
    move => [H2 H3].
    rewrite -H2.
    by apply: Fset_inc1.
  Qed.
  
  Lemma Aset_closure: forall (X: set T), 
    @closure (aset_topology S) X = S.*#X. 
  Proof.
    move => X; rewrite closureE.
    have H4: S.*#X = S.*#(S.*#X) by rewrite Fset_comp compose_rt_rt.
    have H5: X `<=` S.*#X by rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D;apply: subsetUl.
    have H6: @closed (aset_topology S) S.*#X 
      by pose proof Aset_closed' as H1;move: H1; rewrite predeqE /mkset => <-.
    pose proof Aset_closed1 as H7.
    move: H7 => /(_ X) H7.
    
    have H8: smallest (@closed (aset_topology S)) X `<=` S.*#X. 
    apply: smallest_sub. by []. by [].
    have H9:  S.*#X `<=` smallest (@closed (aset_topology S)) X. 
    apply: sub_bigcap => Y.
    rewrite /mkset => -[H9 H10].
    by apply: H7.
    by rewrite eqEsubset.
  Qed.

End Relation_Topology_props.

Section Porder_Topology.
  (* Topology associated to a porder *) 
  (* we directly use the topology associated to the after sets of porder binary relation *)
  Context (disp : Order.disp_t).
  Variable (T : porderType disp).

  Definition rel_porder := [set xy : T*T| (xy.1 <= xy.2)%O].

  Definition Porder_topology := (aset_topology rel_porder). 

  Lemma Porder_open (O: set T) : [set O | O:#(rel_porder) `<=` O] = @open Porder_topology.
  Proof. by apply: Aset_open. Qed.
  
End  Porder_Topology.

Section Porder_Topology1.
  (** * This is not usefull as it is simplified in previous section *)
  
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
  
End Porder_Topology1.

Section Specialization_Porder.
  (** * specialization relation defined with a topology *) 
  
  Variable (T: topologicalType).
  
  Definition specialization_porder := 
    [set xy: T*T  | (@closure T [set xy.2]) xy.1].

  Lemma specialization_porder_reflexive: 
    forall (x:T), specialization_porder (x,x).
  Proof.
    by move => x;rewrite /specialization_porder /=;apply: subset_closure.
  Qed.

  Lemma specialization_porder_transitive:
    forall (x y z :T), 
      specialization_porder (x,y) -> specialization_porder (y,z) 
      -> specialization_porder (x,z).
  Proof.
    move => x y z. 
    rewrite /specialization_porder /= => H1 H2.
    have H3: [set y] `<=` closure [set z] by rewrite sub1set inP. 
    have H4: closed (closure [set z]) by apply: closed_closure.
    move: H4 => /closure_id H4.
    have H5: closure [set y] `<=` closure (closure [set z]) by apply: closure_subset.
    move: H5; rewrite -H4 => H5.
    by apply: H5.
  Qed.

  Definition downset' (X: set T) := [set y :T | exists x, X x /\ specialization_porder (y,x)].
  Definition upset' (X: set T) := [set y :T | exists x, X x /\  specialization_porder (x, y)].

  Lemma closed_is_downset: forall (C: set T), 
      closed C -> (downset' C) `<=` C.
  Proof.
    move => C H1 c [c' [H2 H3]].
    have H4: [set c'] `<=` C by rewrite sub1set inP. 
    move: H4 => /closure_subset H4.
    have ->: C = closure C by rewrite -closure_id.
    by apply H4.
  Qed.
  
  Lemma open_is_upper: forall (O: set T), 
      open O -> (upset' O) `<=` O.
  Proof.
    move => O H1 c [c' [H2 H3]]. 
    absurd_not => H4.
    have H5: O.^c c by [].
    have H6: (downset' O.^c) c' by (exists c).
    have H7: closed O.^c by apply: open_closedC.
    have H8: (downset' O.^c) `<=` O.^c by apply: closed_is_downset.
    have H9: O.^c c' by apply H8.
    by [].
  Qed.

End Specialization_Porder.






