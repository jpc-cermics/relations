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
From mathcomp Require Import all_boot order contra.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets order topology.
Set Warnings "parsing coercions".

From RL Require Import  rel mypreorder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Preorder.

  Variables (T: Type) (R: relation T).

  Definition le := R2rel R.
  Hypothesis le_trans : Coq.ssr.ssrbool.transitive R. (* using coercion *)
  Hypothesis le_refl : Coq.ssr.ssrbool.reflexive R. (* using coercion *)
  
  Fact rel_display : Order.disp_t. Proof. exact. Qed.
  
  Definition lt (x y:T) := ((x,y) \in R) && ~~ ((y, x) \in R).
  
  Lemma lt_prop: forall (x y:T),lt x y = le x y  && ~~ le y x.
  Proof. exact. Qed. 

  Lemma gt_prop: forall (x y:T), lt y x = (le y x) && ~~ (le x y).
  Proof. exact. Qed. 

  (** * to be done 
  
  Lemma ge_trans: Coq.ssr.ssrbool.transitive  (fun x y => le y x).
  
  HB.instance Definition _  := (@isDuallyPreorder.Build rel_display T
                     le lt lt_prop gt_prop le_refl le_refl le_trans ge_trans).
  *) 
          
End Preorder.

Section Topology_adds. 
  (** * additional lemmas for topology_structure *)
  Variables (T: topologicalType).
  
  Lemma closure_if: forall (X Y: set T),
      closed Y -> X `<=` Y -> closure X `<=` Y. 
  Proof.
    by move => X Y ? ?;rewrite closureE /smallest /mkset;apply: bigcap_inf.
  Qed.

  Lemma closure_if1: forall (X Y: set T),
      closed Y -> X `<=` Y -> Y `<=` closure X -> Y = closure X. 
  Proof.
    by move => X Y ? ? ?;rewrite eqEsubset;split;[ |apply: closure_if].
  Qed.

End Topology_adds.

Section Topology_porder.
  (** * additional lemmas for topology_structure *)
  Variables (T: choiceType).
  
  Definition finer (tau tau': Topological T) :=
    (@open (Topological.Pack tau')) `<=` (@open (Topological.Pack tau)).
  
  Definition eqTopological (tau tau': Topological T) := 
    (@open (Topological.Pack tau')) = (@open (Topological.Pack tau)).
  
  Lemma finer_reflexive: forall (tau: Topological T),  finer tau tau.
  Proof. by move => tau. Qed.

  Lemma finer_transitive: forall (tau tau' tau'': Topological T),
      finer tau tau' -> finer tau' tau'' -> finer tau tau''.
  Proof. by move => t t' t'' H1 H2;apply: subset_trans H2 H1. Qed.
  
  Lemma finer_anti: forall (tau tau' : Topological T),
      finer tau tau' -> finer tau' tau -> eqTopological tau tau'.
  Proof. 
    by move => tau tau' ? ?;rewrite /eqTopological eqEsubset.
  Qed.

  (* 
  Definition Topologies := Topological T.
  HB.instance Definition _ Topologies := Equality.on (set_system Topologies).
  Fact topo_display : Order.disp_t. Proof. exact. Qed.

  Definition eqTopologies : eqType := Topologies.

  HB.instance Definition _ := @Order.isPOrder.Build topo_display Topologies
                                finer _ (fun _ _ => erefl) finer_reflexive finer_anti finer_transitive.
  *)
  
End Topology_porder.

Section Intersection_Topology.

  (** * Intersection topology *)
  Definition inter_topology {T : Type} (I: Type) (Tc : I -> Topological T) : Type := T.
  
  Variables (T: choiceType) (I: Type) (Tc: I -> Topological T).

  Local Notation W := (@inter_topology T I Tc).
  
  Definition open_sets' : set (set T) := [ set O: (set T) | forall (i:I), (@open (Topological.Pack (Tc i))) O].
  
  Local Lemma openT : open_sets' [set: W].
  Proof. rewrite /mkset => i;by apply: openT. Qed.
  
  Local Lemma openI : forall A B : set W, 
      open_sets' A -> open_sets' B -> open_sets' (A `&` B).
  Proof. move => A B H1 H2. rewrite /mkset => i. by apply: openI.  Qed.
  
  Local Lemma open_bigU (J : Type) (f : J -> set W):
    (forall (i : J), open_sets' (f i)) -> open_sets' (\bigcup_i f i).
  Proof.  move => H1; rewrite /mkset => i.
          apply: bigcup_open => i0 H2. 
          move: H1;rewrite /open_sets' /mkset => H1.
          by [].
  Qed.
  
  HB.instance Definition _ := Choice.on W.
  Set Warnings "-redundant-canonical-projection".
  HB.instance Definition _ := isOpenTopological.Build W openT openI open_bigU.
  
End Intersection_Topology.

Section Intersection_Topology_facts. 

  Variables (T: choiceType) (I: Type) (Tc : I -> Topological T).
  
  (* recover the opensets of Tau *)
  Lemma topologyI_opens: 
    @open (@inter_topology T I Tc) =
      [ set O :set T | forall (i:I), (@open (Topological.Pack (Tc i))) O].
  Proof. by rewrite predeqE /mkset => O. Qed.
  
  Lemma topologyI_coarser (i:I):
    (@open (@inter_topology T I Tc)) `<=` (@open (Topological.Pack (Tc i))).
  Proof.
    by rewrite topologyI_opens /mkset.    
  Qed.
  
End Intersection_Topology_facts. 

Section Intersection_Topology_Ex.
  (** * using previous definition we consider  *)
  (** * intersection topology of a set of topologies Tc*)

  Variables (T: choiceType) (Tc: set (Topological T)).

  Definition I := {tau: (Topological T) | tau \in Tc}.
  
  Definition TopologyI := (Topological.class (@inter_topology T I (fun i => val i))).
  
  Lemma inter_is_coarser: forall (tau: I), finer (val tau) TopologyI.
  Proof. by move => tau;apply: topologyI_coarser. Qed.

End Intersection_Topology_Ex.

(** * Alexandrov Topologies *)

HB.mixin Record isAOpenTopological T of Topological T  := {
  op_bigI : forall (I : Type) (f : I -> set T), (forall i, open (f i)) ->
    open (\bigcap_i f i);
}.

#[short(type="atopologicalType")]
(** * addin & at the end for default pulling of dependencies *)
HB.structure Definition ATopological := { T of isAOpenTopological T & Topological T}.

Section Alexandrov_props.

  Variables (T: atopologicalType).
  
  Lemma closureU: forall (I : Type) (f : I -> set T),
       \bigcup_i (closure (f i)) = closure (\bigcup_i f i).
  Proof.
    move => I f.
    (** step 1: (\bigcup_i (closure (f i))) is closed *)
    have H1: open (~` \bigcup_i (closure (f i)))
      by rewrite setC_bigcup;apply: op_bigI => i;apply/closed_openC/closed_closure.
    have H2: ~`(~` (\bigcup_i (closure (f i)))) = (\bigcup_i (closure (f i))) 
      by rewrite setCK.
    have H3: closed (\bigcup_i (closure (f i)))
      by rewrite -H2; apply: open_closedC.
    (** step 2: H6: \bigcup_i (closure (f i)) `<=` closure (\bigcup_i (f i)). *)
    have H4: forall (i:I ), (f i) `<=` (\bigcup_i (f i))
        by move => i; apply: bigcup_sup.
    have H5: forall (i:I ), (closure (f i)) `<=` closure (\bigcup_i (f i))
        by move => i; apply: closure_subset.
    have H6: \bigcup_i (closure (f i)) `<=` closure (\bigcup_i (f i))
      by move => i; apply: bigcup_sub.
    (** step 3 *)
    have H7: \bigcup_i (f i) `<=` (\bigcup_i (closure (f i))).
    by apply: subset_bigcup;move => i H8;apply: subset_closure.
    (** Conclusion *) 
    by apply: closure_if1 H3 H7 H6.
  Qed.
  
End Alexandrov_props.

Section Intermediate_results_closed.
  (** * properties of closed sets in topological relation *)

  Context (T: Type) (R: relation T). 
  
  Lemma Rclosed1: [set X | R.*#X = X ] = [set X | R.*#X `<=` X].
  Proof.
    rewrite predeqE /mkset => X;split => [-> // | ?].
    have H1: X `<=` R.*#X
      by rewrite -DuT_eq_Tstar -FsetUl Fset_D;apply: subsetUl.
    by rewrite eqEsubset.
  Qed.
  
  Lemma Rclosed2: [set X | R.*#X `<=` X] = [set X | R.+#X `<=` X].
  Proof.
    rewrite predeqE /mkset => X.
    rewrite -DuT_eq_Tstar -FsetUl Fset_D.
    split => [ H1 | H1].
    - have H2: R.+#X `<=` X `|` R.+#X by apply: subsetUr.
      by apply: (subset_trans H2 H1).
    - have H2: X `<=` X by [].
      have H3: X `|` R.+#X `<=` X `|` X by apply: setUSS.
      by move: H3;rewrite setUid.
  Qed.

  Local Lemma Rclosed3: forall (X: set T),
      R#X `<=` X -> forall (n: nat), R^(n.+1)#X `<=` X.
  Proof. 
    move =>X H1 n. 
    elim: n => [ | n H2]; first by rewrite iter1_id.
    have H3: R^(n.+2)#X = (R^(n.+1) `;` R^(1))#X
      by rewrite -iter_compose addn1.
    rewrite H3 -Fset_comp iter1_id.
    have H4: R^(n.+1)#(R#X) `<=` R^(n.+1)#(X) by apply: Fset_inc1.
    by apply: (subset_trans H4 H2).
  Qed.

  Lemma Rclosed4: [set X | R.+#X `<=` X]= [set X | R#X  `<=` X].
  Proof.
    rewrite predeqE /mkset => X.
    split => [H1 | H1 x [y [H2 H3]]].
    - have H2: R `<=` R.+ by apply: iter1_inc_clos_trans.
      have H3: R#X  `<=` R.+#X by apply: Fset_inc.
      by apply: (subset_trans H3 H1).
    - have [n H4]: exists (n:nat), R^(n.+1) (x,y) by apply: clos_t_iterk.
      have H5: R^(n.+1)#X x by (exists y).
      have H6: R^(n.+1)#X `<=` X by apply: (Rclosed3 H1).
      by move: H5 => /H6 H5.
  Qed.
  
  Lemma Rclosed: [set X | R.*#X = X] = [set X | R#X  `<=` X].
  Proof.
    by rewrite Rclosed1 Rclosed2 Rclosed4. 
  Qed.
  
End Intermediate_results_closed.

Section Intermediate_results_closed_open.
  (** * properties of closed sets in topological relation *)
  Context (T: Type).

  Lemma Rclosed6: forall (R : relation T) (X: set T),
      R#X `<=` X -> (X.^c :#R ) `<=` X.^c.
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
    by rewrite /Aset => R X /Rclosed6; rewrite setCK /Aset inverseK.
  Qed.
  
  (* from closed sets to open set via complement *)
  Lemma Rclosed_complement_open:  forall (R : relation T) (X: set T),
      R#X  `<=` X <-> (X.^c :#R ) `<=` X.^c.
  Proof.
    split;[apply: Rclosed6| apply: Rclosed7].
  Qed.
  
End Intermediate_results_closed_open.  

Section Intermediate_results_open.
  (** * properties of open sets in topological relation *)

  Context (T: Type) (R: relation T). 

  Lemma Ropen1: [set X | X:#R.* = X ] = [set X | X:#R.* `<=` X].
  Proof. by rewrite /Aset RTclosIv;apply: Rclosed1. Qed.
  
  Lemma Ropen2: [set X | X:#R.* `<=` X] = [set X | X:#R.+ `<=` X].
  Proof. by rewrite /Aset RTclosIv TclosIv;apply: Rclosed2. Qed.

  Lemma Ropen4: [set X | X:#R.+ `<=` X]= [set X | X:#R  `<=` X].
  Proof. by rewrite /Aset TclosIv; apply: Rclosed4. Qed.
  
  Lemma Ropen: [set X | X:#R.* = X] = [set X | X:#R  `<=` X].
  Proof. by rewrite Ropen1 Ropen2 Ropen4. Qed.
  
End Intermediate_results_open.


Section Relation_Topology.
  (** * aset_topology: Topology associated to a relation using the After sets *)
  
  Definition aset_topology {T : Type} (V: relation T) : Type := T.
  
  Variables (T: choiceType) (S: relation T).

  Local Notation W := (aset_topology S).
  
  Definition tau : set (set T) := [ set O | O:#S `<=` O]%O.
  
  Local Lemma openT' : tau [set: W].
  Proof. by apply:Aset_T. Qed.
  
  Local Lemma openI' : forall A B : set W, 
      tau A -> tau B -> tau (A `&` B).
  Proof. by move => A B H1 H2;apply: (Aset_stableIf H1 H2). Qed.
  
  Local Lemma open_bigU' (I : Type) (f : I -> set W):
    (forall (i : I), tau (f i)) -> tau (\bigcup_i f i).
  Proof. by apply:Aset_stableU. Qed.
  
  (** * Alexandrov topology *)
  Local Lemma open_bigI' (I : Type) (f : I -> set W):
    (forall (i : I), tau (f i)) -> tau (\bigcap_i f i).
  Proof. by apply:Aset_stableI. Qed.
  
  HB.instance Definition _ := Choice.on W.
  Set Warnings "-redundant-canonical-projection".
  HB.instance Definition _ := isOpenTopological.Build W openT' openI' open_bigU'.
  
End Relation_Topology.
 
Section Relation_Topology_props.
  (** * Checking the AsetTopology *)
  Variables (T: choiceType) (S: relation T). 

  Definition tau_S := aset_topology S.
    
  (* recover the fact that the open sets are given by tau *)
  Lemma Aset_open: [ set O | O:#S `<=` O] = @open tau_S.
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
  
  Lemma Aset_open' : [ set O | O:#S.* =  O] = @open tau_S.
  Proof. by rewrite -Aset_open -Ropen. Qed.
  
  Lemma Aset_closed: [ set O | S#O `<=` O] = @closed tau_S.
  Proof.
    rewrite predeqE /mkset => X.
    rewrite Rclosed_complement_open.
    split. 
    - move => H1. 
      have <-: X.^c.^c = X by rewrite setCK.
      apply: open_closedC.
      pose proof Aset_open as H2.
      by move: H2; rewrite predeqE /mkset => <-.
    - move => /closed_openC H1.
      pose proof Aset_open as H2.
      by move: H2; rewrite predeqE /mkset => ->.
  Qed.
  
  Lemma Aset_closed': [ set O | S.*#O = O] = @closed tau_S.
  Proof. by rewrite Rclosed Aset_closed. Qed.

  Lemma Aset_closed1 (X: set T) : forall (B: set T),
      @closed tau_S B /\ X `<=` B -> S.*#X `<=` B.
  Proof.
    move => B. 
    pose proof Aset_closed' as H1.
    move: H1; rewrite predeqE /mkset => <-.
    move => [H2 H3].
    rewrite -H2.
    by apply: Fset_inc1.
  Qed.
  
  Lemma Aset_closure: forall (X: set T), 
      S.*#X = @closure tau_S X.
  Proof.
    move => X.
    (** step 1: X is included in S.*#X (H5) which is closed (H6) *)
    have H4: S.*#X = S.*#(S.*#X) by rewrite Fset_comp compose_rt_rt.
    have H5: X `<=` S.*#X by rewrite -DuT_eq_Tstar -FsetUl Fset_D;apply: subsetUl.
    have H6: @closed tau_S S.*#X 
      by pose proof Aset_closed' as H1;move: H1; rewrite predeqE /mkset => <-.
    (** step 2 S.*#X `<=` @closure tau_S X. *)
    pose proof Aset_closed1 as H7;move: H7 => /(_ X) H7.
    have H9:  S.*#X `<=` @closure tau_S X
      by rewrite closureE;apply: sub_bigcap => Y;rewrite /mkset => -[H9 H10];apply: H7.
    (** conclude *)
    by apply: closure_if1 H6 H5 H9.
  Qed.

  (** Question: Pourquoi est-ce que tau_S est la + coarser parmi les topologies telles 
      que closure x = S.*#{x} pour tout x
   *)

End Relation_Topology_props.

Section Porder_Topology.
  (** * Topology associated to a porder *) 
  (** This is the topology associated to the after sets of the binary relation
      defined by the porder *)
  Context (disp : Order.disp_t).
  Variable (T : porderType disp).

  Definition rel_porder := [set xy : T*T| (xy.1 <= xy.2)%O].

  Definition Porder_topology := (aset_topology rel_porder). 

  Lemma Porder_open (O: set T) : [set O | O:#(rel_porder) `<=` O] = @open Porder_topology.
  Proof. by apply: Aset_open. Qed.
  
End  Porder_Topology.


Section Specialization_Porder.
  (** * specialization relation defined from a topology *) 
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

 Definition downset (X: set T) := specialization_porder# X. 
 Definition upset (X: set T)  := X:#specialization_porder.
  
  Lemma closed_is_downset: forall (C: set T), 
      closed C -> (downset C) `<=` C.
  Proof.
    move => C H1 c [c' [H2 H3]].
    have H4: [set c'] `<=` C by rewrite sub1set inP. 
    move: H4 => /closure_subset H4.
    have ->: C = closure C by rewrite -closure_id.
    by apply H4.
  Qed.
  
  Lemma open_is_upper: forall (O: set T), 
      open O -> (upset O) `<=` O.
  Proof.
    move => O H1 c [c' [H2 H3]]. 
    absurd_not => H4.
    have H5: O.^c c by [].
    have H6: (downset O.^c) c' by (exists c).
    have H7: closed O.^c by apply: open_closedC.
    have H8: (downset O.^c) `<=` O.^c by apply: closed_is_downset.
    have H9: O.^c c' by apply H8.
    by [].
  Qed.

End Specialization_Porder.

Section finer_topology. 
  (** * If S is a preorder, the aset_topology is the finer topology among *)
  (** * all topologies having S as a specialization_porder *)
  
  Variable (T: choiceType) (S: relation T) (tau': Topological T). 

  Definition Stopologies :=
    [ set tau : Topological T | @specialization_porder (Topological.Pack tau) = S].
  
  Definition tau_S' := aset_topology S.
  
  Lemma St: @specialization_porder (aset_topology S) = S.*.
  Proof.
    rewrite /specialization_porder predeqE /mkset => -[x y] /=.
    rewrite -Aset_closure.
    split;first by rewrite /Fset => -[y1 [H1 /= <-]].
    by move => H1;rewrite /Fset /mkset /=; by exists y. 
  Qed.

  Lemma St':
    (reflexive S /\ transitive S) 
    -> @specialization_porder (aset_topology S) = S.
  Proof.
    by rewrite clos_rt_iff => H1;rewrite [RHS]H1; apply: St.
  Qed.
  
  Lemma St'' (tau: Topological T) : forall (O: set T),
    (reflexive S /\ transitive S) 
    -> @specialization_porder (Topological.Pack tau) = S
    -> @open (Topological.Pack tau) O
    -> @open (aset_topology S) O.
  Proof.
    move => O H1 H2. 
    rewrite -Aset_open /mkset => /open_is_upper H3.
    by move: H3; rewrite /upset H2.
  Qed.

  Lemma tau_S'_in :
    (reflexive S /\ transitive S)
    -> Stopologies (Topological.class tau_S').
  Proof.
    by move => H1;apply: St'.
  Qed.
  
  (** * tau_S' is the finer *) 

End finer_topology. 
