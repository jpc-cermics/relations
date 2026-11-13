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

(******************************************************************************)
(* Correspondence between rel.v (relation T = set (T*T)) and the               *)
(* RelationAlgebra library (hrel T T = T -> T -> Prop), in order to use the    *)
(* decision tactics ka, kat and hkat.                                          *)
(*                                                                             *)
(* Dictionary of operations:                                                   *)
(*                                                                             *)
(*   rel.v          RelationAlgebra                                            *)
(*   -----------------------------------------------------------------------   *)
(*   relation T     hrel T T         (T*T) -> Prop  /  T -> T -> Prop          *)
(*   R = S          R ≡ S     (weq)  equality / extensional equivalence        *)
(*   R `<=` S       R ≦ S     (leq)  inclusion                                 *)
(*   R `;` S        R ⋅ S     (dot)  composition                               *)
(*   'Δ             1         (one)  identity                                  *)
(*   'Δc            0         (bot)  empty relation                            *)
(*   set0           0         (bot)  empty relation                            *)
(*   setT           top       (top)  full relation                             *)
(*   relT           top       (top)  same, named (= setT : relation T)         *)
(*   R `|` S        R + S     (cup)  union                                     *)
(*   R `&` S        R ∩ S     (cap)  intersection                              *)
(*   R.^c           !R        (neg)  complement                                *)
(*   R^-1           R°        (cnv)  converse                                  *)
(*   R^{*}          R^*       (str)  reflexive-transitive closure              *)
(*   R^{+}          R^+       (itr)  transitive closure                        *)
(*   Δ_(X)          [pset X]  (inj)  KAT test                                  *)
(*   Δ_(X.^c)       [!pset X]        complemented test                         *)
(*   L_(X)          [pset X]⋅top                                               *)
(*   R_(X)          top⋅[pset X]                                               *)
(*   R |_(X)        [pset X]⋅R⋅[pset X]                                        *)
(*                                                                             *)
(* Sets (seen as vectors, cf. [vec] and section Vec):                          *)
(*   set T          hrel T unit      heterogeneous relation to a singleton     *)
(*   X = Y          vec X ≡ vec Y                                              *)
(*   X `<=` Y       vec X ≦ vec Y                                              *)
(*   R#X            R ⋅ vec X        foreset                                   *)
(*   X:#R           R° ⋅ vec X       afterset                                  *)
(*   X `|` Y        vec X + vec Y                                              *)
(*   X `&` Y        vec X ∩ vec Y                                              *)
(*   set0 / setT    0 / top                                                    *)
(*                                                                             *)
(* Transport:                                                                  *)
(*   to_hrel R : hrel T T      from rel.v to RelationAlgebra                   *)
(*   of_hrel H : relation T    from RelationAlgebra to rel.v                   *)
(*   pset X    : dset T        from set T to (boolean) KAT tests               *)
(*   vec X     : hrel T unit   from set T to vectors                           *)
(*                                                                             *)
(* Provided tactics:                                                           *)
(*   to_ra_goal : puts the goal in RelationAlgebra form.  Recognizes R = S,    *)
(*                R `<=` S, reflexive R, symmetric R, transitive R, as well as *)
(*                X = Y and X `<=` Y on sets (via vec)                         *)
(*   to_ra      : same, also transporting the hypotheses                       *)
(*   rka        : to_ra_goal then ka      (Kleene algebra)                     *)
(*   rkat       : to_ra_goal then kat     (Kleene algebra with tests)          *)
(*   rhkat      : to_ra      then hkat    (same, with Hoare hypotheses)        *)
(*   rlattice   : to_ra_goal then lattice (bounded lattice: `|`, `&`, set0, setT) *)
(*   rra        : to_ra_goal then ra      (normalisation, weaker goals)        *)
(*   ra_cnv     : pushes converse down to atoms (cnvdot, cnvstr, ...)          *)
(*   rka_cnv    : to_ra_goal then ra_cnv then ka                               *)
(*   rkat_cnv   : to_ra_goal then ra_cnv then kat                              *)
(*                                                                             *)
(* Limitations (cf. section Limites at the end of the file):                   *)
(*   - ka/kat/hkat do not decide fragments containing ^-1 (converse),          *)
(*     `&` (intersection), .^c (complement) or setT (top).                     *)
(*   - for converse, ra_cnv pushes it down to atoms (R° becomes a              *)
(*     fresh atom): rka_cnv/rkat_cnv are then sound but incomplete.            *)
(*     This is enough in practice (cf. paper_relations.v).                     *)
(*   - lattice only decides the bounded lattice fragment, without              *)
(*     distributivity.                                                         *)
(*   - hkat only eliminates Hoare hypotheses (x ≡ 0, [c];p ≡ [c], ...);        *)
(*     a monotonicity hypothesis such as R `<=` S is not one of them.          *)
(*   - on a set goal (hence typed), hkat fails immediately, reporting          *)
(*     "typed hkat is not supported yet".  ka and kat accept typed goals.      *)
(*                                                                             *)
(* The other RelationAlgebra tactics (ra_normalise, mrewrite, dual,            *)
(* solve_rmov, aac_rewrite, ...) are used after to_ra_goal; they are           *)
(* listed in probe/tactiques-RA.md.                                            *)
(* Note: aac_rewrite (and aac_reflexivity) require the AAC instances for the   *)
(* RelationAlgebra operations, which are declared in                           *)
(* RelationAlgebra.rewriting_aac.  This module is NOT imported here (nor by    *)
(* RelationAlgebra.all): add                                                   *)
(*   From RelationAlgebra Require Import rewriting_aac.                        *)
(* to use them.                                                                *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Warnings "-parsing -coercions -notation-incompatible-prefix".
From mathcomp Require Import all_boot order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
(* Export (not Import): clients of this file need the Proper instances         *)
(* of RelationAlgebra, without which setoid_rewrite does not go under          *)
(* the operations and the translation stops after the first pass.              *)
From RelationAlgebra Require Export kat normalisation rewriting kat_tac rel.
Set Warnings "parsing coercions notation-incompatible-prefix".

(* rel.v is loaded last, and exported: its names (relation, compose,           *)
(* iter, ...) must shadow, for clients, those of RelationAlgebra.rel and       *)
(* of Stdlib (Relation_Definitions.relation).  Importing rel_ra is enough,     *)
(* and must be done AFTER the other mathcomp imports.                          *)
From RL Require Export rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * Transport between [relation T] and [hrel T T] *)

Definition to_hrel (T: Type) (R: relation T) : hrel T T := fun x y => R (x,y).
Definition of_hrel (T: Type) (H: hrel T T) : relation T := fun xy => H xy.1 xy.2.

(* injection of a set in boolean tests of KAT *)
Definition pset (T: Type) (X: set T) : dset T := fun x => `[< X x >].

(* a subset seen as a "vector": a heterogeneous relation to a                *)
(* singleton.  The RelationAlgebra monoid is a category, and ka/kat          *)
(* accept typed goals: we can thus decide set equalities built               *)
(* on foresets/aftersets.  (hkat, however, rejects typed goals.)             *)
Definition vec (T: Type) (X: set T) : hrel T unit := fun x _ => X x.

Arguments to_hrel {T} R.
Arguments of_hrel {T} H.
Arguments pset {T} X.
Arguments vec {T} X.

Section Transport.
  Variable (T: Type).
  Variables (R S: relation T) (H: hrel T T).

  Lemma of_hrelK : of_hrel (to_hrel R) = R.
  Proof. by apply/funext => -[x y]. Qed.

  Lemma to_hrelK : to_hrel (of_hrel H) ≡ H.
  Proof. by []. Qed.

  (** inclusion and equality *)

  Lemma to_hrel_leqE : (R `<=` S) <-> (to_hrel R ≦ to_hrel S).
  Proof.
  split => [h x y hxy | h [x y] hxy]; first by apply: (h (x,y) hxy).
  exact: (h x y hxy).
  Qed.

  Lemma to_hrel_weqE : (R = S) <-> (to_hrel R ≡ to_hrel S).
  Proof.
  split => [-> // | h]; apply/funext => -[x y]; apply/propext.
  exact: (h x y).
  Qed.

  (* oriented versions, used by the tactics *)
  Lemma to_hrel_leqW : to_hrel R ≦ to_hrel S -> R `<=` S.
  Proof. by rewrite to_hrel_leqE. Qed.

  Lemma to_hrel_weqW : to_hrel R ≡ to_hrel S -> R = S.
  Proof. by rewrite to_hrel_weqE. Qed.

  Lemma to_hrel_leqF : R `<=` S -> to_hrel R ≦ to_hrel S.
  Proof. by rewrite to_hrel_leqE. Qed.

  Lemma to_hrel_weqF : R = S -> to_hrel R ≡ to_hrel S.
  Proof. by rewrite to_hrel_weqE. Qed.

  (** predicates of rel.v expressed in RelationAlgebra *)

  Lemma to_hrel_reflW : (1 ≦ to_hrel R)%ra -> reflexive R.
  Proof. by move => h x; exact: (h x x (erefl x)). Qed.

  Lemma to_hrel_symW : ((to_hrel R)° ≦ to_hrel R)%ra -> symmetric R.
  Proof. by move => h x y hxy; exact: (h y x hxy). Qed.

  Lemma to_hrel_transW : (to_hrel R ⋅ to_hrel R ≦ to_hrel R)%ra -> transitive R.
  Proof. by move => h y x z h1 h2; apply: (h x z); exists y. Qed.

End Transport.

(** * [to_hrel] is a morphism for all operations *)

Section Morphism.
  Variable (T: Type).
  Implicit Types (R S: relation T) (X Y: set T).

  (** lattice structure *)

  Lemma to_hrel_setU R S : to_hrel (R `|` S) ≡ (to_hrel R + to_hrel S)%ra.
  Proof. by []. Qed.

  Lemma to_hrel_setI R S : to_hrel (R `&` S) ≡ (to_hrel R ∩ to_hrel S)%ra.
  Proof. by []. Qed.

  Lemma to_hrel_set0 : to_hrel (set0: relation T) ≡ (0%ra: hrel T T).
  Proof. by []. Qed.

  Lemma to_hrel_setT : to_hrel (setT: relation T) ≡ (top: hrel T T).
  Proof. by []. Qed.

  (* relT is setT at type relation T, but autorewrite is syntactic:        *)
  (* without this rule relT would remain an opaque atom for the tactics.   *)
  Lemma to_hrel_relT : to_hrel (relT: relation T) ≡ (top: hrel T T).
  Proof. by []. Qed.

  (* complement does not belong to the fragment decided by ka/kat *)
  Lemma to_hrel_setC R : to_hrel (R.^c) ≡ (!(to_hrel R))%ra.
  Proof. by []. Qed.

  (** monoid structure *)

  Lemma to_hrel_compose R S : to_hrel (R `;` S) ≡ (to_hrel R ⋅ to_hrel S)%ra.
  Proof. by move => x y; split => [[z [h1 h2]] | [z h1 h2]]; exists z. Qed.

  Lemma to_hrel_Delta : to_hrel ('Δ: relation T) ≡ (1%ra: hrel T T).
  Proof. by move => x y; rewrite /to_hrel /delta /=; split => [[_ ->] | ->]. Qed.

  Lemma to_hrel_DeltaC : to_hrel ('Δc: relation T) ≡ (0%ra: hrel T T).
  Proof.
  move => x y; rewrite /to_hrel /deltaC /delta /=.
  by split => [[h _] | //]; exact: (h I).
  Qed.

  Lemma to_hrel_inverse R : to_hrel (R^-1) ≡ ((to_hrel R)°)%ra.
  Proof. by []. Qed.

  (** tests *)

  Lemma to_hrel_Delta_set X : to_hrel (Δ_(X)) ≡ ([pset X])%ra.
  Proof.
  move => x y; rewrite /to_hrel /delta /=; split.
  - by move => [h e]; split; [| apply/asboolP].
  - by move => [e h]; split; [apply/asboolP |].
  Qed.

  Lemma to_hrel_DeltaC_set X : to_hrel (deltaC X) ≡ ([pset (~` X)])%ra.
  Proof. exact (to_hrel_Delta_set (~` X)). Qed.

  Lemma to_hrel_Lr X : to_hrel (L_(X)) ≡ ([pset X] ⋅ top)%ra.
  Proof.
  move => x y; rewrite /to_hrel /lrel /=; split.
  - by move => h; exists x; [split; [| apply/asboolP] |].
  - by move => [z [e h] _]; apply/asboolP.
  Qed.

  Lemma to_hrel_Rr X : to_hrel (R_(X)) ≡ (top ⋅ [pset X])%ra.
  Proof.
  move => x y; rewrite /to_hrel /rrel /=; split.
  - by move => h; exists y; [| split; [| apply/asboolP]].
  - by move => [z _ [e h]]; rewrite -e; apply/asboolP.
  Qed.

  (** closures *)

  Lemma to_hrel_RTclos R : to_hrel (R^{*}) ≡ ((to_hrel R)^*)%ra.
  Proof.
  have Hrf: (1 ≦ (to_hrel R)^*)%ra by apply: str_refl.
  have Htr: ((to_hrel R)^* ⋅ (to_hrel R)^* ≦ (to_hrel R)^*)%ra by rewrite str_trans.
  have Hex: (to_hrel R ≦ (to_hrel R)^*)%ra by apply: str_ext.
  apply: antisym.
  - apply: (to_hrel_leqF (S := of_hrel ((to_hrel R)^*)%ra)).
    apply: rtclos_ind => [y x z h1 h2 | x | [x y] h].
    + by apply: (Htr x z); exists y.
    + exact: (Hrf x x (erefl x)).
    + exact: (Hex x y h).
  - apply: str_ind_l1 => [x y e | x y [z h1 h2]].
    + by rewrite /to_hrel -e; exact: (@rtclos_refl T R x).
    + by apply: (@rtclos_trans T R z x y) => //; exact: (@rtclos_sub T R (x,z) h1).
  Qed.

  Lemma to_hrel_Tclos R : to_hrel (R^{+}) ≡ ((to_hrel R)^+)%ra.
  Proof.
  have Htr: ((to_hrel R)^+ ⋅ (to_hrel R)^+ ≦ (to_hrel R)^+)%ra by apply: itr_trans.
  have Hex: (to_hrel R ≦ (to_hrel R)^+)%ra by apply: itr_ext.
  apply: antisym.
  - apply: (to_hrel_leqF (S := of_hrel ((to_hrel R)^+)%ra)).
    apply: tclos_transS => [y x z h1 h2 | [x y] h].
    + by apply: (Htr x z); exists y.
    + exact: (Hex x y h).
  - apply: itr_ind_l1 => [x y h | x y [z h1 h2]].
    + exact: (@tcl_sub T R (x,y) h).
    + by apply: (@comp_tclosS T R (x,y)); exists z.
  Qed.

End Morphism.

(** * Operations on tests *)

Section Pset.
  Variable (T: Type).
  Implicit Types (X Y: set T).

  Lemma psetE X x : (pset X x : Prop) = X x.
  Proof. exact: asboolE. Qed.

  Lemma psetU X Y : (pset (X `|` Y) ≡ pset X ⊔ pset Y)%ra.
  Proof. by move => x; rewrite /pset /setU /= asbool_or. Qed.

  Lemma psetI X Y : (pset (X `&` Y) ≡ pset X ⊓ pset Y)%ra.
  Proof. by move => x; rewrite /pset /setI /= asbool_and. Qed.

  Lemma psetC X : (pset (~` X) ≡ !(pset X))%ra.
  Proof. by move => x; rewrite /pset /setC /= asbool_neg. Qed.

  Lemma psetT : (pset (setT: set T) ≡ top)%ra.
  Proof. by move => x; exact: (asboolT I). Qed.

  Lemma pset0 : (pset (set0: set T) ≡ bot)%ra.
  Proof. by move => x; apply: asboolF. Qed.

End Pset.

(** * Converse: RelationAlgebra laws specialised to [hrel]                   *)

(* The general laws (cnvdot, cnvstr, ...) are about an unknown structure;     *)
(* [rewrite ?cnvdot] then unfolds hrel_cnv into a lambda and destroys         *)
(* the goal.  We thus specialise them to hrel, which makes them usable        *)
(* by autorewrite.                                                            *)

Section Cnv.
  Variable (T: Type).
  Implicit Types (R S: hrel T T).

  Lemma hcnvdot R S : (((R ⋅ S)° ≡ S° ⋅ R°))%ra.   Proof. exact: cnvdot. Qed.
  Lemma hcnvstr R : (((R^*)° ≡ (R°)^*))%ra.        Proof. exact: cnvstr. Qed.
  Lemma hcnvitr R : (((R^+)° ≡ (R°)^+))%ra.        Proof. exact: cnvitr. Qed.
  Lemma hcnvpls R S : (((R + S)° ≡ R° + S°))%ra.   Proof. exact: cnvpls. Qed.
  Lemma hcnvcap R S : (((R ∩ S)° ≡ R° ∩ S°))%ra.   Proof. exact: cnvcap. Qed.
  Lemma hcnvinvol R : (((R°)° ≡ R))%ra.            Proof. exact: cnv_invol. Qed.
  Lemma hcnv1 : (((1: hrel T T)° ≡ 1))%ra.         Proof. exact: cnv1. Qed.
  Lemma hcnv0 : (((0: hrel T T)° ≡ 0))%ra.         Proof. exact: cnv0. Qed.
  Lemma hcnvtop : (((top: hrel T T)° ≡ top))%ra.   Proof. exact: cnvtop. Qed.

  (* a test is self-converse; missing from RelationAlgebra.  Stated for      *)
  (* an arbitrary test (not only pset X) so as to also catch compound        *)
  (* tests [!p], [p ⊔ q], ...                                                *)
  Lemma hcnv_inj (p: dset T) : (([p])° ≡ [p])%ra.
  Proof. by move => x y; split => [[e h] | [e h]]; split; rewrite ?e ?(esym e). Qed.

End Cnv.

(** * Sets seen as vectors                                                   *)

(* [vec] is a morphism of the lattice of subsets, and turns                  *)
(* foreset/afterset into composition.  This is what allows ka to decide      *)
(* equalities about sets and not only about relations.                       *)

Section Vec.
  Variable (T: Type).
  Implicit Types (R: relation T) (X Y: set T).

  Lemma vec_leqE X Y : (X `<=` Y) <-> (vec X ≦ vec Y).
  Proof. by split => h x; [move => [] | move => hx; exact: (h x tt hx)]; exact: h. Qed.

  Lemma vec_weqE X Y : (X = Y) <-> (vec X ≡ vec Y).
  Proof.
  by split => [-> // | h]; apply/funext => x; apply/propext; exact: (h x tt).
  Qed.

  Lemma vec_leqW X Y : vec X ≦ vec Y -> X `<=` Y.
  Proof. by rewrite vec_leqE. Qed.

  Lemma vec_weqW X Y : vec X ≡ vec Y -> X = Y.
  Proof. by rewrite vec_weqE. Qed.

  Lemma vec_leqF X Y : X `<=` Y -> vec X ≦ vec Y.
  Proof. by rewrite vec_leqE. Qed.

  Lemma vec_weqF X Y : X = Y -> vec X ≡ vec Y.
  Proof. by rewrite vec_weqE. Qed.

  (** morphism *)

  Lemma vec_Fset R X : vec (R#X) ≡ (to_hrel R ⋅ vec X)%ra.
  Proof. by move => x []; split => [[y [h1 h2]] | [y h1 h2]]; exists y. Qed.

  Lemma vec_Aset R X : vec (X:#R) ≡ ((to_hrel R)° ⋅ vec X)%ra.
  Proof. exact: vec_Fset. Qed.

  Lemma vec_setU X Y : vec (X `|` Y) ≡ (vec X + vec Y)%ra.
  Proof. by []. Qed.

  Lemma vec_setI X Y : vec (X `&` Y) ≡ (vec X ∩ vec Y)%ra.
  Proof. by []. Qed.

  Lemma vec_setC X : vec (~` X) ≡ (!(vec X))%ra.
  Proof. by []. Qed.

  Lemma vec_set0 : vec (set0: set T) ≡ (0%ra: hrel T unit).
  Proof. by []. Qed.

  Lemma vec_setT : vec (setT: set T) ≡ (top: hrel T unit).
  Proof. by []. Qed.

  (** link between the test and the vector of the same set                  *)

  (* This is the piece missing to the decision tactics: for them,           *)
  (* [pset X] and vec X are two independent atoms, whereas they             *)
  (* denote the same X.  The identity below is what connects them.          *)
  Lemma vec_pset X : vec X ≡ ([pset X] ⋅ top)%ra.
  Proof.
  move => x []; rewrite /vec /pset /=; split.
  - by move => h; exists x; [split; [| apply/asboolP] |].
  - by move => [z [e h] _]; apply/asboolP.
  Qed.

End Vec.

(** * First entry point into a set                                          *)

(* Recurring proof pattern: to reach X, one may assume X was not            *)
(* visited before the end.  This is equation (27) of the csbr paper,        *)
(* i.e. B_L7_E25 / fset_rtclos_deltaC.                                      *)
(*                                                                          *)
(* Out of reach of ka/kat/hkat, and not by accident: the statement relies   *)
(* on the fact that [p] and v denote the same set, an information the       *)
(* decision procedures cannot have since they treat atoms as                *)
(* independent.  The hypothesis [p]⋅top ≡ v provides it; it is itself       *)
(* outside the fragment, since it mentions top.                             *)
(*                                                                          *)
(* The proof is the first-entry-point argument, in KAT + top:               *)
(* ≦ by monotonicity ([!p] ≦ 1), ≧ by str_ind_l' splitting 1 ≡ [p] + [!p]   *)
(* - the [p] branch falls back into the vector, the [!p] branch consumes    *)
(* one step.  This is the same splitting as the induction on the length     *)
(* of the path in the set-based proof (cf. rel1.v).                         *)

Section First_entry.
  Variable (T: Type).

  Lemma first_entry (p: dset T) (r: hrel T T) (v: hrel T unit) :
    (([p]⋅top ≡ v) -> (inj (neg p)⋅r)^*⋅v ≡ r^*⋅v)%ra.
  Proof.
  move => hv.
  have h1: ((inj (neg p): hrel T T) ≦ 1)%ra
    by rewrite -inj_top; apply: inj_leq; apply: leq_xt.
  have hcup: (([p] + inj (neg p): hrel T T) ≡ 1)%ra
    by rewrite -inj_cup cupneg inj_top.
  apply: antisym.
  - apply: dot_leq; last by [].
    by apply: str_leq; rewrite -[X in _ ≦ X]dot1x; apply: dot_leq.
  - apply: str_ind_l'.
    + by rewrite -[X in X ≦ _]dot1x; apply: dot_leq; last by []; apply: str_refl.
    + rewrite -[X in X ≦ _]dot1x -hcup dotplsx; apply/cup_spec; split.
      * transitivity ([p]⋅(top: hrel T unit))%ra;
          first by apply: dot_leq; last by apply: leq_xt.
        by rewrite hv -[X in X ≦ _]dot1x; apply: dot_leq; last by []; apply: str_refl.
      * by rewrite 2!dotA; apply: dot_leq; last by []; apply: str_cons.
  Qed.

  (* Variant with a witness: instead of concluding in a given vector, we      *)
  (* keep track of the first entry point in the form [p]⋅top.  Same           *)
  (* argument, and here [p], r and top are unrelated objects: this is a       *)
  (* genuine theorem of KAT + top, which escapes kat only because kat         *)
  (* stops at KAT.                                                            *)
  (*                                                                          *)
  (* Applies directly, after to_ra_goal, to any goal of the form              *)
  (*     R^{*} `<=` (Δ_(Y.^c) `;` R)^{*} `;` ('Δ `|` Δ_(Y) `;` relT)          *)
  Lemma first_entry_wit (p: dset T) (r: hrel T T) :
    (r^* ≦ (inj (neg p)⋅r)^*⋅(1 + [p]⋅top))%ra.
  Proof.
  have hcup: (([p] + inj (neg p): hrel T T) ≡ 1)%ra
    by rewrite -inj_cup cupneg inj_top.
  set z := ((inj (neg p)⋅r)^*⋅(1 + [p]⋅top))%ra.
  have h1: ((1: hrel T T) ≦ z)%ra.
    rewrite /z -[X in X ≦ _]dot1x; apply: dot_leq; first by apply: str_refl.
    by apply: leq_xcup; left.
  apply: str_ind_l1 => //.
  rewrite -[X in X⋅_ ≦ _]dot1x -hcup dotplsx dotplsx; apply/cup_spec; split.
  - (* [p] branch: we enter the set, the witness [p]⋅top absorbs *)
    rewrite -dotA; transitivity ([p]⋅(top: hrel T T))%ra;
      first by apply: dot_leq; [reflexivity | apply: leq_xt].
    rewrite /z -[X in X ≦ _]dot1x; apply: dot_leq; first by apply: str_refl.
    by apply: leq_xcup; right.
  - (* [!p] branch: we stay outside, one step is consumed *)
    by rewrite /z dotA; apply: dot_leq; [apply: str_cons | reflexivity].
  Qed.

End First_entry.

(** * Tactics *)

(* Two passes: [hrel_morph] translates the structure (and the two special    *)
(* cases 'Δ and 'Δc), then [hrel_test] translates the remaining Δ_(X)        *)
(* into KAT tests.  Order matters: Δ_(setT) must become 1, not [pset setT].  *)

Create HintDb hrel_morph discriminated.
Create HintDb hrel_test discriminated.

#[export] Hint Rewrite
  to_hrel_compose to_hrel_setU to_hrel_setI to_hrel_inverse
  to_hrel_RTclos to_hrel_Tclos
  to_hrel_Delta to_hrel_DeltaC
  to_hrel_Lr to_hrel_Rr
  to_hrel_set0 to_hrel_setT to_hrel_relT : hrel_morph.

#[export] Hint Rewrite
  to_hrel_Delta_set to_hrel_DeltaC_set
  psetU psetI psetC psetT pset0 : hrel_test.

(* Sets are decomposed first: vec_setU must come before vec_Fset,            *)
(* otherwise vec (X `|` R#Y) stays stuck and ka fails on a truncated         *)
(* goal.  autorewrite iterates to a fixpoint, which [rewrite !] does not.    *)
#[export] Hint Rewrite
  vec_Fset vec_Aset vec_setU vec_setI vec_set0 vec_setT : vec_morph.

(* puts the goal in the form [_ ≡ _] or [_ ≦ _] in RelationAlgebra *)
Ltac to_ra_goal :=
  intros;
  (apply: to_hrel_weqW || apply: to_hrel_leqW
   || apply: to_hrel_reflW || apply: to_hrel_symW || apply: to_hrel_transW
   || apply: vec_weqW || apply: vec_leqW
   || idtac);
  autorewrite with vec_morph;
  autorewrite with hrel_morph; autorewrite with hrel_test.

(* also transports the hypotheses (needed for hkat) *)
Ltac to_ra_hyps :=
  intros;
  repeat match goal with
  | h : _ = _ |- _ =>
      let h' := fresh "h" in
      ((have h' := to_hrel_weqF h) || (have h' := vec_weqF h)); clear h;
      autorewrite with vec_morph in h';
      autorewrite with hrel_morph in h'; autorewrite with hrel_test in h'
  | h : _ `<=` _ |- _ =>
      let h' := fresh "h" in
      ((have h' := to_hrel_leqF h) || (have h' := vec_leqF h)); clear h;
      autorewrite with vec_morph in h';
      autorewrite with hrel_morph in h'; autorewrite with hrel_test in h'
  end.

Ltac to_ra := to_ra_hyps; to_ra_goal.

(* pushes converse down to atoms: ka/kat then see R° as a fresh atom.          *)
(* Sound but incomplete (the equational theory of KA + converse is not         *)
(* decided by these tactics).                                                  *)
Create HintDb hrel_cnv discriminated.
#[export] Hint Rewrite
  hcnvdot hcnvstr hcnvitr hcnvpls hcnvcap hcnvinvol
  hcnv1 hcnv0 hcnvtop hcnv_inj : hrel_cnv.

Ltac ra_cnv := autorewrite with hrel_cnv.

Ltac to_ra_cnv := to_ra_goal; ra_cnv.

Ltac rka := to_ra_goal; ka.
Ltac rkat := to_ra_goal; kat.
Ltac rhkat := to_ra; hkat.
Ltac rlattice := to_ra_goal; lattice.
Ltac rra := to_ra_goal; ra.
Ltac rka_cnv := to_ra_cnv; ka.
Ltac rkat_cnv := to_ra_cnv; kat.

(** * Tests *)

Section Tests.
  Variable (T: Type).
  Variables (R S U: relation T) (X Y W: set T).

  (** ** Kleene algebra: rka *)

  Goal (R `|` S)^{*} = (R^{*} `;` S^{*})^{*} .
  Proof. by rka. Qed.

  Goal R^{*} `;` R^{*} = R^{*} .
  Proof. by rka. Qed.

  Goal (R `;` S)^{*} `;` R = R `;` (S `;` R)^{*} .
  Proof. by rka. Qed.

  Goal R^{+} = R `;` R^{*} .
  Proof. by rka. Qed.

  Goal 'Δ `|` R^{+} = R^{*} .
  Proof. by rka. Qed.

  Goal R^{*} `<=` (R `|` S)^{*} .
  Proof. by rka. Qed.

  (** ** Kleene algebra with tests: rkat *)

  Goal Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof. by rkat. Qed.

  Goal (Δ_(X) `;` R)^{*} `;` Δ_(X) = Δ_(X) `;` (R `;` Δ_(X))^{*} .
  Proof. by rkat. Qed.

  Goal Δ_(X) `;` Δ_(X.^c) = set0.
  Proof. by rkat. Qed.

  Goal Δ_(X `&` Y) = Δ_(X) `;` Δ_(Y).
  Proof. by rkat. Qed.

  Goal Δ_(X) `|` Δ_(X.^c) = 'Δ.
  Proof. by rkat. Qed.

  Goal Δ_(X) `;` R `<=` R.
  Proof. by rkat. Qed.

  Goal (R |_(X))^{+} `<=` Δ_(X) `;` R^{+} `;` Δ_(X).
  Proof. by rkat. Qed.

  (** ** Hoare hypotheses: rhkat *)

  Goal R `;` S = set0 -> R `;` S `;` U = set0.
  Proof. by rhkat. Qed.

  Goal Δ_(X) `;` R = R `;` Δ_(X) -> Δ_(X) `;` R^{*} = R^{*} `;` Δ_(X).
  Proof. by rhkat. Qed.

  (** ** predicates reflexive / symmetric / transitive *)

  Goal reflexive (R^{*}).
  Proof. by rka. Qed.

  Goal transitive (R^{+}).
  Proof. by rka. Qed.

  Goal symmetric (R `|` R^-1).
  Proof. by rka_cnv. Qed.

  Goal symmetric (Δ_(X) `;` R^-1 `;` R `;` Δ_(X)).
  Proof. by rka_cnv. Qed.

  (** ** sets (foresets / aftersets): the same tactics *)

  Goal (R `;` S)#X = R#(S#X).
  Proof. by rka. Qed.

  Goal R^{*}#(R^{*}#X) = R^{*}#X.
  Proof. by rka. Qed.

  Goal R^{*}#X = X `|` R#(R^{*}#X).
  Proof. by rka. Qed.

  Goal (R `|` S)^{*}#X = (R^{*} `;` S^{*})^{*}#X.
  Proof. by rka. Qed.

  Goal R#(X `|` Y) = R#X `|` R#Y.
  Proof. by rka. Qed.

  Goal R^{+}#X = R#(R^{*}#X).
  Proof. by rka. Qed.

  Goal R#X `<=` R^{*}#X.
  Proof. by rka. Qed.

  (* idempotence of a closure: the shape of Fset_CW / CBK_Clos *)
  Goal Clos(X|R,W) = Clos(Clos(X|R,W)|R,W).
  Proof. by rka. Qed.

  Goal (X:#R) = R^-1#X.
  Proof. by rka. Qed.

  (** ** lattice: rlattice *)

  Goal R `&` S `<=` R.
  Proof. by rlattice. Qed.

  Goal R `|` S = S `|` R.
  Proof. by rlattice. Qed.

End Tests.

(** * Examples: lemmas of rel.v reproved in one line *)

Section Exemples.
  Variable (T: Type).
  Variables (R S: relation T) (X: set T).

  (* compA *)
  Goal (R `;` S) `;` R = R `;` (S `;` R).
  Proof. by rka. Qed.

  (* rtclosE *)
  Goal R^{*} = 'Δ `|` R^{+} .
  Proof. by rka. Qed.

  (* rtclos_compE *)
  Goal R^{*} `;` R = R^{+} .
  Proof. by rka. Qed.

  (* tclosUl *)
  Goal R `|` (R `;` R^{+}) = R^{+} .
  Proof. by rka. Qed.

  (* tclosUr *)
  Goal R `|` (R^{+} `;` R) = R^{+} .
  Proof. by rka. Qed.

  (* tclosU_comp *)
  Goal R^{+} `|` (R^{+} `;` R^{+}) = R^{+} .
  Proof. by rka. Qed.

  (* tclos_compK *)
  Goal (R^{+} `;` R^{+}) `<=` R^{+} .
  Proof. by rka. Qed.

  (* comp_tclosS / tclos_compS *)
  Goal (R `;` R^{+}) `<=` R^{+} .
  Proof. by rka. Qed.

  Goal (R^{+} `;` R) `<=` R^{+} .
  Proof. by rka. Qed.

  (* equation (27) of the csbr paper (B_L7_E25 / fset_rtclos_deltaC).        *)
  (* Out of reach of rka/rkat/rhkat, cf. first_entry above for the           *)
  (* reason; but provable in RelationAlgebra once the test / vector          *)
  (* link is provided.                                                       *)
  Goal (Δ_(X.^c) `;` R)^{*}#X = R^{*}#X.
  Proof. by to_ra_goal; apply: first_entry; rewrite vec_pset. Qed.

  (* denesting.  The direct proof from the lemmas of rel.v alone takes       *)
  (* about forty lines and first requires an induction principle missing     *)
  (* from rel.v (rtclos_ind requires transitivity of the target, which is    *)
  (* precisely the hard part here): cf. rel1.v, rt_ind_l and denest.         *)
  Goal (R `|` S)^{*} = R^{*} `;` (S `;` R^{*})^{*} .
  Proof. by rka. Qed.

  Goal (R `|` S)^{*} = (R^{*} `;` S)^{*} `;` R^{*} .
  Proof. by rka. Qed.

  Goal (R `|` S)^{+} = R^{*} `;` (S `;` R^{*})^{+} `|` R^{+} .
  Proof. by rka. Qed.

End Exemples.

(** * Limits *)

(* The goals below are outside the decided fragments; the [Fail]s              *)
(* document precisely what cannot be automated by these tactics.               *)

Section Limites.
  Variable (T: Type).
  Variables (R S U: relation T) (X Y: set T).

  (* converse is not in the fragment decided by ka/kat, but ra_cnv           *)
  (* pushes it down to atoms, which is enough in practice                    *)
  Goal (R `;` S)^-1 = S^-1 `;` R^-1.
  Proof. Fail by rka. by rka_cnv. Qed.

  Goal R^{*}^-1 = R^-1^{*} .
  Proof. Fail by rka. by rka_cnv. Qed.

  Goal R^{+}^-1 = R^-1^{+} .
  Proof. Fail by rka. by rka_cnv. Qed.

  Goal (Δ_(X) `;` R `;` Δ_(X))^-1 = Δ_(X) `;` R^-1 `;` Δ_(X).
  Proof. Fail by rkat. by rka_cnv. Qed.

  (* ra_cnv remains incomplete: R° is treated as a fresh atom *)
  Goal R `<=` R^{*} `;` R^-1 `;` R^{*} -> True.
  Proof. by []. Qed.

  (* intersection is not in the ka/kat fragment, but the bounded *)
  (* lattice fragment is handled by lattice *)
  Goal R `&` S `<=` R.
  Proof. Fail by rka. by rlattice. Qed.

  (* distributivity is not in the lattice fragment *)
  Goal (R `|` S) `&` U = (R `&` U) `|` (S `&` U).
  Proof. Fail by rlattice. by rewrite setIUl. Qed.

  (* top (setT, L_(X), R_(X)) is not in the ka/kat fragment *)
  Goal L_(X) `;` R `<=` L_(X).
  Proof. Fail by rkat. Abort.

  (* on sets, hkat rejects typed goals ("typed hkat is not supported") *)
  Goal R `;` S = set0 -> (R `;` S)#X = set0.
  Proof. Fail by rhkat. Abort.

  (* mixing a test and a set intersection leaves the fragment *)
  Goal Δ_(X)#Y = X `&` Y.
  Proof. Fail by rkat. Abort.

  (* hkat does not eliminate a monotonicity hypothesis *)
  Goal R `<=` S -> R^{+} `<=` S^{+} .
  Proof. Fail by rhkat. by apply: tclosS. Qed.

End Limites.
