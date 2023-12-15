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

(* This file is a version of the contents of lib/coq/theories/Relations
 * rewriten with ssreflect proofs. 
 * Jean-Philippe Chancelier 2023.
 *)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Relation_Definition.

  Definition relation (A: Type) := set (A * A).

  Variables (A : Type) (R : relation A).
  
  Section General_Properties_of_Relations.

    Definition reflexive : Prop := forall x:A, R (x,x).
    Definition transitive : Prop := forall x y z:A, R (x,y) -> R (y,z) -> R (x,z).
    Definition symmetric : Prop := forall x y:A, R (x,y) -> R (y,x).
    Definition antisymmetric : Prop := forall x y:A, R (x,y) -> R (y,x) -> x = y.

    (* for compatibility with Equivalence in  ../PROGRAMS/ALG/  *)
    Definition equiv := reflexive /\ transitive /\ symmetric.

  End General_Properties_of_Relations.

  Section Sets_of_Relations.

    Record preorder : Prop :=
      { preord_refl : reflexive; preord_trans : transitive}.

    Record order : Prop :=
      { ord_refl : reflexive;
	ord_trans : transitive;
	ord_antisym : antisymmetric}.

    Record equivalence : Prop :=
      { equiv_refl : reflexive;
	equiv_trans : transitive;
	equiv_sym : symmetric}.

    Record PER : Prop :=  {per_sym : symmetric; per_trans : transitive}.

  End Sets_of_Relations.

  Section Relations_of_Relations.

    Definition inclusion (R1 R2:relation A) : Prop :=
      forall x y:A, R1 (x,y) -> R2 (x,y).

    Definition same_relation (R1 R2:relation A) : Prop :=
      inclusion R1 R2 /\ inclusion R2 R1.

    Definition commut (R1 R2:relation A) : Prop :=
      forall x y:A,
	R1 (y,x) -> forall z:A, R2 (z,y) ->  exists2 y' : A, R2 (y', x) & R1 (z, y').

  End Relations_of_Relations.

End Relation_Definition.

#[global]
Hint Unfold reflexive transitive antisymmetric symmetric: sets.

#[global]
Hint Resolve Build_preorder Build_order Build_equivalence Build_PER
  preord_refl preord_trans ord_refl ord_trans ord_antisym equiv_refl
  equiv_trans equiv_sym per_sym per_trans: sets.

#[global]
Hint Unfold inclusion same_relation commut: sets.

(************************************************************************)
(** * Some operators on relations                                       *)
(************************************************************************)
(** * Initial authors: Bruno Barras, Cristina Cornes                    *)
(** *                                                                   *)
(** * Some of the initial definitions were taken from :                 *)
(** *    Constructing Recursion Operators in Type Theory                *)
(** *    L. Paulson  JSC (1986) 2, 325-355                              *)
(** *                                                                   *)
(** * Further extensions by Pierre Castéran                             *)
(************************************************************************)

(** ** Transitive closure *)

Section Transitive_Closure.

  Variables (A: Type) (R: relation A).

  (** Definition by direct transitive closure *)

  Inductive clos_trans (x: A) : A -> Prop :=
    | t_step (y:A) : R (x,y) -> clos_trans x y
    | t_trans (y z:A) : clos_trans x y -> clos_trans y z -> clos_trans x z.
  
  (** Alternative definition by transitive extension on the left *)

  Inductive clos_trans_1n (x: A) : A -> Prop :=
    | t1n_step (y:A) : R (x,y) -> clos_trans_1n x y
    | t1n_trans (y z:A) : R (x,y) -> clos_trans_1n y z -> clos_trans_1n x z.

  (** Alternative definition by transitive extension on the right *)

  Inductive clos_trans_n1 (x: A) : A -> Prop :=
    | tn1_step (y:A) : R (x,y) -> clos_trans_n1 x y
    | tn1_trans (y z:A) : R (y,z) -> clos_trans_n1 x y -> clos_trans_n1 x z.
  
  Definition clos_t := [set x: A *A | clos_trans x.1 x.2]%classic.
  Definition clos_t_1n := [set x: A *A | clos_trans_1n x.1 x.2]%classic.
  Definition clos_t_n1 := [set x: A *A | clos_trans_n1 x.1 x.2]%classic.

  Inductive clos_t' (x: A*A) : Prop :=
    | t_step': R x -> clos_t' x
    | t_trans' (y:A) : clos_t' (x.1, y) -> clos_t' (y,x.2) -> clos_t' x.

End Transitive_Closure.

(** ** Reflexive closure *)

Section Reflexive_Closure.

  Variables (A: Type) (R: relation A).

  (** Definition by direct transitive closure *)

  Inductive clos_refl (x: A) : A -> Prop :=
    | r_step (y:A) : R (x,y) -> clos_refl x y
    | r_refl : clos_refl x x.

  Definition clos_r := [set x: A * A | clos_refl x.1 x.2]%classic.
  
End Reflexive_Closure.

(** ** Reflexive-transitive closure *)

Section Reflexive_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.

  (** Definition by direct reflexive-transitive closure *)

  Inductive clos_refl_trans (x:A) : A -> Prop :=
    | rt_step (y:A) : R (x,y) -> clos_refl_trans x y
    | rt_refl : clos_refl_trans x x
    | rt_trans (y z:A) :
          clos_refl_trans x y -> clos_refl_trans y z -> clos_refl_trans x z.

  (** Alternative definition by transitive extension on the left *)

  Inductive clos_refl_trans_1n (x: A) : A -> Prop :=
    | rt1n_refl : clos_refl_trans_1n x x
    | rt1n_trans (y z:A) :
         R (x,y) -> clos_refl_trans_1n y z -> clos_refl_trans_1n x z.

  (** Alternative definition by transitive extension on the right *)

 Inductive clos_refl_trans_n1 (x: A) : A -> Prop :=
    | rtn1_refl : clos_refl_trans_n1 x x
    | rtn1_trans (y z:A) :
        R (y,z) -> clos_refl_trans_n1 x y -> clos_refl_trans_n1 x z.

 Definition clos_rt := [set x: A *A | clos_refl_trans x.1 x.2]%classic.
 Definition clos_rt_1n := [set x: A *A | clos_refl_trans_1n x.1 x.2]%classic.
 Definition clos_rt_n1 := [set x: A *A | clos_refl_trans_n1 x.1 x.2]%classic.

End Reflexive_Transitive_Closure.

(** ** Reflexive-symmetric-transitive closure *)

Section Reflexive_Symmetric_Transitive_Closure.

  Variables (A: Type) (R: relation A).

  (** Definition by direct reflexive-symmetric-transitive closure *)

  Inductive clos_refl_sym_trans : A -> A -> Prop :=
    | rst_step (x y:A) : R (x,y) -> clos_refl_sym_trans x y
    | rst_refl (x:A) : clos_refl_sym_trans x x
    | rst_sym (x y:A) : clos_refl_sym_trans x y -> clos_refl_sym_trans y x
    | rst_trans (x y z:A) :
        clos_refl_sym_trans x y ->
        clos_refl_sym_trans y z -> clos_refl_sym_trans x z.

  (** Alternative definition by symmetric-transitive extension on the left *)

  Inductive clos_refl_sym_trans_1n (x: A) : A -> Prop :=
    | rst1n_refl : clos_refl_sym_trans_1n x x
    | rst1n_trans (y z:A) : R (x,y) \/ R (y,x) ->
         clos_refl_sym_trans_1n y z -> clos_refl_sym_trans_1n x z.

  (** Alternative definition by symmetric-transitive extension on the right *)

  Inductive clos_refl_sym_trans_n1 (x: A) : A -> Prop :=
    | rstn1_refl : clos_refl_sym_trans_n1 x x
    | rstn1_trans (y z:A) : R (y,z) \/ R (z,y) ->
         clos_refl_sym_trans_n1 x y -> clos_refl_sym_trans_n1 x z.
  
  Definition clos_rst := [set x: A *A | clos_refl_sym_trans x.1 x.2]%classic.
  Definition clos_rst_1n := [set x: A *A | clos_refl_sym_trans_1n x.1 x.2]%classic.
  Definition clos_rst_n1 := [set x: A *A | clos_refl_sym_trans_n1 x.1 x.2]%classic.

End Reflexive_Symmetric_Transitive_Closure.

(** ** Disjoint union of relations *)

Section Disjoint_Union.
  
  Variables (A B: Type) (leA: relation A) (leB: relation B).

  Inductive le_AsB : A + B -> A + B -> Prop :=
  | le_aa (x y:A) : leA (x,y) -> le_AsB (inl _ x) (inl _ y)
  | le_ab (x:A) (y:B) : le_AsB (inl _ x) (inr _ y)
  | le_bb (x y:B) : leB (x,y) -> le_AsB (inr _ x) (inr _ y).

End Disjoint_Union.

#[global]
Hint Resolve t_step rt_step rt_refl rst_step rst_refl: sets.
#[global]
Hint Immediate rst_sym: sets.

(************************************************************************)
(** * Some properties of the operators on relations                     *)
(************************************************************************)
(** * Initial version by Bruno Barras                                   *)
(************************************************************************)

Section Properties.

  Variables (A: Type) (R : relation A).
  
  Section Clos_Refl_Trans.

    Local Notation "R .*" := (clos_rt R)
                              (at level 8, no associativity, format "R .*").

    (** Correctness of the reflexive-transitive closure operator *)
    Lemma clos_rt_is_preorder : preorder R.*.
    Proof.
      constructor => [x | x y z];[apply rt_refl | apply rt_trans].
    Qed.

    (** Idempotency of the reflexive-transitive closure operator *)
    Lemma clos_rt_idempotent : inclusion R.*.* R.* .
    Proof.
      move => x y; rewrite /clos_rt /mkset.
      by elim => [//| x' | x' y' z' _ H2 _ H4];
                [apply rt_refl| apply rt_trans with y'].
    Qed.

  End Clos_Refl_Trans.

  Section Clos_Refl_Sym_Trans.
    
    (** Reflexive-transitive closure is included in the
    reflexive-symmetric-transitive closure *)

    Lemma clos_rt_clos_rst : inclusion (clos_rt R) (clos_rst R).
    Proof.
      move => x0 y0; rewrite /clos_rt /clos_rst /mkset.
      by elim => [| | x y z _ ? _ ? ];[constructor|apply rst_refl|apply rst_trans with y].
    Qed.

    (** Reflexive closure is included in the
        reflexive-transitive closure *)
    
    Lemma clos_r_clos_rt :
      inclusion (clos_r R) (clos_rt R).
    Proof.
      by move => x y;rewrite /clos_r /clos_rt /mkset; elim => [x0 y0 |];constructor.
    Qed.

    Lemma clos_rt_t : forall x y z,
        clos_rt R (x,y) -> clos_t R (y,z) -> clos_t R (x,z).
    Proof.
      move => x1 y1 z1. rewrite /clos_t /clos_rt /mkset /=.
      by elim => [x y H| | x y z _ H1 _ H2 ?];
                [ apply: t_trans; apply: t_step| | apply: H1 ;apply: H2].
    Qed.
    
    (** Correctness of the reflexive-symmetric-transitive closure *)

    Lemma clos_rst_is_equiv : equivalence (clos_rst R).
    Proof.
      by split;[apply: rst_refl|apply: rst_trans|apply: rst_sym].
    Qed.

    (** Idempotency of the reflexive-symmetric-transitive closure operator *)

    Lemma clos_rst_idempotent :
      inclusion (clos_rst (clos_rst R)) (clos_rst R).
    Proof.
      by move => x' y';rewrite /clos_rst/mkset;
                elim => [// |x | x y _ | x y z _ H1 _ H2];
                       [apply rst_refl| apply rst_sym| apply rst_trans with y].
    Qed.
    
  End Clos_Refl_Sym_Trans.

  Section Equivalences.

    (** *** Equivalences between the different definition of the reflexive,
        symmetric, transitive closures *)

    (** *** Contributed by P. Castéran *)

    (** Direct transitive closure vs left-step extension *)
    Lemma clos_trans_t1n_iff : forall x y,
        clos_trans R x y <-> clos_trans_1n R x y.
    Proof.
      move => x y; split.
      - elim => [x' y' |x' y' z' H1 H2 H3]; first by constructor.
        elim: H2=> [x1 y1| x1 y1 z1 H4 H5 H6 H7]; first by apply t1n_trans. 
        by apply H6 in H7; apply t1n_trans with y1.
      - elim => [ x' y' H | x' y' z' H1 _ H2];first by apply t_step.
        by apply t_trans with y';[apply t_step |].
    Qed.

    (** Direct transitive closure vs right-step extension *)
    Lemma clos_trans_tn1_iff : forall x y,
        clos_trans R x y <-> clos_trans_n1 R x y.
    Proof.
      move => x' y'; split => [H | H].
      - elim: H => [x y H | x y z H1 H2 H3 H4]; first by apply tn1_step.
        elim: H4 => [y1 H5| y1 z1]; first by constructor 2 with y.
        by constructor 2 with y1.
      - elim: H => [y H| y z H1 _ H2]; first by apply: t_step.
        by apply t_trans with y;[ | apply t_step].
    Qed.
    
    (** Direct reflexive-transitive closure is equivalent to
     *  transitivity by left-step extension *)

    
    Lemma clos_rt_rt1n_iff : forall x y,
        clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
    Proof.
      have clos_rt1n_step : forall x' y', R (x',y') -> clos_refl_trans_1n R x' y'
          by move => x y H; constructor 2 with y; [ |constructor 1].
      
      move => x' y'; split => H.
      - elim: H => [x y H|x| x y z H1 H2 H3]; first by apply clos_rt1n_step.
        by apply rt1n_refl.
        by elim: H2 => [ // | x1 y1 z1 H'1 H'2 H'3 H'4];
                      constructor 2 with y1; [ | apply H'3].
      - elim: H => [ x | x y z H1 _ H2]; first by apply: rt_refl.
        by apply rt_trans with y;[ apply rt_step| ].
    Qed.
    
    (** Direct reflexive-transitive closure is equivalent to
     *  transitivity by right-step extension *)
    
    Lemma clos_rt_rtn1_iff : forall x y,
        clos_refl_trans R x y <-> clos_refl_trans_n1 R x y.
    Proof.
      have clos_rtn1_step : forall x' y', R (x',y') -> clos_refl_trans_n1 R x' y'
          by move => x y H; constructor 2 with x; [ |constructor 1].
      
      move => x' y'.
      split.
      - move => H.
        induction H; [by apply clos_rtn1_step| by apply rtn1_refl|].
        move: IHclos_refl_trans1.
        elim IHclos_refl_trans2 => [// |y1 z1 H1 H2 H3].
        by constructor 2 with y1; [ | apply H3].
      - move => H.
        by induction H; [apply rt_refl| apply rt_trans with y;[ |apply rt_step]].
    Qed.
    
    (** Induction on the left transitive step *)

    Lemma clos_refl_trans_ind_left :
      forall (x:A) (P:A -> Prop), P x ->
	                 (forall y z:A, clos_refl_trans R x y -> P y -> R (y,z) -> P z) ->
	                 forall z:A, clos_refl_trans R x z -> P z.
    Proof.
      move => x1 P H H0 z1 H1.
      move: H H0.
      elim: H1 => [x y H1 H2 H3| // |x y z H1 IH1 H2 IH2 H3 H4].
      by apply H3 with (y:=x) (z:=y); [apply rt_refl| | ].
      apply IH2; first by  apply IH1; [ apply H3 | apply H4].
        by move => y0 z0 H6 H7 H8;apply H4 with y0; [apply rt_trans with y | | ].
    Qed.

    (** Induction on the right transitive step *)

    Lemma rt1n_ind_right : forall (P : A -> Prop) (z:A),
        P z ->
        (forall x y, R (x,y) -> clos_refl_trans_1n R y z -> P y -> P x) ->
        forall x, clos_refl_trans_1n R x z -> P x.
    Proof.
      move => P z H1 H2 x H3.
      move: H2 H1.
      elim: H3 => [x1 H1 H2| x1 y1 z1 H1 H2 H3 H4 H5]; first by [].
      by apply H4 with y1; [ | |apply H3].
    Qed.

    Lemma clos_refl_trans_ind_right : forall (P : A -> Prop) (z:A),
        P z ->
        (forall x y, R (x,y) -> P y -> clos_refl_trans R y z -> P x) ->
        forall x, clos_refl_trans R x z -> P x.
    Proof.
      intros P z Hz IH x Hxz.
      apply clos_rt_rt1n_iff in Hxz.
      elim Hxz using rt1n_ind_right; auto.
      clear x Hxz.
      intros x y Hxy Hyz Hy.
      apply clos_rt_rt1n_iff in Hyz.
      eauto.
    Qed.

    (** Direct reflexive-symmetric-transitive closure is equivalent to
    transitivity by symmetric left-step extension *)

    Lemma clos_rst1n_rst  : forall x y,
        clos_refl_sym_trans_1n R x y -> clos_refl_sym_trans R x y.
    Proof.
      move => x y H.
      elim: H => [| x1 y1 z1 H1 H2 H3]; first by apply rst_refl.
      apply rst_trans with y1; last by [].
      by move: H1 => [H4 | H5];[apply rst_step| apply rst_sym;apply rst_step].
    Qed.

    Lemma clos_rst1n_trans : forall x y z,
        clos_refl_sym_trans_1n R x y ->
        clos_refl_sym_trans_1n R y z -> clos_refl_sym_trans_1n R x z.
    Proof.
      move => x y z; elim => [ | x1 y1 z1 H1 H2 H3 H4]; first by [].
      by apply rst1n_trans with y1; [ |apply: H3 H4 ].
    Qed.

    Lemma clos_rst1n_sym : forall x y,
        clos_refl_sym_trans_1n R x y -> clos_refl_sym_trans_1n R y x.
    Proof.
      move => x' y'; elim => [x |x y z D H0 H1 ]; first by constructor 1.
      apply clos_rst1n_trans with y; first by [].
      constructor 2 with x;first by move: D => [ D1 | D2]; [right | left].
      by constructor 1.
    Qed.
    
    Lemma clos_rst_rst1n  : forall x y,
        clos_refl_sym_trans R x y -> clos_refl_sym_trans_1n R x y.
    Proof.
      move => x' y';elim => [x y H| x | x y _ H | x y z _ H2 _ H4].
      by constructor 2 with y;left.
      by constructor 1.
      by apply clos_rst1n_sym.
      by apply clos_rst1n_trans with y.
    Qed.

    Lemma clos_rst_rst1n_iff : forall x y,
        clos_refl_sym_trans R x y <-> clos_refl_sym_trans_1n R x y.
    Proof.
      by split;[ apply clos_rst_rst1n | apply clos_rst1n_rst].
    Qed.

    (** Direct reflexive-symmetric-transitive closure is equivalent to
        transitivity by symmetric right-step extension *)

    Lemma clos_rstn1_rst : forall x y,
        clos_refl_sym_trans_n1 R x y -> clos_refl_sym_trans R x y.
    Proof.
      move => x0 y0 H.
      elim: H => [|y z [H1| H2] H3 H4]; first by apply rst_refl.
      by apply rst_trans with y;[ | apply rst_step].
      by apply rst_trans with y;[ | apply rst_sym;apply rst_step].
    Qed.

    Lemma clos_rstn1_trans : forall x y z,
        clos_refl_sym_trans_n1 R x y ->
        clos_refl_sym_trans_n1 R y z -> clos_refl_sym_trans_n1 R x z.
    Proof.
      by move => x' y' z' H1; elim => [// | x y H2 H3 H4 ]; apply rstn1_trans with x. 
    Qed.

    Lemma clos_rstn1_sym : forall x y,
        clos_refl_sym_trans_n1 R x y -> clos_refl_sym_trans_n1 R y x.
    Proof.
      move => x y H; elim: H => [ |y0 z D H0 H1] ; first by apply rstn1_refl.
      have H : clos_refl_sym_trans_n1 R z y0 
        by ( apply rstn1_trans with (z:=y0) (y:=z); 
             [move: D => [D1| D2]; [right| left] | apply rstn1_refl]).
      by apply clos_rstn1_trans with y0.
    Qed.    
    
    Lemma clos_rst_rstn1 : forall x y,
        clos_refl_sym_trans R x y -> clos_refl_sym_trans_n1 R x y.
    Proof.
      move => x' y' H;elim: H => [x y H1| x| x y _ H1 | x y z _ H2 _ H4 ].
      by apply rstn1_trans with x; left.
      by apply rstn1_refl.
      by apply clos_rstn1_sym.
      by apply clos_rstn1_trans with y.
    Qed.
    
    Lemma clos_rst_rstn1_iff : forall x y,
        clos_refl_sym_trans R x y <-> clos_refl_sym_trans_n1 R x y.
    Proof.
      by split; [apply clos_rst_rstn1|apply clos_rstn1_rst].
    Qed.

  End Equivalences.

End Properties.
