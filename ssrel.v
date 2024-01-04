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

(* This file is a modified version of the contents of lib/coq/theories/Relations
 * using mathcomp to define relations as set (T * T) and ssreflect for proofs
 * See the original files for the list of authors (B. Barras, P. Castéran, C. Cornes)
 * Jean-Philippe Chancelier 2023.
 *)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order boolp classical_sets.
Set Warnings "parsing coercions".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Relation_Definition.

  (* begin snippet relation:: no-out *)  
  Definition relation (T: Type) := set (T * T).
  (* end snippet relation *)  

  Variables (T : Type) (R : relation T).

  Definition reflexive : Prop := forall x:T, R (x,x).
  Definition transitive : Prop := forall x y z:T, R (x,y) -> R (y,z) -> R (x,z).
  Definition symmetric : Prop := forall x y:T, R (x,y) -> R (y,x).
  Definition antisymmetric : Prop := forall x y:T, R (x,y) -> R (y,x) -> x = y.
  
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

End Relation_Definition.

Section Transitive_Closure.
  (** * Transitive closure *)
  Variables (T: Type) (R: relation T).

  (** Definition by direct transitive closure *)
  Inductive clos_trans (x: T) : T -> Prop :=
    | t_step (y:T) : R (x,y) -> clos_trans x y
    | t_trans (y z:T) : clos_trans x y -> clos_trans y z -> clos_trans x z.
  
  (** Alternative definition by transitive extension on the left *)
  Inductive clos_trans_1n (x: T) : T -> Prop :=
    | t1n_step (y:T) : R (x,y) -> clos_trans_1n x y
    | t1n_trans (y z:T) : R (x,y) -> clos_trans_1n y z -> clos_trans_1n x z.

  (** Alternative definition by transitive extension on the right *)
  Inductive clos_trans_n1 (x: T) : T -> Prop :=
    | tn1_step (y:T) : R (x,y) -> clos_trans_n1 x y
    | tn1_trans (y z:T) : R (y,z) -> clos_trans_n1 x y -> clos_trans_n1 x z.

  (* transitive closure as set *)
  Definition clos_t := [set x: T * T | clos_trans x.1 x.2].
  Definition clos_t_1n := [set x: T * T | clos_trans_1n x.1 x.2].
  Definition clos_t_n1 := [set x: T * T | clos_trans_n1 x.1 x.2].
  
  Lemma clos_t_t1n_iff : clos_t =  clos_t_1n.
  Proof.
    rewrite /clos_t /clos_t_1n /mkset predeqE => xy.
    split.
    - elim => [x' y' |x' y' z' H1 H2 H3]; first by constructor.
      elim: H2=> [x1 y1| x1 y1 z1 H4 H5 H6 H7]; first by apply t1n_trans. 
      by apply H6 in H7; apply t1n_trans with y1.
    - elim => [ x' y' H | x' y' z' H1 _ H2];first by apply t_step.
      by apply t_trans with y';[apply t_step |].
  Qed.

  Lemma clos_t_tn1_iff : clos_t = clos_t_n1.
  Proof.
    rewrite /clos_t /clos_t_n1 /mkset predeqE => xy.
    split => [H | H].
    - elim: H => [x y H | x y z H1 H2 H3 H4]; first by apply tn1_step.
      elim: H4 => [y1 H5| y1 z1]; first by constructor 2 with y.
      by constructor 2 with y1.
    - elim: H => [y H| y z H1 _ H2]; first by apply: t_step.
      by apply t_trans with y;[ | apply t_step].
  Qed.

End Transitive_Closure.

Section Reflexive_Closure.
  (** * Reflexive closure *)

  Variables (T: Type) (R: relation T).

  (** Definition by direct transitive closure *)
  Inductive clos_refl (x: T) : T -> Prop :=
    | r_step (y:T) : R (x,y) -> clos_refl x y
    | r_refl : clos_refl x x.

  Definition clos_r := [set x: T * T | clos_refl x.1 x.2].
  
End Reflexive_Closure.

Section Reflexive_Transitive_Closure.
  (** * Reflexive-transitive closure *)

  Variables (T: Type) (R: relation T).
  
  (** Definition by direct reflexive-transitive closure *)
  (* begin snippet clos_refl_trans:: no-out *)  
  Inductive clos_refl_trans (x:T) : T -> Prop :=
  | rt_step (y:T) : R (x,y) -> clos_refl_trans x y
  | rt_refl : clos_refl_trans x x
  | rt_trans (y z:T) :
    clos_refl_trans x y -> clos_refl_trans y z -> clos_refl_trans x z.
  (* end snippet clos_refl_trans *)

  (** Alternative definition by transitive extension on the left *)
  Inductive clos_refl_trans_1n (x: T) : T -> Prop :=
  | rt1n_refl : clos_refl_trans_1n x x
  | rt1n_trans (y z:T) :
    R (x,y) -> clos_refl_trans_1n y z -> clos_refl_trans_1n x z.

  (** Alternative definition by transitive extension on the right *)
  Inductive clos_refl_trans_n1 (x: T) : T -> Prop :=
  | rtn1_refl : clos_refl_trans_n1 x x
  | rtn1_trans (y z:T) :
    R (y,z) -> clos_refl_trans_n1 x y -> clos_refl_trans_n1 x z.

  (* begin snippet clos_rt:: no-out *)  
  Definition clos_rt := [set x: T *T | clos_refl_trans x.1 x.2].
  (* end snippet clos_rt *)  

  Definition clos_rt_1n := [set x: T *T | clos_refl_trans_1n x.1 x.2].
  Definition clos_rt_n1 := [set x: T *T | clos_refl_trans_n1 x.1 x.2].
  
  Lemma clos_rt_rt1n_iff : clos_rt = clos_rt_1n.
  Proof.
    have clos_rt1n_step : forall x' y', R (x',y') -> clos_refl_trans_1n x' y'
        by move => x y H; constructor 2 with y; [ |constructor 1].
    rewrite /clos_rt /clos_rt_1n /mkset predeqE => xy.
    split => H.
    - elim: H => [x y H|x| x y z H1 H2 H3]; first by apply clos_rt1n_step.
      by apply rt1n_refl.
      by elim: H2 => [ // | x1 y1 z1 H'1 H'2 H'3 H'4];
                    constructor 2 with y1; [ | apply H'3].
    - elim: H => [ x | x y z H1 _ H2]; first by apply: rt_refl.
      by apply rt_trans with y;[ apply rt_step| ].
  Qed.
    
  Lemma clos_rt_rtn1_iff : clos_rt = clos_rt_n1.
  Proof.
    have clos_rtn1_step : forall x' y', R (x',y') -> clos_refl_trans_n1 x' y'
        by move => x y H; constructor 2 with x; [ |constructor 1].
    rewrite /clos_rt /clos_rt_n1 /mkset predeqE => xy.
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
  Lemma clos_rt_ind_left :forall (x:T) (P:T -> Prop),
      P x ->
      (forall y z:T, clos_rt (x, y) -> P y -> R (y,z) -> P z) ->
      forall z:T, clos_rt (x, z) -> P z.
  Proof.
    rewrite /clos_rt /mkset /=.
    move => x1 P H H0 z1 H1.
    move: H H0.
    elim: H1 => [x y H1 H2 H3| // |x y z H1 IH1 H2 IH2 H3 H4].
    by apply H3 with (y:=x) (z:=y); [apply rt_refl| | ].
    apply IH2; first by  apply IH1; [ apply H3 | apply H4].
    by move => y0 z0 H6 H7 H8;apply H4 with y0; [apply rt_trans with y | | ].
  Qed.
    
  (** Induction on the right transitive step *)
  Lemma clos_rt1n_ind_right : forall (P : T -> Prop) (z:T),
      P z ->
      (forall x y, R (x,y) -> clos_rt_1n (y, z) -> P y -> P x) ->
      forall x, clos_rt_1n (x,z) -> P x.
  Proof.
    rewrite /clos_rt_1n /mkset/=.
    move => P z H1 H2 x H3.
    move: H2 H1.
    elim: H3 => [x1 H1 H2| x1 y1 z1 H1 H2 H3 H4 H5]; first by [].
    by apply H4 with y1; [ | |apply H3].
  Qed.
  
  Lemma clos_rt_ind_right : forall (P : T -> Prop) (z:T),
      P z ->
      (forall x y, R (x,y) -> P y -> clos_rt (y, z) -> P x) ->
      forall x, clos_rt (x, z) -> P x.
  Proof.
    move => P z Hz IH x Hxz;rewrite clos_rt_rt1n_iff in Hxz.
    elim/clos_rt1n_ind_right: Hxz; first by [].
    by rewrite -clos_rt_rt1n_iff;move => x' y Hxy Hyz Hy;apply: (IH x' y).
  Qed.
  
End Reflexive_Transitive_Closure.

Section Reflexive_Symmetric_Transitive_Closure.
  (** * Reflexive-symmetric-transitive closure *)
  Variables (T: Type) (R: relation T).

  (** Definition by direct reflexive-symmetric-transitive closure *)
  Inductive clos_refl_sym_trans : T -> T -> Prop :=
    | rst_step (x y:T) : R (x,y) -> clos_refl_sym_trans x y
    | rst_refl (x:T) : clos_refl_sym_trans x x
    | rst_sym (x y:T) : clos_refl_sym_trans x y -> clos_refl_sym_trans y x
    | rst_trans (x y z:T) :
        clos_refl_sym_trans x y ->
        clos_refl_sym_trans y z -> clos_refl_sym_trans x z.

  (** Alternative definition by symmetric-transitive extension on the left *)
  Inductive clos_refl_sym_trans_1n (x: T) : T -> Prop :=
    | rst1n_refl : clos_refl_sym_trans_1n x x
    | rst1n_trans (y z:T) : R (x,y) \/ R (y,x) ->
         clos_refl_sym_trans_1n y z -> clos_refl_sym_trans_1n x z.

  (** Alternative definition by symmetric-transitive extension on the right *)
  Inductive clos_refl_sym_trans_n1 (x: T) : T -> Prop :=
    | rstn1_refl : clos_refl_sym_trans_n1 x x
    | rstn1_trans (y z:T) : R (y,z) \/ R (z,y) ->
         clos_refl_sym_trans_n1 x y -> clos_refl_sym_trans_n1 x z.
  
  Definition clos_rst := [set x: T *T | clos_refl_sym_trans x.1 x.2].
  Definition clos_rst_1n := [set x: T *T | clos_refl_sym_trans_1n x.1 x.2].
  Definition clos_rst_n1 := [set x: T *T | clos_refl_sym_trans_n1 x.1 x.2].
  
  Lemma clos_rst_rstn1_iff : clos_rst = clos_rst_n1. 
  Proof.
    have clos_rstn1_trans : transitive (clos_rst_n1)
      by rewrite /transitive /clos_rst_n1 /mkset/= ;
      move => x' y' z' H1; elim => [// | x y H2 H3 H4 ]; apply rstn1_trans with x. 

    have clos_rstn1_sym : symmetric (clos_rst_n1 ).
    rewrite /symmetric /clos_rst_n1 /mkset/=.
    move => x y H; elim: H => [ |y0 z D H0 H1] ; first by apply rstn1_refl.
    have H : clos_refl_sym_trans_n1 z y0 
      by ( apply rstn1_trans with (z:=y0) (y:=z); 
           [move: D => [D1| D2]; [right| left] | apply rstn1_refl]).
    by apply clos_rstn1_trans with y0.
    (* main *)
    rewrite /clos_rst /clos_rst_n1 /mkset predeqE /= => xy.
    split. 
    - move => H;elim: H => [x y H1| x| x y _ H1 | x y z _ H2 _ H4 ].
      by apply rstn1_trans with x; left.
      by apply rstn1_refl.
      by apply clos_rstn1_sym.
      by apply clos_rstn1_trans with y.
    - move => H;elim: H => [|y z [H1| H2] H3 H4]; first by apply rst_refl.
      by apply rst_trans with y;[ | apply rst_step].
      by apply rst_trans with y;[ | apply rst_sym;apply rst_step].
  Qed.

  Lemma clos_rst_rst1n_iff : clos_rst = clos_rst_1n.
  Proof.
    have clos_rst1n_trans : transitive (clos_rst_1n).
    rewrite /transitive /clos_rst_1n /mkset/=.
    move => x y z; elim => [ | x1 y1 z1 H1 H2 H3 H4]; first by [].
    by apply rst1n_trans with y1; [ |apply: H3 H4 ].

    have clos_rst1n_sym : symmetric (clos_rst_1n).
    rewrite /symmetric /clos_rst_1n /mkset/=.
    move => x' y'; elim => [x |x y z D H0 H1 ]; first by constructor 1.
    apply clos_rst1n_trans with y; first by [].
    constructor 2 with x;first by move: D => [ D1 | D2]; [right | left].
    by constructor 1.
    (* main *)
    rewrite /clos_rst /clos_rst_1n /mkset predeqE /= => xy.
    split. 
    - elim => [x y H| x | x y _ H | x y z _ H2 _ H4].
      by constructor 2 with y;left.
      by constructor 1.
      by apply clos_rst1n_sym.
      by apply clos_rst1n_trans with y.
    - elim => [| x1 y1 z1 H1 H2 H3]; first by apply rst_refl.
      apply rst_trans with y1; last by [].
      by move: H1 => [H4 | H4];[apply rst_step| apply rst_sym;apply rst_step].
  Qed.

End Reflexive_Symmetric_Transitive_Closure.

Section Properties.

  Variables (T: Type) (R : relation T).
    
  Lemma clos_rt_clos_rst : ((clos_rt R) `<=` (clos_rst R)).
  Proof.
    rewrite /clos_rt /clos_rst /mkset => xy.
    by elim => [| | x y z _ ? _ ? ];[constructor|apply rst_refl|apply rst_trans with y].
  Qed.

  Lemma clos_r_clos_rt : ((clos_r R) `<=` (clos_rt R)).
  Proof.
    by rewrite /clos_r /clos_rt /mkset => xy; elim => [x y |];constructor.
  Qed.
    
  Lemma clos_rt_t : forall x y z,
      clos_rt R (x,y) -> clos_t R (y,z) -> clos_t R (x,z).
  Proof.
    move => x1 y1 z1. rewrite /clos_t /clos_rt /mkset /=.
    by elim => [x y H| | x y z _ H1 _ H2 ?];
              [ apply: t_trans; apply: t_step| | apply: H1 ;apply: H2].
    Qed.
    
  Lemma clos_rst_is_equiv : equivalence (clos_rst R).
  Proof.
    by split;[apply: rst_refl|apply: rst_trans|apply: rst_sym].
  Qed.
    
  Lemma clos_rst_idempotent :
    ((clos_rst (clos_rst R)) `<=` (clos_rst R)).
  Proof.
    rewrite /clos_rst/mkset => xy.
    by elim => [// |x | x y _ | x y z _ H1 _ H2];
              [apply: rst_refl| apply: rst_sym| apply: rst_trans H1 H2].
  Qed.

  Lemma clos_rt_is_preorder : preorder (clos_rt R). 
  Proof.
    constructor => [x | x y z];[apply rt_refl | apply rt_trans].
  Qed.
  
  Lemma clos_rt_idempotent : ((clos_rt (clos_rt R)) `<=` (clos_rt R)). 
  Proof.
    rewrite /clos_rt /mkset => xy.
    by elim => [//| x' | x' y' z' _ H1 _ H2];[apply: rt_refl | apply: (rt_trans H1 H2)].
  Qed.
  
End Properties.
