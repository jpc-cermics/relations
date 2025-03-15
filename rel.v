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

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order. 
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import ssrel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * relations as sets: (set T*T) *)

Notation "R .+" := (clos_t R) 
                     (at level 2, left associativity, format "R .+").
Notation "R .*" := (clos_rt R) 
                     (at level 2, left associativity, format "R .*").

(* Reserved Notation "R .-1" (at level 2, left associativity, format "R .-1").  *)

Reserved Notation "R `;` U" (at level 51, left associativity, format "R `;` U").

Section Sets_facts.

  Variables (T:Type).
  
  (* usefull to ease moves with views: mem_set and set_mem do the same 
   *)
  Lemma inP: forall (x:T) (X: set T), x \in X <-> X x. 
  Proof.
    by move => x X; rewrite in_setE.
  Qed.
  
  Lemma notempty_exists: forall (X: set T), (exists z, z \in X) <-> (X != set0).
  Proof.
    by move => X;  rewrite set0P;split;[ move => [z /set_mem H1] | move => [z /mem_set H1] ];exists z.
  Qed.
  
  (* begin snippet Sone:: no-out *)  
  Lemma empty_notexists: forall (X: set T), X = set0 <-> ~ (exists z, z \in X).
  Proof.
    move => X.
    split.
    - by move => -> [z /inP ?]. 
    - move => H1; rewrite predeqE => x.
      by split => [/inP H2 | H2];[have H3: exists (z:T), z \in X by (exists x) |].
  Qed.
  (* end snippet Sone *) 

  (* begin snippet Stwo:: no-out *)  
  Lemma empty_iff: forall (X: set T), ~ (X != set0) <-> X = set0.
  (* end snippet Stwo *)  
  Proof.
    by move => X;rewrite -notempty_exists empty_notexists.
  Qed.
  
  Lemma W_part : forall (X Y Z: set T),
      (Y `<=` X) /\ (Z= X `\` Y) -> Y `&` Z = set0.
  Proof.
    move => X Y Z [? H2];rewrite empty_notexists H2.
    by move => [z /inP [? [_ ?]]].
  Qed.

  Lemma Union_empty : forall (X Y: set T), X `|` Y = set0 <-> (X = set0) /\ ( Y = set0).
  Proof.
    move => X Y; split => [H | [H1 H2]].
    - split;rewrite empty_notexists;move => [z H1].
      have H3:  X `|` Y != set0 
        by rewrite -notempty_exists;exists z;rewrite in_setE;left; rewrite -in_setE.
      by rewrite -empty_iff in H.
      have H3:  X `|` Y != set0 
        by rewrite -notempty_exists;exists z;rewrite in_setE;right; rewrite -in_setE.
      by rewrite -empty_iff in H.
    - by rewrite H1 H2 setU0.
  Qed.
  
End Sets_facts. 

Section Union_facts.
  (** * union of relations using set unions *)
  Variables (T: Type) (R S U: relation T).
  
  Lemma union_inc_b : S `<=` U -> R `<=` U -> (S `|` R) `<=` U.
  Proof.
    move => H1 H2; have <- : U `|` R = U by apply setUidPl.
    by apply setSU.
  Qed.
  
End Union_facts.

Section Inverse.
  
  Variables (T: Type) (R S: relation T).
  
  (* begin snippet Sthree *)  
  Definition inverse (T: Type) (R: relation T): relation T := [set x | R (x.2,x.1)].
  (* end snippet Sthree *)  

  Local Notation "R .-1" := (@inverse _ R) : classical_set_scope.
  
  Lemma inverse_inverse (U : relation T):  U.-1.-1 = U.
  Proof. rewrite /inverse /mkset predeqE; tauto. Qed.
  
  Lemma inverse_sym : R.-1 = R <-> symmetric R.
  Proof.
    rewrite predeqE /symmetric. 
    split => [ H1 x y /H1 // H | H1 [x y]].
    by rewrite /=; split; apply H1.
  Qed.
  
  Lemma inverse_star : R.*.-1 = R.-1.* .
  Proof.
    rewrite /clos_rt /inverse /mkset predeqE => xy /=.
    by split;(elim => [x y /= ?| |x y z _ ? _ ?];
                     [apply: rt_step|apply: rt_refl |apply: (rt_trans (y:=y))]).
  Qed.
  
  Lemma inverse_clos_t : R.+.-1 = R.-1.+ .
  Proof.
    rewrite /clos_t /inverse /mkset /= predeqE => xy /=.
    by split;(elim => [x y H|x y z _ H2 _ H4];
                     [apply: t_step |apply: (t_trans (y:=y))]).
  Qed.
  
  Lemma inverse_eq : R= S <-> R.-1 = S.-1.
  Proof.
    have H0: forall (X Y: relation T), X = Y -> X.-1 = Y.-1
        by move => X Y H;rewrite /inverse /mkset /predeqE H.
    split; first by apply H0.
    move => H1; have H2: R.-1.-1 = S.-1.-1 by apply H0.
    by rewrite -[R]inverse_inverse -[S]inverse_inverse.
  Qed.
  
  Lemma inverse_union : (R `|` S).-1 = R.-1 `|` S.-1.
  Proof.
    by rewrite /inverse /mkset /predeqE.
  Qed.

  Lemma inverse_inc : R `<=` S -> R.-1 `<=` S.-1. 
  Proof.
    by rewrite /inverse /mkset /predeqE /subset;move => H1 x /H1 H2.
  Qed.

End Inverse.

Notation "R .-1" := (@inverse _ R). 

#[global]
  Hint Resolve inverse_star inverse_clos_t: relations.

Section Compose.
  
  Definition compose (T: Type) (R U: relation T): relation T := 
    [set x | exists (z: T), R (x.1,z) /\ U (z,x.2)].

End Compose. 

Notation "R `;` U" := (compose R U).

Section Compose_facts. 
  
  Variables (T: Type) (R S U : relation T).

  Lemma Test: compose R S `<=` setT.
  Proof.
    move => x [z [H1 H2]]. 
    by [].
  Qed.
  
  Lemma composeA : (R `;` S) `;` U = R `;` (S `;` U).
  Proof.
    rewrite predeqE => x'.
    split => [ [z [[w /= [? ?]] ?]] | [z [? [ w [? ?]]]]].
    by (exists w);split; [ | exists z; split].
    by (exists w);split; [ exists z | ].
  Qed.

  Lemma composeDr : (R `|` S) `;` U = (R `;` U) `|` (S `;` U).
  Proof.
    rewrite predeqE => x.
    split.
    by move => [z [[? | ? ] ?]]; [ left| right]; exists z.
    by move => [|] [ z [? ?]];[exists z; split; [ left | ] | exists z; split; [right |]].
  Qed.
  
  Lemma composeDl : R `;` (S `|` U) = (R `;` S) `|` (R `;` U).
  Proof.
    rewrite predeqE => x.
    split.
    by move => [z [H1 [H3|H4]]];[ left; exists z; split | right; exists z; split].
    move => [[z [H1 H2]] | [z [H1 H2]]];
           first by exists z; split; [ | left].
                      by exists z;  split; [ | right]. 
  Qed.
  
  Lemma compose_inc : S `<=` U ->(R `;` S) `<=` (R `;` U). 
  Proof.
    rewrite /subset => H x [z [H1 H2]].
    by exists z; split; [ | apply H].
  Qed.
  
  Lemma composer_inc : S `<=` U ->(S `;` R ) `<=` (U `;` R). 
  Proof.
    rewrite /subset => H x [z [? ?]].
    by exists z; split; [apply H | ].
  Qed.
  
  Lemma inverse_compose : (R `;` S).-1 = S.-1 `;` R.-1.
  Proof.
    rewrite predeqE => x.
    by split;move => [z [? ?]]; exists z; split.
  Qed.
  
  Lemma RRm_inverse : (R `;` R.-1).-1 = R `;` R.-1.
  Proof.
    have RRm_sym : symmetric (R `;` R.-1)
        by move => x y [z [H1 H2]];exists z; split; [apply H2| apply H1].
    by apply inverse_sym, RRm_sym.
  Qed. 
  
End Compose_facts.

#[global]
  Hint Resolve inverse_compose composeDl composeDr composeA : relations.

Section Delta.

  (** `;` Simplifier en enlevant le \in ça doit simplifire les preuves qui suivent *)
  Definition DeltaE (T: Type) (X: set T) : relation T := 
    [set x | X x.1 /\ x.1 = x.2].

  Definition DeltaCE (T: Type) (X: set T) : relation T := 
    DeltaE (~` X).
  
  Definition Lr (T: Type) (X: set T) : relation T := [set x | X x.1].
  Definition Rr (T: Type) (X: set T) : relation T := [set x | X x.2].

End Delta.

Notation "Δ_( W )" := (@DeltaE _ W) 
                        (at level 2, no associativity, format "Δ_( W )").

Notation "L_( W )" := (@Lr _ W)
                        (at level 2, no associativity, format "L_( W )").

Notation "R_( W )" := (@Rr _ W)
                        (at level 2, no associativity, format "R_( W )").

Notation "W .^c" := (~` W) 
                      (at level 2, left associativity, format "W .^c").
Notation "'Δ" := (DeltaE setT) (at level 2, no associativity).
Notation "'Δc" := (DeltaCE setT) (at level 2, no associativity).

Section Delta_facts.
  
  Variables (T: Type) (R: relation T) (X Y: set T).

  Lemma DeltaE_sym :  symmetric Δ_(X).
  Proof.
    rewrite /symmetric /DeltaE /mkset /=. 
    by move => x y [H1 <-]; split.
  Qed.
  
  Lemma DeltaE_trans : transitive Δ_(X).
  Proof.
    rewrite /symmetric /DeltaE /mkset /=. 
    by move => x y z [/= H1 H2] [H3 H4]; split; [ | rewrite H2 H4].
  Qed.
  
  Lemma DeltaE_inc :   X `<=` Y -> Δ_(X) `<=` Δ_(Y).
  Proof.
    rewrite /symmetric /DeltaE /mkset /subset /=.
    by move =>  H [x y] [H1 <-];split;[apply H |].
  Qed.

  Lemma DeltaE_inv :  Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof.
    rewrite /DeltaE /compose /mkset predeqE /=.
    move => [x y]; split.
    by move => [z [[H1 H2] [H3 H4]]]; split; [ | rewrite H2].
    by move => [H1 H2]; exists x; split; split.
  Qed.

  Lemma DeltaE_inverse :  Δ_(X).-1 = Δ_(X). 
  Proof.
    rewrite /DeltaE /inverse /mkset predeqE /=.
    by move => [x y] /=; split; move => [H1 <-].
  Qed.
  
  Lemma DeltaE_compose : forall (X' Y': set T), Δ_(X') `;` Δ_(Y') = Δ_(X' `&` Y').
  Proof.
    move => X' Y'.
    rewrite /DeltaE /compose /mkset predeqE.
    move => xy /=;split => [[z [[H1 <-] [H2 <-]]] | [[H1 H2] <-]]. 
    by []. 
    by exists xy.1. 
  Qed.
  
  Lemma Delta_Id : forall (x y:T), 'Δ (x,y) <-> x = y.
  Proof.
    rewrite /DeltaE /mkset /=.
    by move => x y; split;first by move => [H1 ->].
  Qed.

  Lemma DeltaEP : forall (x y:T), Δ_(X) (x,y) <-> X x /\ x = y.
  Proof.
    by move=> x y;rewrite /DeltaE /mkset /=.
  Qed.
  
  Lemma DeltaE_inc_D : Δ_(X) `<=` 'Δ.
  Proof.
    rewrite /DeltaE /mkset /subset /=.
    by move => [x y] /= [H1 <-].
  Qed.
  

  Lemma WWcI: X `&` X.^c = set0.
  Proof.
    rewrite /mkset predeqE.
    by move => x;split => [ [? H2] | ?];[rewrite /setC  mksetE in H2 |].
  Qed.
  
  Lemma DeltaLco : Δ_(X) `;` R = L_(X) `&` R.
  Proof.
    rewrite /Lr /DeltaE /compose /mkset /setI predeqE /= => [[x y]] /=.
    by split => [[z [[? <-] ?]] | [? ?]];[ | exists x].
  Qed.

  Lemma DeltaRco : R `;` Δ_(X) = R `&` R_(X).
  Proof.
    rewrite /Rr /DeltaE /compose /mkset /setI predeqE /= => [[x y]] /=.
    by split => [[z [? [? <-]]] | [? ?]];[ | exists y].
  Qed.
  
  Lemma DeltaW_Wc : Δ_(X) `;` Δ_(X.^c) = 'Δc.
  Proof.
    rewrite DeltaE_compose WWcI /DeltaCE /DeltaE /setC /set0 predeqE. 
    by move => [x y] /=;split => [ [? _] // | [? _] // ].
  Qed.
  
  Lemma DeltaWc_W : Δ_(X.^c) `;` Δ_(X) = 'Δc.
  Proof.
    rewrite DeltaE_compose setIC WWcI /DeltaCE /DeltaE /setC /set0 predeqE. 
    by move => [x y]/=;split; move => [H1 <-].
  Qed.
  
  Lemma DeltaC_union_ideml : 'Δc `|` R = R.
  Proof.
    rewrite /setU /DeltaCE /DeltaE /setC /mkset predeqE => x /=.
    by split => [[[? _] | ?] | H1];[ | | right].
  Qed.
  
  Lemma DeltaC_union_idemr :  R `|` 'Δc = R.
  Proof.
    by rewrite setUC; apply DeltaC_union_ideml.
  Qed.
  
  Lemma DeltaC_compose_absorbl : 'Δc `;` R = 'Δc.
  Proof.
    rewrite /compose /DeltaCE /DeltaE /setC /mkset predeqE => x /=.
    by split => [ [z [[? _] _]] | [? _]].
  Qed.
  
  Lemma DeltaC_compose_absorbr :  R `;` 'Δc = 'Δc.
  Proof.
    rewrite /compose /DeltaCE /DeltaE /setC /mkset predeqE => x /=. 
    by split => [ [z [_ [? _]]] | [? _]].
  Qed.
  
  Lemma DeltaE_union : forall (X' Y':set T), Δ_(X') `|` Δ_(Y') = Δ_(X' `|` Y').
  Proof.
    move => X' Y'.
    rewrite /DeltaE /setU /mkset predeqE => x /=.
    split.
    by move => [[H1 <-] | [H1 <-]];[split;[left |] | split;[right |]].
    by move => [[H1 | H1] <-];[left | right].
  Qed.

  Lemma WWcU: X `|` X.^c = setT.
  Proof.
    rewrite /setU /setC /mkset predeqE => x.
    by split => _;[ rewrite -in_setE in_setT | apply lem].
  Qed. 
    
  Lemma DeltaE_comp : Δ_(X) `|` Δ_(X.^c) = 'Δ.
  Proof.
    by rewrite DeltaE_union WWcU. 
  Qed.
  
  Lemma DeltaE_compose_same : Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof.
    have H1: X `&` X = X
      by rewrite /setI /mkset predeqE;move => x;split;[move => [? _] |].
    by rewrite DeltaE_compose H1.
  Qed.
  
  Lemma Delta_idem_l : 'Δ `;` R = R.  
  Proof.
    rewrite /compose predeqE => [[x y]] /=.
    split.
    by move => [z [/Delta_Id<-  ?]]. 
    by move => ? ; exists x; split;[ apply Delta_Id |].
  Qed.
  
  Lemma Delta_idem_r : R `;` 'Δ = R.  
  Proof.
    rewrite /compose /DeltaE /mkset predeqE => [[x y]] /=.
    split.
    by move => [z [? /Delta_Id<-]].
    by move => ?; exists y; split;[| apply Delta_Id].
  Qed.
  
  Lemma Delta_clos_trans_ends : (R `;` Δ_(X)).+ =  (R `;` Δ_(X)).+ `;` Δ_(X).
  Proof.
    rewrite /compose /DeltaE /clos_t /mkset predeqE => [[x' y']]/=.
    split; last by elim => z' [? [? <-]].
    elim => x y. 
    + move => /= [z [H1 [H2 H3]]].
      exists y; split;
        first by apply t_step;exists y;split;[rewrite -H3|split;[rewrite -H3|]].
      by split;[rewrite -H3| ].
    + move => z H1 [z1 [H2 H'2]] H3 [z2 [H4 [H'4 H''4]]].
      by exists z; split;[ apply t_trans with y |split; rewrite -H''4].
  Qed.
  
  Lemma Delta_clos_trans_starts : (Δ_(X) `;` R).+ = Δ_(X) `;` (Δ_(X) `;` R).+.
  Proof.
    rewrite /compose /DeltaE /clos_t /mkset predeqE => [[x' y']]/=.
    split; last  by move => [z [[H1 <-] H2]].
    elim => x y. 
    by move => [z [[H1 H2] H3]];
              exists z;split;[split|apply t_step;exists z;split;[split;[rewrite -H2|]|]].
    by move => z _ [x1 [[H2 <-] H3]] _ [y1 [[H4 <-] H5]];
              exists x; split; [split | apply t_trans with y]. 
  Qed.
  
  Lemma clos_refl_trans_containsD: Δ_(X) `<=` R.* .
  Proof.
    rewrite /subset /DeltaE /clos_rt /mkset.
    by move => [x y] [H1 ->];apply rt_refl.
  Qed.

  Lemma R_restrict : forall (x y: T),  
      x \in X /\ y \in X -> 
      (R (x,y) <-> let DR:= (Δ_(X) `;` R `;` Δ_(X)) in DR (x,y)).
  Proof.
    rewrite /compose /DeltaE /mkset /=.
    move => x y [/inP H1 /inP H2].
    split=> [ H3 | [z [[t [[H3 ->] H4] [H5 <-]]]] //].
    by (exists y; split;[ exists x; split | ]).
  Qed.

  Lemma R_restrict_l : forall (x y: T),
      x \in X -> (R (x,y) <-> let DR:= (Δ_(X) `;` R) in DR (x,y)).
  Proof.
    rewrite /compose /DeltaE /mkset /= => [x y /inP ?].
    split => [? | [z [[? ->] ?] ] //].
    by (exists x; split).
  Qed.
  
  Lemma DeltaCsubset: (Δ_(X) `;` R `<=` R).
  Proof.
    rewrite /subset /DeltaE /compose /mkset /=.
    by move => [x y] /= => [[z [[_ <-] H2]]].
  Qed.
  
  Lemma DeltaCsubsetl: (R `;` Δ_(X) `<=` R).
  Proof.
    rewrite /subset /DeltaE /compose /mkset /=.
    by move => [x y] /= => [[z [H2 [_ <-]]]].
  Qed.
    
End Delta_facts.

#[global]
  Hint Resolve DeltaE_union DeltaCE DeltaE_inverse DeltaE_inv Delta_idem_l Delta_idem_r : relations.

Section Foresets.

  Definition Fset (T:Type) (R: relation T) (Y: set T) : set T :=
    [set x | exists (y: T), R (x,y) /\ Y y].

  Definition Aset (T:Type) (R: relation T) (Y: set T) : set T :=
    Fset R.-1 Y. 

End Foresets.

(* Foreset of Y for the relation R*)
Notation "R # Y" := (Fset R Y) 
                      (at level 3, no associativity, format "R # Y").

(* Foreset of {y} for the relation R*)
Notation "R #_( y )" := (Fset R ([set y]))
                          (at level 3, no associativity, format "R #_( y )").

Notation "Y :# R" := (Aset R Y) 
                       (at level 3, no associativity, format "Y :# R").

(* Foreset of {y} for the relation R*)
Notation " y _:# R" := (Aset R ([set y]))
                          (at level 3, no associativity, format " y _:# R").

(* Closure of Y for the relation R and subset W *)
Notation "Clos( Y | R , W )" :=  (Fset ((Δ_(W.^c) `;` R).* ) Y)
                                 (at level 3, no associativity, format "Clos( Y | R , W )").    

(* Closure of {y} for the relation R and subset W *)
Notation "Clos_( y | R , W )" := (Fset ((Δ_(W.^c) `;` R).* ) ([set y]))
                                 (at level 3, no associativity, format "Clos_( y | R , W )").    

Section Foreset_facts.
  
  Variables (T:Type) (R S: relation T) (X Y: set T).

  (* 
  Lemma Singl_iff: forall (x y:T), x \in [set y] <-> x = y.
  Proof.
    by move => x y; rewrite in_setE;split => [ | ->].
  Qed.
  *)

  Lemma Fset_D :   'Δ#X = X.
  Proof.
    rewrite /Fset /DeltaE /mkset predeqE /=.
    move => x.
    split.
    by move => [x' [/Delta_Id -> H1]].
    by move => H; exists x; split;[split|].
  Qed.

  Lemma Fset_DE : Δ_(Y)#X = Y `&` X.
  Proof.
    rewrite /Fset /DeltaE /mkset predeqE /=.
    move => x.
    split.
    by move => [x' [[H1 H'1] H2]];split; [ | rewrite H'1]. 
    by move => [H1 H2]; exists x.
  Qed.
  
  Lemma Fset_DCE : Δ_(Y.^c)#X = X `\` Y.
  Proof.
    rewrite /Fset /DeltaE /setC /mkset predeqE /=.
    move => x.
    split.
    by move => [x' [[H1 H'1] H2]];split; [rewrite H'1 |].
    by move => [H1 H2]; exists x.
  Qed.
  
  Lemma Fset_inc : R `<=` S -> R#X `<=` S#X.
  Proof.
    move => H x [y [H1 H2]].
    by exists y; split; [apply: H | ].
  Qed.
  
  Lemma Fset_inc1 : X `<=` Y -> R#X `<=` R#Y.
  Proof.
    move => H x [y [H1 H2]].
    exists y. split. by []. by apply H.
  Qed.
  
  Lemma set_inc2: forall (x: T), x \in X <->  [set x] `<=` X.
  Proof.
    move => x;split.
    - by move => /set_mem ? y /= -> .
    - by rewrite in_setE => H1; apply: H1. 
  Qed.
  
  Lemma Fset_comp : S # (R # X) = (S `;` R) # X.
  Proof.
    rewrite /Fset /compose /Fset /mkset predeqE /=.
    move => x; split.
    move => [z [H1 H2]]. 
    move: H2 => [y [H2 H3]].
    by (exists y);split; [ exists z;split |]. 
    by move => [ y [[z [H3 H4]] H2]];exists z; split;[|exists y].
  Qed.
  
  Lemma Fset_union_rel : S#X `|` R#X = (S `|` R) # X.
  Proof.
    rewrite /Fset /setU /mkset predeqE /=.
    move => x; split. 
    - move => [[y [H1 H2]] | [y [H1 H2]]].
      exists y. split. by left. by [].
      exists y. split. by right. by [].
    - move => [y [[H1|H2] H3]].
      by left;exists y. 
      by right;exists y. 
  Qed.
  
  Lemma Fset_union : R#(X `|` Y) = (R#X) `|` (R#Y).
  Proof.
    rewrite /Fset /setU /mkset predeqE /=.
    move => x; split. 
    - move => [z [H1 H2]].
      move: H2 => [H2 | H2].
      left. by exists z.
      right. by exists z.
    - move => [[y [H1 H2]] | [y [H1 H2]]].
      exists y. split. by []. by left.
      exists y. split. by []. by right.
  Qed.
  
  (* Foreset in extension *)

  Definition Fset_ext := fun (x:T) => (exists y, Y y /\ R#_(y) x).
  
  Lemma Fset_union_set : forall (x:T), (R#Y) x <-> exists y, Y y /\ R#_(y) x.
  Proof.
    move => x.
    rewrite /Fset /mkset /=.
    split.
    - move => [y [H1 H2]].
      exists y. split. by []. exists y. split. by []. by [].
    - move => [y [H1 H2]]. 
      move: H2 => [z [H2 H3]].
      exists z.
      split. by [].
      by rewrite H3.
  Qed.

  Lemma Fset_union_ext : (R#Y) = Fset_ext. 
  Proof.
    rewrite /Fset_ext predeqE.
    move => x. 
    split => H. 
    by rewrite -Fset_union_set.
    by rewrite  Fset_union_set. 
  Qed.

  Lemma Union_Setminus : X `|` Y = X `|` (Y `\` X). 
  Proof.
    rewrite /setU /setD /mkset predeqE => x.
    split.
    - move => [H1 | H1].
      by left.
      pose proof lem (X x) as [H2 | H2].
      by left.
      by right.
    - move => [H1| [H1 H2]].
      by left.
      by right.
  Qed.
  
  Lemma Fset_intersect : forall (x y:T), (exists z, R#_(x) z /\ S#_(y) z)
                                    <-> let RmR := R.-1 `;` S in RmR (x,y). 
  Proof.
    rewrite /Fset /mkset.
    move => x y.
    split. 
    - move => [ z [H1 H2]].
      move: H1 => [r [H1 H1']].
      move: H2 => [t [H2 H2']].
      have -> : x = r by [].
      have <- : t = y by [].
      exists z. split. by rewrite /inverse /=. by [].
    - rewrite /inverse; move => [z /= [H1 H2]].
      exists z.
      split. exists x.  by []. 
      exists y. by []. 
  Qed.
  
  Lemma Fset_singleton: forall (x:T), reflexive R -> R#_(x) x. 
  Proof.
    move => x H.  rewrite /Fset /mkset. exists x.  by []. 
  Qed.
  
  Lemma Fset_rt_singleton: forall (x:T), R.*#_(x) x. 
  Proof.
    move => x.  rewrite /Fset /mkset. exists x.
    split. by apply rt_refl. by [].
  Qed.

  Lemma Fset_restrict : X `<=` Y -> R#X = (R `;` Δ_(Y))# X.
  Proof.
    rewrite /subset /Fset /compose /DeltaE /mkset predeqE /=. 
    move => H x; split. 
    - move => [y [H1 H2]].
      exists y. split. exists y. split. by []. split. apply H. by []. by []. by [].
    - by move => [y [[z [H1 [_ <- ]]] H4]];(exists z). 
  Qed.
  
  Lemma Fset_t0: forall (x y:T) (R':relation T), R' (x, y) <-> R'#_(y) x. 
  Proof.
    by move => x y R'; split => [H1 | [z [H1 /= <-]]];[exists y |].
  Qed.
  
  Lemma Fset_t1: forall (x y:T), R (x, y) -> R.+#_(y) x. 
  Proof.
    move => x y H1.
    rewrite /Fset /clos_rt /mkset /=.
    exists y. split. by apply t_step. by []. 
  Qed.
  
  Lemma Fset_t2: forall (x y:T), 
      (exists (x1:T), R (x, x1) /\ R.+#_(y) x1) -> R.+#_(y) x. 
  Proof.
    move => x y' [x1 [H1 H2]].  
    move: H2. rewrite /Fset /clos_t /mkset /=.
    move => [y [H2 <-]].
    exists y. split. apply t_trans with x1. by apply t_step. by [].
    by [].
  Qed.

  Lemma Fset_t3: forall (x y z:T), 
      R.+#_(y) x /\ R (y, z) -> R.+#_(z) x. 
  Proof.
    move => x y z. rewrite /Fset clos_t_tn1_iff /clos_t_n1 /mkset /=.  
    move => [[y' [H1 <-]] H2].
    by (exists z); split;[apply tn1_trans with y'| ].
  Qed.
  
  Lemma Fset_t4: forall (y z:T), 
      R (y, z) -> ( (R.+)#_(y) `<=` (R.+)#_(z) ).
  Proof.
    move => y z H1 x H2. by apply Fset_t3 with y.
  Qed.

  Lemma Fset_t5: forall (y z:T), 
      y \in (R.+)#_(z) -> ((R.+)#_(y) `<=` (R.+)#_(z) ).
  Proof.
    move => y z. 
    rewrite inP -Fset_t0 => H1.
    move => t; rewrite -2!Fset_t0 => H2. 
    by apply t_trans with y.
  Qed.

End Foreset_facts.

Section Closure_facts.

  Variables (T: Type) (E: relation T) (W: set T).

  Lemma Clos_x_x : forall (x:T), Clos_(x | E,W) x.
  Proof.
    rewrite /Fset /mkset /= => x.
    exists x;split. apply rt_refl. by []. 
  Qed.
  
  Lemma Clos_to_singleton: forall (X: set T) (x:T),
      Clos(X | E, W) x <-> exists y, X y /\ Clos_(y |E ,W) x.
  Proof.
    by split; rewrite Fset_union_set.
  Qed.    
  
  Lemma Clos_union: forall (X Y: set T),
      Clos(X `|` Y| E,W) = Clos(X| E,W) `|` Clos(Y| E,W).
  Proof.
    by move => X Y; rewrite Fset_union.
  Qed.
  
  Lemma Clos_s_inc: forall (X Y: set T) (x:T),
      X x -> Clos_(x| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    move => X Y x' /inP/set_inc2 H1.
    have H2:  Clos_(x'|E,W) `<=` Clos(X | E,W) 
      by apply Fset_inc1.
    have H3:  Clos(X|E,W) `<=` Clos(X `|` Y|E,W)
      by apply Fset_inc1; apply subsetUl.
    by apply subset_trans with Clos(X|E,W).
  Qed.
  
  Lemma Clos_inc_l: forall (X Y: set T),
      Clos(X| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    by move => X Y x; rewrite Clos_union; left.
  Qed.    
  
  Lemma Clos_inc_r: forall (X Y: set T),
      Clos(X| E,W) `<=` Clos(Y `|` X| E,W).
  Proof.
    by move => X Y x; rewrite Clos_union; right.
  Qed.    
  
  Lemma Clos_contains: forall (X: set T),
      X `<=` W -> X `<=` Clos(X| E,W).
  Proof.
    move => X H1 x H2. 
    by rewrite /Fset /mkset;exists x;split;[apply rt_refl| ].
  Qed.    
  
End Closure_facts.


Section Clos_trans_facts.  

  Variables (T:Type) (R S: relation T).

  Fixpoint iter (T:Type) (R: relation T) (n : nat) : relation T :=
    match n with 
    | 0 => 'Δ
    | n'.+1 => (iter R n') `;` R
    end.
  
  Lemma iter1_id: iter R 1 = R.
  Proof.
    by rewrite /iter Delta_idem_l.
  Qed.
  
  Lemma clos_t_sym: symmetric R -> symmetric (R.+).
  Proof.
    move => H1 x' y';rewrite /clos_t /=.
    elim => [x y ? |x y z _ ? _ ?]; first by apply t_step, H1.
    by apply t_trans with y.
  Qed.
  
  Lemma iter_compose : forall (n1 n2: nat), iter R (addn n1 n2) = (iter R n1) `;` (iter R n2).
  Proof.
    move => n1 n2.
    elim: n2 n1 => [ n1  | n1 H n0]; first by rewrite addn0 Delta_idem_r.
    by rewrite [addn n0 n1.+1]addnS /iter -/iter -[RHS]composeA H.
  Qed.

  (* R^{+} x y => exists n s.t R^k x y.  *) 
  
  Lemma clos_t_iterk: forall (x y:T), R.+ (x,y) -> exists (n:nat), (iter R n.+1) (x,y).
  Proof.
    move => x' y'. rewrite /clos_t /mkset /fst /snd.
    elim => [ x y H1 |  x y z H1 [n1 H2] H3 [n2 H4] ].
    by (exists 0; rewrite /iter Delta_idem_l).
    by exists (addn n1.+1 n2);rewrite -addnS iter_compose;exists y; split.
  Qed.
  
  Lemma iterk_inc_clos_trans: forall (n : nat), (iter R (n.+1)) `<=` R.+.
  Proof.
    elim => [ | n H [x y] H2]. 
    by rewrite /iter Delta_idem_l /clos_t /mkset => [[x y] /= H1]; apply: t_step.
    by move: H2 => [z [H1 H2]]; apply H in H1; apply t_trans with z; [ | apply t_step].
  Qed.
  
  Lemma iter1_inc_clos_trans: R `<=` R.+.
  Proof.
    have H1: (iter R 1) `<=` R.+ by apply iterk_inc_clos_trans.
    by rewrite /iter Delta_idem_l in H1.
  Qed.
  
  Lemma clos_t_inc : R `<=` S -> (R.+ ) `<=` (S.+ ).
  Proof.
    move => H [x' y'] ;rewrite /clos_t /mkset /=;elim => [x y ? | x y z _ H1 _ H2].
    by apply: t_step; apply: H.
    by apply: t_trans H1 H2.
  Qed.
  
  Lemma clos_t_sep_n : forall (n: nat) (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ (iter R n.+1) (x, y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x',y')).
  Proof.
    move => n x y W.
    elim: n x y => [x y [H1 [H2 H3]] | n H0 y y' ].
    by exists x; exists y; rewrite /iter Delta_idem_l in H3.
    rewrite /iter -/iter.
    move => [H2 [H3 [z [/= H4 H5]]]].
    pose proof lem (z \in W) as [H6 | H6].
    - by (exists z; exists y').
    - have H10: exists x' y' : T, x' \in W /\ y' \in W.^c /\ R (x', y').
      apply H0 with y z.
      split. by [].
      split. rewrite in_setE in H6. by rewrite /setC in_setE. 
      by [].
      move: H10 => [x2 [y2 [H11 [H12 H13]]]].
      by exists x2; exists y2.
  Qed.
  
  Lemma clos_t_sep : forall (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R.+ (x,y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x', y')).
  Proof.
    move => x y W [H1 [H2 H3]].
    apply clos_t_iterk in H3.
    move: H3 => [n' H3].
    by apply clos_t_sep_n with n' x y.
  Qed.
  
End Clos_trans_facts. 

Notation "R ^( n )" := (@iter _ R n) 
                     (at level 2, left associativity, format "R ^( n )").

Section Clos_trans_facts_1.
  
  Variables (T: Type) (R S Z U: relation T).

  Local Lemma clos_trans_inc: forall (V W: relation T), 
      (forall (n:nat), Z `;` (V^(n.+1)) `;` U = Z `;` (W^(n.+1)) `;` U) 
      -> Z `;` V.+ `;` U `<=` Z `;` W.+ `;` U.
  Proof.
    move => V W H;rewrite /compose /mkset.
    move => [x y] /= [u [[t [H1 H2]] H3]].
    have [n H4]: exists n, (iter V n.+1) (t, u) by apply: clos_t_iterk.
    have H5: (Z `;` iter V n.+1 `;` U) (x, y) by (exists u; split; [exists t;split | ]).
    have H6: (Z `;` iter W n.+1 `;` U) (x, y) by rewrite -H.
    move: H6 => [u' [[t' [H'1 H'2]] H'3]].
    by exists u'; split; [exists t'; split;[ | apply: iterk_inc_clos_trans H'2] | ].
  Qed.
  
  Lemma clos_trans_eq:
    (forall (n:nat), Z `;` (R^(n.+1)) `;` U = Z `;` (S^(n.+1)) `;` U)
    -> Z `;` R.+ `;` U = Z `;` S.+ `;` U.
  Proof.
    by move => H;rewrite predeqE;split;[apply: clos_trans_inc | apply: clos_trans_inc].
  Qed.
  
End Clos_trans_facts_1.

Section Clos_refl_trans_facts.

  Fixpoint sumRk (T:Type) (R: relation T) (n : nat) : relation T :=
    match n with 
    | 0 => 'Δ
    | n'.+1 => 'Δ `|` (R `;` (sumRk R n'))
    end.
  
  Variables (T: Type) (R S: relation T) (X Y: set T).
  
  Lemma clos_t_clos_rt: (R.+) `<=` R.*.
  Proof.
    move => [x' y']; rewrite /clos_t /clos_rt /mkset.
    elim => [x y | x y z _ H1 _ H2 ]; first by constructor.
    by apply rt_trans with y.
  Qed.

  Lemma clos_refl_trans_inc : R `<=` S -> (R.* ) `<=` (S.* ).
  Proof.
    move => H [x' y']; rewrite /clos_rt /mkset.
    
    elim => [x y ? | x | x y z _ H1 _ H2].
    by apply: rt_step; apply: H.
    by apply: rt_refl.
    by apply: rt_trans H1 H2.
  Qed.

  Lemma sumRk_0 : sumRk R 0 = 'Δ.
  Proof.
    rewrite predeqE /DeltaE /mkset /= => [[x' y']].
    split. 
    - move => /Delta_Id -> /=. split.  by []. by [].
    - by [].
  Qed.

  Lemma sumRk_1 : sumRk R 1 = 'Δ `|` R. 
  Proof.
    by rewrite /sumRk Delta_idem_r.
  Qed.
  
  Lemma sumRk_kp1_l : forall (n: nat), sumRk R (n.+1) = 'Δ `|`  (R `;` (sumRk R n)).
  Proof.
    by move => n.
  Qed.
  
  Lemma sumRk_kp1_r : forall (n: nat), sumRk R (n.+1) = 'Δ `|` ((sumRk R n) `;` R).
  Proof.
    elim => [ | n H]; first by rewrite sumRk_0 Delta_idem_l sumRk_1. 
    rewrite [in LHS]sumRk_kp1_l H composeDl  Delta_idem_r.
    rewrite setUA -composeA -[R in ('Δ `|` R `|` _)]Delta_idem_l -setUA.
    by rewrite -composeDr -sumRk_kp1_l H.
  Qed.

  Lemma Delta_inc_sumRk :  forall  (n: nat),   'Δ `<=` (sumRk R n).
  Proof.
    elim => [ | n H]; first  by rewrite sumRk_0.
    by rewrite sumRk_kp1_l;apply: subsetUl.
  Qed.

  Lemma sumRk_inc_sumRkp1 : forall (n: nat),
      (sumRk R n)  `<=` (sumRk R (n.+1)).
  Proof.
    elim => [ | n H]; first by rewrite sumRk_0 sumRk_1; apply subsetUl.
    have H1: ('Δ `|` (R `;` (sumRk R n))) `<=` ('Δ `|` (R `;` (sumRk R (n.+1))))
      by apply setUS;apply compose_inc.
    by rewrite sumRk_kp1_l; rewrite sumRk_kp1_l.
  Qed.
  
  Lemma sumRk_compose1 : forall (n: nat), sumRk R (n.+1) = (sumRk R n) `;` ('Δ `|` R). 
  Proof.
    move => n.
    have H1:  (sumRk R n)  `<=` (sumRk R (n.+1)) by apply sumRk_inc_sumRkp1.
    rewrite -setUidPl setUC in H1.
    rewrite -H1 sumRk_kp1_r setUA.
    have -> : sumRk R n `|` 'Δ = sumRk R n 
      by apply  setUidPl; apply Delta_inc_sumRk.
    by rewrite [RHS]composeDl Delta_idem_r.
  Qed.
  
  Lemma sumRk_compose2 : forall (n: nat),  sumRk R n = ('Δ `|` R)^(n).
  Proof.
    elim => [  | n H];first  by rewrite /sumRk /iter.
    by rewrite [in RHS]/iter -/iter -H -sumRk_compose1.
  Qed.
  
  Lemma sumRk_compose : forall (n1 n2: nat),
      sumRk R (n1 + n2) = (sumRk R n1) `;` (sumRk R n2).
  Proof.
    move => n1 n2; elim: n2 n1 => [ n1  | n1 H n2]. 
    by rewrite addn0 sumRk_0 Delta_idem_r. 
    by rewrite -addSnnS H !sumRk_compose2 -!iter_compose addSnnS. 
  Qed.
  
  Lemma sumRk_inc_clos_refl_trans: forall (n : nat), (sumRk R n) `<=` (R.*).
  Proof.
    elim => [/= | n H [x y] [/Delta_Id -> |H2]]; first by apply clos_refl_trans_containsD.
    by apply rt_refl.
    by move: H2 => [z [H1 H2]]; apply H in H2;apply rt_trans with z;[apply rt_step |].
  Qed.
  
  Lemma clos_rt_sumRk: forall (x y:T),  R.* (x, y) -> exists (n:nat), (sumRk R n) (x,y).
  Proof.
    move => x' y'. rewrite /clos_rt /mkset /=.
    elim =>[ x y /= H | x  | x y z H1 [n1 H2] H3 [n2 H4] ].
    exists 1;right;exists y. split. by []. by rewrite /sumRk Delta_Id.
    exists 0. by rewrite /sumRk  Delta_Id.
    by exists (addn n1 n2); rewrite sumRk_compose;exists y;split.
  Qed.

  Lemma clos_t_decomp_rt: R `|` (R `;` R.+) = R.+.
  Proof.
    rewrite predeqE => [[x' y']]. split.
    - move => [H1| [z [H1 H2]]].
      + by apply t_step.
      + by apply t_trans with z; [apply t_step|].
    - rewrite /clos_t /setU /mkset /=.
      elim => x y.
      + by left.
      + move => z H1 [H2|[z' [H2 H5]]] H3 [H4|[z'' [H4 H6]]].
        by right; exists y; split.
        by right; exists y; split.
        by right; exists z'; split; [ | apply t_trans with y].
        by right; exists z'; split; [ | apply t_trans with y].
  Qed.
  
  Lemma clos_t_decomp_2: R.+ `|` (R.+ `;` R.+) = R.+.
  Proof.
    rewrite predeqE => [[x' y']]. split;rewrite /clos_t /setU /compose /mkset /=.
    by move => [H1| [z [H1 H2]]]; [ | by apply t_trans with z].
    elim => x y; first  by left; apply t_step.
    move => z H1 [H2|[z' [H2 H5]]] H3 [H4|[z'' [H4 H6]]]; right.
    by exists y; split.
    by exists y; split.
    by exists z'; split; [ | apply t_trans with y].
    by exists z'; split; [ | apply t_trans with y].
  Qed.
  
  Lemma clos_tI:  (R.+ `;` R.+) `<=` R.+.
  Proof.
    have H2: (R.+ `|` R.+`;`R.+ `<=` R.+) by rewrite  clos_t_decomp_2.
    by move: H2;rewrite subUset => [[_ ?]].
  Qed.
  
  Lemma clos_t_decomp_rt_r: R `|` (R.+ `;` R) = R.+.
  Proof.
    rewrite predeqE => [[x' y']]. split;rewrite /clos_t /setU /compose /mkset /=.
    - move => [H1| [z [H1 H2]]]; first by apply t_step.
      by apply t_trans with z; [ | apply t_step].
    - elim => x y; first by left.
      move => z H1 [H2|[z' [H2 H5]]] H3 [H4|[z'' [H4 H6]]]; right.
      by exists y; split.
      by exists z''; split; [by apply t_trans with y | ].
      by exists y; split.
      by exists z'';split;[apply t_trans with z';[|apply t_trans with y;[apply t_step |]]|].
  Qed.

  Lemma DuT_eq_Tstar:  'Δ `|` R.+ = R.*.  
  Proof.
    rewrite predeqE => [[x' y']]. split;rewrite /clos_t /clos_rt /setU /compose /mkset.
    
    (* -> *) move => [/Delta_Id -> | H2]; [apply rt_refl | apply clos_t_clos_rt].
    (* <- *) by [].
    rewrite /=. 
    elim => [x0 y0 H| x0 | x0 y0 z _ [H1|H2] _ [H3|H4]].
    - by right; apply t_step.
    - by left; apply Delta_Id.
    - by left; move: H1 => /Delta_Id ->.
      by right; move : H1 => /Delta_Id ->.
      by right; move : H3 => /Delta_Id <-.
      by right; apply t_trans with y0.    
  Qed.

  Lemma r_clos_rt_clos_t: R `;` R.* = R.+.
  Proof.
    by rewrite -DuT_eq_Tstar composeDl Delta_idem_r clos_t_decomp_rt.
  Qed.
  
  Lemma clos_rt_r_clos_t: R.* `;` R = R.+.
  Proof.
    by rewrite -DuT_eq_Tstar composeDr Delta_idem_l clos_t_decomp_rt_r.
  Qed.

End Clos_refl_trans_facts.

Section Clos_refl_trans_facts1.
  
  Lemma L1 : forall (T: Type) (R S: relation T),
      R.* `;` S.* = ('Δ `|` R.+) `;` ('Δ `|` S.+ ).
  Proof.
    by move => T R S; rewrite !DuT_eq_Tstar.
  Qed.
  
  Lemma L2 : forall (T: Type) (R S: relation T),
      R.* `;` S.* = 'Δ `|` R.+ `|` S.+ `|` (R.+ `;` S.+). 
  Proof.
    move => T R S.
    by rewrite -!DuT_eq_Tstar
         !composeDl !composeDr DeltaE_inv Delta_idem_l Delta_idem_r setUA.
  Qed.

  Lemma compose_rt_rt : forall (T: Type) (R: relation T),  R.* `;` R.* = R.*. 
  Proof.
    by move => T R;rewrite L2 -setUA clos_t_decomp_2 -setUA setUid DuT_eq_Tstar.
  Qed.
  
End Clos_refl_trans_facts1.

Section Clos_Fset.
  
  Lemma E30 : forall (T:Type) (R: relation T) (X Y: set T),
      'Δ#X `|` R#Y = 'Δ#X `|` (Δ_(X.^c) `;` R)#Y.
  Proof.
    by move => A R X Y; rewrite Fset_D Union_Setminus -Fset_DCE Fset_comp.
  Qed.
  
  Lemma Fset_n : forall (T:Type) (R: relation T) (Y:set T) (n : nat),
      (sumRk R n)#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
  Proof.
    move => T R Y n x H.
    have H0: forall (n':nat), (sumRk R n') # Y = (sumRk ( Δ_(Y.^c) `;` R) n') # Y
        by elim => [ | n' H'];[rewrite /sumRk 
                             |rewrite -!Fset_union_rel -!/sumRk -!Fset_comp 
                              -[in RHS]H' !Fset_comp -[in RHS]E30].
    
    have H1: ((sumRk R n) # Y) `<=` ((sumRk (Δ_(Y.^c) `;` R) n) # Y)
      by move => x' H1;rewrite -H0.
    have H2: ((sumRk (Δ_(Y.^c) `;` R) n) # Y) `<=` ((Δ_(Y.^c) `;` R).* # Y)
      by move => H2; apply: Fset_inc; apply: sumRk_inc_clos_refl_trans.
    by apply: H2; apply: H1.
  Qed.

  Lemma Fset_rt: forall (T: Type) (R: relation T) (Y:set T),
      (Δ_(Y.^c) `;` R).*#Y = R.*#Y.
  Proof.
    move => T R Y.
    have H0: (Δ_(Y.^c) `;` R).* `<=`  (R.* )
      by apply: clos_refl_trans_inc; move => [x y] [z [ [_ /= ->] H2]]. 
    have E29_1:  (Δ_(Y.^c) `;` R).*#Y `<=` R.*#Y
      by apply Fset_inc.
    have E29_2:  R.*#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
    move => x [z [H1 H2]];
           suff: exists n : nat, sumRk R n (x, z); last by apply: clos_rt_sumRk.
    by move => [n H3];(suff: (Fset (sumRk R n) Y) x; 
                      first by move => H; apply Fset_n in H);
              exists z; split.
    rewrite predeqE => x. split.
    by apply: E29_1. 
    by apply: E29_2.
  Qed.
  
End Clos_Fset.

Section Relation_restricted.
  (** * XXX to be done with sigma_types *)
  Definition Restrict (T:Type) (R: relation T) (X: set T) := 
    [ set x | X x.1 /\ X x.2 /\ R x].
  
  Lemma Rest (T:Type) (X: set T) (R: relation T) : (Restrict R X) = Δ_(X) `;` R `;` Δ_(X).
  Proof.
    rewrite predeqE => [[x y]].
    split => [[/= H1 [H2 H3]] | [z [[t [[/= H1 H'1] H2]] [/= H3 H'3]]]].
    by (exists y;split;[ exists x;split | ]).
    by split; [ | split; [rewrite -H'3 | rewrite H'1 -H'3]].
  Qed.

End Relation_restricted.

