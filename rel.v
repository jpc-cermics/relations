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
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import ssrel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * relations as sets: (set T*T) *)

Definition relation T := set (T * T).

Notation "R .+" := (clos_t R) 
                     (at level 2, left associativity, format "R .+").
Notation "R .*" := (clos_rt R) 
                     (at level 2, left associativity, format "R .*").
Reserved Notation "R .-1" (at level 2, left associativity, format "R .-1"). 

Section Sets_facts.

  Variables (A:Type).

  (* usefull to ease changes mixed with moves *)
  Lemma inP: forall (x:A) (X: set A), x \in X <-> X x. 
  Proof.
    by move => x X; rewrite in_setE.
  Qed.

  Lemma inP_Test: forall (x:A) (X Y: set A), x \in X `|` Y -> True.
    by move => x X Y /inP [H1 | H1].
  Qed.
    
  Lemma notempty_exists: forall (X: set A), (exists z, z \in X) <-> (X != set0)%classic.
  Proof.
    by move => X; rewrite set0P;split;move => [z /inP H1]; exists z. 
  Qed.
  
  Lemma empty_notexists: forall (X: set A), X = set0 <-> ~ (exists z, z \in X).
  Proof.
    move => X.
    split.
    - by move => -> [z /inP H1]. 
    - move => H1. rewrite predeqE => x.
      by split => [/inP H2 | H2];[have H3: exists (z:A), z \in X by (exists x) |].
  Qed.
  
  Lemma empty_iff: forall (X: set A), ~ (X != set0) <-> X = set0.
  Proof.
    by move => X;rewrite -notempty_exists empty_notexists.
  Qed.
  
  Lemma W_part : forall (X Y Z: set A),
      (Y `<=` X) /\ (Z= X `\` Y) -> Y `&` Z = set0.
  Proof.
    move => X Y Z [? H2];rewrite empty_notexists H2.
    by move => [z /inP [? [_ ?]]].
  Qed.
  
  Lemma In_Setminus : forall (X Y: set A), (X `\` Y) `<=` X. 
  Proof.
    by move => X Y x [? ?].
  Qed.

  Lemma Union_empty : forall (X Y: set A), X `|` Y = set0 <-> (X= set0) /\ ( Y = set0).
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
  Variables (A: Type) (R S T: relation A).

  Lemma unionC: R `|` S = S `|` R.
  Proof. by rewrite setUC. Qed.
  
  Lemma unionA:  (R `|` S) `|` T = R `|` (S `|` T).
  Proof. by rewrite -setUA. Qed.
  
  Lemma union_RR:  R `|` R = R.
  Proof. by apply setUid. Qed.
  
  Lemma union_containsl: R `<=` (R `|` S). 
  Proof. by apply subsetUl. Qed.
  
  Lemma union_containsr : S `<=` (R `|` S). 
  Proof. by apply subsetUr. Qed.
  
  Lemma union_inc_eq : S `<=` R <-> R `|` S = R.
  Proof. by rewrite setUidPl. Qed. 
  
  Lemma union_inc_l : S `<=` T -> (R `|` S) `<=` (R `|` T). 
  Proof. by apply setUS. Qed.
  
  Lemma union_inc_r : S `<=` T -> (S `|` R) `<=` (T `|` R).
  Proof. by apply setSU. Qed.
  
  Lemma union_inc_b : S `<=` T -> R `<=` T -> (S `|` R) `<=` T.
  Proof.
    move => H1 H2; have <- : T `|` R = T by apply setUidPl.
    by apply setSU.
  Qed.

End Union_facts.

Section Inverse.
  
  Variables (A: Type) (R S: relation A).
  
  Definition inverse (A: Type) (R: relation A): relation A := [set x | R (x.2,x.1)].

  Local Notation "R .-1" := (@inverse _ R) : classical_set_scope.
  
  Lemma inverse_inverse (U : relation A):  U.-1.-1 = U.
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
    have H0: forall (X Y: relation A), X = Y -> X.-1 = Y.-1
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
  
  Definition compose (A: Type) (R T: relation A): relation A := 
    [set x | exists (z: A), R (x.1,z) /\ T (z,x.2)]%classic.

  Definition compose' (A: Type) (R T: relation A): relation A := 
    [set xy | exists2 z, R (xy.1, z) & T (z, xy.2)]%classic.

End Compose. 

Notation "R * T" := (compose R T).

Section Compose_facts. 
  
  Variables (A: Type) (R S T : relation A).

  Lemma Test: compose R S `<=` setT.
  Proof.
    move => x [z [H1 H2]]. 
    by [].
  Qed.
  
  Lemma Test': compose' R S `<=` setT.
  Proof.
    move => x [z H1 H2]. 
    by [].
  Qed.
  
  Lemma composeA : (R * S) * T = R * (S * T).
  Proof.
    rewrite predeqE => x'.
    split => [ [z [[w /= [? ?]] ?]] | [z [? [ w [? ?]]]]].
    by (exists w);split; [ | exists z; split].
    by (exists w);split; [ exists z | ].
  Qed.

  Lemma composeDr : (R `|` S) * T = (R * T) `|` (S * T).
  Proof.
    rewrite predeqE => x.
    split.
    by move => [z [[? | ? ] ?]]; [ left| right]; exists z.
    by move => [|] [ z [? ?]];[exists z; split; [ left | ] | exists z; split; [right | ]].
  Qed.
  
  Lemma composeDl : R * (S `|` T) = (R * S) `|` (R * T).
  Proof.
    rewrite predeqE => x.
    split.
    by move => [z [H1 [H3|H4]]];[ left; exists z; split | right; exists z; split].
    move => [[z [H1 H2]] | [z [H1 H2]]];
           first by exists z; split; [ | left].
                      by exists z;  split; [ | right]. 
  Qed.
  
  Lemma compose_inc : S `<=` T ->(R * S) `<=` (R * T). 
  Proof.
    rewrite /subset => H x [z [H1 H2]].
    by exists z; split; [ | apply H].
  Qed.
  
  Lemma composer_inc : S `<=` T ->(S * R ) `<=` (T *R). 
  Proof.
    rewrite /subset => H x [z [? ?]].
    by exists z; split; [apply H | ].
  Qed.
  
  Lemma inverse_compose : (R * S).-1 = S.-1 * R.-1.
  Proof.
    rewrite predeqE => x.
    by split;move => [z [H1 H2]]; exists z; split.
  Qed.
  
  Lemma RRm_inverse : (R * R.-1).-1 = R * R.-1.
  Proof.
    have RRm_sym : symmetric (R * R.-1)
        by move => x y [z [H1 H2]];exists z; split; [apply H2| apply H1].
    by apply inverse_sym, RRm_sym.
  Qed. 
  
End Compose_facts.

#[global]
  Hint Resolve inverse_compose composeDl composeDr composeA : relations.

Section Delta.

  (** * Simplifier en enlevant le \in ça doit simplifire les preuves qui suivent *)
  Definition DeltaE (A: Type) (X: set A) : relation A := 
    [set x | x.1 \in X /\ x.1 = x.2]%classic.

  Definition DeltaCE (A: Type) (X: set A) : relation A := 
    DeltaE (~` X).
  
End Delta.

Notation "Δ_( W )" := (@DeltaE _ W) 
                        (at level 2, no associativity, format "Δ_( W )").
Notation "W .^c" := (~` W) 
                      (at level 2, left associativity, format "W .^c").
Notation "'Δ" := (DeltaE setT) (at level 2, no associativity).
Notation "'Δc" := (DeltaCE setT) (at level 2, no associativity).

Section Delta_facts.
  
  Variables (A: Type) (R: relation A) (X Y: set A).

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
    move =>  H [x y] /=; rewrite !in_setE => [[H1 <-]]. 
    by split;[apply H |].
  Qed.

  Lemma DeltaE_inv :  Δ_(X) * Δ_(X) = Δ_(X).
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
  
  Lemma Delta_Id : forall (x y:A), 'Δ (x,y) <-> x = y.
  Proof.
    rewrite /DeltaE /mkset /=.
    move => x y; split;first by move => [H1 ->].
    by move => H1; split;[apply mem_setT|].
  Qed.
  
  Lemma DeltaE_inc_D : Δ_(X) `<=` 'Δ.
  Proof.
    rewrite /DeltaE /mkset /subset /=.
    by move => [x y] /= [H1 <-]; split;[apply mem_setT|].
  Qed.
  
  Lemma DeltaW_XXXX : forall (X' Y': set A), Δ_(X') * Δ_(Y') = Δ_(X' `&` Y').
  Proof.
    move => X' Y'.
    rewrite /DeltaE /compose /mkset predeqE.
    move => [x y] /=; rewrite !in_setE.
    split => [[z [[H1 <-] [H2 <-]]] | [[H1 H2] <-]]. 
    by rewrite !in_setE in H2.
    by exists x; rewrite in_setE. 
  Qed.

  Lemma WWcI: X `&` X.^c = set0.
    Proof.
      rewrite /mkset predeqE.
      by move => x;split => [ [? H2] | ?];[rewrite /setC  mksetE in H2 |].
    Qed.
    
  Lemma DeltaW_Wc : Δ_(X) * Δ_(X.^c) = 'Δc.
  Proof.
    rewrite DeltaW_XXXX WWcI /DeltaCE /DeltaE /setC /set0 predeqE. 
    move => [x y]/=.
    by split; rewrite !in_setE; move => [H1 <-].
  Qed.
  
  Lemma DeltaWc_W : Δ_(X.^c) * Δ_(X) = 'Δc.
  Proof.
    rewrite DeltaW_XXXX setIC WWcI /DeltaCE /DeltaE /setC /set0 predeqE. 
    move => [x y]/=.
    by split; rewrite !in_setE; move => [H1 <-].
  Qed.
  
  Lemma DeltaC_union_ideml : 'Δc `|` R = R.
  Proof.
    rewrite /setU /DeltaCE /DeltaE /setC /mkset predeqE. 
    move => [x y]/=.
    split.
    by move => [[H1 H2] | H1];[rewrite in_setE in H1 |].
    by move => H1; right.
  Qed.
  
  Lemma DeltaC_union_idemr :  R `|` 'Δc = R.
  Proof.
    by rewrite unionC; apply DeltaC_union_ideml.
  Qed.

  Lemma DeltaC_compose_absorbl : 'Δc * R = 'Δc.
  Proof.
    rewrite /compose /DeltaCE /DeltaE /setC /mkset predeqE. 
    move => [x y]/=; split.
    by move => [z [[ H1 _] _]];rewrite in_setE in H1.
    by move => [H1 _]; rewrite in_setE in H1.
  Qed.
  
  Lemma DeltaC_compose_absorbr :  R * 'Δc = 'Δc.
  Proof.
    rewrite /compose /DeltaCE /DeltaE /setC /mkset predeqE. 
    move => [x y]/=; split.
    by move => [z [_ [H1 _]]];rewrite in_setE in H1.
    by move => [H1 _]; rewrite in_setE in H1.
  Qed.
  
  Lemma DeltaE_union : forall (X' Y':set A), Δ_(X') `|` Δ_(Y') = Δ_(X' `|` Y').
  Proof.
    move => X' Y'.
    rewrite /DeltaE /setU /mkset predeqE.
    move => [x y] /=; rewrite !in_setE.
    split.
    by move => [[H1 <-] | [H1 <-]];[split;[left |] | split;[right |]].
    by move => [[H1 | H1] <-];[left | right].
  Qed.

  Lemma WWcU: X `|` X.^c = setT.
    Proof.
      rewrite /setU /setC /mkset predeqE.
      by move => x; split => _;[ rewrite -in_setE in_setT | apply lem].
    Qed. 
    
  Lemma DeltaE_comp : Δ_(X) `|` Δ_(X.^c) = 'Δ.
  Proof.
    by rewrite DeltaE_union WWcU. 
  Qed.

  (* XXXX deja vu *)
  Lemma DeltaE_compose : forall (Y: set A), 
      Δ_(X) * Δ_(Y) = Δ_(X `&` Y).
  Proof.
    by move => Y'; rewrite DeltaW_XXXX.
  Qed.
  
  Lemma DeltaE_compose_same : Δ_(X) * Δ_(X) = Δ_(X).
  Proof.
    have H1: X `&` X = X
      by rewrite /setI /mkset predeqE;move => x;split;[move => [? _] |].
    by rewrite DeltaW_XXXX H1.
  Qed.
  
  Lemma Delta_idem_l : 'Δ * R = R.  
  Proof.
    rewrite /compose /DeltaE /mkset predeqE.
    move => [x y]/=.
    split.
    by move => [z [/Delta_Id->  H2]].
    by move => H1; exists x; split;[ apply Delta_Id |].
  Qed.
  
  Lemma Delta_idem_r : R * 'Δ = R.  
  Proof.
    rewrite /compose /DeltaE /mkset predeqE.
    move => [x y]/=.
    split.
    by move => [z [H1 /Delta_Id<-]].
    by move => H1; exists y; split;[| apply Delta_Id].
  Qed.
  
  Lemma Delta_clos_trans_ends : (R * Δ_(X)).+ =  (R * Δ_(X)).+ * Δ_(X).
  Proof.
    rewrite /compose /DeltaE /clos_t /mkset predeqE.
    move => [x' y']/=.
    split; last by elim => z' [H1 [H2 <-]].
    elim => x y. 
    + move => /= [z [H1 [H2 H3]]].
      exists y; split; first by apply t_step; exists y; split;[rewrite -H3 | split; [rewrite -H3| ]].
      by split;[rewrite -H3| ].
    + move => z H1 [z1 [H2 H'2]] H3 [z2 [H4 [H'4 H''4]]].
      by exists z; split;[ apply t_trans with y |split; rewrite -H''4].
  Qed.
  
  Lemma Delta_clos_trans_starts : (Δ_(X)* R).+ = Δ_(X) * (Δ_(X) * R).+.
  Proof.
    rewrite /compose /DeltaE /clos_t /mkset predeqE.
    move => [x' y']/=.
    split; last  by move => [z [[H1 <-] H2]].
    elim => x y. 
    by move => [z [[H1 H2] H3]];
              exists z; split; [split | apply t_step; exists z; split; [split; [rewrite -H2 | ]|]].
    by move => z _ [x1 [[H2 <-] H3]] _ [y1 [[H4 <-] H5]];
              exists x; split; [split | apply t_trans with y]. 
  Qed.

  Lemma clos_refl_trans_containsD: Δ_(X) `<=` R.* .
  Proof.
    rewrite /subset /DeltaE /clos_rt /mkset.
    by move => [x y] [H1 ->];apply rt_refl.
  Qed.

  Lemma R_restrict : forall (x y: A),  
      x \in X /\ y \in X -> 
      (R (x,y) <-> let DR:= (Δ_(X) * R * Δ_(X)) in DR (x,y)).
  Proof.
    rewrite /compose /DeltaE /mkset /=.
    move => x y [H1 H2].
    split=> [ H3 | [z [[t [[H3 ->] H4] [H5 <-]]]] //].
    by (exists y; split;[ exists x; split | ]).
  Qed.

  Lemma R_restrict_l : forall (x y: A),
      x \in X -> (R (x,y) <-> let DR:= (Δ_(X) * R) in DR (x,y)).
  Proof.
    rewrite /compose /DeltaE /mkset /=.
    move => x y H1.
    split => [ H2 | [z [[H2 ->] H3] ] //].
    by (exists x; split).
  Qed.
  
  Lemma DeltaCsubset: (Δ_(X) * R `<=` R).
  Proof.
    rewrite /subset /DeltaE /compose /mkset /=.
    by move => [x y] /= => [[z [[_ <-] H2]]].
  Qed.
  
  Lemma DeltaCsubsetl: (R * Δ_(X) `<=` R).
  Proof.
    rewrite /subset /DeltaE /compose /mkset /=.
    by move => [x y] /= => [[z [H2 [_ <-]]]].
  Qed.
    
End Delta_facts.

#[global]
  Hint Resolve DeltaE_union DeltaCE DeltaE_inverse DeltaE_inv Delta_idem_l Delta_idem_r : relations.

Section Foresets.

  Definition Fset (A:Type) (R: relation A) (Y: set A) : set A :=
    [set x | exists (y: A), R (x,y) /\ y \in Y]%classic.
    
End Foresets.

(* Foreset of Y for the relation R*)
Notation "R # Y" := (Fset R Y) 
                      (at level 3, no associativity, format "R # Y").

(* Foreset of {y} for the relation R*)
Notation "R #_( y )" := (Fset R ([set y]))
                          (at level 3, no associativity, format "R #_( y )").

(* Closure of Y for the relation R and subset W *)
Notation "Clos( Y | R , W )" :=  (Fset ((Δ_(W.^c) * R).* ) Y)
                                 (at level 3, no associativity, format "Clos( Y | R , W )").    

(* Closure of {y} for the relation R and subset W *)
Notation "Clos_( y | R , W )" := (Fset ((Δ_(W.^c) * R).* ) ([set y]))
                                 (at level 3, no associativity, format "Clos_( y | R , W )").    

Section Foreset_facts.
  
  Variables (A:Type) (R S: relation A) (X Y: set A).

  (* XXXX à remonter *)
  Lemma Singl_iff: forall (x y:A), x \in [set y] <-> x = y.
  Proof.
    move => x y. rewrite in_setE.
    split. 
    by [].
    by move => ->.
  Qed.
  
  Lemma Fset_D :   'Δ#X = X.
  Proof.
    rewrite /Fset /DeltaE /mkset predeqE /=.
    move => x.
    split.
    by move => [x' [/Delta_Id -> H1]]; rewrite in_setE in H1.
    by move => H; exists x; split;[split;[apply mem_setT|] | rewrite in_setE].
  Qed.

  Lemma Fset_DE : Δ_(Y)#X = Y `&` X.
  Proof.
    rewrite /Fset /DeltaE /mkset predeqE /=.
    move => x.
    split.
    by move => [x' [[H1 H'1] H2]];rewrite !in_setE in H2 H1;
              split; [ | rewrite H'1]. 
    by move => [H1 H2]; exists x; rewrite !in_setE.
  Qed.
  
  Lemma Fset_DCE : Δ_(Y.^c)#X = X `\` Y.
  Proof.
    rewrite /Fset /DeltaE /setC /mkset predeqE /=.
    move => x.
    split.
    by move => [x' [[H1 H'1] H2]];rewrite !in_setE in H2 H1;
              split; [rewrite H'1 |].
    by move => [H1 H2]; exists x; rewrite !in_setE.
  Qed.
  
  Lemma Fset_inc : R `<=` S -> R#X `<=` S#X.
  Proof.
    move => H x [y [H1 H2]].
    by exists y; split; [apply: H | ].
  Qed.
  
  Lemma Fset_inc1 : X `<=` Y -> R#X `<=` R#Y.
  Proof.
    move => H x [y [H1 H2]]. rewrite inE in H2.
    exists y. rewrite inE. split. by []. by apply H.
  Qed.
  
  Lemma set_inc2: forall (x: A), x \in X <->  [set x] `<=` X.
  Proof.
    move => x. split.
    - move => ? y ?. 
      by (have H2: x = y by []); rewrite -in_setE -H2. 
    - move => H1.
      by rewrite in_setE; apply H1. 
  Qed.
  
  Lemma Fset_comp : S # (R # X) = (S * R) # X.
  Proof.
    rewrite /Fset /compose /Fset /mkset predeqE /=.
    move => x; split.
    move => [z [H1 H2]]. rewrite !in_setE in H2. 
    move: H2 => [y [H2 H3]]; rewrite !in_setE in H3.
    by (exists y);split; [ exists z;split |  rewrite in_setE]. 
    by move => [ y [[z [H3 H4]] H2]]; exists z; split;
              [ | rewrite in_setE; exists y].
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
    - move => [z [H1 H2]]. rewrite !in_setE in H2.  
      move: H2 => [H2 | H2].
      left. exists z. by rewrite in_setE.
      right. exists z. by rewrite in_setE.
    - move => [[y [H1 H2]] | [y [H1 H2]]].
      exists y. split. by []. rewrite in_setE. rewrite in_setE in H2. by left.
      exists y. split. by []. rewrite in_setE. rewrite in_setE in H2. by right.
  Qed.
  
  (* Foreset in extension *)

  Definition Fset_ext := fun (x:A) => (exists y, y \in Y /\ x \in R#_(y)).
  
  Lemma Fset_union_set : forall (x:A), x \in (R#Y) <-> exists y, y \in Y /\ x \in R#_(y).
  Proof.
    move => x.
    rewrite /Fset /mkset /=.
    split.
    - rewrite in_setE. move => [y [H1 H2]].
      exists y. split. by []. rewrite in_setE. exists y. split. by []. by rewrite in_setE.
    - move => [y [H1 H2]]. rewrite !in_setE in H1 H2 *.
      move: H2 => [z [H2 H3]].
      exists z.
      rewrite in_setE in H3.
      split. by [].
      have -> : z = y by []. 
      by rewrite in_setE.
  Qed.

  Lemma Fset_union_ext : (R#Y) = Fset_ext. 
  Proof.
    rewrite /Fset_ext predeqE.
    move => x. 
    split => H. 
    by rewrite -Fset_union_set in_setE.
    by rewrite -in_setE Fset_union_set. 
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
  
  Lemma Fset_intersect : forall (x y:A), (exists z, z \in R#_(x) /\ z \in S#_(y))
                                    <-> let RmR := R.-1 * S in RmR (x,y). 
  Proof.
    rewrite /Fset /mkset.
    move => x y.
    split. 
    - move => [ z [H1 H2]].
      rewrite !in_setE in H1 H2.
      move: H1 => [r [H1 H1']].
      move: H2 => [t [H2 H2']].
      rewrite !in_setE in H1' H2'.
      have -> : x = r by [].
      have <- : t = y by [].
      exists z. split. by rewrite /inverse /=. by [].
    - rewrite /inverse; move => [z /= [H1 H2]].
      exists z. rewrite !in_setE.
      split. exists x. rewrite in_setE.  by []. 
      exists y. rewrite in_setE. by []. 
  Qed.
  
  Lemma Fset_singleton: forall (x:A), reflexive R -> x \in R#_(x). 
  Proof.
    move => x H.  rewrite in_setE /Fset /mkset. exists x. rewrite in_setE.  by []. 
  Qed.
  
  Lemma Fset_rt_singleton: forall (x:A), x \in R.*#_(x). 
  Proof.
    move => x.  rewrite in_setE /Fset /mkset. exists x.
    split. by apply rt_refl. by rewrite in_setE.
  Qed.

  Lemma Fset_restrict : X `<=` Y -> R#X = (R* Δ_(Y))# X.
  Proof.
    rewrite /subset /Fset /compose /DeltaE /mkset predeqE /=. 
    move => H x; split. 
    - move => [y [H1 H2]].
      exists y. split. exists y. split. by []. split. rewrite in_setE. apply H. by rewrite -in_setE. by []. by [].
    - by move => [y [[z [H1 [_ <- ]]] H4]];(exists z). 
  Qed.

  
  Lemma Fset_t1: forall (x y:A), R (x, y) -> x \in R.+#_(y). 
  Proof.
    move => x y H1.
    rewrite in_setE /Fset /clos_rt /mkset /=.
    exists y. split. by apply t_step. by rewrite Singl_iff.
  Qed.
  
  Lemma Fset_t2: forall (x y:A), 
      (exists (x1:A), R (x, x1) /\ x1 \in R.+#_(y)) -> x \in R.+#_(y). 
  Proof.
    move => x y' [x1 [H1 H2]].  
    move: H2. rewrite /Fset /clos_t /mkset /= !in_setE.
    move => [y [H2 /Singl_iff <-]].
    exists y. split. apply t_trans with x1. by apply t_step. by [].
    by rewrite Singl_iff. 
  Qed.

  Lemma Fset_t3: forall (x y z:A), 
      x \in R.+#_(y) /\ R (y, z) -> x \in R.+#_(z) . 
  Proof.
    move => x y z. rewrite !in_setE /Fset /clos_t /mkset /=.  
    move => [[y' [/clos_trans_tn1_iff H1 /Singl_iff <-]] H2].
    by (exists z);rewrite Singl_iff; split;[rewrite clos_trans_tn1_iff;apply tn1_trans with y'| ].
  Qed.
  
  Lemma Fset_t4: forall (y z:A), 
      R (y, z) -> ( (R.+)#_(y) `<=` (R.+)#_(z) ).
  Proof.
    move => y z H1 x H2. rewrite -in_setE. apply Fset_t3 with y.
    by rewrite in_setE.
  Qed.

End Foreset_facts.

Section Closure_facts.

  Variables (A: Type) (E: relation A) (W: set A).

  Lemma Clos_x_x : forall (x:A), x \in Clos_(x | E,W).
  Proof.
    rewrite /Fset /mkset /= => x.
    rewrite in_setE.
    exists x;split. apply rt_refl. by apply /Singl_iff.
  Qed.
  
  Lemma Clos_to_singleton: forall (X: set A) (x:A),
      x \in Clos(X | E, W) <-> exists y, y \in X /\ x \in Clos_(y |E ,W).
  Proof.
    by split;move => /Fset_union_set ?.
  Qed.    
  
  Lemma Clos_union: forall (X Y: set A),
      Clos(X `|` Y| E,W) = Clos(X| E,W) `|` Clos(Y| E,W).
  Proof.
    by move => X Y; rewrite Fset_union.
  Qed.
  
  Lemma Clos_s_inc: forall (X Y: set A) (x:A),
      x \in X -> Clos_(x| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    move => X Y x' /set_inc2 H1.
    have H2:  Clos_(x'|E,W) `<=` Clos(X | E,W) 
      by apply Fset_inc1.
    have H3:  Clos(X|E,W) `<=` Clos(X `|` Y|E,W)
      by apply Fset_inc1; apply subsetUl.
    by apply subset_trans with Clos(X|E,W).
  Qed.
  
  Lemma Clos_inc_l: forall (X Y: set A),
      Clos(X| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    by move => X Y x; rewrite Clos_union; left.
  Qed.    
  
  Lemma Clos_inc_r: forall (X Y: set A),
      Clos(X| E,W) `<=` Clos(Y `|` X| E,W).
  Proof.
    by move => X Y x; rewrite Clos_union; right.
  Qed.    
  
  Lemma Clos_contains: forall (X: set A),
      X `<=` W -> X `<=` Clos(X| E,W).
  Proof.
    move => X H1 x H2. 
    by rewrite /Fset /mkset;exists x;split;[apply rt_refl| rewrite in_setE].
  Qed.    
  
End Closure_facts.


Section Clos_trans_facts.  

  Variables (A:Type) (R S: relation A).

  Fixpoint iter (A:Type) (R: relation A) (n : nat) : relation A :=
    match n with 
    | 0 => 'Δ
    | n'.+1 => (iter R n') * R
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
  
  Lemma iter_compose : forall (n1 n2: nat), iter R (addn n1 n2) = (iter R n1) * (iter R n2).
  Proof.
    move => n1 n2.
    elim: n2 n1 => [ n1  | n1 H n0]; first by rewrite addn0 Delta_idem_r.
    by rewrite [addn n0 n1.+1]addnS /iter -/iter -[RHS]composeA H.
  Qed.

  (* R^{+} x y => exists n s.t R^k x y.  *) 
  
  Lemma clos_t_iterk: forall (x y:A), R.+ (x,y) -> exists (n:nat), (iter R n.+1) (x,y).
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
  
  Lemma clos_t_sep_n : forall (n: nat) (x y: A) (W:set A),
      x\in W /\ y \in W.^c /\ (iter R n.+1) (x, y)
      ->  (exists (x' y': A), x'\in W /\ y' \in W.^c /\ R (x',y')).
  Proof.
    move => n x y W.
    elim: n x y => [x y [H1 [H2 H3]] | n H0 y y' ].
    by exists x; exists y; rewrite /iter Delta_idem_l in H3.
    rewrite /iter -/iter.
    move => [H2 [H3 [z [/= H4 H5]]]].
    pose proof lem (z \in W) as [H6 | H6].
    - by (exists z; exists y').
    - have H10: exists x' y' : A, x' \in W /\ y' \in W.^c /\ R (x', y').
      apply H0 with y z.
      split. by [].
      split. rewrite in_setE in H6. by rewrite /setC in_setE. 
      by [].
      move: H10 => [x2 [y2 [H11 [H12 H13]]]].
      by exists x2; exists y2.
  Qed.
  
  Lemma clos_t_sep : forall (x y: A) (W:set A),
      x\in W /\ y \in W.^c /\ R.+ (x,y)
      ->  (exists (x' y': A), x'\in W /\ y' \in W.^c /\ R (x', y')).
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

  Variables (A: Type) (R S T U: relation A).

  Local Lemma clos_trans_inc: forall (V W: relation A), 
      (forall (n:nat), T*(V^(n.+1))* U = T*(W^(n.+1))*U) -> T*V.+*U `<=` T*W.+ *U.
  Proof.
    move => V W H;rewrite /compose /mkset.
    move => [x y] /= [u [[t [H1 H2]] H3]].
    have [n H4]: exists n, (iter V n.+1) (t, u) by apply: clos_t_iterk.
    have H5: (T * iter V n.+1 * U) (x, y) by (exists u; split; [exists t;split | ]).
    have H6: (T * iter W n.+1 * U) (x, y) by rewrite -H.
    move: H6 => [u' [[t' [H'1 H'2]] H'3]].
    by exists u'; split; [exists t'; split;[ | apply: iterk_inc_clos_trans H'2] | ].
  Qed.
  
  Lemma clos_trans_eq:
    (forall (n:nat), T*(R^(n.+1))*U = T*(S^(n.+1))*U) -> T*R.+*U = T*S.+*U.
  Proof.
    by move => H;rewrite predeqE;split;[apply: clos_trans_inc | apply: clos_trans_inc].
  Qed.

End Clos_trans_facts_1.

Section Clos_refl_trans_facts.

  Fixpoint sumRk (A:Type) (R: relation A) (n : nat) : relation A :=
    match n with 
    | 0 => 'Δ
    | n'.+1 => 'Δ `|` (R * (sumRk R n'))
    end.
  
  Variables (A: Type) (R S: relation A) (X Y: set A).
  
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
    - move => /Delta_Id -> /=. split. apply mem_setT. by [].
    - by [].
  Qed.

  Lemma sumRk_1 : sumRk R 1 = 'Δ `|` R. 
  Proof.
    by rewrite /sumRk Delta_idem_r.
  Qed.
  
  Lemma sumRk_kp1_l : forall (n: nat), sumRk R (n.+1) = 'Δ `|`  (R * (sumRk R n)).
  Proof.
    by move => n.
  Qed.
  
  Lemma sumRk_kp1_r : forall (n: nat), sumRk R (n.+1) = 'Δ `|` ((sumRk R n) * R).
  Proof.
    elim => [ | n H]; first by rewrite sumRk_0 Delta_idem_l sumRk_1. 
    rewrite [in LHS]sumRk_kp1_l H composeDl  Delta_idem_r.
    rewrite -unionA -composeA -[R in ('Δ `|` R `|` _)]Delta_idem_l unionA.
    by rewrite -composeDr -sumRk_kp1_l H.
  Qed.

  Lemma Delta_inc_sumRk :  forall  (n: nat),   'Δ `<=` (sumRk R n).
  Proof.
    elim => [ | n H]; first  by rewrite sumRk_0.
    by rewrite sumRk_kp1_l;apply: union_containsl.
  Qed.

  Lemma sumRk_inc_sumRkp1 : forall (n: nat),
      (sumRk R n)  `<=` (sumRk R (n.+1)).
  Proof.
    elim => [ | n H]; first by rewrite sumRk_0 sumRk_1; apply union_containsl.
    have H1: ('Δ `|` R*(sumRk R n)) `<=` ('Δ `|` R*(sumRk R (n.+1)))
      by apply union_inc_l;apply compose_inc.
    by rewrite sumRk_kp1_l; rewrite sumRk_kp1_l.
  Qed.
  
  Lemma sumRk_compose1 : forall (n: nat), sumRk R (n.+1) = (sumRk R n) * ('Δ `|` R). 
  Proof.
    move => n.
    have H1:  (sumRk R n)  `<=` (sumRk R (n.+1)) by apply sumRk_inc_sumRkp1.
    rewrite union_inc_eq unionC in H1.
    rewrite -H1 sumRk_kp1_r -unionA.
    have -> : sumRk R n `|` 'Δ = sumRk R n 
      by apply union_inc_eq; apply Delta_inc_sumRk.
    by rewrite [RHS]composeDl Delta_idem_r.
  Qed.
  
  Lemma sumRk_compose2 : forall (n: nat),  sumRk R n = ('Δ `|` R)^(n).
  Proof.
    elim => [  | n H];first  by rewrite /sumRk /iter.
    by rewrite [in RHS]/iter -/iter -H -sumRk_compose1.
  Qed.
  
  Lemma sumRk_compose : forall (n1 n2: nat),
      sumRk R (n1 + n2) = (sumRk R n1) * (sumRk R n2).
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
  
  Lemma clos_rt_sumRk: forall (x y:A),  R.* (x, y) -> exists (n:nat), (sumRk R n) (x,y).
  Proof.
    move => x' y'. rewrite /clos_rt /mkset /=.
    elim =>[ x y /= H | x  | x y z H1 [n1 H2] H3 [n2 H4] ].
    exists 1;right;exists y. split. by []. by rewrite /sumRk Delta_Id.
    exists 0. by rewrite /sumRk  Delta_Id.
    by exists (addn n1 n2); rewrite sumRk_compose;exists y;split.
  Qed.

  Lemma clos_t_decomp_rt: R `|` (R * R.+) = R.+.
  Proof.
    rewrite predeqE => [[x' y']]. split.
    - move => [H1| [z [H1 H2]]].
      + by apply t_step.
      + by apply t_trans with z; [apply t_step|].
    - rewrite /clos_t /setU /mkset /=.
      elim => x y.
      + by left.
      + move => z H1 [H2|[z' [H2 H5]]] H3 [H4|[z'' [H4 H6]]].
        * by right; exists y; split.
        * by right; exists y; split.
        * by right; exists z'; split; [ | apply t_trans with y].
        * by right; exists z'; split; [ | apply t_trans with y].
  Qed.
  
  Lemma clos_t_decomp_2: R.+ `|` (R.+ * R.+) = R.+.
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
  
  Lemma clos_t_decomp_rt_r: R `|` (R.+ * R) = R.+.
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

  Lemma r_clos_rt_clos_t: R * R.* = R.+.
  Proof.
    by rewrite -DuT_eq_Tstar composeDl Delta_idem_r clos_t_decomp_rt.
  Qed.
  
  Lemma clos_rt_r_clos_t: R.* * R = R.+.
  Proof.
    by rewrite -DuT_eq_Tstar composeDr Delta_idem_l clos_t_decomp_rt_r.
  Qed.

End Clos_refl_trans_facts.

Section Clos_refl_trans_facts1.
  
  Lemma L1 : forall (A: Type) (R S: relation A),
      R.* * S.* = ('Δ `|` R.+) * ('Δ `|` S.+ ).
  Proof.
    by move => A R S; rewrite !DuT_eq_Tstar.
  Qed.
  
  Lemma L2 : forall (A: Type) (R S: relation A),
      R.* * S.* = 'Δ `|` R.+ `|` S.+ `|` R.+ * S.+. 
  Proof.
    move => A R S.
    by rewrite -!DuT_eq_Tstar
         !composeDl !composeDr DeltaE_inv Delta_idem_l Delta_idem_r -unionA.
  Qed.

  Lemma compose_rt_rt : forall (A: Type) (R: relation A),  R.* * R.* = R.*. 
  Proof.
    by move => A R;rewrite L2 unionA clos_t_decomp_2 unionA union_RR DuT_eq_Tstar.
  Qed.
  
End Clos_refl_trans_facts1.

Section Clos_Fset.

  Lemma E30 : forall (A:Type) (R: relation A) (X Y: set A),
      'Δ#X `|` R#Y = 'Δ#X `|` (Δ_(X.^c)*R)#Y.
  Proof.
    by move => A R X Y; rewrite Fset_D Union_Setminus -Fset_DCE Fset_comp.
  Qed.
  
  Lemma Fset_n : forall (A:Type) (R: relation A) (Y:set A) (n : nat),
      (sumRk R n)#Y `<=` (Δ_(Y.^c) * R).*#Y.
  Proof.
    move => A R Y n x H.
    have H0: forall (n':nat), (sumRk R n') # Y = (sumRk ( Δ_(Y.^c) * R) n') # Y
        by elim => [ | n' H'];[rewrite /sumRk 
                             |rewrite -!Fset_union_rel -!/sumRk -!Fset_comp 
                              -[in RHS]H' !Fset_comp -[in RHS]E30].
    
    have H1: ((sumRk R n) # Y) `<=` ((sumRk (Δ_(Y.^c) * R) n) # Y)
      by move => x' H1;rewrite -H0.
    have H2: ((sumRk (Δ_(Y.^c) * R) n) # Y) `<=` ((Δ_(Y.^c) * R).* # Y)
      by move => H2; apply: Fset_inc; apply: sumRk_inc_clos_refl_trans.
    by apply: H2; apply: H1.
  Qed.

  Lemma Fset_rt: forall (A: Type) (R: relation A) (Y:set A),
      (Δ_(Y.^c)*R).*#Y = R.*#Y.
  Proof.
    move => A R Y.
    have H0: (Δ_(Y.^c) * R).* `<=`  (R.* )
      by apply: clos_refl_trans_inc; move => [x y] [z [ [_ /= ->] H2]]. 
    have E29_1:  (Δ_(Y.^c)* R).*#Y `<=` R.*#Y
      by apply Fset_inc.
    have E29_2:  R.*#Y `<=` (Δ_(Y.^c)*R).*#Y.
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

  Definition Restrict (A:Type) (R: relation A) (X: set A) := 
    [ set x | x.1 \in X /\ x.2 \in X /\ R x]%classic.
  
  Lemma Rest (A:Type) (X: set A) (R: relation A) : (Restrict R X) = Δ_(X) * R * Δ_(X).
  Proof.
    rewrite predeqE => [[x y]].
    split => [[/= H1 [H2 H3]] | [z [[t [[/= H1 H'1] H2]] [/= H3 H'3]]]].
    by (exists y;split;[ exists x;split | ]).
    by split; [ | split; [rewrite -H'3 | rewrite H'1 -H'3]].
  Qed.

End Relation_restricted.

