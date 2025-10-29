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
(* relations defined as set (T * T)                                           *)
(* thus using properties from classical_sets.v                                *)
(* R2rel can be used to coerce a relation T to rel T                          *) 
(******************************************************************************)

(* XXXX the .-1 notation is not good as it clashes with .-1 of nat *)

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

Reserved Notation "R .+" (at level 1, left associativity, format "R .+").
(* Reserved Notation "R .-1" (at level 2, left associativity, format "R .-1").  *)

Reserved Notation "R .*" (at level 1, left associativity, format "R .*").

Reserved Notation "R `;` U" (at level 51, left associativity, format "R `;` U").

(* begin snippet relation:: no-out *)  
Definition relation (T: Type) := set (T * T).
(* end snippet relation *)  

(* possible Corecion of relation T to rel T *)
Definition R2rel (T: Type) (R: relation T) : rel T := (fun x y => ((x,y) \in R)).
Global Coercion R2rel : relation >-> rel.

Section Relation_Definition.
  
  Variables (T : Type). 

  (** We could use reflexive, transitive, ... from  Coq.ssr.ssrbool 
      using the coercion to rel T *)
  
  Definition reflexive (R : relation T) : Prop := forall x:T, R (x,x).
  Definition transitive (R : relation T): Prop := forall x y z:T, R (x,y) -> R (y,z) -> R (x,z).
  Definition symmetric (R : relation T): Prop := forall x y:T, R (x,y) -> R (y,x).
  Definition antisymmetric (R : relation T): Prop := forall x y:T, R (x,y) -> R (y,x) -> x = y.
  Definition asymmetric (R : relation T): Prop := forall x y:T, R (x,y) -> ~ R (y,x).
  Definition irreflexive (R : relation T) : Prop := forall x:T, ~ R (x,x).
  
  Record preorder (R : relation T) : Prop :=
    { preord_refl: reflexive R; preord_trans: transitive R}.

  (** * partial order *)
  Record porder (R : relation T) : Prop :=
    { poset_refl: reflexive R; poset_antisym: antisymmetric R;poset_trans : transitive R}.
  
  (** * strict partial order *)
  Record sporder (R : relation T) : Prop := 
    { sorder_irefl: irreflexive R; sorder_transitive: transitive R}.

  (** * equivalence relation *)
  Record equivalence (R : relation T) : Prop :=
    { equiv_refl : reflexive R; equiv_trans : transitive R; equiv_sym : symmetric R}.

  Lemma irP (R : relation T): irreflexive R -> (asymmetric R <-> antisymmetric R).
  Proof. move => Ir. split => [Asy x y /Asy ? ? //| Atsy x y /[dup] H0 H1 H2]. 
         by move: (Atsy x y H1 H2) H0 => ->;apply: Ir.
  Qed.

  (* sorder is also asymmetric *)
  Lemma sporder_asym (R : relation T): transitive R -> irreflexive R -> asymmetric R.
  Proof. by move => Tr Ir x y H1 H2; pose proof (Ir x (Tr x y x H1 H2)). Qed.

  (* sorder is also antisymmetric *)
  Lemma sporder_antisym (R : relation T): transitive R -> irreflexive R -> antisymmetric R.
  Proof. by move => Tr Ir x y H1 H2; pose proof (Ir x (Tr x y x H1 H2)). Qed.
  
End Relation_Definition.


Section Sets_facts.
  
  Variables (T:Type).
  
  (* should be replaced by in_setE *)
  Lemma inP: forall (x:T) (X: set T), x \in X <-> X x. 
  Proof. by move => x X; rewrite in_setE. Qed.
  
  Lemma notempty_exists: forall (X: set T), (exists z, z \in X) <-> (X != set0).
  Proof.
    by move => X;rewrite set0P;split;[move => [z /set_mem ?]|move => [z /mem_set ?]];exists z.
  Qed.
    
  (* begin snippet Sone:: no-out *)  
  Lemma empty_notexists: forall (X: set T), X = set0 <-> ~ (exists z, z \in X).
  Proof.
    move => X;split;first by move => -> [z /inP ?]. 
    move => H1; rewrite predeqE => x.
    by split => [/inP H2 | H2];[have H3: exists (z:T), z \in X by (exists x) |].
  Qed.
  (* end snippet Sone *) 
  
  (* begin snippet Stwo:: no-out *)  
  Lemma empty_iff: forall (X: set T), ~ (X != set0) <-> X = set0.
  (* end snippet Stwo *)  
  Proof.
    by move => X;rewrite -notempty_exists empty_notexists.
  Qed.

  Lemma notempty_iff: forall (X: set T), ~ (X = set0) <-> X != set0.
  Proof.
    move => X;split.
    by move => /empty_notexists /contrapT /notempty_exists H1. 
    by move => /notempty_exists H1 /empty_notexists H2.
  Qed.
  
  Lemma W_part : forall (X Y Z: set T),
      (Y `<=` X) /\ (Z= X `\` Y) -> Y `&` Z = set0.
  Proof.
    move => X Y Z [? H2];rewrite empty_notexists H2.
    by move => [z /inP [? [_ ?]]].
  Qed.
  
End Sets_facts. 

Section Union_facts.
  (** * union of relations using set unions *)
  Variables (T: Type) (R S U: relation T).
  
  Lemma union_inc_b : S `<=` U -> R `<=` U -> (S `|` R) `<=` U.
  Proof.
    by move => H1 H2;(have <- : U `|` R = U by apply setUidPl);apply setSU.
  Qed.
  
End Union_facts.

Section Inverse.
  
  Variables (T: Type) (R S: relation T).
  
  (* begin snippet Sthree *)  
  Definition inverse (T: Type) (R: relation T): relation T := [set x | R (x.2,x.1)].
  (* end snippet Sthree *)  

  Local Notation "R .-1" := (@inverse _ R) : classical_set_scope.
  
  Lemma inverse_inverse (U : relation T):  U.-1.-1 = U.
  Proof. by rewrite /inverse /mkset predeqE /=;tauto. Qed.
  
  Lemma inverse_sym : R.-1 = R <-> symmetric R.
  Proof.
    by rewrite predeqE /symmetric;split => [  H0 x y /H0 // | H1 [x y]];split; apply H1.
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
  Proof. by move => H x [z [? ?]];exists z;split;[|apply: H]. Qed.
  
  Lemma composer_inc : S `<=` U ->(S `;` R ) `<=` (U `;` R). 
  Proof. by move => H x [z [? ?]];exists z;split;[apply: H|]. Qed.
  
  Lemma inverse_compose : (R `;` S).-1 = S.-1 `;` R.-1.
  Proof. by rewrite predeqE => x;split;move => [z [? ?]];exists z;split. Qed.

  Lemma RRm_sym:  symmetric (R `;` R.-1).
  Proof. by move => x y [z [H1 H2]];exists z;split;[apply: H2|apply: H1]. Qed.
  
  Lemma RRm_inverse : (R `;` R.-1).-1 = R `;` R.-1.
  Proof. by apply/inverse_sym/RRm_sym. Qed. 
  
End Compose_facts.

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
  
  Lemma DeltaE_inc Z: X `<=` Z -> Δ_(X) `<=` Δ_(Z).
  Proof.
    rewrite /symmetric /DeltaE /mkset /subset /=.
    by move =>  H [x y] [H1 <-];split;[apply H |].
  Qed.

  Lemma DeltaEsub: Δ_(X) `<=` 'Δ.
  Proof. by apply: (@DeltaE_inc setT). Qed.
  
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
  
  (* XXXXXX identique a Lemma DeltaEsub: Δ_(X) `<=` 'Δ. *)
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

Section Iter_facts. 

  Variables (T:Type) (R S: relation T).

  Fixpoint iter (T:Type) (R: relation T) (n : nat) : relation T :=
    match n with 
    | 0 => 'Δ
    | n'.+1 => (iter R n') `;` R
    end.
  
  Local Notation "R ^( n )" :=
    (@iter _ R n) 
      (at level 2, left associativity, format "R ^( n )").

  Lemma iter1_id (U: relation T): U^(1) = U.
  Proof. by rewrite /iter Delta_idem_l. Qed.

  Lemma iter_compose (U: relation T): 
    forall (n1 n2: nat), U^(addn n1 n2) = U^(n1) `;` U^(n2).
  Proof.
    move => n1 n2;elim: n2 n1 => [ n1  | n1 H n0];
                               first by rewrite addn0 Delta_idem_r.
    by rewrite [addn n0 n1.+1]addnS /iter -/iter -[RHS]composeA H.
  Qed.
  
  Lemma iter_delta (n: nat): (DeltaE (@setT T))^(n) = 'Δ.
  Proof. 
    elim: n. exact. move => n Hr.
    by rewrite -addn1 (iter_compose 'Δ n 1) Hr iter1_id Delta_idem_l.
  Qed.

  Lemma iter_include (n:nat): R `<=` S -> R^(n) `<=` S^(n).
  Proof.
    elim: n => [_ //| n Hr H1]. 
    move: (iter_compose R n 1) (iter_compose S n 1) => H2 H3.
    have H4: R^(n)`;`R^(1) `<=` S^(n)`;`R^(1) by apply: composer_inc;apply:Hr.
    have H5: S^(n)`;`R^(1) `<=` S^(n)`;`S^(1) by apply: compose_inc;rewrite 2!iter1_id.
    rewrite -addn1 H2 H3.
    by apply: subset_trans H4 H5.
  Qed.
  
  Lemma iter_subset: transitive S ->  R `<=` S -> forall n, n > 0 -> R^(n) `<=` S.
  Proof.
    move => Ht H1;elim => [//| n Hr H2 [x y]].
    have H2': R^(1) `<=` S by rewrite iter1_id.
    case H3: (n == 0);first by  move: H3 => /eqP -> => /H2'.
    move: H3 => /neq0_lt0n /Hr H3. 
    rewrite -addn1 (iter_compose R n 1) => -[z [/H3 H4 /H2' H5]].
    by apply: (Ht x z y H4 H5). 
  Qed. 
  
  Lemma inverse_iter (n: nat) : R^(n).-1 = (R.-1)^(n).
  Proof.
    elim: n =>[| n H1];first  by rewrite /iter DeltaE_inverse.
    move: (@iter_compose R n 1) (iter_compose R.-1 1 n)=> H2. 
    rewrite iter1_id => H3.
    by rewrite -addn1 H2 inverse_compose H1 iter1_id -H3 addnC. 
  Qed.
  
  Lemma iter_C (n:nat): R^(n)`;`R = R `;` R^(n).
  Proof.
    move: (iter_compose R n 1) (iter_compose R 1 n).
    by rewrite  iter1_id addnC => <- <-.
  Qed.
  
  Lemma iter_sym (n:nat): symmetric R -> symmetric R^(n).
  Proof.
    move => Hs.
    elim: n => [H1 | n Hr x y];first by apply: DeltaE_sym.
    rewrite -addn1;move: (iter_compose R n 1) => H1.  
    rewrite {1}H1 iter1_id /= => -[z /=[/Hr H2 /Hs H3]].
    by rewrite addnC (iter_compose R 1 n) iter1_id;(exists z).
  Qed.

  Lemma iterD_sub (n: nat): ('Δ `|` R)^(n) `<=` ('Δ `|` R)^(n.+1).
  Proof.
    rewrite -{1}addn1 (iter_compose ('Δ `|` R) n 1) iter1_id composeDl Delta_idem_r.
    by apply: subsetUl.
  Qed.
  
  Lemma iterDr X: forall (n: nat), 0 < n -> (R`;`Δ_(X))^(n) = (R`;`Δ_(X))^(n)`;`Δ_(X).
  Proof.
    have H1: (R`;`Δ_(X))^(1) = (R`;`Δ_(X))^(1) `;`Δ_(X)
      by rewrite iter1_id composeA DeltaE_inv.
    by case => [//| n _];rewrite -addn1 (iter_compose (R`;`Δ_(X)) n 1) composeA -H1.
  Qed.
  
  Lemma iterDl X: forall (n: nat), 0 < n -> (Δ_(X)`;`R)^(n) = Δ_(X)`;`(Δ_(X)`;`R)^(n).
  Proof.
    have H1: (Δ_(X)`;`R)^(1) = Δ_(X)`;`(Δ_(X)`;`R)^(1)
      by rewrite iter1_id -composeA DeltaE_inv.
    case => [//| n _].
    by rewrite -addn1 addnC (iter_compose (Δ_(X)`;`R) 1 n) -[RHS]composeA -H1.
  Qed.
  
  Lemma bigcup_iter0: \bigcup_(i < 1) R^(i) = 'Δ. 
  Proof. 
    rewrite predeqE => -[x y];split.
    by move => [n +]; rewrite II1 => -> /Delta_Id ->.
    by move => ?; exists 0.
  Qed.
  
  Lemma bigcupC I (F : I -> relation T) (P : set I) U:
    \bigcup_(i in P) (F i `;` U) = (\bigcup_(i in P) F i) `;` U.
  Proof.
    apply/predeqP => -[x y]. split. 
    by move => [n Pn [z /= [H1 H2]]];exists z;split;[exists n|]. 
    by move => [z [[n Pn /= H1] /= H2]];exists n;[|exists z].
  Qed.

End Iter_facts. 

Notation "R ^( n )" := (@iter _ R n) 
                     (at level 2, left associativity, format "R ^( n )").


Section Clos_trans_facts.  

  Variables (T:Type) (R S: relation T).
  
  Definition Tclos (R: relation T) := \bigcup_ (n >= 1) (iter R n).
  
  Local Notation "R .+" := (Tclos R) 
                                (at level 1, left associativity, format "R .+").
  
  Lemma Tclos_r: (Tclos R) `;` S = \bigcup_ (n >= 1) ((iter R n) `;` S).
  Proof. by rewrite -bigcupC. Qed.
  
  Lemma Tclos_in: forall S, transitive S -> R `<=` S -> R.+  `<=` S.
  Proof.
    by move => S' Ht H1 [x y] [n /= H2];move: (iter_subset Ht H1 H2) => H3 /H3 ?.
  Qed.
  
  Lemma TclosT: transitive R.+.
  Proof.
    move => x y z -[n1 /= H1 ?] -[n2 /= H3 ?];exists (n1 + n2).
    by rewrite /= (addn_gt0 n1 n2);apply/orP;left. 
    by rewrite (iter_compose R n1 n2);exists y.
  Qed.
  
  Lemma TclosS: R `<=` R.+.
  Proof.
    by move => [x y] ?;exists 1;[| rewrite iter1_id].
  Qed.
  
  (* mathematical def of closure 
     smallest [set S | transitive S] R
     is also \bigcap_(S in [set S | transitive S /\ R `<=` S]) S *)
  
  Lemma TclosE: R.+ = smallest [set S | transitive S] R. 
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [n /= H1 H2 S' [H3 H4]].
      by move: (iter_subset H3 H4) => H5;move: (H5 n H1) H2 => H6 /H6 H2.
    + move => /= H2.
      have: [set S | transitive S /\ R `<=` S] R.+
        by split;[apply: TclosT|apply: TclosS].
      by move => /H2.
  Qed.

  Lemma clos_t_iterk:
     forall (x y:T), R.+ (x,y) -> exists (n:nat), (iter R n.+1) (x,y).
  Proof.
    move => x y [n H1 ?];exists (n.-1)%N. 
    by have -> : n.-1.+1 = n by apply: ltn_predK H1. 
  Qed.
  
  Lemma iterk_inc_clos_trans: forall (n : nat), R^(n.+1) `<=` R.+.
  Proof. by move => n xy H1;exists n.+1. Qed.
  
  Lemma inverse_clos_t: R.+.-1 = R.-1.+ .
  Proof.
    rewrite predeqE => -[x y] /=;split => [[n ? ?]| [n H1]].
    by (exists n);[ exact|rewrite -inverse_iter].
    by rewrite -inverse_iter => ?;exists n.
  Qed.
  
  Lemma clos_t_sym: symmetric R -> symmetric R.+.
  Proof. by move => Hs x y [n /= H1 /(iter_sym Hs) H2];exists n. Qed.

  Lemma iter1_inc_clos_trans: R `<=` R.+.
  Proof. by move => xy H1;exists 1;[ | rewrite iter1_id]. Qed.
  
  Lemma clos_t_inc: R `<=` S -> R.+ `<=` S.+ .
  Proof. by move => H1 xy [n /= H2 H3];(exists n);[|apply: (@iter_include T R S)]. Qed.
  
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
    - have H10: exists x' y' : T, x' \in W /\ y' \in W.^c /\ R (x', y')
              by (apply H0 with y z;
                  split;[|split;rewrite in_setE in H6;[rewrite /setC in_setE|]]).
      by move: H10 => [x2 [y2 [? [? ?]]]];exists x2; exists y2.
  Qed.
  
  Lemma clos_t_sep: forall (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R.+ (x,y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x', y')).
  Proof.
    move => x y W [H1 [H2 /clos_t_iterk [n' H3]]].
    by apply clos_t_sep_n with n' x y.
  Qed.

  Lemma Delta_clos_trans_ends X: (R `;` Δ_(X)).+ =  (R `;` Δ_(X)).+ `;` Δ_(X).
  Proof.
    rewrite predeqE => -[x y]; split;last by move=> [z /= [+ [_ /= H3]]];rewrite H3.
    move=> [n Pn];rewrite (iterDr R X Pn) => -[z /= [H2 H3]].
    by (exists z);split;[exists n|].
  Qed.

  Lemma Delta_clos_trans_starts X: (Δ_(X) `;` R).+ = Δ_(X) `;` (Δ_(X) `;` R).+.
  Proof.
    rewrite predeqE => -[x y]; split;last by move=> [z /= [[_ /= H3]]];rewrite H3.
    move=> [n Pn];rewrite (iterDl R X Pn) => -[z /= [H2 H3]].
    by (exists z);split;[|exists n].
  Qed.
  
End Clos_trans_facts. 

Notation "R .+" :=
  (Tclos R) (at level 1, left associativity, format "R .+").

Section Clos_trans_facts_1.
  
  Variables (T: Type) (R S Z U: relation T).

  Local Lemma clos_trans_inc: forall (V W: relation T), 
      (forall (n:nat), Z `;` (V^(n.+1)) `;` U = Z `;` (W^(n.+1)) `;` U) 
      -> Z `;` V.+ `;` U `<=` Z `;` W.+ `;` U.
  Proof.
    move => V W H0 [x y] [z [[t /=[H1 [n H2 H3]]] /=H4]].
    move: H0 => /(_ (n.-1)%N);(have ->: n.-1.+1 = n by apply: ltn_predK H2);move => H0.
    have [z' [[t' /=[H1' H2']] H4']]: (Z`;`W^(n)`;`U) (x,y) by rewrite -H0;exists z;split;[exists t|].
    by exists z';split;[exists t';split;[|exists n]|].
  Qed.
  
  Lemma clos_trans_eq:
    (forall (n:nat), Z `;` (R^(n.+1)) `;` U = Z `;` (S^(n.+1)) `;` U)
    -> Z `;` R.+ `;` U = Z `;` S.+ `;` U.
  Proof.
    by move => H;rewrite predeqE;split;[apply: clos_trans_inc | apply: clos_trans_inc].
  Qed.
  
  Lemma clos_t_composer: (R `;` R.+) `<=` R.+.
  Proof. 
    move => [x y] [z [/= H1 [n /= H2 H3]]]. 
    by exists (n.+1);[exact | rewrite -addn1 addnC (iter_compose R 1 n) iter1_id;exists z].
  Qed.
  
  Lemma clos_t_composel: (R.+ `;` R) `<=` R.+.
  Proof. 
    move => [x y] [z [[n /= H2 H3] /= H1]].
    by exists (n.+1);[exact | rewrite -addn1 (iter_compose R n 1) iter1_id;exists z].
  Qed.
  
  Lemma clos_t_decomp_rt: R `|` (R `;` R.+) = R.+ .
  Proof.
    rewrite predeqE => -[x y];split;
                      first by move => [? | ?];[apply: TclosS | apply: clos_t_composer].
    + move => [n /= H2].
      case H1: (1 == n);first by move: H1 => /eqP <-;rewrite iter1_id => H3;left.
      have H3': n.-1.+1 = n by apply: ltn_predK H2. 
      have H5: 1 < n by move:H2;rewrite leq_eqVlt H1 orFb.
      have H6: (0 < n.-1)%N by rewrite -(ltn_add2r 1) addn1 [n.-1 + 1]addn1 H3'.
      rewrite -H3' -addn1 addnC (iter_compose R 1 (n.-1)%N) iter1_id => -[z [H7 H8]].
      by right;exists z;split;[| exists (n.-1)%N].
  Qed.
  
  Lemma clos_tI:  (R.+ `;` R.+) `<=` R.+.
  Proof. 
    move => [x y] [z [[n1 /= H1 H1'] [n2 /= H2 H2']]].
    have H3: R^(n1 + n2) (x, y) by move: (iter_compose R n1 n2) => ->;(exists z).
    have H6: 0 < n1 + n2 by rewrite addn_gt0 H1 H2.
    by exists (n1 + n2).
  Qed.
  
  Lemma clos_t_decomp_2: R.+ `|` (R.+ `;` R.+) = R.+.
  Proof. by rewrite predeqE => -[x y];split => [[? //| /clos_tI ?//] | ?];by left. Qed.
  
  Lemma clos_t_decomp_rt_r: R `|` (R.+ `;` R) = R.+.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [H1| [z /= [[n H1 H2] H3]]]; first by apply iter1_inc_clos_trans.
      by (exists n.+1);[|rewrite -addn1 (iter_compose R n 1) iter1_id; exists z].
    + move => [n /= H1].
      case H2: (1 == n);first by move: H2 => /eqP <-; rewrite iter1_id => H3;left.
      have H3': n.-1.+1 = n by apply: ltn_predK H1. 
      rewrite -H3' -addn1 (iter_compose R (n.-1)%N 1)  iter1_id => -[z /= [H3 H4]].
      have H5: 1 < n by move:H1;rewrite leq_eqVlt H2 orFb.
      have H6: (0 < n.-1)%N by rewrite -(ltn_add2r 1) addn1 [n.-1 + 1]addn1 H3'.
      by right;exists z;split;[exists (n.-1)%N |].
  Qed.

End Clos_trans_facts_1.

Section Clos_refl_trans_facts.

  Variables (T: Type) (R S: relation T) (X Y: set T).
  
  Definition RTclos (R: relation T) := \bigcup_ n (iter R n).

  Local Notation "R .*" := (RTclos R) 
                             (at level 1, left associativity, format "R .*").
  
  (* A proof with bigcup *)
  Lemma RTclosE U: U.* = 'Δ `|` U.+.
  Proof. 
    by rewrite /RTclos (bigcup_splitn 1) 
      -(@bigcup_mkord (T*T) 1 (fun n => U^(n))) bigcup_iter0 (@bigcup_addn (T*T)).
  Qed.

  Lemma RTclos_dec U: U.* = 'Δ `|` U.+.
  Proof.
    rewrite predeqE => -[x y].
    split;last by move => [/Delta_Id -> | [n /= H1 H2]];[exists 0|exists n].
    move => [n _ ].
    case H2: (n == 0);first by move: H2 => /eqP -> /Delta_Id ->;left.
    by move: H2 => /neq0_lt0n H2 H3;right;(exists n). 
  Qed.
  
  Lemma RTclos_in: forall S, transitive S -> reflexive S -> R `<=` S -> R.*  `<=` S.
  Proof.
    move => S' Ht Hr H1 [x y] [n _]. 
    case H2: (n == 0);first by move: H2 => /eqP -> /Delta_Id ->.
    by move: H2 => /neq0_lt0n H2;move: (iter_subset Ht H1 H2) => H3 /H3 ?.
  Qed.
  
  Lemma RTclosT: transitive R.*.
  Proof.
    rewrite RTclos_dec.
    move => x y z [/Delta_Id -> //|[n1 /= H1 H2]]. 
    move => [/Delta_Id <- // | [n2 /= H3 H4]].
    by right;(exists n1).
    right. 
    have H5: R^(n1 + n2) (x,z) by rewrite iter_compose;exists y.
    have H6: 0 < n1 + n2 by rewrite addn_gt0 H1 H3.
    by exists (n1 + n2).
  Qed.
  
  Lemma RTclosR: reflexive R.*.
  Proof. by rewrite RTclos_dec; move => x; left. Qed.
  
  Lemma RTclosS: R `<=` R.*.
  Proof. by rewrite RTclos_dec;move => [x y] ?;right;exists 1;[|rewrite iter1_id]. Qed.
  
  (* mathematical def of closure 
     smallest [set S | transitive S] R
     is also \bigcap_(S in [set S | transitive S /\ R `<=` S]) S *)
  
  Lemma RTclosIff: R.* = smallest [set S | reflexive S /\ transitive S] R. 
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [n /= H1 H2 S' [[H3 H3'] H4]].
      case H5: (n == 0);first by move: H5 H2 => /eqP -> /Delta_Id ->.
      move: H5 => /neq0_lt0n H5.
      by move: (iter_subset H3' H4 H5) H2 => H6 /H6 H2. 
    + move => /= H2.
      have: [set S | (reflexive S /\ transitive S) /\ R `<=` S] R.*
        by split;[split;[apply: RTclosR|apply: RTclosT]|apply: RTclosS].
      by move => /H2.
  Qed.
  
  Lemma inverse_star : R.*.-1 = R.-1.* .
  Proof.
    (* XXX H1 could be in inverse *)
    have H1: 'Δ.-1 = 'Δ by move => T';rewrite predeqE => -[x y];split => /Delta_Id /= ->. 
    by rewrite 2!RTclos_dec inverse_union inverse_clos_t H1.
  Qed.
  
  Lemma clos_refl_trans_containsD: Δ_(X) `<=` R.* .
  Proof.
    have H1:  'Δ `<=` R.* by rewrite RTclos_dec;apply: subsetUl.
    by apply subset_trans with 'Δ;[apply: @DeltaEsub|].
  Qed.
  
  Lemma clos_t_clos_rt: R.+ `<=` R.*.
  Proof. by rewrite RTclos_dec;apply: subsetUr. Qed.
  
  Lemma clos_refl_trans_inc: R `<=` S -> R.* `<=` S.*.
  Proof. by move => H1;rewrite 2!RTclos_dec;apply/setUS/clos_t_inc. Qed.
  
  Lemma DuT_eq_Tstar:  'Δ `|` R.+ = R.*.  
  Proof. by rewrite RTclos_dec. Qed.
  
  Lemma r_clos_rt_clos_t: R `;` R.* = R.+.
  Proof.
    by rewrite -DuT_eq_Tstar composeDl Delta_idem_r clos_t_decomp_rt.
  Qed.
  
  Lemma clos_rt_r_clos_t: R.* `;` R = R.+.
  Proof.
    by rewrite -DuT_eq_Tstar composeDr Delta_idem_l clos_t_decomp_rt_r.
  Qed.
    
  Section clos_rt.
    
    (* sumRk R n = 'Δ `|` R `|` R^(2) `|` R^(n) = ('Δ `|` R)^(n). *)
    Fixpoint sumRk (T:Type) (R: relation T) (n : nat) : relation T :=
      match n with 
      | 0 => 'Δ
      | n'.+1 => 'Δ `|` (R `;` (sumRk R n'))
      end.
    
    Lemma sumRk_0 : sumRk R 0 = 'Δ.
    Proof. by rewrite predeqE => -[x y];split => [/Delta_Id -> |]. Qed.
    
    Lemma sumRk_1 : sumRk R 1 = 'Δ `|` R. 
    Proof. by rewrite /sumRk Delta_idem_r. Qed.
    
    Lemma sumRk_kp1_l : forall (n: nat), sumRk R (n.+1) = 'Δ `|`  (R `;` (sumRk R n)).
    Proof. by move => n. Qed.
    
    Local Lemma Delta_inc_sumRk :  forall  (n: nat),   'Δ `<=` (sumRk R n).
    Proof. by elim => [| n H];[rewrite sumRk_0 | rewrite sumRk_kp1_l;apply: subsetUl]. Qed.
    
    Local Lemma sumRk_inc_sumRkp1 : forall (n: nat), (sumRk R n)  `<=` (sumRk R (n.+1)).
    Proof.
      elim => [| n H]; first by rewrite sumRk_0 sumRk_1; apply subsetUl.
      by rewrite 2!sumRk_kp1_l;apply/setUS/compose_inc.
    Qed.
    
    Local Lemma RsumRk_inc_sumRkp1 :  forall (n: nat), R `;` (sumRk R n)  `<=` (sumRk R (n.+1)).
    Proof. 
      elim => [| n H1];first by rewrite sumRk_0 sumRk_1 Delta_idem_r; apply/subsetUr.
      by rewrite 2!sumRk_kp1_l;apply/subsetUr.
    Qed.
    
    Local Lemma sumRk_composel (n: nat): sumRk R (n.+1) =('Δ `|` R) `;` (sumRk R n). 
    Proof.
      rewrite [RHS]composeDr Delta_idem_l eqEsubset.
      split; first by rewrite sumRk_kp1_l;apply/setSU/Delta_inc_sumRk.
      by apply: union_inc_b;[apply: sumRk_inc_sumRkp1|apply: RsumRk_inc_sumRkp1].
    Qed.
    
    Local Lemma sumRk_compose2 : forall (n: nat),  sumRk R n = ('Δ `|` R)^(n).
    Proof.
      elim => [  | n H];first  by rewrite /sumRk /iter.
      by rewrite -addn1 addnC (iter_compose ('Δ `|` R) 1 n) iter1_id -H;apply/sumRk_composel.
    Qed.
    
    Local Lemma sumRk_compose' (n1 n2: nat): sumRk R (n1 + n2) = (sumRk R n1) `;` (sumRk R n2).
    Proof.  by rewrite 3!sumRk_compose2; apply: iter_compose. Qed.
    
    Local Lemma sumRk_inc_clos_refl_trans: forall (n : nat), (sumRk R n) `<=` R.*.
    Proof.
      elim => [|n Hr];first by rewrite sumRk_0 => [[x y] H1];exists 0.
      rewrite sumRk_composel composeDr Delta_idem_l.
      have H2: R `;` R.* `<=` R.* by apply: (subset_trans _ clos_t_clos_rt);rewrite r_clos_rt_clos_t.
      have H3: R`;`sumRk R n `<=` R `;` R.* by apply: compose_inc. 
      by apply: (union_inc_b Hr);apply: (subset_trans H3 H2).
    Qed.
    
    Local Lemma clos_rt_sumRk (x y:T):  R.* (x, y) -> exists (n:nat), (sumRk R n) (x,y).
    Proof.
      have H3: R `<=` 'Δ `|` R by apply: subsetUr.
      rewrite RTclos_dec => -[/Delta_Id -> | [n H1 H2]];first by (exists 0).
      by exists n; rewrite sumRk_compose2;apply: (iter_include H3).
    Qed.
    
    Lemma clos_rt_D_clos_t: R.* = ('Δ `|` R).+.
    Proof.
      rewrite predeqE => -[x y];split.
      + move => /clos_rt_sumRk [n +];rewrite sumRk_compose2.
        case H1: (n == 0).
      + move: H1 => /eqP ->; rewrite /= => H1.
        have H2: ('Δ `|` R) (x, y) by rewrite /setU;left.
        by apply: iter1_inc_clos_trans. 
      + move: H1 => /neq0_lt0n/prednK H1.
        pose proof (@iterk_inc_clos_trans T ('Δ `|` R) (n.-1)%N) as H2. 
        by move: H2; rewrite H1 => H2 /H2 H3.
      + move => /(@clos_t_iterk T ('Δ `|` R) x y) [n H1].
        by move: H1; rewrite -sumRk_compose2 => /sumRk_inc_clos_refl_trans.
    Qed.

  End clos_rt.
  
  Section clos_rt.

    Variables (U: relation T).
    Hypothesis Hi : U `<=` 'Δ.
    Hypothesis Hc1: U `;`  R = R. 
    Hypothesis Hc2: R `;`  U = R. 
    Hypothesis Hn: forall n,  U^(n) = U.
    
    (* sumRk R n = 'Δ `|` R `|` R^(2) `|` R^(n) = ('Δ `|` R)^(n). *)
    Fixpoint sumRk' (T:Type) (R S: relation T) (n : nat) : relation T :=
      match n with 
      | 0 => S
      | n'.+1 => S `|` (R `;` (sumRk' R S n'))
      end.
    
    Lemma sumRk_0' : sumRk' R U 0 = U.
    Proof. by rewrite predeqE => -[x y];split. Qed.
    
    Lemma sumRk_1' : sumRk' R U 1 = U `|` R. 
    Proof. by rewrite /sumRk' Hc2. Qed.
    
    Lemma sumRk_kp1_l' : forall (n: nat), sumRk' R U (n.+1) = U `|`  (R `;` (sumRk' R U n)).
    Proof. by move => n. Qed.
    
    Local Lemma Delta_inc_sumRk' :  forall  (n: nat), U `<=` (sumRk' R U n).
    Proof. by elim => [| n H];[rewrite sumRk_0' | rewrite sumRk_kp1_l';apply: subsetUl]. Qed.
    
    Local Lemma sumRk_inc_sumRkp1' : forall (n: nat), (sumRk' R U n)  `<=` (sumRk' R U (n.+1)).
    Proof.
      elim => [| n H]; first by rewrite sumRk_0' sumRk_1'; apply subsetUl.
      by rewrite 2!sumRk_kp1_l';apply/setUS/compose_inc.
    Qed.

    Local Lemma RsumRk_inc_sumRkp1' :  forall (n: nat), R `;` (sumRk' R U n)  `<=` (sumRk' R U (n.+1)).
    Proof. 
      elim => [| n H1];first by rewrite sumRk_0' sumRk_1' Hc2; apply/subsetUr.
      by rewrite 2!sumRk_kp1_l';apply/subsetUr.
    Qed.

    Lemma SRsumk': forall (n: nat), U`;`sumRk' R U n = sumRk' R U n.
    Proof.
      move: (Hn 2);rewrite /iter Delta_idem_l => H1.
      elim => [| n Hr];first by rewrite sumRk_0' H1.  
      by rewrite sumRk_kp1_l' composeDl H1 -composeA Hc1.
    Qed.
    
    Local Lemma sumRk_composel' (n: nat): sumRk' R U (n.+1) =(U `|` R) `;` (sumRk' R U n). 
    Proof.
      rewrite [RHS]composeDr SRsumk' eqEsubset.
      split; first by rewrite sumRk_kp1_l';apply/setSU/Delta_inc_sumRk'.
      by apply: union_inc_b;[apply: sumRk_inc_sumRkp1'|apply: RsumRk_inc_sumRkp1'].
    Qed.
      
    Local Lemma sumRk_compose2' : forall (n: nat), sumRk' R U n.+1 = (U `|` R)^(n.+1).
    Proof.
      elim => [// | n Hr];first by rewrite sumRk_1' iter1_id.
      rewrite sumRk_composel' Hr.
      by move:(iter_compose (U `|` R) 1 n.+1);rewrite iter1_id addnC addn1 => ->.
    Qed.
    (* 
    Local Lemma sumRk_compose' (n1 n2: nat): sumRk R U (n1 + n2) = (sumRk R U n1) `;` (sumRk R U n2).
    Proof.  by rewrite 3!sumRk_compose2; apply: iter_compose. Qed.
    *)
    
    Local Lemma sumRk_inc_clos_refl_trans': forall (n : nat), (sumRk' R U n) `<=` R.*.
    Proof.
      elim => [|n Hr];first by rewrite sumRk_0' => [[x y] H1];exists 0;[ |apply: Hi].
      rewrite sumRk_composel' composeDr SRsumk'. 
      have H2: R `;` R.* `<=` R.* by apply: (subset_trans _ clos_t_clos_rt);rewrite r_clos_rt_clos_t.
      have H3: R`;`sumRk' R U n `<=` R `;` R.* by apply: compose_inc. 
      by apply: (union_inc_b Hr);apply: (subset_trans H3 H2).
    Qed.
    
    Local Lemma clos_rt_sumRk' (x y:T): 
      R.* (x, y) -> 'Δ (x,y) \/ exists (n:nat), (sumRk' R U n) (x,y).
    Proof.
      have H3: R `<=` U `|` R by apply: subsetUr.
      rewrite RTclos_dec => -[/Delta_Id -> | [n H1 H2]];first by left. 
      have H5 : n.-1.+1 = n by apply: ltn_predK H1. 
      by right;(exists n);rewrite -H5 sumRk_compose2' H5;apply: (iter_include H3).
    Qed.
  
  End clos_rt.

  Lemma Delta_n: forall (n: nat), ('Δ)^(n) = ('Δ : relation T). 
  Proof.
    elim => [| n Hr];first  by rewrite /iter.
    by rewrite -addn1 (iter_compose 'Δ n 1) Hr iter1_id Delta_idem_l.
  Qed.
    
  Lemma clos_rt_D_clos_t': R.* = ('Δ `|` R).+.
  Proof.
    move: (@clos_rt_sumRk' ('Δ) (Delta_idem_l R) (Delta_idem_r R) Delta_n) => H0.
    rewrite predeqE => -[x y];split.
    + move => /H0 [? | [n +]];first by (exists 1);[| rewrite iter1_id;left].
      case H1: (n == 0).
      ++ move: H1 => /eqP ->; rewrite /= => H1.
         have H2: ('Δ `|` R) (x, y) by rewrite /setU;left.
         by apply: iter1_inc_clos_trans. 
      ++ move: (H1) => /neq0_lt0n/prednK H1'.
         move: (@sumRk_compose2' ('Δ) 
                  (Delta_idem_l R) (Delta_idem_r R) Delta_n (n.-1)%N) =>H2. 
         pose proof (@iterk_inc_clos_trans T ('Δ `|` R) (n.-1)%N) as H3. 
         by rewrite -H1' H2 => /H3 H4.
    + move => /(@clos_t_iterk T ('Δ `|` R) x y) [n H1].
      have H2: 'Δ `<=` ('Δ: relation T). by [].
      move: (@sumRk_compose2' ('Δ) 
               (Delta_idem_l R) (Delta_idem_r R) Delta_n n) =>H3. 
      move: (@sumRk_inc_clos_refl_trans' ('Δ) H2
               (Delta_idem_l R) (Delta_idem_r R) Delta_n (n.+1)) => H4.
      by move: H1;rewrite -H3 => /H4 H1.
  Qed.

End Clos_refl_trans_facts.

Notation "R .*" := (RTclos R) 
                     (at level 1, left associativity, format "R .*").

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

Section Foresets.

  Definition Fset (T:Type) (R: relation T) (Y: set T) : set T :=
    [set x | exists (y: T), R (x,y) /\ Y y].

  Definition Aset (T:Type) (R: relation T) (Y: set T) : set T :=
    Fset R.-1 Y. 

  (* check that it coincide with usual definition *)
  Lemma AsetE  (T:Type) (R: relation T) (Y: set T):
    (Aset R Y) = [set x | exists (y: T), R (y,x) /\ Y y].
  Proof. by rewrite /Aset/Fset.  Qed.

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

  Lemma Fset_D :   'Δ#X = X.
  Proof.
    rewrite /Fset predeqE => x;split =>[[x' [/Delta_Id -> ?]] //| ?].
    by exists x;rewrite Delta_Id.
  Qed.

  Lemma Fset_DE Z: Δ_(Z)#X = Z `&` X.
  Proof.
    by rewrite /Fset/DeltaE predeqE /= => x;split => [[x' [[? <-] ?]] //| [? ?]];exists x.
  Qed.
  
  Lemma Fset_DCE : Δ_(Y.^c)#X = X `\` Y.
  Proof.
    rewrite /Fset/DeltaE/setC predeqE /= => x;split;first by move => [x' [[? <-] ?]].
    by move => [? ?];exists x.
  Qed.
  
  Lemma Fset_inc : R `<=` S -> R#X `<=` S#X.
  Proof.
    by move => H x [y [? ?]];by exists y;split;[apply: H |].
  Qed.
  
  Lemma Fset_inc1 : X `<=` Y -> R#X `<=` R#Y.
  Proof.
    by move => H x [y [? ?]];exists y;split;[|apply: H].
  Qed.
  
  Lemma set_inc2: forall (x: T), x \in X <->  [set x] `<=` X.
  Proof.
    move => x;split => [/set_mem ? y /= -> // |].
    by rewrite in_setE => H1; apply: H1. 
  Qed.
  
  Lemma Fset_comp : S # (R # X) = (S `;` R) # X.
  Proof.
    rewrite /Fset /compose /Fset predeqE /=.
    move => x; split => [ [z [? [y [? ?]]]] | [ y [[z [? ?]] ?]]].
    by (exists y);split;[exists z;split|]. 
    by (exists z);split;[|exists y].
  Qed.
  
  Lemma Fset_union_rel : S#X `|` R#X = (S `|` R) # X.
  Proof.
    rewrite /Fset /setU predeqE /= => x; split. 
    by move => [[y [? ?]] | [y [? ?]]];exists y;[split;[left|]|split;[right|]].
    by move => [y [[?|?] ?]];[left|right];exists y.
  Qed.
  
  Lemma Fset_union : R#(X `|` Y) = (R#X) `|` (R#Y).
  Proof.
    rewrite /Fset /setU predeqE /= => x; split. 
    by move => [z [? [?|?]]];[left|right];exists z.
    by move => [[y [? ?]]|[y [? ?]]];exists y;[split;[|left]|split;[|right]].
  Qed.

  Lemma FsetI : R#(X `&` Y) `<=` (R#X) `&` (R#Y).
  Proof.
    by move => x [y [? [? ?]]];split;exists y.
  Qed.
  
  (* Foreset in extension *)
  Lemma Fset_union_set : forall (x:T), (R#Y) x <-> exists y, Y y /\ R#_(y) x.
  Proof.
    move => x;rewrite /Fset /mkset /=.
    split => [[y [? ?]]|[y [? [z [? H3]]]]].
    by (exists y);split;[|exists y; split].
    by (exists z);split;[ |rewrite H3].
  Qed.

  Lemma Union_Setminus : X `|` Y = X `|` (Y `\` X). 
  Proof.
    rewrite /setU /setD /mkset predeqE => x.
    by split => [[?|?]|[?|[? ?]]];
            [left|pose proof lem (X x) as [?|?];[left|right]|left|right].
  Qed.
  
  Lemma Fset_intersect : forall (x y:T), (exists z, R#_(x) z /\ S#_(y) z)
                                    <-> let RmR := R.-1 `;` S in RmR (x,y). 
  Proof.
    rewrite /Fset /mkset => x y.
    split => [[z [[r [H1 H1']] [t [H2 H2']]]]|[z /= [? ?]]].
    have [-> <-]: x = r /\ t = y by [].
    by (exists z);split;[rewrite /inverse /=|].
    by (exists z);split;[exists x|exists y].
  Qed.
  
  Lemma Fset_singleton: forall (x:T), reflexive R -> R#_(x) x. 
  Proof.
    by move => x H;rewrite /Fset /mkset;exists x.
  Qed.
  
  Lemma Fset_rt_singleton: forall (x:T), R.*#_(x) x. 
  Proof.
    by move => x; exists x;split;[apply: RTclosR |].
  Qed.
  
  Lemma Fset_restrict : X `<=` Y -> R#X = (R `;` Δ_(Y))# X.
  Proof.
    rewrite /subset /Fset /compose /DeltaE /mkset predeqE /= => H x.
    split => [[y [H1 H2]]| [y [[z [H1 [_ <- ]]] H4]]];last by (exists z).
    by exists y;split;[exists y;split;[by [] |by split;[apply H|]]|]. 
  Qed.
  
  Lemma Fset_t0: forall (x y:T) (R':relation T), R' (x, y) <-> R'#_(y) x. 
  Proof.
    by move => x y R'; split => [H1 | [z [H1 /= <-]]];[exists y |].
  Qed.

  Lemma Fset_t1: forall (x y:T), R (x, y) -> R.+#_(y) x. 
  Proof.
    by move => x y H1;rewrite /Fset;exists y;split;[exists 1;[|rewrite iter1_id]|].
  Qed.
  
  Lemma Fset_t2: forall (x y:T), 
      (exists (x1:T), R (x, x1) /\ R.+#_(y) x1) -> R.+#_(y) x. 
  Proof.
    move => x y' [x1 [H1 [y [[n /=H2' H2] <-]]]];exists y;split;last by exact. 
    have H3: R^(1+n) (x,y) by rewrite (iter_compose R 1 n) iter1_id;exists x1. 
    by exists (1+n). 
  Qed.
  
  Lemma Fset_t3: forall (x y z:T), 
      R.+#_(y) x /\ R (y, z) -> R.+#_(z) x. 
  Proof.
    move => x y z [[t [[n /= H1' H1] /= <-]] H3].
    have H4: R^(n.+1) (x,z) by rewrite -addn1 (iter_compose R n 1) iter1_id;exists t. 
    by exists z;split;[exists (n.+1)|].
  Qed.
  
  Lemma Fset_t4: forall (y z:T), 
      R (y, z) -> ( R.+#_(y) `<=` R.+#_(z) ).
  Proof.
    by move => y z ? x ?;apply Fset_t3 with y.
  Qed.

  Lemma Fset_t5: forall (y z:T), 
      y \in R.+#_(z) -> (R.+#_(y) `<=` R.+#_(z) ).
  Proof.
    move => y z /inP H1 t;move:H1;rewrite -3!Fset_t0 => H1 H2.
    by apply: (TclosT H2 H1). 
  Qed.

End  Foreset_facts.

Section Foreset_topology_facts.

  Variables (T:Type) (R: relation T).

  (** * Fset and bigcup *)
  Lemma Fset_bigcup: forall (I: Type) (F : I -> set T),
      R#( \bigcup_ i (F i) ) =  \bigcup_ i (R# (F i)).
  Proof.
    move => I F;rewrite /Fset predeqE => x;split.
    by move => [y [H1 [n Pn Fny]]]; exists n;[ | exists y].
    by move => [n Pn [y [H1 H2]]];exists y;split;[|exists n].
  Qed.
  
  (** * Fset and bigcap *)
  Lemma Fset_bigcap: forall (I: Type) (F : I -> set T),
      R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)).
  Proof.
    by move => I F x [y [H1 H2]];exists y; split;[| apply: H2]. 
  Qed.
  
  Lemma Fset_stableU: forall (I: Type) (F : I -> set T),
      (forall i, R#(F i) `<=` (F i)) -> R#(\bigcup_ i (F i)) `<=` (\bigcup_ i (F i)).
  Proof.
    by move => I F H1;rewrite Fset_bigcup => x [n Pn Fn];exists n;[|apply: H1].
  Qed.

  Lemma Fset_stableI: forall (I: Type) (F : I -> set T),
      (forall i, R#(F i) `<=` (F i)) -> R#(\bigcap_ i (F i)) `<=` (\bigcap_ i (F i)).
  Proof.
    move => I F H1. 
    have H2: (\bigcap_ i R#(F i)) `<=` (\bigcap_ i (F i))
      by move => x H2 i /H2/H1 H3.
    have H3: R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)) by apply:Fset_bigcap.
    by apply: (subset_trans H3 H2).
  Qed.
  
  Lemma Fset_stableIf: forall (A B: set T),
      R#A  `<=` A -> R#B  `<=` B -> R#(A `&` B)  `<=` A   `&` B.
  Proof.
    move => A B ? ?.
    have H1: (R#A) `&`  (R#B)  `<=`  A   `&` B by apply: setISS.
    apply: (subset_trans _ H1); apply: FsetI.
  Qed.
  
  Lemma Fset_0 : R#set0 `<=` set0.
  Proof. by move => x [y [_ H1]]. Qed.

  Lemma Fset_T : R#setT `<=` setT.
  Proof.  by []. Qed.

End Foreset_topology_facts.

Section Aset_topology_facts.

  Variables (T:Type) (R: relation T).
  
  Lemma Aset_bigcup: forall (I: Type) (F : I -> set T),
      ( \bigcup_ i (F i) ):#R =  \bigcup_ i ((F i):#R).
  Proof.
    by move => I F;apply: Fset_bigcup.
  Qed.

  Lemma Aset_bigcap: forall (I: Type) (F : I -> set T),
      (\bigcap_ i (F i)):#R `<=`  \bigcap_ i ((F i):#R).
  Proof.
    by move => I F;apply: Fset_bigcap.
  Qed.

  Lemma Aset_stableU: forall (I: Type) (F : I -> set T),
      (forall i, (F i):#R `<=` (F i)) -> (\bigcup_ i (F i)):#R `<=` (\bigcup_ i (F i)).
  Proof.
    by move => I F H1;apply: Fset_stableU.
  Qed.

  Lemma Aset_stableI: forall (I: Type) (F : I -> set T),
      (forall i, (F i):#R `<=` (F i)) -> (\bigcap_ i (F i)):#R `<=` (\bigcap_ i (F i)).
  Proof.
    by move => I F H1;apply: Fset_stableI.
  Qed.
  
  Lemma Aset_stableIf: forall (A B: set T),
      A:#R `<=` A -> B:#R `<=` B -> (A `&` B):#R  `<=` A `&` B.
  Proof.
    by move => A B ? ?;apply: Fset_stableIf.
  Qed.
  
  Lemma Aset_0 : set0:#R `<=` set0.
  Proof. by move => x [y [_ H1]]. Qed.
  
  Lemma Aset_T : setT:#R `<=` setT.
  Proof. by []. Qed.

End Aset_topology_facts.

Section Closure_facts.

  Variables (T: Type) (E: relation T) (W: set T).

  Lemma Clos_x_x : forall (x:T), Clos_(x | E,W) x.
  Proof. by move => x;exists x;split;[apply RTclosR|]. Qed.
  
  Lemma Clos_Ew: forall (x y: T),  Clos_(x | E,W) y <-> (Δ_(W.^c) `;` E).* (y, x).
  Proof.
    move => x' y';split;first by move => [z [?  <-]].
    by move => ?;exists x';split.
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
    by move => X ? x ?;rewrite /Fset /mkset;exists x;split;[apply RTclosR|].
  Qed.    

  Lemma ClosU_containsl: forall (X Y: set T),
      X `<=` W -> X `<=` Clos(X `|` Y | E,W).
  Proof.
    move => X Y H0.
    have H2: X `<=` Clos( X | E,W)  by apply:Clos_contains.
    by apply: (subset_trans H2);apply: Clos_inc_l.
  Qed.

  Lemma ClosU_containsr: forall (X Y: set T),
      Y `<=` W -> Y `<=` Clos(X `|` Y | E,W).
  Proof.
    move => X Y H0.
    have H2: Y `<=` Clos( Y | E,W)  by apply:Clos_contains.
    by apply: (subset_trans H2);apply: Clos_inc_r.
  Qed.
  
End Closure_facts.



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
    by rewrite predeqE => x;split;[apply: E29_1|apply: E29_2].
  Qed.
  
End Clos_Fset.

Section Relation_restricted.
  Definition Restrict (T:Type) (R: relation T) (X: set T) := 
    [ set x | X x.1 /\ X x.2 /\ R x].
  
  Lemma Rest (T:Type) (X: set T) (R: relation T):
    (Restrict R X) = Δ_(X) `;` R `;` Δ_(X).
  Proof.
    rewrite predeqE => [[x y]].
    split => [[/= H1 [H2 H3]] | [z [[t [[/= H1 H'1] H2]] [/= H3 H'3]]]].
    by (exists y;split;[ exists x;split | ]).
    by split; [ | split; [rewrite -H'3 | rewrite H'1 -H'3]].
  Qed.

End Relation_restricted.

Section clos_rt.
  (* reflexive and transitive properties using relation equalities *)

  Lemma clos_r_iff (T: Type) (R: relation T): 
    reflexive R <-> R ='Δ  `|` R.
  Proof.
    split => [? | ->];last by move => ?;left.
    by rewrite eqEsubset;split =>[[? ?]|[? ?]];[move=> ?;right | move => [/Delta_Id -> | ?]].
  Qed.


  Lemma clos_tn_iff (T: Type) (R: relation T): 
    forall (n: nat), transitive R -> (iter R n.+1) `<=` R.
  Proof.
    move => n H1.
    elim: n.
    - by rewrite iter1_id.
    - move => n H2.
      rewrite -addn1 iter_compose iter1_id => -[x y] -[z [/H2 /= H3 /= H4]].
      by apply: (H1 x z _). 
  Qed.
  
  Lemma clos_t_iff (T: Type) (R: relation T): 
    transitive R <-> R = R.+.
  Proof.
    split => [H0 | ->];last first. 
    by move => x y z H1 H2; rewrite -clos_t_decomp_2;right;exists y. 
    rewrite eqEsubset;split.
    - apply: iter1_inc_clos_trans.
    - move => [x y] H1. 
      pose proof (clos_t_iterk H1) as [n H2].
      by apply: (clos_tn_iff H0 H2).
  Qed.

  Lemma clos_rt_iff (T: Type) (R: relation T): 
    (reflexive R /\  transitive R) <-> R = R.*.
  Proof.
    rewrite -DuT_eq_Tstar.
    split => [ [/clos_r_iff H1 /clos_t_iff H2] | H1].
    - by rewrite -H2 -H1.
    - split. 
      by rewrite H1;left;rewrite Delta_Id.
      rewrite H1 => x y z [/Delta_Id H2 |H2] [/Delta_Id H3| H3]. 
      by rewrite H2 -H3; left.
      by rewrite H2; right.
      by rewrite -H3;right.
      by right;apply: (TclosT H2 H3).
  Qed.

End clos_rt.


Section Asymmetric. 
  (** * Asymmetric part of a relation *) 
    
  Variables (T: Type) (R: relation T).
  
  Definition Asym (R: relation T): relation T := [set xy | R xy /\ ~ (R.-1 xy)].
  
  Lemma Asym_antisymmetric: antisymmetric  (Asym R).
  Proof. by move => x y [_ ?] [? _]. Qed.

  Lemma Asym_irreflexive: irreflexive (Asym R).
  Proof. by move => x [? ?]. Qed.

  Lemma Asym_asymmetric : asymmetric (Asym R). 
  Proof. by apply/(irP Asym_irreflexive)/Asym_antisymmetric. Qed.
  
  Lemma Asym_preserve_transitivity: transitive R -> transitive (Asym R).
  Proof.
    move => H0 x y z [H1 /= H1'] [H2 /= H2'];split => [ | /= H3].
    by apply: H0 H1 H2.
    by have: R (y,x) by apply: H0 H2 H3.
  Qed.
  
  Lemma AsymE: antisymmetric R /\ irreflexive R <-> Asym R = R.
  Proof.
    split; last by move => <-;split;
                          [apply: Asym_antisymmetric | apply: Asym_irreflexive].
    move => [H1 H2].
    rewrite predeqE => [[x y]]; split => [[H3 _] // | H3]. 
    split; first by [].
    by move: H3 => /[dup] H3 /H1 H3' /H3' H4; move: H3; rewrite H4 => /H2 H3.
  Qed.

  Lemma AsymI: forall (R: relation T), Asym R `<=` R.
  Proof. by move => R' [a b] [? _]. Qed.

  Lemma AsymInvol: Asym (Asym R) = (Asym R).
  Proof.
    rewrite predeqE => [[a b]];split => [[? _] //| H1]. 
    split => [// | H2];pose proof (Asym_antisymmetric H1 H2) as H3.
    by move: H1;rewrite H3;apply: Asym_irreflexive.
  Qed.
  
  Lemma AsymIncl: R.+ `;` Asym(R.+) `<=`  Asym(R.+).
  Proof.
    move: AsymI => /(_ R.+) H3 => [[x y] [z /= [H1 /[dup] H2 /H3 H4]]].
    split =>[| H5]; first by apply: (TclosT H1 H4).
    have H6: R.+ (y,z) by apply: (TclosT H5 H1).
    by move: H2 => [_ H2].
  Qed.
    
  Lemma AsymIncr: Asym(R.+) `;` R.+ `<=`  Asym(R.+).
  Proof.
    move: AsymI => /(_ R.+) H3 => [[x y] [z /= [/[dup] H2 /H3 H4 H1]]].
    split =>[| H5]; first by apply: (TclosT H4 H1).
    have H6: R.+ (z,x) by apply: (TclosT H1 H5).
    by move: H2 => [_ H2 ].
  Qed.

End Asymmetric. 

Section Independent_set.
  (** * Independence of sets with respect to a relation *)
  
  Variables (T: Type) (R: relation T).

  (* begin snippet RelIndep:: no-out *)    
  Definition RelIndep (R: relation T) (S: set T) :=
    forall (x y:T),  x \in S -> y \in S -> ~(x = y) -> ~( R (x,y)).
  (* end snippet RelIndep *)    
  
  Lemma RelIndep_I: forall (Q R: relation T) (S: set T),
      Q `<=` R -> RelIndep R S -> RelIndep Q S.
  Proof.
    move => Q R' S H1 H2 x y H3 H4 H5 /H1 H6.
    by pose proof (H2 x y) H3 H4 H5.
  Qed.
  
  Lemma RelIndep_set0: RelIndep R set0.
  Proof. by move => x y /inP H3 _ _ _. Qed.
  
  Lemma RelIndep_set1: forall (x: T), RelIndep R [set x].
  Proof. by move => x x1 x2 /inP -> /inP -> H4. Qed.
  
  Lemma RelIndep_U: forall X x,
      RelIndep R X -> ~(x \in R#X) -> ~(x \in (X:#R)) -> RelIndep R (X `|` [set x]).
  Proof.
    move => X x H2 H3 H4 x1 x2 /inP 
             [/inP H5 | /inP H5] /inP [/inP H6 |/inP H6] H7 H8.
    rewrite /RelIndep in H2.
    + by apply: ((H2 x1 x2) H5 H6 H7 H8).
    + move: H6 H4 => /inP <- H4. 
      by have H9: x2 \in X:#R by rewrite inP;exists x1; rewrite inP in H5.
    + move: H5 H3 => /inP <- H3. 
      by have H9: x1 \in R#X by rewrite inP;exists x2;rewrite inP in H6.
    + by move: H5 H6 H7 => /inP -> /inP ->. 
  Qed.
  
End Independent_set.

Section EquivalencePartition.

  Variables (T: Type) (R: relation T).

  (* Définition de la classe d'équivalence de x *)
  Definition class_of (x : T) := [set y: T| R (x,y)].

  Definition Quotient := {E : set T| exists x : T, E = class_of x }.

  (* Hypothèse : R est une relation d'équivalence *)
  Hypothesis R_equiv : equivalence R.

  (* Ensemble des classes d'équivalence (possiblement avec répétitions) *)
  Definition Classes := [set C | exists x:T, C = class_of x].
  
  (* Lemme 1 : Chaque classe est non vide *)
  Lemma classe_non_vide : forall (x : T) C, Classes C ->  (C != set0).
  Proof.
    move: (R_equiv) => [R_ref _ _].
    rewrite /Classes/class_of => x C -[x0 H1]. 
    rewrite -notempty_exists H1 /mkset. exists x0.
    by apply/inP. 
  Qed.

  (* Lemme 2 : Deux classes sont égales ou disjointes *)
  Lemma classes_disjointes_ou_egales :
    forall (x y : T), (exists z : T, R (x,z) /\ R (y,z)) -> class_of x = class_of y.
  Proof.
    move: (R_equiv) => [R_ref R_tr R_sy] x y [z [H1 H2]].
    rewrite predeqE;move => x0;split.
    + rewrite/class_of/mkset => H3.
      by pose proof (R_tr y x x0 (R_tr y z x H2 (R_sy x z H1)) H3).
    + rewrite/class_of/mkset => H3.
      by pose proof (R_tr x y x0 (R_tr x z y H1 (R_sy y z H2)) H3).
  Qed.

  (* Lemme 3 : Toute l'union des classes couvre T *)
  Lemma union_classes_couvre_E : forall x : T, exists C : set T, Classes C /\ C x.
  Proof.
    move: (R_equiv) => [R_ref _ _] x; exists (class_of x).
    by split;[rewrite /Classes/mkset;exists x;exact| rewrite /class_of/mkset].
  Qed.

  Lemma ER_union: \bigcup_ (C in Classes) (fun C  => C) C = setT.
  Proof.
    rewrite predeqE => x.
    split;first exact.
    move => H0. 
    by move: (union_classes_couvre_E x) => [C [H1 H2]]; exists C.
  Qed.

  Lemma ER_empty (C C': set T):
    C \in Classes -> C' \in Classes -> (exists z, C z /\ C' z) -> C = C'.
  Proof.
    rewrite /Classes;move => /inP [x ->] /inP [x' ->] [z H1].
    by apply: classes_disjointes_ou_egales;exists z. 
  Qed.
  
  Lemma ER_check (C C': set T):
    (C `&` C') != set0 <-> exists z, C z /\ C' z.
  Proof.
    split. 
    by move => /notempty_exists [z /inP [H1 H2]];exists z.
    by move => [z [H1 H2]];apply/notempty_exists;exists z;apply/inP. 
  Qed.

End EquivalencePartition.
