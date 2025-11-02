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
(*                                                                            *)
(* R.-1        : inverse of the relation R  R.-1 (x,y) <-> R (y,x)            *)
(* XXXX the .-1 notation is not good as it clashes with .-1 of nat: change it to ^-1 *)
(* R `;` S     : composition: (R `;` S) (x,y) <-> exists z, R (x,z) /\ S (z,y)*)
(* Δ_( W )     : diagonal relation on a subset                                *)
(* 'Δ          : diagonal relation on setT  'Δ = Δ_(setT)                     *)
(* 'Δc         : diagonal relation on set0  'Δ = Δ_(set0)                     *)
(* L_( W )     : relation W x setT                                            *)
(* R_( W )     : relation setT x X                                            *)
(* R^(n)       : n-iterate of composition                                     *) 
(* W .^c       : complementary (~` W) XXXXX                                   *)
(* R.+         : transitive closure of R                                      *)
(* R.*         : reflexive transitive closure of R                            *)
(* R#Y         : Foreset of the subset Y by relation R                        *)
(* R#_(y)      : Foreset of the subset [set y] by relation R                  *)
(* Y:#R        : Afterset of the subset Y by relation R                       *)
(* y_:#R       : Afterset of the subset [set y] by relation R                 *)
(* Clos(Y|R,W) : closure of Y for the relation Δ_(W.^c) `;` R                 *)
(* Clos_(y|R,W): closure of [set y] for the relation Δ_(W.^c) `;` R           *)
(* XXXX Rajouter ce qui est a la fin *)
(******************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order. 
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * relations as sets: (set T*T) *)

(* begin snippet relation:: no-out *)  
Definition relation (T: Type) := set (T * T).
(* end snippet relation *)  

(* begin snippet Sthree *)  
Definition inverse (T: Type) (R:relation T) : relation T := [set x | R (x.2,x.1)].
(* end snippet Sthree *)  

Notation "R .-1" := (@inverse _ R) : classical_set_scope.
Notation "R ^-1" := (@inverse _ R) : classical_set_scope.
Definition compose (T: Type) (R U: relation T): relation T := 
    [set x | exists (z: T), R (x.1,z) /\ U (z,x.2)].
Notation "R `;` U" := 
  (@compose _ R U) (at level 51, left associativity, format "R `;` U").

Definition Delta (T: Type) (X: set T) : relation T := 
  [set x | X x.1 /\ x.1 = x.2].

Notation "'Δ" := (Delta setT) (at level 2, no associativity).

Definition DeltaC (T: Type) (X: set T) : relation T := 
  Delta (~` X).

Definition Lr (T: Type) (X: set T) : relation T := [set x | X x.1].
Definition Rr (T: Type) (X: set T) : relation T := [set x | X x.2].

Definition iter (T: Type) R S n : relation T:=
  let fix loop m := if m is i.+1 then (loop i) `;` R else S in loop n.

Definition Tclos (T: Type) (R: relation T) := \bigcup_ (n >= 1) (iter R 'Δ n).

Definition RTclos (T: Type) (R: relation T) := \bigcup_ n (iter R 'Δ n).

Definition Fset (T:Type) (R: relation T) (Y: set T) : set T :=
  [set x | exists (y: T), R (x,y) /\ Y y].

Definition Aset (T:Type) (R: relation T) (Y: set T) : set T :=
  Fset R.-1 Y. 

(* begin snippet RelIndep:: no-out *)    
Definition RelIndep (T: Type) (R: relation T) (S: set T) :=
  forall (x y:T),  x \in S -> y \in S -> ~(x = y) -> ~( R (x,y)).
(* end snippet RelIndep *)    

(* possible Corecion of relation T to rel T *)
Definition R2rel (T: Type) (R: relation T) : rel T := (fun x y => ((x,y) \in R)).
Global Coercion R2rel : relation >-> rel.

Notation "Δ_( W )" := (@Delta _ W) 
                        (at level 2, no associativity, format "Δ_( W )").
Notation "L_( W )" := (@Lr _ W)
                        (at level 2, no associativity, format "L_( W )").
Notation "R_( W )" := (@Rr _ W)
                        (at level 2, no associativity, format "R_( W )").
Notation "W .^c" := (~` W) 
                      (at level 2, left associativity, format "W .^c").

Notation "'Δc" := (DeltaC setT) (at level 2, no associativity).
Notation "R ^( n )" := (@iter _ R 'Δ n) 
                         (at level 2, left associativity, format "R ^( n )").
Notation "R .+" := (Tclos R) (at level 1, left associativity, format "R .+").
Notation "R .*" := (RTclos R) (at level 1, left associativity, format "R .*").

(* Foreset of Y for the relation R*)
Notation "R # Y" := (Fset R Y) (at level 3, no associativity, format "R # Y").

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

Section Relation_Facts.
  
  Context {T : Type}.
  Implicit Types (T : Type) (R S: relation T) (X Y: set T).

  (** We could use reflexive, transitive, ... from  Coq.ssr.ssrbool 
      using the coercion to rel T *)
  
  Definition reflexive R : Prop := forall x:T, R (x,x).
  Definition transitive R: Prop := forall x y z:T, R (x,y) -> R (y,z) -> R (x,z).
  Definition symmetric R: Prop := forall x y:T, R (x,y) -> R (y,x).
  Definition antisymmetric R: Prop := forall x y:T, R (x,y) -> R (y,x) -> x = y.
  Definition asymmetric R: Prop := forall x y:T, R (x,y) -> ~ R (y,x).
  Definition irreflexive R : Prop := forall x:T, ~ R (x,x).
  
  Record preorder R : Prop :=
    { preord_refl: reflexive R; preord_trans: transitive R}.

  (** * partial order *)
  Record porder R : Prop :=
    { poset_refl: reflexive R; poset_antisym: antisymmetric R;poset_trans : transitive R}.
  
  (** * strict partial order *)
  Record sporder R : Prop := 
    { sorder_irefl: irreflexive R; sorder_trans: transitive R}.

  (** * equivalence relation *)
  Record equivalence R : Prop :=
    { equiv_refl : reflexive R; equiv_trans : transitive R; equiv_sym : symmetric R}.

  Lemma irP R: irreflexive R -> (asymmetric R <-> antisymmetric R).
  Proof. move => Ir. split => [Asy x y /Asy ? ? //| Atsy x y /[dup] H0 H1 H2]. 
         by move: (Atsy x y H1 H2) H0 => ->;apply: Ir.
  Qed.

  (* sorder is also asymmetric *)
  Lemma sporder_asym R: transitive R -> irreflexive R -> asymmetric R.
  Proof. by move => Tr Ir x y H1 H2; pose proof (Ir x (Tr x y x H1 H2)). Qed.

  (* sorder is also antisymmetric *)
  Lemma sporder_antisym R: transitive R -> irreflexive R -> antisymmetric R.
  Proof. by move => Tr Ir x y H1 H2; pose proof (Ir x (Tr x y x H1 H2)). Qed.
  
  (** * Sets_facts *)
  
  (* should be replaced by in_setE *)
  Lemma inP (T': Type) (x:T') (X: set T'): x \in X <-> X x. 
  Proof. by rewrite in_setE. Qed.
  
  Lemma notempty_exists (T': Type) (X:set T'): (exists z, z \in X) <-> (X != set0).
  Proof.
    by rewrite set0P;split;[move => [z /set_mem ?]|move => [z /mem_set ?]];exists z.
  Qed.
    
  (* begin snippet Sone:: no-out *)  
  Lemma empty_notexists (T': Type) (X:set T'): X = set0 <-> ~ (exists z, z \in X).
  Proof.
    split =>[-> [z]| H1];first by rewrite in_set0. 
    by rewrite predeqE => x;split => [/inP ?|];[have H2: exists z, z \in X by (exists x)|].
  Qed.
  (* end snippet Sone *) 
  
  (* begin snippet Stwo:: no-out *)  
  Lemma empty_iff (T': Type) (X:set T'): ~ (X != set0) <-> X = set0.
  (* end snippet Stwo *)  
  Proof. by rewrite -notempty_exists empty_notexists. Qed.

  Lemma notempty_iff X: ~ (X = set0) <-> X != set0.
  Proof.
    split;first by move => /empty_notexists /contrapT /notempty_exists H1. 
    by move => /notempty_exists H1 /empty_notexists H2.
  Qed.
  
  Lemma W_part X Y Z: (Y `<=` X) /\ (Z= X `\` Y) -> Y `&` Z = set0.
  Proof. by move => [? H2];rewrite empty_notexists H2;move => [z /inP [? [_ ?]]]. Qed.
  
  (** * Union of relations *)
  
  Lemma union_inc_b (R S U:relation T): S `<=` U -> R `<=` U -> (S `|` R) `<=` U.
  Proof. by move => H1 H2;(have <- : U `|` R = U by apply setUidPl);apply setSU. Qed.
  
  (** XXXX doit exister dans classical_sets *)
  Lemma WWcI X: X `&` X.^c = set0.
  Proof. by rewrite predeqE => x;split => [[?]|?];[rewrite /setC mksetE|]. Qed.
  
  Lemma WWcU X: X `|` X.^c = setT.
  Proof. by rewrite predeqE => x;split => _;[rewrite -in_setE in_setT|apply: lem]. Qed.

  (** *  Inverse *)
  
  Lemma inverseK R:  R.-1.-1 = R.
  Proof. by rewrite /inverse /mkset predeqE /=;tauto. Qed.
  
  Lemma inverse_sym R: R.-1 = R <-> symmetric R.
  Proof. by rewrite predeqE;split => [H0 x y /H0 //|H1 [x y]];split;apply H1. Qed.
  
  Lemma inverseE R S: R = S <-> R.-1 = S.-1.
  Proof. by split =>[->//| H1];rewrite -[R]inverseK -[S]inverseK H1. Qed.
  
  Lemma inverseU R S: (R `|` S).-1 = R.-1 `|` S.-1.
  Proof. by rewrite /predeqE. Qed.

  Lemma inverseS R S: R `<=` S -> R.-1 `<=` S.-1. 
  Proof. by move => H1 x /H1 H2. Qed.

  (** * Composition *)

  Lemma composeA R S U: (R `;` S) `;` U = R `;` (S `;` U).
  Proof.
    rewrite predeqE => x';split => [ [z [[w /= [? ?]] ?]] | [z [? [ w [? ?]]]]].
    by (exists w);split; [|exists z; split].
    by (exists w);split; [exists z|].
  Qed.

  Lemma composeDr  R S U: (R `|` S) `;` U = (R `;` U) `|` (S `;` U).
  Proof.
    rewrite predeqE => x;split.
    by move => [z [[? | ? ] ?]];[left|right];exists z.
    by move => [|] [ z [? ?]];[exists z; split;[left|]|exists z;split;[right|]].
  Qed.
  
  Lemma composeDl R S U: R `;` (S `|` U) = (R `;` S) `|` (R `;` U).
  Proof.
    rewrite predeqE => x;split => [[z [H1 H2]] | H1].
    by move: H2 => [H2|H2];[left;exists z;split|right;exists z; split].
    by move: H1 => [[z [H1 H2]] | [z [H1 H2]]];(exists z);split;[|left| |right]. 
  Qed.
  
  Lemma composeSl R S U: S `<=` U ->(R `;` S) `<=` (R `;` U). 
  Proof. by move => H x [z [? ?]];exists z;split;[|apply: H]. Qed.
  
  Lemma composeSr R S U: S `<=` U ->(S `;` R ) `<=` (U `;` R). 
  Proof. by move => H x [z [? ?]];exists z;split;[apply: H|]. Qed.
  
  Lemma composeIv  R S: (R `;` S).-1 = S.-1 `;` R.-1.
  Proof. by rewrite predeqE => x;split;move => [z [? ?]];exists z;split. Qed.

  Lemma RRm_sym R:  symmetric (R `;` R.-1).
  Proof. by move => x y [z [H1 H2]];exists z;split;[apply: H2|apply: H1]. Qed.
  
  Lemma RRm_inverse R: (R `;` R.-1).-1 = R `;` R.-1.
  Proof. by apply/inverse_sym/RRm_sym. Qed. 

  (** Delta *)
    
  Lemma Dset_sym X:  symmetric Δ_(X).
  Proof. by move => x y [+ /= <-] => /= H1;split. Qed.
  
  Lemma Dset_trans X: transitive Δ_(X).
  Proof. by move => x y z [/= ? H2] [? H4];split;[|rewrite H2 H4]. Qed.
  
  Lemma DsetS X Y: X `<=` Y -> Δ_(X) `<=` Δ_(Y).
  Proof. by move =>  H [x y] [H1 /= <-];split;[apply: H|]. Qed.

  Lemma DeltaS X: Δ_(X) `<=` 'Δ.
  Proof. by apply: DsetS. Qed.

  Lemma Dset_compose X Y: Δ_(X) `;` Δ_(Y) = Δ_(X `&` Y).
  Proof. by rewrite predeqE
         => -[x y];split=>[[z [[? /= <-][? /= <-]]]|[[? ?] /= <-]];[|exists x]. Qed.
  
  Lemma DsetK X:  Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof. by rewrite Dset_compose setIid. Qed.

  Lemma DsetIv X: Δ_(X).-1 = Δ_(X). 
  Proof. by rewrite predeqE /inverse => -[x y] /=;split;move => [H1 /= <-]. Qed.
  
  Lemma DeltaIv: 'Δ.-1 = ('Δ : relation T).
  Proof. by apply:  DsetIv. Qed.
  
  Lemma DeltaP (x y: T): 'Δ (x,y) <-> x = y.
  Proof. by split => [[_ ? //]| ->]. Qed.
  
  Lemma DsetE X (x y:T): Δ_(X) (x,y) <-> X x /\ x = y.
  Proof. exact. Qed.
  
  Lemma DeltaLco X R: Δ_(X) `;` R = L_(X) `&` R.
  Proof. by rewrite predeqE /= => [[x y]] /=;split => [[z [[? /= <-] ?]]|[? ?]];[|exists x].  Qed.

  Lemma DeltaRco X R: R `;` Δ_(X) = R `&` R_(X).
  Proof. by rewrite  predeqE /= => [[x y]] /=;split => [[z [? [? /= <-]]]|[? ?]];[|exists y]. Qed.

  Lemma Delta0: Δ_(set0) = ('Δc: relation T).
  Proof. by rewrite predeqE => -[x y];split => [/DsetE [? _] | [/= ? _]]. Qed.
  
  Lemma DeltaW_Wc X: Δ_(X) `;` Δ_(X.^c) = 'Δc.
  Proof.
    rewrite predeqE -Delta0=> -[x y];split.
    by move => [z [/DsetE [? <-] /DsetE [? _]] //].
    by move => /DsetE [? _].
  Qed.
    
  Lemma DeltaWc_W X: Δ_(X.^c) `;` Δ_(X) = 'Δc.
  Proof. by rewrite Dset_compose setIC WWcI Delta0. Qed.
  
  Lemma DeltaC_union_ideml R: 'Δc `|` R = R.
  Proof.
    rewrite eqEsubset;split;last by apply: subsetUr.
    by move => -[x y] [[H1 _]|]//;rewrite setCT in H1.
  Qed.
  
  Lemma DeltaC_union_idemr R:  R `|` 'Δc = R.
  Proof.  by rewrite setUC; apply DeltaC_union_ideml. Qed.
  
  Lemma DeltaC_compose_absorbl R: 'Δc `;` R = 'Δc.
  Proof.  by rewrite predeqE => x;split => [[z [[/= ? _] _]]|[/= ? _]] //. Qed.
  
  Lemma DeltaC_compose_absorbr R:  R `;` 'Δc = 'Δc.
  Proof. by rewrite predeqE => x;split => [[z [_ [/= ? _]]]|[/= ? _]] //. Qed.
  
  Lemma DsetU X Y: Δ_(X) `|` Δ_(Y) = Δ_(X `|` Y).
  Proof.
    rewrite predeqE => -[x y];split.
    by move => [|] [/= ? /= <-];apply/DsetE;split;[left| |right| ].
    by move => [[? | ?] /= <-];[left|right].
  Qed.
  
  Lemma Dset_compZ X: Δ_(X) `|` Δ_(X.^c) = 'Δ.
  Proof. by rewrite DsetU WWcU. Qed.
  
  Lemma Dset_compose_same X: Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof. by rewrite Dset_compose setIid.  Qed.
  
  Lemma Delta_idem_l R: 'Δ `;` R = R.  
  Proof.
    rewrite predeqE => -[x y];split=> [[z [/DeltaP <- ?]]| ?];first exact.
    by exists x;split;[rewrite DeltaP |].
  Qed.
  
  Lemma Delta_idem_r R: R `;` 'Δ = R.  
  Proof.
    rewrite predeqE => -[x y];split => [[z [? /DeltaP /= <-]] |];first exact.
    by move => ?; exists y; split;[| apply DeltaP].
  Qed.
  
  Lemma R_restrict R X (x y: T): 
    x \in X /\ y \in X -> (R (x,y) <-> (Δ_(X) `;` R `;` Δ_(X)) (x,y)).
  Proof.
    rewrite /compose /Delta /mkset /=.
    move => [/inP H1 /inP H2];split=> [ H3 | [z [[t [[H3 ->] H4] [H5 <-]]]] //].
    by (exists y; split;[ exists x; split | ]).
  Qed.

  Lemma R_restrict_l R X (x y: T): x \in X -> (R (x,y) <-> (Δ_(X) `;` R) (x,y)).
  Proof. by move => /inP ?;split => [? | [z [[? /= ->] ?] ] //];(exists x; split). Qed.
  
  Lemma DeltaCsubset R X: (Δ_(X) `;` R `<=` R).
  Proof. by move => -[x y] /= => [[z [[_ /= <-] ?]]]. Qed.
  
  Lemma DeltaCsubsetl R X: (R `;` Δ_(X) `<=` R).
  Proof. by move => -[x y] /= => [[z [H2 [_ /= <-]]]]. Qed.
    
  (** * Composition iteration *)
  
  Lemma iter1_id R: R^(1) = R.
  Proof. by rewrite /iter Delta_idem_l. Qed.

  Lemma iter_compose1r R n: R^(n.+1) = R^(n) `;` R.
  Proof. by elim: n => [//|n ?]. Qed.
  
  Lemma iter_compose R n1 n2: R^(n1 + n2) = R^(n1) `;` R^(n2).
  Proof.
    elim: n2 n1 => [n1| n1 H n0];first by rewrite addn0  Delta_idem_r.
    by rewrite [addn n0 n1.+1]addnS iter_compose1r H composeA -iter_compose1r.
  Qed.

  Lemma iter_compose1l R n: R^(n.+1) = R `;` R^(n).
  Proof. by rewrite -addn1 addnC (iter_compose R 1 n) iter1_id. Qed.
  
  Lemma iter_delta (n: nat): 'Δ^(n) = ('Δ :relation T).
  Proof. 
    by elim: n => [//|n Hr];rewrite -addn1 (iter_compose 'Δ n 1)
                                      Hr iter1_id Delta_idem_l.
  Qed.

  Lemma iter_include R S (n:nat): R `<=` S -> R^(n) `<=` S^(n).
  Proof.
    elim: n => [_ //| n Hr H1];rewrite -addn1 (iter_compose R n 1) (iter_compose S n 1).
    have H4: R^(n)`;`R^(1) `<=` S^(n)`;`R^(1) by apply: composeSr;apply:Hr.
    by apply: (subset_trans H4 _);apply: composeSl;rewrite 2!iter1_id.
  Qed.
  
  Lemma iter_subset R S: transitive S ->  R `<=` S -> forall n, n > 0 -> R^(n) `<=` S.
  Proof.
    move => Ht H1;elim => [//| n Hr H2 [x y]].
    have H2': R^(1) `<=` S by rewrite iter1_id.
    case H3: (n == 0);first by move: H3 => /eqP -> => /H2'.
    move: H3 => /neq0_lt0n /Hr H3.
    rewrite -addn1 (iter_compose R n 1) => -[z [/H3 H4 /H2' H5]];apply: (Ht x z y H4 H5). 
  Qed. 
  
  Lemma inverse_iter R (n: nat) : R^(n).-1 = (R.-1)^(n).
  Proof.
    elim: n =>[| n H1];first  by rewrite /iter DsetIv.
    by rewrite -addn1 (iter_compose R n 1) composeIv
                  addnC (iter_compose R.-1 1 n) H1 !iter1_id. 
  Qed.
  
  Lemma iter_C R (n:nat): R^(n)`;`R = R `;` R^(n).
  Proof. by move: (iter_compose R n 1) (iter_compose R 1 n);rewrite  iter1_id addnC => <- <-. Qed.
  
  Lemma iter_sym R (n:nat): symmetric R -> symmetric R^(n).
  Proof.
    move => Hs.
    elim: n => [H1 | n Hr x y];first by apply: Dset_sym.
    rewrite -addn1;move: (iter_compose R n 1) => H1.  
    rewrite {1}H1 iter1_id /= => -[z /=[/Hr H2 /Hs H3]].
    by rewrite addnC (iter_compose R 1 n) iter1_id;(exists z).
  Qed.

  Lemma iterD_sub R (n: nat): ('Δ `|` R)^(n) `<=` ('Δ `|` R)^(n.+1).
  Proof.
    rewrite -{1}addn1 (iter_compose ('Δ `|` R) n 1) iter1_id composeDl Delta_idem_r.
    by apply: subsetUl.
  Qed.
  
  Lemma iterDr R X: forall (n: nat), 0 < n -> (R`;`Δ_(X))^(n) = (R`;`Δ_(X))^(n)`;`Δ_(X).
  Proof.
    have H1: (R`;`Δ_(X))^(1) = (R`;`Δ_(X))^(1) `;`Δ_(X) by rewrite iter1_id composeA DsetK.
    by case => [//| n _];rewrite -addn1 (iter_compose (R`;`Δ_(X)) n 1) composeA -H1.
  Qed.
  
  Lemma iterDl R X: forall (n: nat), 0 < n -> (Δ_(X)`;`R)^(n) = Δ_(X)`;`(Δ_(X)`;`R)^(n).
  Proof.
    have H1: (Δ_(X)`;`R)^(1) = Δ_(X)`;`(Δ_(X)`;`R)^(1)
      by rewrite iter1_id -composeA DsetK.
    case => [//| n _].
    by rewrite -addn1 addnC (iter_compose (Δ_(X)`;`R) 1 n) -[RHS]composeA -H1.
  Qed.
  
  Lemma bigcup_iter0 R: \bigcup_(i < 1) R^(i) = 'Δ. 
  Proof. by rewrite predeqE => -[x y];split => [[n]|?];[rewrite II1 => -> /DeltaP ->|exists 0]. Qed.
  
  Lemma bigcupC I (F : I -> relation T) (P : set I) U:
    \bigcup_(i in P) (F i `;` U) = (\bigcup_(i in P) F i) `;` U.
  Proof.
    apply/predeqP => -[x y]. split. 
    by move => [n Pn [z /= [H1 H2]]];exists z;split;[exists n|]. 
    by move => [z [[n Pn /= H1] /= H2]];exists n;[|exists z].
  Qed.

  (** * Reflexive Closure *)
  
  Lemma delUrel R S: reflexive S -> R `<=` S -> 'Δ `|` R  `<=` S.
  Proof. by move => ? Hs -[x y] [/DeltaP -> // | /Hs ?]. Qed.
  
  Lemma RclosE R: 'Δ `|` R = smallest [set S | reflexive S] R. 
  Proof. 
    rewrite eqEsubset. split.
    by move => -[x y] [/DeltaP ->S [? _] // |];apply: sub_smallest.
    by apply: smallest_sub;[left | apply: subsetUr].
  Qed.
  
  (** * Transitive closure  *)
  
  Lemma Tclos_r R S: (Tclos R) `;` S = \bigcup_ (n >= 1) R^(n) `;` S.
  Proof. by rewrite -bigcupC. Qed.
  
  Lemma Tclos_in R S: transitive S -> R `<=` S -> R.+ `<=` S.
  Proof. by move => Ht H1 [x y] [n /= H2];move: (iter_subset Ht H1 H2) => H3 /H3 ?. Qed.
  
  Lemma TclosT R: transitive R.+.
  Proof.
    move => x y z -[n1 /= H1 ?] -[n2 /= H3 ?];exists (n1 + n2).
    by rewrite /= (addn_gt0 n1 n2);apply/orP;left. 
    by rewrite (iter_compose R n1 n2);exists y.
  Qed.
  
  Lemma TclosS R: R `<=` R.+.
  Proof. by move => [x y] ?;exists 1;[| rewrite iter1_id]. Qed.
  
  (* mathematical def of closure 
     smallest [set S | transitive S] R
     is also \bigcap_(S in [set S | transitive S /\ R `<=` S]) S *)
  
  Lemma TclosE R: R.+ = smallest [set S | transitive S] R. 
  Proof.
    rewrite predeqE => -[x y];split => [[n /= H1 H2 S' [H3 H4]]|].
    by move: (iter_subset H3 H4) => H5;move: (H5 n H1) H2 => H6 /H6 H2.
    by apply: (@smallest_sub _ transitive _ R.+ (@TclosT _) (@TclosS _)). 
  Qed.

  Lemma iterk_inc_clos_trans R: forall (n : nat), R^(n.+1) `<=` R.+.
  Proof. by move => n xy H1;exists n.+1. Qed.
  
  Lemma clos_t_iterk R (x y:T): R.+ (x,y) -> exists (n:nat), R^(n.+1) (x,y).
  Proof.
    by move => [n H1 ?];exists (n.-1)%N;have ->: n.-1.+1 = n by apply: ltn_predK H1. 
  Qed.

  Lemma clos_t_iterk' R (x y:T): (exists (n:nat), R^(n.+1) (x,y)) -> R.+ (x,y).
  Proof. by move => [n H1];apply: (@iterk_inc_clos_trans R n). Qed.
  
  Lemma inverse_clos_t R: R.+.-1 = R.-1.+ .
  Proof.
    rewrite predeqE => -[x y] /=;split => [[n ? ?]| [n H1]].
    by (exists n);[ exact|rewrite -inverse_iter].
    by rewrite -inverse_iter => ?;exists n.
  Qed.
  
  Lemma clos_t_sym R: symmetric R -> symmetric R.+.
  Proof. by move => Hs x y [n /= H1 /(iter_sym Hs) H2];exists n. Qed.

  Lemma iter1_inc_clos_trans R: R `<=` R.+.
  Proof. by move => xy H1;exists 1;[ | rewrite iter1_id]. Qed.
  
  Lemma clos_t_inc R S: R `<=` S -> R.+ `<=` S.+ .
  Proof. 
    by move => H1 xy [n /= H2 H3];(exists n);[|apply: (@iter_include R S n H1)]. Qed.
  
  Lemma clos_t_sep_n R: forall (n: nat) (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R^(n.+1) (x, y)
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
  
  Lemma clos_t_sep R: forall (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R.+ (x,y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x', y')).
  Proof.
    move => x y W [H1 [H2 /clos_t_iterk [n' H3]]].
    by apply clos_t_sep_n with n' x y.
  Qed.

  Lemma Delta_clos_trans_ends R X: (R `;` Δ_(X)).+ =  (R `;` Δ_(X)).+ `;` Δ_(X).
  Proof.
    rewrite predeqE => -[x y];split;last by move=> [z[+[_ /= H3]]];rewrite H3.
    move=> [n Pn];rewrite (iterDr R X Pn) => -[z /= [H2 H3]].
    by (exists z);split;[exists n|].
  Qed.

  Lemma Delta_clos_trans_starts R X: (Δ_(X) `;` R).+ = Δ_(X) `;` (Δ_(X) `;` R).+.
  Proof.
    rewrite predeqE => -[x y]; split;last by move=> [z[[_ /= H3]]];rewrite H3.
    move=> [n Pn];rewrite (iterDl R X Pn) => -[z /= [H2 H3]].
    by (exists z);split;[|exists n].
  Qed.
  
  Local Lemma clos_trans_inc (Z V U W: relation T):
    (forall (n:nat), Z `;` (V^(n.+1)) `;` U = Z `;` (W^(n.+1)) `;` U) 
    -> Z `;` V.+ `;` U `<=` Z `;` W.+ `;` U.
  Proof.
    move => H0 [x y] [z [[t /=[H1 [n H2 H3]]] /=H4]].
    move: H0 => /(_ (n.-1)%N);(have ->: n.-1.+1 = n by apply: ltn_predK H2);move => H0.
    have [z' [[t' /=[H1' H2']] H4']]: (Z`;`W^(n)`;`U) (x,y) by rewrite -H0;exists z;split;[exists t|].
    by exists z';split;[exists t';split;[|exists n]|].
  Qed.
  
  Lemma clos_trans_eq (Z R S U: relation T):
    (forall (n:nat), Z `;` (R^(n.+1)) `;` U = Z `;` (S^(n.+1)) `;` U)
    -> Z `;` R.+ `;` U = Z `;` S.+ `;` U.
  Proof.
    by move => H;rewrite predeqE;split;[apply: clos_trans_inc | apply: clos_trans_inc].
  Qed.
  
  Lemma clos_t_composer R: (R `;` R.+) `<=` R.+.
  Proof. 
    by move => [x y] [z [? [n ? ?]]];
              exists (n.+1);[exact | rewrite iter_compose1l;exists z].
  Qed.
  
  Lemma clos_t_composel R: (R.+ `;` R) `<=` R.+.
  Proof. 
    by move => [x y] [z [[n ? ?] ?]];
              exists (n.+1);[exact | rewrite iter_compose1r;exists z].
  Qed.
  
  Lemma clos_t_decomp_rt R: R `|` (R `;` R.+) = R.+ .
  Proof.
    rewrite eqEsubset;split;first by
      apply: (union_inc_b (@TclosS _) (@clos_t_composer _)).
    move => -[x y] [n /= H2].
    case H1: (1 == n);first by move: H1 => /eqP <-;rewrite iter1_id => H3;left.
    have H3': n.-1.+1 = n by apply: ltn_predK H2. 
    have H5: 1 < n by move:H2;rewrite leq_eqVlt H1 orFb.
    have H6: (0 < n.-1)%N by rewrite -(ltn_add2r 1) addn1 [n.-1 + 1]addn1 H3'.
    rewrite -H3' (iter_compose1l R (n.-1)%N) => -[z [H7 H8]].
    by right;exists z;split;[| exists (n.-1)%N].
  Qed.

  Lemma clos_t_decomp_rt' R: R `|` (R `;` R.+) = R.+ .
  Proof.
    rewrite eqEsubset;split;first by
      apply: (union_inc_b (@TclosS _) (@clos_t_composer _)).
    move => -[x y] /(@clos_t_iterk R x y) [n].
    case H3: (n == 0);first by move: H3 => /eqP ->;rewrite iter1_id => H3;left.
    move: H3 => /neq0_lt0n H3;rewrite (iter_compose1l R) => -[z /= [H1 H2]].
    by right;exists z;split;[|exists n].
  Qed.
  
  Lemma clos_tI R:  (R.+ `;` R.+) `<=` R.+.
  Proof. 
    move => [x y] [z [/clos_t_iterk [n1 H1] /clos_t_iterk [n2 H2]]].
    by exists (n1.+1 + n2.+1);[exact | rewrite (iter_compose R n1.+1 n2.+1);exists z].
  Qed.
  
  Lemma clos_t_decomp_2 R: R.+ `|` (R.+ `;` R.+) = R.+.
  Proof. by rewrite predeqE => -[x y];split => [[? //| /clos_tI ?//] | ?];left. Qed.
  
  Lemma clos_t_decomp_rt_r R: R `|` (R.+ `;` R) = R.+.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [H1| [z /= [/clos_t_iterk [n1 H1] H3]]];
             first by apply: iter1_inc_clos_trans.
      by (exists n1.+2);[| rewrite (iter_compose1r R n1.+1);exists z].
    + move => /clos_t_iterk [n].
      case H2: (n == 0); first by move: H2 => /eqP ->;rewrite iter1_id;left.
      move: H2 => /neq0_lt0n H2;rewrite (iter_compose1r R n) => -[z [H3 H4]].
      by right;exists z;split;[exists n|].
  Qed.
  
  (** * Reflexive Transitive Closure *)
  
  (* A proof with bigcup *)
  Lemma RTclosE R: R.* = 'Δ `|` R.+.
  Proof. 
    by rewrite /RTclos (bigcup_splitn 1) 
      -(@bigcup_mkord _ 1 (fun n => R^(n))) bigcup_iter0 bigcup_addn.
  Qed.

  Lemma RTclos_dec R: R.* = 'Δ `|` R.+.
  Proof.
    rewrite predeqE => -[x y].
    split;last by move => [/DeltaP -> | [n /= H1 H2]];[exists 0|exists n].
    move => [n _ ].
    case H2: (n == 0);first by move: H2 => /eqP -> /DeltaP ->;left.
    by move: H2 => /neq0_lt0n H2 H3;right;(exists n). 
  Qed.
  
  Lemma RTclos_in R S: transitive S -> reflexive S -> R `<=` S -> R.* `<=` S.
  Proof.
    move => Ht Hr H1 [x y] [n _]. 
    case H2: (n == 0);first by move: H2 => /eqP -> /DeltaP ->.
    by move: H2 => /neq0_lt0n H2;move: (iter_subset Ht H1 H2) => H3 /H3 ?.
  Qed.
  
  Lemma RTclosT R: transitive R.*.
  Proof.
    rewrite RTclos_dec.
    move => x y z [/DeltaP -> //| /clos_t_iterk [n1 H1]].  
    move => [/DeltaP <- //|/clos_t_iterk [n2 H2]];first by right;(exists n1.+1).
    by right;exists (n1.+1 + n2.+1);[exact|rewrite iter_compose;exists y].
  Qed.
  
  Lemma RTclosR R: reflexive R.*.
  Proof. by rewrite RTclos_dec; move => x; left. Qed.
  
  Lemma RTclosS R: R `<=` R.*.
  Proof. by rewrite RTclos_dec;move => [x y] ?;right;exists 1;[|rewrite iter1_id]. Qed.
  
  (* coincide with mathematical def of closure  *)
  Lemma RTclosIff R: R.* = smallest [set S | reflexive S /\ transitive S] R. 
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [n /= H1 H2 S' [[H3 H3'] H4]].
      case H5: (n == 0);first by move: H5 H2 => /eqP -> /DeltaP ->.
      move: H5 => /neq0_lt0n H5.
      by move: (iter_subset H3' H4 H5) H2 => H6 /H6 H2. 
    + move => /= H2.
      have: [set S | (reflexive S /\ transitive S) /\ R `<=` S] R.*
        by split;[split;[apply: RTclosR|apply: RTclosT]|apply: RTclosS].
      by move => /H2.
  Qed.
  
  Lemma inverse_star R: R.*.-1 = R.-1.* .
  Proof. by rewrite 2!RTclos_dec inverseU inverse_clos_t DeltaIv. Qed.
  
  Lemma clos_refl_trans_containsD R X: Δ_(X) `<=` R.* .
  Proof. by rewrite RTclos_dec;apply: subset_trans;[apply: DeltaS|apply: subsetUl].  Qed.
  
  Lemma clos_t_clos_rt R: R.+ `<=` R.*.
  Proof. by rewrite RTclos_dec;apply: subsetUr. Qed.
  
  Lemma clos_refl_trans_inc R S: R `<=` S -> R.* `<=` S.*.
  Proof. by move => H1;rewrite 2!RTclos_dec;apply/setUS/clos_t_inc. Qed.
  
  Lemma DuT_eq_Tstar R:  'Δ `|` R.+ = R.*.  
  Proof. by rewrite RTclos_dec. Qed.
  
  Lemma r_clos_rt_clos_t R: R `;` R.* = R.+.
  Proof. by rewrite -DuT_eq_Tstar composeDl Delta_idem_r clos_t_decomp_rt. Qed.
  
  Lemma clos_rt_r_clos_t R: R.* `;` R = R.+.
  Proof. by rewrite -DuT_eq_Tstar composeDr Delta_idem_l clos_t_decomp_rt_r. Qed.
    
  (* sumRk R n = 'Δ `|` R `|` R^(2) `|` R^(n) = ('Δ `|` R)^(n). *)
  Fixpoint sumRk (T:Type) (R: relation T) (n : nat) : relation T :=
    match n with 
    | 0 => 'Δ
    | n'.+1 => 'Δ `|` (R `;` (sumRk R n'))
    end.
    
  Lemma sumRk_0 R: sumRk R 0 = 'Δ.
  Proof. by rewrite predeqE => -[x y];split => [/DeltaP -> |]. Qed.
    
  Lemma sumRk_1 R: sumRk R 1 = 'Δ `|` R. 
  Proof. by rewrite /sumRk Delta_idem_r. Qed.
    
  Lemma sumRk_kp1_l R: forall (n: nat), sumRk R (n.+1) = 'Δ `|`  (R `;` (sumRk R n)).
  Proof. by move => n. Qed.
    
  Local Lemma Delta_inc_sumRk R: forall (n: nat), 'Δ `<=` (sumRk R n).
  Proof. by elim => [| n H];[rewrite sumRk_0 | rewrite sumRk_kp1_l;apply: subsetUl]. Qed.
  
  Local Lemma sumRk_inc_sumRkp1 R: forall (n: nat), (sumRk R n)  `<=` (sumRk R (n.+1)).
  Proof.
    elim => [| n H]; first by rewrite sumRk_0 sumRk_1; apply subsetUl.
    by rewrite 2!sumRk_kp1_l;apply/setUS/composeSl.
  Qed.
  
  Local Lemma RsumRk_inc_sumRkp1 R:  forall (n: nat), R `;` (sumRk R n)  `<=` (sumRk R (n.+1)).
  Proof. 
    elim => [| n H1];first by rewrite sumRk_0 sumRk_1 Delta_idem_r; apply/subsetUr.
    by rewrite 2!sumRk_kp1_l;apply/subsetUr.
  Qed.
  
  Local Lemma sumRk_composel R (n: nat): sumRk R (n.+1) =('Δ `|` R) `;` (sumRk R n). 
  Proof.
    rewrite [RHS]composeDr Delta_idem_l eqEsubset.
    split; first by rewrite sumRk_kp1_l;apply/setSU/Delta_inc_sumRk.
    by apply: union_inc_b;[apply: sumRk_inc_sumRkp1|apply: RsumRk_inc_sumRkp1].
  Qed.
  
  Local Lemma sumRk_compose2 R: forall (n: nat),  sumRk R n = ('Δ `|` R)^(n).
  Proof.
    by elim => [// |n H];rewrite (iter_compose1l ('Δ `|` R) n) -H;apply/sumRk_composel.
  Qed.
  
  Local Lemma sumRk_compose' R (n1 n2: nat): sumRk R (n1 + n2) = (sumRk R n1) `;` (sumRk R n2).
  Proof.  by rewrite 3!sumRk_compose2; apply: iter_compose. Qed.
  
  Local Lemma sumRk_inc_clos_refl_trans R: forall (n : nat), (sumRk R n) `<=` R.*.
  Proof.
    elim => [|n Hr];first by rewrite sumRk_0 => [[x y] ?];exists 0.
    rewrite sumRk_composel composeDr Delta_idem_l.
    have H2: R `;` R.* `<=` R.* by rewrite r_clos_rt_clos_t;apply: clos_t_clos_rt.
    have H3: R`;`sumRk R n `<=` R `;` R.* by apply: composeSl. 
    by apply: (union_inc_b Hr);apply: (subset_trans H3 H2).
  Qed.
  
  Local Lemma clos_rt_sumRk R (x y:T):  R.* (x, y) -> exists (n:nat), (sumRk R n) (x,y).
  Proof.
    have H3: R `<=` 'Δ `|` R by apply: subsetUr.
    rewrite RTclos_dec => -[/DeltaP -> | [n H1 H2]];first by (exists 0).
    by exists n; rewrite sumRk_compose2;apply: (iter_include H3).
  Qed.
  
  Lemma clos_rt_D_clos_t R: R.* = ('Δ `|` R).+.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => /clos_rt_sumRk [n +];rewrite sumRk_compose2.
      case H1: (n == 0).
    + move: H1 => /eqP ->; rewrite /= => H1.
      have H2: ('Δ `|` R) (x, y) by rewrite /setU;left.
      by apply: iter1_inc_clos_trans. 
    + move: H1 => /neq0_lt0n/prednK H1.
      pose proof (@iterk_inc_clos_trans ('Δ `|` R) (n.-1)%N) as H2.
      by move: H2; rewrite H1 => H2 /H2 H3.
    + move => /(@clos_t_iterk ('Δ `|` R) x y) [n H1].
      by move: H1; rewrite -sumRk_compose2 => /sumRk_inc_clos_refl_trans.
  Qed.
  
  Section WIP.
    Variables (R U: relation T).
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
      by rewrite 2!sumRk_kp1_l';apply/setUS/composeSl.
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
      have H2: R `;` R.* `<=` R.* by rewrite r_clos_rt_clos_t;apply: clos_t_clos_rt.
      have H3: R`;`sumRk' R U n `<=` R `;` R.* by apply: composeSl. 
      by apply: (union_inc_b Hr);apply: (subset_trans H3 H2).
    Qed.
    
    Local Lemma clos_rt_sumRk' (x y:T): 
      R.* (x, y) -> 'Δ (x,y) \/ exists (n:nat), (sumRk' R U n) (x,y).
    Proof.
      have H3: R `<=` U `|` R by apply: subsetUr.
      rewrite RTclos_dec => -[/DeltaP -> | [n H1 H2]];first by left. 
      have H5 : n.-1.+1 = n by apply: ltn_predK H1. 
      by right;(exists n);rewrite -H5 sumRk_compose2' H5;apply: (iter_include H3).
    Qed.
    
  End WIP.
  (* 
  Lemma Delta_n: forall (n: nat), ('Δ)^(n) = ('Δ : relation T). 
  Proof.
    elim => [| n Hr];first  by rewrite /iter.
    by rewrite -addn1 (iter_compose 'Δ n 1) Hr iter1_id Delta_idem_l.
  Qed.
  
  Lemma clos_rt_D_clos_t' R : R.* = ('Δ `|` R).+.
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
  *) 

  (** * Reflexive and Transitive Closure *)
  Lemma L1 R S: R.* `;` S.* = ('Δ `|` R.+) `;` ('Δ `|` S.+ ).
  Proof. by rewrite !DuT_eq_Tstar. Qed.
  
  Lemma L2 R S: R.* `;` S.* = 'Δ `|` R.+ `|` S.+ `|` (R.+ `;` S.+). 
  Proof.
    by rewrite -!DuT_eq_Tstar
         !composeDl !composeDr DsetK Delta_idem_l Delta_idem_r setUA.
  Qed.

  Lemma compose_rt_rt R: R.* `;` R.* = R.*. 
  Proof. by rewrite L2 -setUA clos_t_decomp_2 -setUA setUid DuT_eq_Tstar. Qed.

  (** * Foresets *)

  (* check that it coincide with usual definition *)
  Lemma AsetE  R Y: (Aset R Y) = [set x | exists (y: T), R (y,x) /\ Y y].
  Proof. by rewrite /Aset/Fset.  Qed.
  
  Lemma Fset_D X: 'Δ#X = X.
  Proof.
    rewrite /Fset predeqE => x;split =>[[x' [/DeltaP -> ?]] //| ?].
    by exists x;rewrite DeltaP.
  Qed.

  Lemma Fset_DE X Z: Δ_(Z)#X = Z `&` X.
  Proof.
    by rewrite /Fset/Delta predeqE /= => x;split => [[x' [[? <-] ?]] //| [? ?]];exists x.
  Qed.
  
  Lemma Fset_DCE X Y: Δ_(Y.^c)#X = X `\` Y.
  Proof.
    rewrite /Fset/Delta/setC predeqE /= => x;split;first by move => [x' [[? <-] ?]].
    by move => [? ?];exists x.
  Qed.
  
  Lemma Fset_inc R S X: R `<=` S -> R#X `<=` S#X.
  Proof.
    by move => H x [y [? ?]];by exists y;split;[apply: H |].
  Qed.
  
  Lemma Fset_inc1 R X Y: X `<=` Y -> R#X `<=` R#Y.
  Proof.
    by move => H x [y [? ?]];exists y;split;[|apply: H].
  Qed.
  
  Lemma set_inc2 X: forall (x: T), x \in X <->  [set x] `<=` X.
  Proof.
    move => x;split => [/set_mem ? y /= -> // |].
    by rewrite in_setE => H1; apply: H1. 
  Qed.
  
  Lemma Fset_comp R S X: S # (R # X) = (S `;` R) # X.
  Proof.
    rewrite /Fset /compose /Fset predeqE /=.
    move => x; split => [ [z [? [y [? ?]]]] | [ y [[z [? ?]] ?]]].
    by (exists y);split;[exists z;split|]. 
    by (exists z);split;[|exists y].
  Qed.
  
  Lemma Fset_union_rel R S X: S#X `|` R#X = (S `|` R) # X.
  Proof.
    rewrite /Fset /setU predeqE /= => x; split. 
    by move => [[y [? ?]] | [y [? ?]]];exists y;[split;[left|]|split;[right|]].
    by move => [y [[?|?] ?]];[left|right];exists y.
  Qed.
  
  Lemma Fset_union R X Y: R#(X `|` Y) = (R#X) `|` (R#Y).
  Proof.
    rewrite /Fset /setU predeqE /= => x; split. 
    by move => [z [? [?|?]]];[left|right];exists z.
    by move => [[y [? ?]]|[y [? ?]]];exists y;[split;[|left]|split;[|right]].
  Qed.

  Lemma FsetI R X Y: R#(X `&` Y) `<=` (R#X) `&` (R#Y).
  Proof.  by move => x [y [? [? ?]]];split;exists y. Qed.
  
  (* Foreset in extension *)
  Lemma Fset_union_set R Y: forall (x:T), (R#Y) x <-> exists y, Y y /\ R#_(y) x.
  Proof.
    move => x;rewrite /Fset /mkset /=.
    split => [[y [? ?]]|[y [? [z [? H3]]]]].
    by (exists y);split;[|exists y; split].
    by (exists z);split;[ |rewrite H3].
  Qed.

  Lemma Union_Setminus X Y: X `|` Y = X `|` (Y `\` X). 
  Proof.
    rewrite /setU /setD /mkset predeqE => x.
    by split => [[?|?]|[?|[? ?]]];
            [left|pose proof lem (X x) as [?|?];[left|right]|left|right].
  Qed.
  
  Lemma Fset_intersect R S: forall (x y:T), (exists z, R#_(x) z /\ S#_(y) z) <-> (R.-1 `;` S) (x,y). 
  Proof.
    rewrite /Fset /mkset => x y.
    split => [[z [[r [H1 H1']] [t [H2 H2']]]]|[z /= [? ?]]].
    have [-> <-]: x = r /\ t = y by [].
    by (exists z);split;[rewrite /inverse /=|].
    by (exists z);split;[exists x|exists y].
  Qed.
  
  Lemma Fset_singleton R: forall (x:T), reflexive R -> R#_(x) x. 
  Proof.
    by move => x H;rewrite /Fset /mkset;exists x.
  Qed.
  
  Lemma Fset_rt_singleton R: forall (x:T), R.*#_(x) x. 
  Proof.
    by move => x; exists x;split;[apply: RTclosR |].
  Qed.
  
  Lemma Fset_restrict R X Y : X `<=` Y -> R#X = (R `;` Δ_(Y))# X.
  Proof.
    rewrite /subset /Fset /compose /Delta /mkset predeqE /= => H x.
    split => [[y [H1 H2]]| [y [[z [H1 [_ <- ]]] H4]]];last by (exists z).
    by exists y;split;[exists y;split;[by [] |by split;[apply H|]]|]. 
  Qed.
  
  Lemma Fset_t0 R: forall (x y:T), R (x, y) <-> R#_(y) x. 
  Proof.
    by move => x y ; split => [H1 | [z [H1 /= <-]]];[exists y |].
  Qed.

  Lemma Fset_t1 R: forall (x y:T), R (x, y) -> R.+#_(y) x. 
  Proof.
    by move => x y H1;rewrite /Fset;exists y;split;[exists 1;[|rewrite iter1_id]|].
  Qed.
  
  Lemma Fset_t2 R: forall (x y:T), (exists (x1:T), R (x, x1) /\ R.+#_(y) x1) -> R.+#_(y) x. 
  Proof.
    move => x y' [x1 [H1 [y [[n /=H2' H2] <-]]]];exists y;split;last by exact. 
    have H3: R^(1+n) (x,y) by rewrite (iter_compose R 1 n) iter1_id;exists x1. 
    by exists (1+n). 
  Qed.
  
  Lemma Fset_t3 R: forall (x y z:T), R.+#_(y) x /\ R (y, z) -> R.+#_(z) x. 
  Proof.
    move => x y z [[t [[n /= H1' H1] /= <-]] H3].
    have H4: R^(n.+1) (x,z) by rewrite -addn1 (iter_compose R n 1) iter1_id;exists t. 
    by exists z;split;[exists (n.+1)|].
  Qed.
  
  Lemma Fset_t4 R: forall (y z:T), R (y, z) -> ( R.+#_(y) `<=` R.+#_(z) ).
  Proof.
    by move => y z ? x ?;apply Fset_t3 with y.
  Qed.

  Lemma Fset_t5 R: forall (y z:T), y \in R.+#_(z) -> (R.+#_(y) `<=` R.+#_(z) ).
  Proof.
    move => y z /inP H1 t;move:H1;rewrite -3!Fset_t0 => H1 H2.
    by apply: (TclosT H2 H1). 
  Qed.

  (** * Elements for Foreset Topology *)

  (** * Fset and bigcup *)
  Lemma Fset_bigcup R: forall (I: Type) (F : I -> set T),
      R#( \bigcup_ i (F i) ) =  \bigcup_ i (R# (F i)).
  Proof.
    move => I F;rewrite /Fset predeqE => x;split.
    by move => [y [H1 [n Pn Fny]]]; exists n;[ | exists y].
    by move => [n Pn [y [H1 H2]]];exists y;split;[|exists n].
  Qed.
  
  (** * Fset and bigcap *)
  Lemma Fset_bigcap R: forall (I: Type) (F : I -> set T),
      R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)).
  Proof.
    by move => I F x [y [H1 H2]];exists y; split;[| apply: H2]. 
  Qed.
  
  Lemma Fset_stableU R: forall (I: Type) (F : I -> set T),
      (forall i, R#(F i) `<=` (F i)) -> R#(\bigcup_ i (F i)) `<=` (\bigcup_ i (F i)).
  Proof.
    by move => I F H1;rewrite Fset_bigcup => x [n Pn Fn];exists n;[|apply: H1].
  Qed.

  Lemma Fset_stableI R: forall (I: Type) (F : I -> set T),
      (forall i, R#(F i) `<=` (F i)) -> R#(\bigcap_ i (F i)) `<=` (\bigcap_ i (F i)).
  Proof.
    move => I F H1. 
    have H2: (\bigcap_ i R#(F i)) `<=` (\bigcap_ i (F i))
      by move => x H2 i /H2/H1 H3.
    have H3: R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)) by apply:Fset_bigcap.
    by apply: (subset_trans H3 H2).
  Qed.
  
  Lemma Fset_stableIf R: forall (A B: set T),
      R#A  `<=` A -> R#B  `<=` B -> R#(A `&` B)  `<=` A   `&` B.
  Proof.
    move => A B ? ?.
    have H1: (R#A) `&`  (R#B)  `<=`  A   `&` B by apply: setISS.
    apply: (subset_trans _ H1); apply: FsetI.
  Qed.
  
  Lemma Fset_0 R: R#set0 `<=` set0.
  Proof. by move => x [y [_ H1]]. Qed.

  Lemma Fset_T R: R#setT `<=` setT.
  Proof.  by []. Qed.

  (** Elements for After set Topology *)
  
  Lemma Aset_bigcup R: forall (I: Type) (F : I -> set T),
      ( \bigcup_ i (F i) ):#R =  \bigcup_ i ((F i):#R).
  Proof.
    by move => I F;apply: Fset_bigcup.
  Qed.

  Lemma Aset_bigcap R: forall (I: Type) (F : I -> set T),
      (\bigcap_ i (F i)):#R `<=`  \bigcap_ i ((F i):#R).
  Proof.
    by move => I F;apply: Fset_bigcap.
  Qed.

  Lemma Aset_stableU R: forall (I: Type) (F : I -> set T),
      (forall i, (F i):#R `<=` (F i)) -> (\bigcup_ i (F i)):#R `<=` (\bigcup_ i (F i)).
  Proof.
    by move => I F H1;apply: Fset_stableU.
  Qed.

  Lemma Aset_stableI R: forall (I: Type) (F : I -> set T),
      (forall i, (F i):#R `<=` (F i)) -> (\bigcap_ i (F i)):#R `<=` (\bigcap_ i (F i)).
  Proof.
    by move => I F H1;apply: Fset_stableI.
  Qed.
  
  Lemma Aset_stableIf R: forall (A B: set T),
      A:#R `<=` A -> B:#R `<=` B -> (A `&` B):#R  `<=` A `&` B.
  Proof.
    by move => A B ? ?;apply: Fset_stableIf.
  Qed.
  
  Lemma Aset_0 R: set0:#R `<=` set0.
  Proof. by move => x [y [_ H1]]. Qed.
  
  Lemma Aset_T R: setT:#R `<=` setT.
  Proof. by []. Qed.

  (** Closures *) 
  
  Lemma Clos_x_x R X: forall (x:T), Clos_(x | R, X) x.
  Proof. by move => x;exists x;split;[apply RTclosR|]. Qed.
  
  Lemma Clos_Ew E W: forall (x y: T),  Clos_(x | E,W) y <-> (Δ_(W.^c) `;` E).* (y, x).
  Proof.
    move => x' y';split;first by move => [z [?  <-]].
    by move => ?;exists x';split.
  Qed.
  
  Lemma Clos_to_singleton E W : forall (X: set T) (x:T),
      Clos(X | E, W) x <-> exists y, X y /\ Clos_(y |E ,W) x.
  Proof.
    by split; rewrite Fset_union_set.
  Qed.    
  
  Lemma Clos_union E W : forall (X Y: set T),
      Clos(X `|` Y| E,W) = Clos(X| E,W) `|` Clos(Y| E,W).
  Proof.
    by move => X Y; rewrite Fset_union.
  Qed.
  
  Lemma Clos_s_inc E W : forall (X Y: set T) (x:T),
      X x -> Clos_(x| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    move => X Y x' /inP/set_inc2 H1.
    have H2:  Clos_(x'|E,W) `<=` Clos(X | E,W) 
      by apply Fset_inc1.
    have H3:  Clos(X|E,W) `<=` Clos(X `|` Y|E,W)
      by apply Fset_inc1; apply subsetUl.
    by apply subset_trans with Clos(X|E,W).
  Qed.
  
  Lemma Clos_inc_l E W : forall (X Y: set T),
      Clos(X| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    by move => X Y x; rewrite Clos_union; left.
  Qed.    
  
  Lemma Clos_inc_r E W : forall (X Y: set T),
      Clos(X| E,W) `<=` Clos(Y `|` X| E,W).
  Proof.
    by move => X Y x; rewrite Clos_union; right.
  Qed.    
  
  Lemma Clos_contains E W : forall (X: set T),
      X `<=` W -> X `<=` Clos(X| E,W).
  Proof.
    by move => X ? x ?;rewrite /Fset /mkset;exists x;split;[apply RTclosR|].
  Qed.    

  Lemma ClosU_containsl E W : forall (X Y: set T),
      X `<=` W -> X `<=` Clos(X `|` Y | E,W).
  Proof.
    move => X Y H0.
    have H2: X `<=` Clos( X | E,W)  by apply:Clos_contains.
    by apply: (subset_trans H2);apply: Clos_inc_l.
  Qed.

  Lemma ClosU_containsr E W : forall (X Y: set T),
      Y `<=` W -> Y `<=` Clos(X `|` Y | E,W).
  Proof.
    move => X Y H0.
    have H2: Y `<=` Clos( Y | E,W)  by apply:Clos_contains.
    by apply: (subset_trans H2);apply: Clos_inc_r.
  Qed.
  
  Lemma E30 R X Y: 'Δ#X `|` R#Y = 'Δ#X `|` (Δ_(X.^c) `;` R)#Y.
  Proof.
    by  rewrite Fset_D Union_Setminus -Fset_DCE Fset_comp.
  Qed.
  
  Lemma Fset_n R Y: forall (n : nat), (sumRk R n)#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
  Proof.
    move => n x H.
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

  Lemma Fset_rt R Y: (Δ_(Y.^c) `;` R).*#Y = R.*#Y.
  Proof.
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
  
  (** Restriction on Relation *)

  Definition Restrict (T:Type) (R: relation T) (X: set T) := 
    [ set x | X x.1 /\ X x.2 /\ R x].
  
  Lemma Rest X R: (Restrict R X) = Δ_(X) `;` R `;` Δ_(X).
  Proof.
    rewrite predeqE => [[x y]].
    split => [[/= H1 [H2 H3]] | [z [[t [[/= H1 H'1] H2]] [/= H3 H'3]]]].
    by (exists y;split;[ exists x;split | ]).
    by split; [ | split; [rewrite -H'3 | rewrite H'1 -H'3]].
  Qed.

  (* reflexive and transitive properties using relation equalities *)
  
  Lemma clos_r_iff R: reflexive R <-> R ='Δ  `|` R.
  Proof.
    split => [? | ->];last by move => ?;left.
    by rewrite eqEsubset;split =>[[? ?]|[? ?]];[move=> ?;right | move => [/DeltaP -> | ?]].
  Qed.


  Lemma clos_tn_iff R: forall (n: nat), transitive R -> R^(n.+1) `<=` R.
  Proof.
    move => n H1.
    elim: n.
    - by rewrite iter1_id.
    - move => n H2.
      rewrite -addn1 iter_compose iter1_id => -[x y] -[z [/H2 /= H3 /= H4]].
      by apply: (H1 x z _). 
  Qed.
  
  (** XXXX A simplifier une partie vient du fait que R.+ est le smallest *)
  Lemma clos_t_iff R: transitive R <-> R = R.+.
  Proof.
    split => [H0 | ->];
            last by move => x y z ? ?; rewrite -clos_t_decomp_2;right;exists y.
    rewrite eqEsubset;split;first by apply: iter1_inc_clos_trans.
    by move => [x y] /clos_t_iterk [n H2];apply: (clos_tn_iff H0 H2).
  Qed.

  Lemma clos_rt_iff R: (reflexive R /\  transitive R) <-> R = R.*.
  Proof.
    rewrite -DuT_eq_Tstar.
    split => [ [/clos_r_iff H1 /clos_t_iff H2] | H1];first by rewrite -H2 -H1.
    split; first  by rewrite H1;left;rewrite DeltaP.
    by rewrite H1 => x y z [/DeltaP H2 |H2] [/DeltaP H3| H3];
                 [rewrite H2 -H3; left | rewrite H2; right 
                 | rewrite -H3;right |right;apply: (TclosT H2 H3)].
  Qed.
  
  (** * Asymmetric part of a relation *) 
  
  Definition Asym (R: relation T): relation T := [set xy | R xy /\ ~ (R.-1 xy)].
  
  Lemma Asym_antisymmetric R: antisymmetric  (Asym R).
  Proof. by move => x y [_ ?] [? _]. Qed.

  Lemma Asym_irreflexive R: irreflexive (Asym R).
  Proof. by move => x [? ?]. Qed.

  Lemma Asym_asymmetric R: asymmetric (Asym R). 
  Proof. by rewrite (irP (@Asym_irreflexive R));apply: Asym_antisymmetric. Qed.
  
  Lemma Asym_preserve_transitivity R: transitive R -> transitive (Asym R).
  Proof.
    move => H0 x y z [H1 /= H1'] [H2 /= H2'];split => [ | /= H3].
    by apply: H0 H1 H2.
    by have: R (y,x) by apply: H0 H2 H3.
  Qed.
  
  Lemma AsymE R: antisymmetric R /\ irreflexive R <-> Asym R = R.
  Proof.
    split; last by move => <-;split;
                          [apply: Asym_antisymmetric | apply: Asym_irreflexive].
    move => [H1 H2].
    rewrite predeqE => [[x y]]; split => [[H3 _] // | H3]. 
    split; first by [].
    by move: H3 => /[dup] H3 /H1 H3' /H3' H4; move: H3; rewrite H4 => /H2 H3.
  Qed.

  Lemma AsymI R: forall (R: relation T), Asym R `<=` R.
  Proof. by move => R' [a b] [? _]. Qed.

  Lemma AsymInvol R: Asym (Asym R) = (Asym R).
  Proof.
    rewrite predeqE => [[a b]];split => [[? _] //| H1]. 
    split => [// | H2];pose proof (Asym_antisymmetric H1 H2) as H3.
    by move: H1;rewrite H3;apply: Asym_irreflexive.
  Qed.
  
  Lemma AsymIncl R: R.+ `;` Asym(R.+) `<=`  Asym(R.+).
  Proof.
    move: AsymI => /(_ R.+) H3 => [[x y] [z /= [H1 /[dup] H2 /H3 H4]]].
    split =>[| H5]; first by apply: (TclosT H1 H4).
    have H6: R.+ (y,z) by apply: (TclosT H5 H1).
    by move: H2 => [_ H2].
  Qed.
    
  Lemma AsymIncr R: Asym(R.+) `;` R.+ `<=`  Asym(R.+).
  Proof.
    move: AsymI => /(_ R.+) H3 => [[x y] [z /= [/[dup] H2 /H3 H4 H1]]].
    split =>[| H5]; first by apply: (TclosT H4 H1).
    have H6: R.+ (z,x) by apply: (TclosT H1 H5).
    by move: H2 => [_ H2 ].
  Qed.

  (** * Independent sets with respect to a relation *)
  
  Lemma RelIndep_I R S X: R `<=` S -> RelIndep S X -> RelIndep R X.
  Proof. by move => H1 H2 x y H3 H4 H5;move: (H2 x y H3 H4 H5) => ? /H1 ?. Qed.
  
  Lemma RelIndep_set0 R: RelIndep R set0.
  Proof. by move => x y /inP H3 _ _ _. Qed.
  
  Lemma RelIndep_set1 R: forall (x: T), RelIndep R [set x].
  Proof. by move => x x1 x2 /inP -> /inP -> H4. Qed.
  
  Lemma RelIndep_U R: forall X x,
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
  
  (** * Partition induced by and Equivalence Relation *)
  
  (* Définition de la classe d'équivalence de x *)
  Definition class_of R (x : T) := [set y: T| R (x,y)].

  Definition Quotient R := {E : set T| exists x : T, E = class_of R x }.

  (* Ensemble des classes d'équivalence (possiblement avec répétitions) *)
  Definition Classes R:= [set C | exists x:T, C = class_of R x].
  
  (* Lemme 1 : Chaque classe est non vide *)
  Lemma classe_non_vide R: equivalence R -> forall C, Classes R C -> (C != set0).
  Proof. move => [R_ref _ _ ] C -[x0 ->];rewrite -notempty_exists;exists x0; apply/inP. exact. Qed.
         
  (* Lemme 2 : Deux classes sont égales ou disjointes *)
  Lemma classes_disjointes_ou_egales R: equivalence R ->
    forall (x y : T), (exists z : T, R (x,z) /\ R (y,z)) -> class_of R x = class_of R y.
  Proof.
    move => [R_ref R_tr R_sy] x y [z [H1 H2]].
    rewrite predeqE;move => x0;split.
    + rewrite/class_of/mkset => H3.
      by pose proof (R_tr y x x0 (R_tr y z x H2 (R_sy x z H1)) H3).
    + rewrite/class_of/mkset => H3.
      by pose proof (R_tr x y x0 (R_tr x z y H1 (R_sy y z H2)) H3).
  Qed.

  (* Lemme 3 : Toute l'union des classes couvre T *)
  Lemma union_classes_couvre_E R: equivalence R -> forall x : T, exists C : set T, Classes R C /\ C x.
  Proof.
    move => [R_ref _ _] x; exists (class_of R x).
    by split;[rewrite /Classes/mkset;exists x;exact| rewrite /class_of/mkset].
  Qed.

  Lemma ER_union R:  equivalence R -> \bigcup_ (C in (Classes R)) (fun C  => C) C = setT.
  Proof.
    move => He;rewrite predeqE => x;split => [// | _].
    by move: (union_classes_couvre_E He x) => [C [H1 H2]];  exists C.
  Qed.

  Lemma ER_empty R (C C': set T): equivalence R ->
    C \in Classes R -> C' \in Classes R -> (exists z, C z /\ C' z) -> C = C'.
  Proof.
    move => He /inP [x ->] /inP [x' ->] [z H1].
    by apply: ((classes_disjointes_ou_egales He) x x');exists z.
  Qed.
  
  Lemma ER_check (C C': set T):
    (C `&` C') != set0 <-> exists z, C z /\ C' z.
  Proof.
    split. 
    by move => /notempty_exists [z /inP [H1 H2]];exists z.
    by move => [z [H1 H2]];apply/notempty_exists;exists z;apply/inP. 
  Qed.

End Relation_Facts.
