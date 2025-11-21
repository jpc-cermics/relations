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
(* R^-1        : inverse of the relation R  R^-1 (x,y) <-> R (y,x)            *)
(* R `;` S     : composition: (R `;` S) (x,y) <-> exists z, R (x,z) /\ S (z,y)*)
(* Δ_(X)       : diagonal relation on subset  X                               *)
(* 'Δ          : diagonal relation on setT  'Δ = Δ_(setT)                     *)
(* 'Δc         : diagonal relation on set0  'Δ = Δ_(set0)                     *)
(* L_(X)       : relation (X x setT)                                          *)
(* R_(X)       : relation (setT x X)                                          *)
(* R^(n)       : n-iterate of composition                                     *) 
(* X.^c        : complementary (~` X)                                         *)
(* R.+         : transitive closure of R                                      *)
(* R.*         : reflexive transitive closure of R                            *)
(* R#Y         : Foreset of the subset Y by relation R                        *)
(* R#_(y)      : Foreset of the subset [set y] by relation R                  *)
(* Y:#R        : Afterset of the subset Y by relation R                       *)
(* y_:#R       : Afterset of the subset [set y] by relation R                 *)
(* Clos(Y|R,W) : closure of Y for the relation Δ_(W.^c) `;` R                 *)
(* Clos_(y|R,W): closure of [set y] for the relation Δ_(W.^c) `;` R           *)
(* Restrict'   : from relation T to relation X where X is a set T             *)
(*               [set xy : X*X | R ((sval xy.1),(sval xy.2))].                *)
(* Partition induced by and Equivalence Relation                              *)
(* Asym        : Asymmetric part of a relation, [set xy | R xy /\ ~ (R^-1 xy)] *)
(* Independent sets with respect to a relation                                *)
(******************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot order. 
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
Definition inverse (T: Type) (R: relation T) : relation T := [set x | R (x.2,x.1)].
(* end snippet Sthree *)  

(* Notation "R .-1" := (@inverse _ R) : classical_set_scope. *)
Notation "R ^-1" := (@inverse _ R) : classical_set_scope.
Definition compose T (R S: relation T) : relation T := [set x | exists (z: T), R (x.1,z) /\ S (z,x.2)].
Notation "R `;` U" := 
  (@compose _ R U) (at level 51, left associativity, format "R `;` U").

Definition Delta T X: relation T := [set x | X x.1 /\ x.1 = x.2].

Notation "'Δ" := (Delta setT) (at level 2, no associativity).

Definition DeltaC T X: relation T := Delta (~` X).
Definition Lr T X: relation T := [set x | X x.1].
Definition Rr T X: relation T := [set x | X x.2].

Definition iter (T: Type) (R: relation T) S n : relation T:=
  let fix loop m := if m is i.+1 then (loop i) `;` R else S in loop n.

Definition Tclos T (R: relation T): relation T := \bigcup_ (n >= 1) (iter R 'Δ n).

Definition RTclos T (R: relation T): relation T := \bigcup_ n (iter R 'Δ n).

Definition Fset T (R: relation T) X : set T := [set x | exists (y: T), R (x,y) /\ X y].
Definition Aset T (R: relation T) X : set T :=  Fset R^-1 X. 

(* begin snippet RelIndep:: no-out *)    
Definition RelIndep (T:Type) (R: relation T) (S: set T) :=
  forall (x y:T),  x \in S -> y \in S -> ~(x = y) -> ~( R (x,y)).
(* end snippet RelIndep *)    

(* possible Corecion of relation T to rel T *)
Definition R2rel (T: Type) (R: relation T) : rel T := (fun x y => ((x,y) \in R)).
Global Coercion R2rel : relation >-> rel.

Notation "Δ_( X )" := (@Delta _ X) 
                        (at level 2, no associativity, format "Δ_( X )").
Notation "L_( X )" := (@Lr _ X)
                        (at level 2, no associativity, format "L_( X )").
Notation "R_( X )" := (@Rr _ X)
                        (at level 2, no associativity, format "R_( X )").
Notation "X .^c" := (~` X) 
                      (at level 2, right associativity, format "X .^c").

Notation "'Δc" := (DeltaC setT) (at level 2, no associativity).
Notation "R ^( n )" := (@iter _ R 'Δ n) 
                         (at level 2, right associativity, format "R ^( n )").
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

Notation "R |_( X )" := (Δ_(X) `;` R `;` Δ_(X))
                       (at level 3, no associativity, format "R |_( X )").

Section Relation_Facts.
  
  Context (T : Type).
  Implicit Types (T : Type) (R S U: relation T) (X Y: set T).

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
  
  Lemma union_inc_b (R S U:relation T): S `<=` U -> R `<=` U -> (S `|` R) `<=` U.
  Proof. by move => H1 H2;(have <- : U `|` R = U by apply setUidPl);apply setSU. Qed.

  Lemma Union_Setminus X Y: X `|` Y = X `|` (Y `\` X). 
  Proof.
    rewrite /setU /setD /mkset predeqE => x.
    by split => [[?|?]|[?|[? ?]]];
            [left|pose proof lem (X x) as [?|?];[left|right]|left|right].
  Qed.
  
  (** *  Inverse of a relation *)
  
  (**  R^-1^-1 = R *)
  Lemma inverseK: involutive (@inverse T). 
  Proof. by move => R; rewrite predeqE /= => -[x y]. Qed.
  
  Lemma inverse_sym R: R^-1 = R <-> symmetric R.
  Proof. by rewrite predeqE;split => [H0 x y /H0 //|H1 [x y]];split;apply H1. Qed.
  
  Lemma inverseE R S: R = S <-> R^-1 = S^-1.
  Proof. by split =>[->//| H1];rewrite -[R]inverseK -[S]inverseK H1. Qed.
  
  Lemma inverseU R S: (R `|` S)^-1 = R^-1 `|` S^-1.
  Proof. by rewrite /predeqE. Qed.

  Lemma inverseS R S: R `<=` S -> R^-1 `<=` S^-1. 
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
  
  Lemma composeIv  R S: (R `;` S)^-1 = S^-1 `;` R^-1.
  Proof. by rewrite predeqE => x;split;move => [z [? ?]];exists z;split. Qed.

  Lemma RRm_sym R:  symmetric (R `;` R^-1).
  Proof. by move => x y [z [H1 H2]];exists z;split;[apply: H2|apply: H1]. Qed.
  
  Lemma RRm_inverse R: (R `;` R^-1)^-1 = R `;` R^-1.
  Proof. by apply/inverse_sym/RRm_sym. Qed. 

  (** * Delta_(X) *)
 
  Lemma DsetE X (x y:T): Δ_(X) (x,y) <-> X x /\ x = y.
  Proof. exact. Qed.
    
  Lemma Dset_sym X:  symmetric Δ_(X).
  Proof. by move => x y [+ /= <-] => /= H1;split. Qed.
  
  Lemma Dset_trans X: transitive Δ_(X).
  Proof. by move => x y z [/= ? H2] [? H4];split;[|rewrite H2 H4]. Qed.
  
  Lemma DsetS X Y: X `<=` Y -> Δ_(X) `<=` Δ_(Y).
  Proof. by move =>  H [x y] [H1 /= <-];split;[apply: H|]. Qed.

  Lemma DsetC X Y: Δ_(X) `;` Δ_(Y) = Δ_(X `&` Y).
  Proof. by rewrite predeqE
         => -[x y];split=>[[z [[? /= <-][? /= <-]]]|[[? ?] /= <-]];[|exists x]. Qed.
  
  Lemma DsetK X:  Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof. by rewrite DsetC setIid. Qed.

  Lemma DsetIv X: Δ_(X)^-1 = Δ_(X). 
  Proof. by rewrite predeqE /inverse => -[x y] /=;split;move => [H1 /= <-]. Qed.

  Lemma DsetU X Y: Δ_(X) `|` Δ_(Y) = Δ_(X `|` Y).
  Proof.
    rewrite predeqE => -[x y];split;last by  move => [[? | ?] /= <-];[left|right].
    by move => [|] [/= ? /= <-];apply/DsetE;split;[left| |right| ].
  Qed.
  
  (** * Delta relation  *)
  
  Lemma DeltaP (x y: T): 'Δ (x,y) <-> x = y.
  Proof. by split => [[_ ? //]| ->]. Qed.

  Lemma DeltaS X: Δ_(X) `<=` 'Δ.
  Proof. by apply: DsetS. Qed.
  
  Lemma DeltaIv: 'Δ^-1 = ('Δ : relation T).
  Proof. by apply:  DsetIv. Qed.

  (* 'Δ `;` R = R.  *)
  Lemma DeltaCl: left_id 'Δ (@compose T). 
  Proof. by move => R;rewrite predeqE => -[x y];split=> [[z [/DeltaP <- ?]] //| ?];exists x;split. Qed.
  
  (* R `;` 'Δ = R.   *)
  Lemma DeltaCr: right_id 'Δ (@compose T). 
  Proof. by move => R;rewrite predeqE => -[x y];split => [[z [? /DeltaP /= <-]]// | ?];exists y;split.  Qed.
  
  Lemma DeltaLco X R: Δ_(X) `;` R = L_(X) `&` R.
  Proof. by rewrite predeqE /= => [[x y]] /=;split => [[z [[? /= <-] ?]]|[? ?]];[|exists x].  Qed.

  Lemma DeltaRco X R: R `;` Δ_(X) = R `&` R_(X).
  Proof. by rewrite  predeqE /= => [[x y]] /=;split => [[z [? [? /= <-]]]|[? ?]];[|exists y]. Qed.

  Lemma Delta0: Δ_(set0) = ('Δc: relation T).
  Proof. by rewrite predeqE => -[x y];split => [/DsetE [? _] | [/= ? _]]. Qed.
  
  Lemma DeltaCc X: Δ_(X) `;` Δ_(X.^c) = 'Δc.
  Proof.
    rewrite predeqE -Delta0=> -[x y];split.
    by move => [z [/DsetE [? <-] /DsetE [? _]] //].
    by move => /DsetE [? _].
  Qed.
  
  Lemma DeltacC X: Δ_(X.^c) `;` Δ_(X) = 'Δc.
  Proof. by rewrite DsetC setIC -setDE setDv Delta0. Qed.
  
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
  
  Lemma DeltaCsubset R X: (Δ_(X) `;` R `<=` R).
  Proof. by move => -[x y] /= => [[z [[_ /= <-] ?]]]. Qed.
  
  Lemma DeltaCsubsetl R X: (R `;` Δ_(X) `<=` R).
  Proof. by move => -[x y] /= => [[z [H2 [_ /= <-]]]]. Qed.
    
  (** * Composition iteration *)
  
  Lemma iter1_id R: R^(1) = R.
  Proof. by rewrite /iter DeltaCl. Qed.

  Lemma iter_compose1r R n: R^(n.+1) = R^(n) `;` R.
  Proof. by elim: n => [//|n ?]. Qed.
  
  Lemma iter_compose R n1 n2: R^(n1 + n2) = R^(n1) `;` R^(n2).
  Proof.
    elim: n2 n1 => [n1| n1 H n0];first by rewrite addn0  DeltaCr.
    by rewrite [addn n0 n1.+1]addnS iter_compose1r H composeA -iter_compose1r.
  Qed.

  Lemma iter_compose1l R n: R^(n.+1) = R `;` R^(n).
  Proof. by rewrite -addn1 addnC (iter_compose R 1 n) iter1_id. Qed.
  
  Lemma iter_delta (n: nat): 'Δ^(n) = ('Δ :relation T).
  Proof. 
    by elim: n => [//|n Hr];rewrite -addn1 (iter_compose 'Δ n 1)
                                      Hr iter1_id DeltaCl.
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
  
  Lemma inverse_iter R (n: nat) : R^(n)^-1 = (R^-1)^(n).
  Proof.
    elim: n =>[| n H1];first  by rewrite /iter DsetIv.
    by rewrite -addn1 (iter_compose R n 1) composeIv
                  addnC (iter_compose R^-1 1 n) H1 !iter1_id. 
  Qed.
  
  Lemma iter_C R (n:nat): R^(n) `;` R = R `;` R^(n).
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
    rewrite -{1}addn1 (iter_compose ('Δ `|` R) n 1) iter1_id composeDl DeltaCr.
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
    by rewrite -addn1 addnC (iter_compose (Δ_(X)`;`R) 1 n) -[in RHS]composeA -H1.
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
  
  Lemma Tclos_r R S:  R.+ `;` S = \bigcup_ (n >= 1) R^(n) `;` S.
  Proof. by rewrite -bigcupC. Qed.
  
  Lemma Tclos_in R S: transitive S -> R `<=` S -> R.+ `<=` S.
  Proof. by move => Ht H1 [x y] [n /= H2];move: (iter_subset Ht H1 H2) => H3 /H3 ?. Qed.
  
  Lemma clos_t_iterk R (x y:T): R.+ (x,y) -> exists (n:nat), R^(n.+1) (x,y).
  Proof.
    by move => [n H1 ?];exists (n.-1);have ->: n.-1.+1 = n by apply: ltn_predK H1. 
  Qed.
  
  Lemma TclosT R: transitive R.+.
  Proof. by move => x y z /clos_t_iterk [n1 H1] /clos_t_iterk [n2 H2];
                   exists (n1.+1 + n2.+1);[|rewrite iter_compose;exists y].
  Qed.
  
  Lemma TclosS R S: R `<=` S -> R.+ `<=` S.+ .
  Proof. 
    by move => H1 xy [n /= H2 H3];(exists n);[|apply: (@iter_include R S n H1)]. Qed.
  
  Lemma TclosSu R: R `<=` R.+.
  Proof. by move => [x y] ?;exists 1;[| rewrite iter1_id]. Qed.
  
  (* mathematical def of closure 
     smallest [set S | transitive S] R
     is also \bigcap_(S in [set S | transitive S /\ R `<=` S]) S *)
  
  Lemma TclosE R: R.+ = smallest [set S | transitive S] R. 
  Proof.
    rewrite predeqE => -[x y];split => [[n /= H1 H2 S' [H3 H4]]|].
    by move: (iter_subset H3 H4) => H5;move: (H5 n H1) H2 => H6 /H6 H2.
    by apply: (@smallest_sub _ transitive _ R.+ (@TclosT _) (@TclosSu _)). 
  Qed.

  Lemma iterk_inc_clos_trans R: forall (n : nat), R^(n.+1) `<=` R.+.
  Proof. by move => n xy H1;exists n.+1. Qed.
  

  Lemma clos_t_iterk' R (x y:T): (exists (n:nat), R^(n.+1) (x,y)) -> R.+ (x,y).
  Proof. by move => [n H1];apply: (@iterk_inc_clos_trans R n). Qed.
  
  Lemma TclosIv R: R.+^-1 = R^-1.+ .
  Proof.
    rewrite predeqE => -[x y] /=;split => [[n ? ?]| [n H1]].
    by (exists n);[ exact|rewrite -inverse_iter].
    by rewrite -inverse_iter => ?;exists n.
  Qed.
  
  Lemma clos_t_sym R: symmetric R -> symmetric R.+.
  Proof. by move => Hs x y [n /= H1 /(iter_sym Hs) H2];exists n. Qed.

  Lemma iter1_inc_clos_trans R: R `<=` R.+.
  Proof. by move => xy H1;exists 1;[ | rewrite iter1_id]. Qed.
  
  
  Lemma clos_t_sep_n R: forall (n: nat) (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R^(n.+1) (x, y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x',y')).
  Proof.
    move => n x y W.
    elim: n x y => [x y [H1 [H2 H3]] | n H0 y y' ].
    by exists x; exists y; rewrite /iter DeltaCl in H3.
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
  
  Lemma clos_trans_inc (Z V U W: relation T):
    (forall (n:nat), Z `;` (V^(n.+1)) `;` U = Z `;` (W^(n.+1)) `;` U) 
    -> Z `;` V.+ `;` U `<=` Z `;` W.+ `;` U.
  Proof.
    move => H0 [x y] [z [[t /=[H1 [n H2 H3]]] /=H4]].
    move: H0 => /(_ (n.-1));(have ->: n.-1.+1 = n by apply: ltn_predK H2);move => H0.
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
      apply: (union_inc_b (@TclosSu _) (@clos_t_composer _)).
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

  Lemma RTclos_in R S: transitive S -> reflexive S -> R `<=` S -> R.* `<=` S.
  Proof.
    move => Ht Hr H1 [x y] [n _]. 
    case H2: (n == 0);first by move: H2 => /eqP -> /DeltaP ->.
    by move: H2 => /neq0_lt0n H2;move: (iter_subset Ht H1 H2) => H3 /H3 ?.
  Qed.
  
  Lemma RTclosT R: transitive R.*.
  Proof.
    rewrite RTclosE => x y z [/DeltaP -> //| /clos_t_iterk [n1 H1]].
    move => [/DeltaP <- //|/clos_t_iterk [n2 H2]];first by right;(exists n1.+1).
    by right;exists (n1.+1 + n2.+1);[exact|rewrite iter_compose;exists y].
  Qed.
  
  Lemma RTclosR R: reflexive R.*.
  Proof. by rewrite RTclosE; move => x; left. Qed.
  
  Lemma RTclosSu R: R `<=` R.*.
  Proof. by rewrite RTclosE;move => [x y] ?;right;exists 1;[|rewrite iter1_id]. Qed.
  
  (* coincide with mathematical def of closure  *)
  Lemma RTclos_smallest R: R.* = smallest [set S | reflexive S /\ transitive S] R. 
  Proof.
    rewrite RTclosE eqEsubset;split; first by 
      move => -[x y] [/DeltaP -> //| /clos_t_iterk [n H2]] S' [[H3 H3'] H4];
             [|apply: (@iter_subset R S' H3' H4 n.+1)].
    rewrite -RTclosE; move => -[x y] H2.
      have: [set S | (reflexive S /\ transitive S) /\ R `<=` S] R.*
        by split;[split;[apply: RTclosR|apply: RTclosT]|apply: RTclosSu].
      by move => /H2.
  Qed.
  
  Lemma RTclosIv R: R.*^-1 = R^-1.* .
  Proof. by rewrite 2!RTclosE inverseU TclosIv DeltaIv. Qed.
  
  Lemma RTclos_containsD R X: Δ_(X) `<=` R.* .
  Proof. by rewrite RTclosE;apply: subset_trans;[apply: DeltaS|apply: subsetUl].  Qed.
  
  Lemma clos_t_clos_rt R: R.+ `<=` R.*.
  Proof. by rewrite RTclosE;apply: subsetUr. Qed.
  
  Lemma clos_refl_trans_inc R S: R `<=` S -> R.* `<=` S.*.
  Proof. by move => H1;rewrite 2!RTclosE;apply/setUS/TclosS. Qed.
  
  Lemma DuT_eq_Tstar R:  'Δ `|` R.+ = R.*.  
  Proof. by rewrite RTclosE. Qed.
  
  Lemma r_clos_rt_clos_t R: R `;` R.* = R.+.
  Proof. by rewrite -DuT_eq_Tstar composeDl DeltaCr clos_t_decomp_rt. Qed.
  
  Lemma clos_rt_r_clos_t R: R.* `;` R = R.+.
  Proof. by rewrite -DuT_eq_Tstar composeDr DeltaCl clos_t_decomp_rt_r. Qed.
    
  Definition iterU (T: Type) (R: relation T) n : relation T := [set xy | exists k, k < n.+1 /\ R^(k) xy].
  
  Lemma iterU0 R: iterU R 0 = 'Δ.
  Proof. by rewrite predeqE => -[x y];split => [[k] |/DeltaP ->];[rewrite ltnS leqn0 => -[/eqP -> H1]|exists 0]. Qed.

  Lemma iterU_split R n: iterU R (n.+1) = 'Δ `|`  (R `;` (iterU R n)).
  Proof. 
    rewrite predeqE => -[x y]. split.
    + move => [k [H1 H2]].
      case H3: (k == 0). move: H3 => /eqP H3. rewrite H3 in H2. by left.
      move: H3 => /neq0_lt0n H3.
      have H4: k.-1.+1 = k by apply: ltn_predK H3. 
      move: H2; rewrite -H4 iter_compose1l.
      move => [z [H5 H6]].
      right. exists z. split. by [].
      by (exists k.-1); split;[rewrite -H4 in H1|].
    + move => [H1 | [z [H1 [k [H2 H3]]]]];first by ( exists 0).
      by exists k.+1;split;[| rewrite iter_compose1l;exists z].
  Qed.
  
  Lemma iterU_inc_clos_refl_trans R: forall (n : nat), (iterU R n) `<=` R.*.
  Proof.
    elim => [|n Hr];first by rewrite iterU0 => [[x y] ?];exists 0.
    rewrite iterU_split  RTclosE;apply: setUS;move => -[x y] [z [? /Hr]].
    by rewrite RTclosE => -[/DeltaP /= <- | H2];[apply: TclosSu| apply: clos_t_composer;exists z].
  Qed.
  
  Lemma clos_rt_iterU R (x y:T): R.* (x, y) -> exists (n:nat), (iterU R n) (x,y).
  Proof. by rewrite RTclosE => -[/DeltaP -> | [n H1 H2]];[(exists 0);rewrite iterU0| exists n;exists n].
  Qed.

  (* transitive (reflexive closure) = (reflexive (transitive closure)) *)
  Lemma Rclos_Tclos R: 'Δ `|` R.+ = ('Δ `|` R).+.
  Proof. 
    have H0: R `<=` 'Δ `|` R by apply: subsetUr.
    have H1: 'Δ `<=` 'Δ `|` R by apply: subsetUl.
    have H2: 'Δ `|` R `<=` ('Δ `|` R).+  by apply: TclosSu.
    have H3: R `<=`  ('Δ `|` R).+ by apply: (subset_trans  H0 H2).
    have H4: 'Δ  `<=`  ('Δ `|` R).+ by apply: (subset_trans  H1 H2).
    have H5: reflexive ('Δ `|` R).+. move =>x; have: 'Δ (x,x) by [];apply:H4.
    have H6: transitive ('Δ `|` R).+ by apply: TclosT.
    have H8:'Δ `|` R `<=` ('Δ `|` R.+) by apply: setUS;apply: TclosSu.
    have H7: transitive ('Δ `|` R.+) by rewrite -RTclosE;apply: RTclosT.
    rewrite eqEsubset;split.
    + by rewrite -RTclosE RTclos_smallest;apply: @smallest_sub. 
    + by rewrite TclosE;apply: @smallest_sub.
  Qed.

  (** * Reflexive and Transitive Closure *)
  Lemma L1 R S: R.* `;` S.* = ('Δ `|` R.+) `;` ('Δ `|` S.+ ).
  Proof. by rewrite !DuT_eq_Tstar. Qed.
  
  Lemma L2 R S: R.* `;` S.* = 'Δ `|` R.+ `|` S.+ `|` (R.+ `;` S.+). 
  Proof.
    by rewrite -!DuT_eq_Tstar
         !composeDl !composeDr DsetK DeltaCl DeltaCr setUA.
  Qed.

  Lemma compose_rt_rt R: R.* `;` R.* = R.*. 
  Proof. by rewrite L2 -setUA clos_t_decomp_2 -setUA setUid DuT_eq_Tstar. Qed.

  (** * Foresets *)
  
  Lemma Fset_D X: 'Δ#X = X.
  Proof. by rewrite predeqE => x;split =>[[x' [/DeltaP -> ?]] //| ?];exists x;rewrite DeltaP. Qed.
  
  Lemma Fset_DE X Z: Δ_(Z)#X = Z `&` X.
  Proof. by rewrite /Fset/Delta predeqE/= => x;split => [[x' [[? <-] ?]] //| [? ?]];exists x. Qed.
  
  Lemma Fset_DCE X Y: Δ_(Y.^c)#X = X `\` Y.
  Proof.
    rewrite /Fset/Delta/setC predeqE /= => x;split;first by move => [x' [[? <-] ?]].
    by move => [? ?];exists x.
  Qed.
  
  Lemma Fset_inc R S X: R `<=` S -> R#X `<=` S#X.
  Proof. by move => H x [y [? ?]];by exists y;split;[apply: H |]. Qed.
  
  Lemma Fset_inc1 R X Y: X `<=` Y -> R#X `<=` R#Y.
  Proof. by move => H x [y [? ?]];exists y;split;[|apply: H]. Qed.
  
  Lemma set_inc2 X x: x \in X <->  [set x] `<=` X.
  Proof. by split => [/set_mem ? y /= -> // |];rewrite in_setE;apply. Qed.
  
  Lemma Fset_comp R S X: S # (R # X) = (S `;` R) # X.
  Proof.
    rewrite /Fset /compose /Fset predeqE /=.
    move => x; split => [ [z [? [y [? ?]]]] | [ y [[z [? ?]] ?]]].
    by (exists y);split;[exists z;split|]. 
    by (exists z);split;[|exists y].
  Qed.
  
  Lemma FsetUl R S X: S#X `|` R#X = (S `|` R) # X.
  Proof.
    rewrite /Fset /setU predeqE /= => x; split. 
    by move => [[y [? ?]] | [y [? ?]]];exists y;[split;[left|]|split;[right|]].
    by move => [y [[?|?] ?]];[left|right];exists y.
  Qed.

  Lemma Fset_s R x y: R#_(x) y <-> R (y,x).
  Proof. by split => [[y' [H1 /= <-] //] | ?];exists x. Qed.
  
  Lemma FsetUr R X Y: R#(X `|` Y) = (R#X) `|` (R#Y).
  Proof.
    rewrite /Fset /setU predeqE /= => x; split. 
    by move => [z [? [?|?]]];[left|right];exists z.
    by move => [[y [? ?]]|[y [? ?]]];exists y;[split;[|left]|split;[|right]].
  Qed.

  Lemma FsetI R X Y: R#(X `&` Y) `<=` (R#X) `&` (R#Y).
  Proof.  by move => x [y [? [? ?]]];split;exists y. Qed.

  (* Foreset in extension *)
  Lemma Fset_union_set R X x: (R#X) x <-> exists y, X y /\ R#_(y) x.
  Proof. by split => [[y [? ?]]|[y [+ [z [+ /= H3]]]]];[(exists y);rewrite Fset_s| rewrite H3;exists y]. Qed.
  
  Lemma Fset_intersect R S x y: (exists z, R#_(x) z /\ S#_(y) z) <-> (R^-1 `;` S) (x,y). 
  Proof. split.
    by move => [z [/Fset_union_set [x' [/= -> /Fset_s ?]] /Fset_union_set [y' [/= -> /Fset_s ?]]]];(exists z).
    by move => [z /= [H1 H2]];exists z;rewrite 2!Fset_s.
  Qed.

  Lemma Fset_singleton R: forall (x:T), reflexive R -> R#_(x) x. 
  Proof. by move => x H;rewrite /Fset /mkset;exists x.   Qed.
  
  Lemma Fset_rt_singleton R: forall (x:T), R.*#_(x) x. 
  Proof. by move => x; exists x;split;[apply: RTclosR |]. Qed.
  
  Lemma Fset_restrict R X Y : X `<=` Y -> R#X = (R `;` Δ_(Y))# X.
  Proof.
    rewrite predeqE /= => H x.
    split => [[y [H1 H2]]|[y [[z [/= H1 /DsetE [_ <-]]] H4]]];last by (exists z).
    by (exists y);split;[exists y;split;[by [] |by split;[apply H|]]|]. 
  Qed.
  
  Lemma Fset_t0 R: forall (x y:T), R (x, y) <-> R#_(y) x. 
  Proof. by move => x y ; split => [H1 | [z [H1 /= <-]]];[exists y |]. Qed.

  Lemma Fset_t1 R x y: R (x, y) -> R.+#_(y) x. 
  Proof. by move => ?;exists y;split;[exists 1;[|rewrite iter1_id]|]. Qed.
  
  Lemma Fset_t2 R: forall (x y:T), (exists (x1:T), R (x, x1) /\ R.+#_(y) x1) -> R.+#_(y) x. 
  Proof.
    move => x y' [x1 [H1 [y [[n /=H2' H2] <-]]]];exists y;split;last by exact. 
    by exists (n.+1);[|rewrite iter_compose1l;exists x1].
  Qed.
  
  Lemma Fset_t3 R: forall (x y z:T), R.+#_(y) x /\ R (y, z) -> R.+#_(z) x. 
  Proof.
    move => x y z [[t [[n /= H1' H1] /= <-]] H3].
    by exists z;split;[exists (n.+1);[| rewrite iter_compose1r;exists t]|].
  Qed.
  
  Lemma Fset_t4 R: forall (y z:T), R (y, z) -> ( R.+#_(y) `<=` R.+#_(z) ).
  Proof. by move => y z ? x ?;apply Fset_t3 with y. Qed.

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

  (** * Ater sets *) 
  
  (* check that it coincide with usual definition *)
  Lemma AsetE  R Y: (Aset R Y) = [set x | exists (y: T), R (y,x) /\ Y y].
  Proof. by rewrite /Aset/Fset.  Qed.
  
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

  (** * Closures *) 
  
  Lemma Clos_x_x R X: forall (x:T), Clos_(x | R, X) x.
  Proof. by move => x;exists x;split;[apply RTclosR|]. Qed.
  
  Lemma Clos_Ew E W: forall (x y: T),  Clos_(x | E,W) y <-> (Δ_(W.^c) `;` E).* (y, x).
  Proof.
    move => x' y';split;first by move => [z [?  <-]].
    by move => ?;exists x';split.
  Qed.
  
  Lemma Clos_to_singleton E W X x: Clos(X |E, W) x <-> exists y, X y /\ Clos_(y |E, W) x.
  Proof. by split; rewrite Fset_union_set.  Qed.    
  
  Lemma Clos_union E W X Y:  Clos(X `|` Y| E,W) = Clos(X| E,W) `|` Clos(Y| E,W).
  Proof. by rewrite FsetUr. Qed.
  
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
  
  Lemma Clos_inc_l E W X Y: Clos(X| E,W) `<=` Clos(X `|` Y| E,W).
  Proof. by move => x; rewrite Clos_union; left.  Qed.    
  
  Lemma Clos_inc_r E W X Y: Clos(X| E,W) `<=` Clos(Y `|` X| E,W).
  Proof. by move => x; rewrite Clos_union; right. Qed.    
  
  Lemma Clos_contains E W X: X `<=` W -> X `<=` Clos(X| E,W).
  Proof. by move => ? x ?;rewrite /Fset /mkset;exists x;split;[apply RTclosR|].  Qed.    

  Lemma ClosU_containsl E W X Y: X `<=` W -> X `<=` Clos(X `|` Y | E,W).
  Proof.
    move => H0.
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
  Proof. by  rewrite Fset_D Union_Setminus -Fset_DCE Fset_comp. Qed.
  
  Lemma Fset_iterU R Y n: (iterU R n)#Y = (iterU ( Δ_(Y.^c) `;` R) n)#Y.
  Proof.
    elim:n => [ | n' H'];first by rewrite 2!iterU0.
    by rewrite 2!iterU_split -2!FsetUl -[in RHS]Fset_comp
            -[in RHS]H' [in RHS]Fset_comp [in RHS]composeA E30.
  Qed.
  
  Lemma Fset_n R Y n: (iterU R n)#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
  Proof. by rewrite Fset_iterU;apply: Fset_inc;apply: iterU_inc_clos_refl_trans. Qed.
  
  Lemma Fset_rt R Y: (Δ_(Y.^c) `;` R).*#Y = R.*#Y.
  Proof.
    rewrite eqEsubset;split. 
    by apply: Fset_inc; apply: (clos_refl_trans_inc (@DeltaCsubset _ Y.^c)).
    have E29_2:  R.*#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
    move => x [z [H1 H2]];
           suff: exists n : nat, iterU R n (x, z); last by apply: clos_rt_iterU.
    by move => [n H3];(suff: (Fset (iterU R n) Y) x; 
                      first by move => H; apply Fset_n in H);
              exists z; split.
    by [].
  Qed.
  
  (** *  Restriction of a relation to a subset *)

  Lemma R_restrict R X (x y: T): 
    x \in X /\ y \in X -> (R (x,y) <-> (Δ_(X) `;` R `;` Δ_(X)) (x,y)).
  Proof.
    rewrite /compose /Delta /mkset /=.
    move => [/inP H1 /inP H2];split=> [ H3 | [z [[t [[H3 ->] H4] [H5 <-]]]] //].
    by (exists y; split;[ exists x; split | ]).
  Qed.

  Lemma R_restrict_l R X (x y: T): x \in X -> (R (x,y) <-> (Δ_(X) `;` R) (x,y)).
  Proof. by move => /inP ?;split => [? | [z [[? /= ->] ?] ] //];(exists x; split). Qed.

  Definition Restrict R X :=  [set x | X x.1 /\ X x.2 /\ R x].
  
  (* equivalent expression with Dset *)
  Lemma RestrictE' R X: (Restrict R X) = (R |_(X)).
  Proof.
    rewrite predeqE => [[x y]].
    split => [[/= H1 [H2 H3]] | [z [[t [[/= H1 H'1] H2]] [/= H3 H'3]]]].
    by (exists y;split;[ exists x;split | ]).
    by split; [ | split; [rewrite -H'3 | rewrite H'1 -H'3]].
  Qed.
  
  Lemma Dset_restrict X: Δ_(X) = ('Δ |_(X)).
  Proof. by rewrite DeltaCr DsetK. Qed.

  Lemma Dset_restrict' X: Δ_(X) = (Δ_(X) |_(X)).
  Proof. by rewrite 2!DsetK. Qed.
  
  Lemma RestrictE R X x y: (R |_(X)) (x,y) <-> X x /\ X y /\ R (x,y).
  Proof.
    by split => [[x' [[y' [/DsetE /= [? <-] ?]] /DsetE [? <-]]] //
               | [? [? ?]]];exists y;split;[exists x|].
  Qed.
  
  Lemma RestrictK R X: (R |_(X)) |_(X) = R|_(X).
  Proof. by rewrite 2!composeA DsetK -2!composeA DsetK. Qed.
    
  Lemma RTRestrict R X: (R |_(X)).+ = (R |_(X)).+ |_(X). 
  Proof. 
    by rewrite {1}composeA  Delta_clos_trans_starts -composeA {1}Delta_clos_trans_ends -composeA.
  Qed.

  Lemma RestrictU R S X: (R `|` S) |_(X) = (R |_(X)) `|` (S |_(X)).
  Proof.
    rewrite predeqE => -[x y];split. 
    by move => /RestrictE [? [? [? | ?]]];[left|right];rewrite RestrictE.
    by move => [|] /RestrictE [? [? ?]];rewrite RestrictE;split;[|split;[|left]| |split;[|right]].
  Qed.
  
  Lemma main1 R X: ('Δ `|` R|_(X))`;`Δ_(X) = ('Δ `|` R) |_(X).
  Proof. by rewrite composeDr DeltaCl composeA DsetK RestrictU -Dset_restrict. Qed.
  
  Lemma main2 R X:  Δ_(X) `;` ('Δ `|` R|_(X)) = ('Δ `|` R) |_(X).
  Proof. by rewrite composeDl DeltaCr -2!composeA DsetK RestrictU -Dset_restrict. Qed.
  
  Lemma main3 R X: ('Δ `|` R|_(X)) |_(X) = ('Δ `|` R) |_(X).
  Proof. by rewrite composeA main1 -main2 -composeA DsetK. Qed.
         
  Lemma main4 R S X: (forall n, R^(n.+1)|_(X) = S^(n.+1)|_(X)) -> R.+ |_(X) `<=` S.+ |_(X).
  Proof.
    move => H0  -[x y] /RestrictE [H1 [H2 /clos_t_iterk [n H3]]].
    have: R^(n.+1)|_(X) (x,y) by apply/RestrictE. 
    rewrite (H0 n) => /RestrictE [H1' [H2' H3']].
    by apply /RestrictE;split;[|split;[|exists n.+1]].
  Qed.

  Lemma main5 R S X: (forall n, R^(n.+1)|_(X) = S^(n.+1)|_(X)) -> R.+ |_(X) = S.+ |_(X).
  Proof. by move => H0; rewrite eqEsubset; split; apply: main4. Qed.
  
  Lemma Main0 X R n: ('Δ `|` R|_(X))^(n.+1)|_(X) = (('Δ `|` R)|_(X))^(n.+1)|_(X).
    elim: n. by rewrite 2!iter1_id main3 RestrictK.
    move => n Hr.
    rewrite {1}iter_compose1r {1}composeA {1}composeA main1.
    rewrite -[('Δ `|` R)|_(X) in LHS]RestrictK -3!composeA.
    rewrite Hr -[in Y in (_ `;` Y = _)]DsetK -composeA.
    rewrite [(('Δ `|` R)|_(X))^(n.+1)|_(X)`;`('Δ `|` R)|_(X)`;`Δ_(X)]composeA.
    rewrite [(('Δ `|` R)|_(X))^(n.+1)|_(X)`;`(('Δ `|` R)|_(X)`;`Δ_(X))]composeA.
    rewrite [Δ_(X)`;`(('Δ `|` R)|_(X))^(n.+1)`;`(Δ_(X)`;`(('Δ `|` R)|_(X)`;`Δ_(X)))]composeA.
    rewrite -[Δ_(X)`;`(('Δ `|` R)|_(X)`;`Δ_(X))]composeA RestrictK composeA -iter_compose1r.
    exact.
  Qed. 
  
  Lemma Main1 X R: Δ_(X) `|` (R|_(X)).+ = (Δ_(X) `|` (R|_(X))).+.
  Proof. 
    rewrite [in LHS]RTRestrict {1}Dset_restrict -RestrictU.
    rewrite Rclos_Tclos {5}Dset_restrict -RestrictU  [in RHS]RTRestrict.
    apply: main5;apply: Main0.
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
  
  Lemma clos_t_iff R: transitive R <-> R = R.+.
  Proof. by split => [/@smallest_id H1 | ->];[rewrite TclosE H1|apply: TclosT]. Qed.
  
  Lemma clos_rt_iff R: (reflexive R /\ transitive R) <-> R = R.*.
  Proof.
    split => [ | ->];last by by split;[apply: RTclosR R|apply: RTclosT].
    pose proof (@smallest_id _ (fun R => (reflexive R /\ transitive R)) R ) as H1.
    by move => /H1 H2; rewrite RTclos_smallest H2.
  Qed.
      
  (** * Asymmetric part of a relation *) 
  
  Definition Asym (R: relation T): relation T := [set xy | R xy /\ ~ (R^-1 xy)].
  
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
  Lemma classes_disjointes_ou_egales R:
    equivalence R -> forall (x y: T), (exists z, R (x,z) /\ R (y,z)) -> class_of R x = class_of R y.
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

Section Restrict_to_subset.
  
  (** * Considering (R: relation S) with (S: set T) *)

  Context (T: eqType).
  Implicit Types (R S: relation T) (X: set T).

  (** some helpers to understand sval *)
  Lemma Inset X (v: X) : ((sval v) \in X).
  Proof. by rewrite inP; apply: set_valP. Qed.

  Lemma setIn X v: (v \in X) -> exists v' : X, v = sval v'.
  Proof. by move => H0;exists (exist _ v H0). Qed.
  
  Definition Restrict' (T: Type) (X:set T) (R: relation T): relation X := 
    [set xy : X*X | R ((sval xy.1),(sval xy.2))].
  
  Lemma RestrictP R X: (@Restrict' _ X R) = (@Restrict' _ X (R |_(X))).
  Proof.
    rewrite /Restrict' predeqE => -[x y] /= ; split; last first.
    by move => [z [[t [/DsetE /= [_ <-] H4]] /DsetE [_ <-]]].
    move => H1;exists (sval y);split;last by rewrite DsetE /=;split;[apply: set_valP|].
    by (exists (sval x));rewrite DsetE /=;split;[split;[apply: set_valP|]|].
  Qed.
  
  Definition Extend (T: Type) (X:set T) (R: relation X) :=
    [set xy | exists x : X, exists y: X, xy.1 = (sval x) /\ xy.2 =(sval y) /\ R (x,y)].

  Lemma Extend_restrict X R: @Extend _ X (@Restrict' _ X R) = (R |_(X)).
  Proof.
    rewrite RestrictP predeqE /Restrict' => -[x y]; split.
    by move => [x' [y' /= [-> [-> H3]]]].
    move => /[dup] H0 [z [[t [/DsetE /= [/inP H1 H1'] H4]] /DsetE [/inP H2 H2']]].
    rewrite H2' in H2.
    move: (H1) (H2) => /setIn [x' H1''] /setIn [y' H2''].
    by exists x';exists y';rewrite /mkset -H1'' -H2''.  
  Qed.
  
  Lemma ExtendU X (R S: relation X): (Extend R) `|` (Extend S) = Extend (R `|` S).
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [|] [x' [y' /= [H2 [H3 H4]]]].
      by (exists x';exists y');rewrite -H2 -H3 /=;split;[|split;[|left]].
      by (exists x';exists y');rewrite -H2 -H3 /=;split;[|split;[|right]].
    + move => [x' [y' /= [H2 [H3 [H4 | H4]]]]].
      by left;(exists x';exists y');rewrite -H2 -H3 /=. 
      by right;(exists x';exists y');rewrite -H2 -H3 /=. 
  Qed. 
  
  Lemma Extend_compose X (R S: relation X): Extend (R `;` S) = Extend R `;` Extend S.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [x' [y' /= [? [? [z' /= [? ?]]]]]].
      by exists (sval z');split;[exists x';exists z'| exists z';exists y'].
    + move => [z [[x' [z' /= [-> [-> H3]]]]] [z'' [y' /= [H4 [-> H6]]]]].
      exists x';exists y';split;[exact|split;[exact|]].
      by exists z';split;[| have ->: z' = z'' by apply: val_inj].
  Qed.
  
  Lemma Extend_iter X R n: @Extend _ X (@Restrict' _ X R)^(n.+1) = (R |_(X))^(n.+1).
  Proof.
    elim: n => [| n Hn];first by rewrite !iter1_id Extend_restrict.
    rewrite -addn1 (iter_compose (R|_(X)) n.+1 1) (iter_compose (Restrict' R) n.+1 1).
    by rewrite Extend_compose Hn !iter1_id Extend_restrict.
  Qed.

  Lemma Extend_tclos X R: @Extend _ X (@Restrict' _ X R).+ = (R |_(X)).+.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [x' [y' /= [? [? H3]]]]. 
      move: H3 => /(@clos_t_iterk _ ((@Restrict' _ X R)) x' y') [ n H3].
      by (exists n.+1);[| rewrite -Extend_iter;(exists x';exists y')].
    + move => /(@clos_t_iterk _ (R|_(X)) x y) [n H3];move: H3; rewrite -Extend_iter. 
      by move => [x' [y']] H1;(exists x';exists y');move: H1 => [-> [-> /iterk_inc_clos_trans ?]]. 
  Qed.

  Lemma RestrictEq R S X: (R |_(X)) = (S |_(X)) <-> (@Restrict' _ X R) = (@Restrict' _ X S).
  Proof.
    by split => [H|H];[rewrite (RestrictP R) (RestrictP S) H| rewrite -2!Extend_restrict H].
  Qed.
  
  Lemma Restrict_extend X (R:relation X): (@Restrict' _ X (Extend R)) = R.
  Proof.
    rewrite predeqE => -[x y]; split;last by (exists x;exists y).
    by move => [x' [y' /= [/val_inj <- [/val_inj <- ?]]]].
  Qed.
  
  Lemma Restrict_delta X: ('Δ: relation X) = (@Restrict' _ X 'Δ).
  Proof. 
    rewrite predeqE => -[x y];split;first by move => /@DeltaP ->. 
    by move => /DeltaP/= H1; rewrite DeltaP;apply: val_inj.
  Qed.
  
  Lemma RestrictU' X R S: (@Restrict' _ X R) `|` (@Restrict' _ X S) = (@Restrict' _ X (R `|` S)).
  Proof. by rewrite predeqE => -[x y];split;move => [?|?];[left|right|left|right]. Qed.
  
  Lemma Main X R: (Δ_(X) `|` (R|_(X)).+) = (Δ_(X) `|` (R|_(X))).+.
  Proof. 
    rewrite {4}Dset_restrict -RestrictU.
    rewrite [in LHS]RTRestrict {1}Dset_restrict -RestrictU.
    rewrite -Extend_tclos -Extend_restrict -RestrictU' -Extend_tclos Restrict_extend
             -Restrict_delta Rclos_Tclos Restrict_delta RestrictU'.
    by [].
  Qed.
  
End Restrict_to_subset.


