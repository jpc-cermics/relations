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
(* rel_of can be used to coerce a relation T to rel T                         *) 
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
(* restrict_sub   : from relation T to relation X where X is a set T          *)
(*               [set xy : X*X | R ((sval xy.1),(sval xy.2))].                *)
(* Partition induced by and Equivalence Relation                              *)
(* asym        : Asymmetric part of a relation, [set xy | R xy /\ ~ (R^-1 xy)] *)
(* Independent sets with respect to a relation                                *)
(******************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot order. 
From mathcomp Require Import mathcomp_extra boolp contra.
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

Definition delta T X: relation T := [set x | X x.1 /\ x.1 = x.2].

Notation "'Δ" := (delta setT) (at level 2, no associativity).

Definition deltaC T X: relation T := delta (~` X).
Definition lrel T X: relation T := [set x | X x.1].
Definition rrel T X: relation T := [set x | X x.2].

(* the universal relation on T, i.e. T x T. *)
Definition relT {T: Type} : relation T := setT.

Definition iter (T: Type) (R: relation T) S n : relation T:=
  let fix loop m := if m is i.+1 then (loop i) `;` R else S in loop n.

Definition tclos T (R: relation T): relation T := \bigcup_ (n >= 1) (iter R 'Δ n).

Definition rtclos T (R: relation T): relation T := \bigcup_ n (iter R 'Δ n).

Definition fset T (R: relation T) X : set T := [set x | exists (y: T), R (x,y) /\ X y].
Definition aset T (R: relation T) X : set T :=  fset R^-1 X. 

(* begin snippet RelIndep:: no-out *)    
Definition indep (T:Type) (R: relation T) (S: set T) :=
  forall (x y:T),  x \in S -> y \in S -> ~(x = y) -> ~( R (x,y)).
(* end snippet RelIndep *)    

(* possible Coercion of relation T to rel T *)
Definition rel_of (T: Type) (R: relation T) : rel T := (fun x y => asbool (R (x,y))).
Definition rel_to (T: Type) (R: rel T) : relation T := (fun xy => R xy.1 xy.2).
(* Global Coercion rel_of : relation >-> rel. *)

Notation "Δ_( X )" := (@delta _ X) 
                        (at level 2, no associativity, format "Δ_( X )").
Notation "L_( X )" := (@lrel _ X)
                        (at level 2, no associativity, format "L_( X )").
Notation "R_( X )" := (@rrel _ X)
                        (at level 2, no associativity, format "R_( X )").
Notation "X .^c" := (~` X) 
                      (at level 2, right associativity, format "X .^c").

Notation "'Δc" := (deltaC setT) (at level 2, no associativity).
Notation "R ^( n )" := (@iter _ R 'Δ n) 
                         (at level 2, right associativity, format "R ^( n )").
Notation "R .+" := (tclos R) (at level 1, left associativity, format "R .+").
Notation "R .*" := (rtclos R) (at level 1, left associativity, format "R .*").

(* Foreset of Y for the relation R*)
Notation "R # Y" := (fset R Y) (at level 3, no associativity, format "R # Y").

(* Foreset of {y} for the relation R*)
Notation "R #_( y )" := (fset R ([set y]))
                          (at level 3, no associativity, format "R #_( y )").

Notation "Y :# R" := (aset R Y) 
                       (at level 3, no associativity, format "Y :# R").

(* Foreset of {y} for the relation R*)
Notation " y _:# R" := (aset R ([set y]))
                          (at level 3, no associativity, format " y _:# R").

(* Closure of Y for the relation R and subset W *)

Notation "Clos( Y | R , W )" :=  (fset ((Δ_(W.^c) `;` R).* ) Y)
                                 (at level 3, no associativity, format "Clos( Y | R , W )").    

(* Closure of {y} for the relation R and subset W *)
Notation "Clos_( y | R , W )" := (fset ((Δ_(W.^c) `;` R).* ) ([set y]))
                                 (at level 3, no associativity, format "Clos_( y | R , W )").    

Notation "R |_( X )" := (Δ_(X) `;` R `;` Δ_(X))
                       (at level 3, no associativity, format "R |_( X )").

Section Relation_Facts.
  
  Context (T : Type).
  Implicit Types (T : Type) (R S U: relation T) (X Y: set T).

  (** link with ssrbool.v 
             reflexive R <-> R is reflexive.
           irreflexive R <-> R is irreflexive.
             symmetric R <-> R (in rel T) is symmetric (equation).
         pre_symmetric R <-> R is symmetric (implication).
         antisymmetric R <-> R is antisymmetric.
                 total R <-> R is total.
            transitive R <-> R is transitive.
       left_transitive R <-> R is a congruence on its left hand side.
      right_transitive R <-> R is a congruence on its right hand side.
       equivalence_rel R <-> R is an equivalence relation.

    we also define asymmetric R: Prop := forall x y:T, R (x,y) -> ~ R (y,x).
    
   **)
  
  Definition reflexive R : Prop := forall x:T, R (x,x).
  
  Lemma reflexiveP R : reflexive R <-> ssrbool.reflexive (rel_of R).
  Proof. by split => + x => /(_ x);rewrite asboolE. Qed.
  
  Definition transitive R: Prop := forall y x z:T, R (x,y) -> R (y,z) -> R (x,z).

  Lemma transitiveP R : transitive R <-> ssrbool.transitive (rel_of R).
  Proof. by split => + y x z => /(_ y x z);rewrite 3!asboolE. Qed.
  
  Definition symmetric R: Prop := forall x y:T, R (x,y) -> R (y,x).

  Lemma symmetricP R : symmetric R <-> ssrbool.symmetric (rel_of R).
  Proof.
    split => + x y. 
    by move => /[dup] /(_ x y) ? /(_ y x) ?;apply/asboolP/asboolP.  
    move => /(_ x y) Hsy.
    rewrite -(asboolE (R (x,y)))  -(asboolE (R (y,x))).
    have <-: (rel_of R) x y = `[< R (x, y) >] by [].
    have <-: (rel_of R) y x = `[< R (y, x) >] by [].
    by rewrite Hsy.
  Qed.
  
  Definition antisymmetric R: Prop := forall x y:T, R (x,y) -> R (y,x) -> x = y.

  Lemma antisymmetricP R :antisymmetric R  <-> ssrbool.antisymmetric (rel_of R).
  Proof. 
    split => + x y.
    by move => /(_ x y) Has /andP [/asboolP ? /asboolP ?];apply: Has.
    by move => /(_ x y) Has ? ?;apply/Has/andP;split;apply/asboolP.
  Qed.
  
  Definition asymmetric R: Prop := forall x y:T, R (x,y) -> ~ R (y,x).

  Definition irreflexive R : Prop := forall x:T, ~ R (x,x).
  
  Lemma irreflexiveP R: irreflexive R  <-> ssrbool.irreflexive (rel_of R).
  Proof. by split => + x => /(_ x);[move => /asboolF|move => /asboolP]. Qed.
  
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

  Lemma asym_antisymP R: irreflexive R -> (asymmetric R <-> antisymmetric R).
  Proof. move => Ir. split => [Asy x y /Asy ? ? //| Atsy x y /[dup] H0 H1 H2]. 
         by move: (Atsy x y H1 H2) H0 => ->;apply: Ir.
  Qed.

  Lemma asym_irr R: asymmetric R -> irreflexive R. 
  Proof. by move => + x + => /(_ x x) As /[dup] Rxx /As notRxx. Qed.
  
  (* sporder is also asymmetric *)
  Lemma trans_irr_asym R: transitive R -> irreflexive R -> asymmetric R.
  Proof. by move => Tr Ir x y H1 H2; pose proof (Ir x (Tr y x x H1 H2)). Qed.
  
  Lemma sporder_asym R: sporder R -> asymmetric R.
  Proof. by move => [Hir Ht];apply: trans_irr_asym. Qed.
  
  (* sporder is also antisymmetric *)
  Lemma trans_irr_antisym R: transitive R -> irreflexive R -> antisymmetric R.
  Proof. by move => Tr Ir x y H1 H2; pose proof (Ir x (Tr y x x H1 H2)). Qed.

  Lemma sporder_antisym R: sporder R -> antisymmetric R.
  Proof. by move => [Hir Ht];apply: trans_irr_antisym. Qed.

  Lemma sporderV R: sporder R -> sporder R^-1.
  Proof.
    move => [Hi Ht];split => [x /Hi //|]. 
    by move: Ht => + y x z /[swap] => /(_ y z x) Ht /Ht H2 /H2.
  Qed.
  
  Lemma asymmetricV R: asymmetric R ->  asymmetric R^-1.
  Proof. by move => + x y => /(_ x y) Ha /Ha . Qed.

  (** * Sets_facts *)
  
  Lemma setUD X Y: X `|` Y = X `|` (Y `\` X). 
  Proof.
    rewrite /setU /setD /mkset predeqE => x.
    by split => [[?|?]|[?|[? ?]]];
            [left|pose proof lem (X x) as [?|?];[left|right]|left|right].
  Qed.
  
  (** * relT universal relation  *)

  Lemma relT_prod: relT = (@setT T) `*` (@setT T).
  Proof. rewrite predeqE => -[x y];by split. Qed.

  Lemma subrelT R: R `<=` relT.
  Proof. by apply: subsetT.  Qed.

  (** *  Inverse of a relation *)
  
  (**  R^-1^-1 = R *)
  Lemma inverseK: involutive (@inverse T). 
  Proof. by move => R; rewrite predeqE /= => -[x y]. Qed.
  
  Lemma invP R: R^-1 = R <-> symmetric R.
  Proof. by rewrite predeqE;split => [H0 x y /H0 //|H1 [x y]];split;apply H1. Qed.
  
  Lemma invE R S: R = S <-> R^-1 = S^-1.
  Proof. by split =>[->//| H1];rewrite -[R]inverseK -[S]inverseK H1. Qed.
  
  Lemma invU R S: (R `|` S)^-1 = R^-1 `|` S^-1.
  Proof. by rewrite /predeqE. Qed.

  Lemma inverseS R S: R `<=` S -> R^-1 `<=` S^-1. 
  Proof. by move => H1 x /H1 H2. Qed.

  (** * Complementary *)
  
  Lemma invC R: R.^c^-1 = (R^-1).^c.
  Proof. by rewrite predeqE => -[x y];split. Qed.
  
  (** * Composition *)

  Lemma compA R S U: (R `;` S) `;` U = R `;` (S `;` U).
  Proof.
    rewrite predeqE => x';split => [ [z [[w /= [? ?]] ?]] | [z [? [ w [? ?]]]]].
    by (exists w);split; [|exists z; split].
    by (exists w);split; [exists z|].
  Qed.

  Lemma compUl  R S U: (R `|` S) `;` U = (R `;` U) `|` (S `;` U).
  Proof.
    rewrite predeqE => x;split.
    by move => [z [[? | ? ] ?]];[left|right];exists z.
    by move => [|] [ z [? ?]];[exists z; split;[left|]|exists z;split;[right|]].
  Qed.
  
  Lemma compUr R S U: R `;` (S `|` U) = (R `;` S) `|` (R `;` U).
  Proof.
    rewrite predeqE => x;split => [[z [H1 H2]] | H1].
    by move: H2 => [H2|H2];[left;exists z;split|right;exists z; split].
    by move: H1 => [[z [H1 H2]] | [z [H1 H2]]];(exists z);split;[|left| |right]. 
  Qed.
  
  Lemma compS R S U: S `<=` U ->(R `;` S) `<=` (R `;` U). 
  Proof. by move => H x [z [? ?]];exists z;split;[|apply: H]. Qed.
  
  Lemma compSl R S U: S `<=` U ->(S `;` R ) `<=` (U `;` R). 
  Proof. by move => H x [z [? ?]];exists z;split;[apply: H|]. Qed.
  
  Lemma compSS (R S U V: relation T) :
    R `<=` U -> S `<=` V -> (R `;` S) `<=` (U `;` V).
  Proof.
    by move => H1 H2;apply: (subset_trans (@compSl S R U H1) (@compS U S V H2)).
  Qed.

  Lemma compV  R S: (R `;` S)^-1 = S^-1 `;` R^-1.
  Proof. by rewrite predeqE => x;split;move => [z [? ?]];exists z;split. Qed.

  Lemma comp_invV_sym R:  symmetric (R `;` R^-1).
  Proof. by move => x y [z [H1 H2]];exists z;split;[apply: H2|apply: H1]. Qed.
  
  Lemma comp_invVV R: (R `;` R^-1)^-1 = R `;` R^-1.
  Proof. by apply/invP/comp_invV_sym. Qed. 

  (** * Delta_(X) *)
 
  Lemma deltaE X (x y:T): Δ_(X) (x,y) <-> X x /\ x = y.
  Proof. exact. Qed.
    
  Lemma delta_sym X:  symmetric Δ_(X).
  Proof. by move => x y [+ /= <-] => /= H1;split. Qed.
  
  Lemma delta_trans X: transitive Δ_(X).
  Proof. by move => x y z [/= ? H2] [? H4];split;[|rewrite H2 H4]. Qed.
  
  Lemma deltaS X Y: X `<=` Y -> Δ_(X) `<=` Δ_(Y).
  Proof. by move =>  H [x y] [H1 /= <-];split;[apply: H|]. Qed.

  Lemma deltaI X Y: Δ_(X) `;` Δ_(Y) = Δ_(X `&` Y).
  Proof. by rewrite predeqE
         => -[x y];split=>[[z [[? /= <-][? /= <-]]]|[[? ?] /= <-]];[|exists x]. Qed.
  
  Lemma deltaK X:  Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof. by rewrite deltaI setIid. Qed.

  Lemma deltaV X: Δ_(X)^-1 = Δ_(X). 
  Proof. by rewrite predeqE /inverse => -[x y] /=;split;move => [H1 /= <-]. Qed.

  Lemma deltaU X Y: Δ_(X) `|` Δ_(Y) = Δ_(X `|` Y).
  Proof.
    rewrite predeqE => -[x y];split;last by  move => [[? | ?] /= <-];[left|right].
    by move => [|] [/= ? /= <-];apply/deltaE;split;[left| |right| ].
  Qed.
  
  Lemma delta_lrel X R: Δ_(X) `;` R = L_(X) `&` R.
  Proof. by rewrite predeqE /= => [[x y]] /=;split => [[z [[? /= <-] ?]]|[? ?]];[|exists x].  Qed.

  Lemma delta_rrel X R: R `;` Δ_(X) = R `&` R_(X).
  Proof. by rewrite  predeqE /= => [[x y]] /=;split => [[z [? [? /= <-]]]|[? ?]];[|exists y]. Qed.

  Lemma delta0: Δ_(set0) = ('Δc: relation T).
  Proof. by rewrite predeqE => -[x y];split => [/deltaE [? _] | [/= ? _]]. Qed.
  
  Lemma deltaCr X: Δ_(X) `;` Δ_(X.^c) = 'Δc.
  Proof.
    rewrite predeqE -delta0=> -[x y];split.
    by move => [z [/deltaE [? <-] /deltaE [? _]] //].
    by move => /deltaE [? _].
  Qed.
  
  Lemma deltaCl X: Δ_(X.^c) `;` Δ_(X) = 'Δc.
  Proof. by rewrite deltaI setIC -setDE setDv delta0. Qed.
  
  (** * delta relation  *)
  
  Lemma deltaTP (x y: T): 'Δ (x,y) <-> x = y.
  Proof. by split => [[_ ? //]| ->]. Qed.
  
  Lemma deltaTS X: Δ_(X) `<=` 'Δ.
  Proof. by apply: deltaS. Qed.
  
  Lemma deltaTV: 'Δ^-1 = ('Δ : relation T).
  Proof. by apply:  deltaV. Qed.

  (* 'Δ `;` R = R.  *)
  Lemma comp1x: left_id 'Δ (@compose T). 
  Proof. by move => R;rewrite predeqE => -[x y];split=> [[z [/deltaTP <- ?]] //| ?];exists x;split. Qed.
  
  (* R `;` 'Δ = R.   *)
  Lemma compx1: right_id 'Δ (@compose T). 
  Proof. by move => R;rewrite predeqE => -[x y];split => [[z [? /deltaTP /= <-]]// | ?];exists y;split.  Qed.

  Lemma deltaTCP (x y: T): 'Δ.^c (x,y) <-> ~ (x = y).
  Proof.
    split => [+ H1 | H1].
    by rewrite H1 -inE in_setC notin_setE deltaTP. 
    by rewrite -inE in_setC  notin_setE => /deltaTP ?.
  Qed.
  
  Lemma deltaC0U R: 'Δc `|` R = R.
  Proof.
    rewrite eqEsubset;split;last by apply: subsetUr.
    by move => -[x y] [[H1 _]|]//;rewrite setCT in H1.
  Qed.
  
  Lemma deltaCU0 R:  R `|` 'Δc = R.
  Proof.  by rewrite setUC; apply deltaC0U. Qed.
  
  Lemma comp0x R: 'Δc `;` R = 'Δc.
  Proof.  by rewrite predeqE => x;split => [[z [[/= ? _] _]]|[/= ? _]] //. Qed.
  
  Lemma compx0 R:  R `;` 'Δc = 'Δc.
  Proof. by rewrite predeqE => x;split => [[z [_ [/= ? _]]]|[/= ? _]] //. Qed.
  
  Lemma delta_compS R X: (Δ_(X) `;` R `<=` R).
  Proof. by move => -[x y] /= => [[z [[_ /= <-] ?]]]. Qed.
  
  Lemma comp_deltaS R X: (R `;` Δ_(X) `<=` R).
  Proof. by move => -[x y] /= => [[z [H2 [_ /= <-]]]]. Qed.

  (** * Composition iteration *)
  
  Lemma iter1 R: R^(1) = R.
  Proof. by rewrite /iter comp1x. Qed.

  Lemma iter_compose1r R n: R^(n.+1) = R^(n) `;` R.
  Proof. by elim: n => [//|n ?]. Qed.
  
  Lemma iter_compose R n1 n2: R^(n1 + n2) = R^(n1) `;` R^(n2).
  Proof.
    elim: n2 n1 => [n1| n1 H n0];first by rewrite addn0  compx1.
    by rewrite [addn n0 n1.+1]addnS iter_compose1r H compA -iter_compose1r.
  Qed.

  Lemma iterSl R n: R^(n.+1) = R `;` R^(n).
  Proof. by rewrite -addn1 addnC (iter_compose R 1 n) iter1. Qed.
  
  Lemma iterT (n: nat): 'Δ^(n) = ('Δ :relation T).
  Proof. 
    by elim: n => [//|n Hr];rewrite -addn1 (iter_compose 'Δ n 1)
                                      Hr iter1 comp1x.
  Qed.

  Lemma iter_include R S (n:nat): R `<=` S -> R^(n) `<=` S^(n).
  Proof.
    elim: n => [_ //| n Hr H1];rewrite -addn1 (iter_compose R n 1) (iter_compose S n 1).
    have H4: R^(n)`;`R^(1) `<=` S^(n)`;`R^(1) by apply: compSl;apply:Hr.
    by apply: (subset_trans H4 _);apply: compS;rewrite 2!iter1.
  Qed.
  
  Lemma iter_transS R S: transitive S ->  R `<=` S -> forall n, n > 0 -> R^(n) `<=` S.
  Proof.
    move => Ht H1;elim => [//| n Hr H2 [x y]].
    have H2': R^(1) `<=` S by rewrite iter1.
    case H3: (n == 0);first by move: H3 => /eqP -> => /H2'.
    move: H3 => /neq0_lt0n /Hr H3.
    rewrite -addn1 (iter_compose R n 1) => -[z [/H3 H4 /H2' H5]];apply: (Ht z x y H4 H5). 
  Qed. 
  
  Lemma iterV R (n: nat) : R^(n)^-1 = (R^-1)^(n).
  Proof.
    elim: n =>[| n H1];first  by rewrite /iter deltaV.
    by rewrite -addn1 (iter_compose R n 1) compV
                  addnC (iter_compose R^-1 1 n) H1 !iter1. 
  Qed.
  
  Lemma iterC R (n:nat): R^(n) `;` R = R `;` R^(n).
  Proof. by move: (iter_compose R n 1) (iter_compose R 1 n);rewrite  iter1 addnC => <- <-. Qed.
  
  Lemma iter_sym R (n:nat): symmetric R -> symmetric R^(n).
  Proof.
    move => Hs.
    elim: n => [H1 | n Hr x y];first by apply: delta_sym.
    rewrite -addn1;move: (iter_compose R n 1) => H1.  
    rewrite {1}H1 iter1 /= => -[z /=[/Hr H2 /Hs H3]].
    by rewrite addnC (iter_compose R 1 n) iter1;(exists z).
  Qed.

  Lemma iter_deltaUS R (n: nat): ('Δ `|` R)^(n) `<=` ('Δ `|` R)^(n.+1).
  Proof.
    rewrite -{1}addn1 (iter_compose ('Δ `|` R) n 1) iter1 compUr compx1.
    by apply: subsetUl.
  Qed.
  
  Lemma iter_deltar R X: forall (n: nat), 0 < n -> (R`;`Δ_(X))^(n) = (R`;`Δ_(X))^(n)`;`Δ_(X).
  Proof.
    have H1: (R`;`Δ_(X))^(1) = (R`;`Δ_(X))^(1) `;`Δ_(X) by rewrite iter1 compA deltaK.
    by case => [//| n _];rewrite -addn1 (iter_compose (R`;`Δ_(X)) n 1) compA -H1.
  Qed.
  
  Lemma iter_deltal R X: forall (n: nat), 0 < n -> (Δ_(X)`;`R)^(n) = Δ_(X)`;`(Δ_(X)`;`R)^(n).
  Proof.
    have H1: (Δ_(X)`;`R)^(1) = Δ_(X)`;`(Δ_(X)`;`R)^(1)
      by rewrite iter1 -compA deltaK.
    case => [//| n _].
    by rewrite -addn1 addnC (iter_compose (Δ_(X)`;`R) 1 n) -[in RHS]compA -H1.
  Qed.
  
  Lemma bigcup_iter1 R: \bigcup_(i < 1) R^(i) = 'Δ. 
  Proof. by rewrite predeqE => -[x y];split => [[n]|?];[rewrite II1 => -> /deltaTP ->|exists 0]. Qed.
  
  Lemma bigcup_compl I (F : I -> relation T) (P : set I) U:
    \bigcup_(i in P) (F i `;` U) = (\bigcup_(i in P) F i) `;` U.
  Proof.
    apply/predeqP => -[x y]. split. 
    by move => [n Pn [z /= [H1 H2]]];exists z;split;[exists n|]. 
    by move => [z [[n Pn /= H1] /= H2]];exists n;[|exists z].
  Qed.

  (** * Reflexive Closure *)
  
  Lemma deltaU_reflS R S: reflexive S -> R `<=` S -> 'Δ `|` R  `<=` S.
  Proof. by move => ? Hs -[x y] [/deltaTP -> // | /Hs ?]. Qed.
  
  Lemma rclosE R: 'Δ `|` R = smallest [set S | reflexive S] R. 
  Proof. 
    rewrite eqEsubset. split.
    by move => -[x y] [/deltaTP ->S [? _] // |];apply: sub_smallest.
    by apply: smallest_sub;[left | apply: subsetUr].
  Qed.
  
  (** * Transitive closure  *)
  
  Lemma tclos_compr R S:  R.+ `;` S = \bigcup_ (n >= 1) R^(n) `;` S.
  Proof. by rewrite -bigcup_compl. Qed.
  
  Lemma tclos_transS R S: transitive S -> R `<=` S -> R.+ `<=` S.
  Proof. by move => Ht H1 [x y] [n /= H2];move: (iter_transS Ht H1 H2) => H3 /H3 ?. Qed.
  
  Lemma tclos_iterP R (x y:T): R.+ (x,y) -> exists (n:nat), R^(n.+1) (x,y).
  Proof.
    by move => [n H1 ?];exists (n.-1);have ->: n.-1.+1 = n by apply: ltn_predK H1. 
  Qed.
  
  Lemma tclos_trans R: transitive R.+.
  Proof. by move => y x z /tclos_iterP [n1 H1] /tclos_iterP [n2 H2];
                   exists (n1.+1 + n2.+1);[|rewrite iter_compose;exists y].
  Qed.
  
  Lemma tclosS R S: R `<=` S -> R.+ `<=` S.+ .
  Proof. 
    by move => H1 xy [n /= H2 H3];(exists n);[|apply: (@iter_include R S n H1)]. Qed.
  
  Lemma tcl_sub R: R `<=` R.+.
  Proof. by move => [x y] ?;exists 1;[| rewrite iter1]. Qed.
  
  (* mathematical def of closure 
     smallest [set S | transitive S] R
     is also \bigcap_(S in [set S | transitive S /\ R `<=` S]) S *)
  
  Lemma tclosE R: R.+ = smallest [set S | transitive S] R. 
  Proof.
    rewrite predeqE => -[x y];split => [[n /= H1 H2 S' [H3 H4]]|].
    by move: (iter_transS H3 H4) => H5;move: (H5 n H1) H2 => H6 /H6 H2.
    by apply: (@smallest_sub _ transitive _ R.+ (@tclos_trans _) (@tcl_sub _)). 
  Qed.

  Lemma iterS_tclos R: forall (n : nat), R^(n.+1) `<=` R.+.
  Proof. by move => n xy H1;exists n.+1. Qed.
  

  Lemma tclos_iterPV R (x y:T): (exists (n:nat), R^(n.+1) (x,y)) -> R.+ (x,y).
  Proof. by move => [n H1];apply: (@iterS_tclos R n). Qed.
  
  Lemma tclosV R: R.+^-1 = R^-1.+ .
  Proof.
    rewrite predeqE => -[x y] /=;split => [[n ? ?]| [n H1]].
    by (exists n);[ exact|rewrite -iterV].
    by rewrite -iterV => ?;exists n.
  Qed.
  
  Lemma tclos_sym R: symmetric R -> symmetric R.+.
  Proof. by move => Hs x y [n /= H1 /(iter_sym Hs) H2];exists n. Qed.

  Lemma iter_sep R: forall (n: nat) (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R^(n.+1) (x, y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x',y')).
  Proof.
    move => n x y W.
    elim: n x y => [x y [H1 [H2 H3]] | n H0 y y' ].
    by exists x; exists y; rewrite /iter comp1x in H3.
    rewrite /iter -/iter.
    move => [H2 [H3 [z [/= H4 H5]]]].
    pose proof lem (z \in W) as [H6 | H6].
    - by (exists z; exists y').
    - have H10: exists x' y' : T, x' \in W /\ y' \in W.^c /\ R (x', y')
              by (apply H0 with y z;
                  split;[|split;rewrite in_setE in H6;[rewrite /setC in_setE|]]).
      by move: H10 => [x2 [y2 [? [? ?]]]];exists x2; exists y2.
  Qed.
  
  Lemma tclos_sep R: forall (x y: T) (W:set T),
      x\in W /\ y \in W.^c /\ R.+ (x,y)
      ->  (exists (x' y': T), x'\in W /\ y' \in W.^c /\ R (x', y')).
  Proof.
    move => x y W [H1 [H2 /tclos_iterP [n' H3]]].
    by apply iter_sep with n' x y.
  Qed.

  Lemma tclos_deltar R X: (R `;` Δ_(X)).+ =  (R `;` Δ_(X)).+ `;` Δ_(X).
  Proof.
    rewrite predeqE => -[x y];split;last by move=> [z[+[_ /= H3]]];rewrite H3.
    move=> [n Pn];rewrite (iter_deltar R X Pn) => -[z /= [H2 H3]].
    by (exists z);split;[exists n|].
  Qed.

  Lemma tclos_deltal R X: (Δ_(X) `;` R).+ = Δ_(X) `;` (Δ_(X) `;` R).+.
  Proof.
    rewrite predeqE => -[x y]; split;last by move=> [z[[_ /= H3]]];rewrite H3.
    move=> [n Pn];rewrite (iter_deltal R X Pn) => -[z /= [H2 H3]].
    by (exists z);split;[|exists n].
  Qed.
  
  Lemma tclos_iterS (Z V U W: relation T):
    (forall (n:nat), Z `;` (V^(n.+1)) `;` U = Z `;` (W^(n.+1)) `;` U) 
    -> Z `;` V.+ `;` U `<=` Z `;` W.+ `;` U.
  Proof.
    move => H0 [x y] [z [[t /=[H1 [n H2 H3]]] /=H4]].
    move: H0 => /(_ (n.-1));(have ->: n.-1.+1 = n by apply: ltn_predK H2);move => H0.
    have [z' [[t' /=[H1' H2']] H4']]: (Z`;`W^(n)`;`U) (x,y) by rewrite -H0;exists z;split;[exists t|].
    by exists z';split;[exists t';split;[|exists n]|].
  Qed.
  
  Lemma tclos_iterE (Z R S U: relation T):
    (forall (n:nat), Z `;` (R^(n.+1)) `;` U = Z `;` (S^(n.+1)) `;` U)
    -> Z `;` R.+ `;` U = Z `;` S.+ `;` U.
  Proof. by move => H;rewrite predeqE;split;apply: tclos_iterS.  Qed.
  
  Lemma comp_tclosS R: (R `;` R.+) `<=` R.+.
  Proof. 
    by move => [x y] [z [? [n ? ?]]];
              exists (n.+1);[exact | rewrite iterSl;exists z].
  Qed.
  
  Lemma tclos_compS R: (R.+ `;` R) `<=` R.+.
  Proof. 
    by move => [x y] [z [[n ? ?] ?]];
              exists (n.+1);[exact | rewrite iter_compose1r;exists z].
  Qed.
  
  Lemma tclosUl R: R `|` (R `;` R.+) = R.+ .
  Proof.
    rewrite eqEsubset;split;first by 
      rewrite subUset;split;[apply:tcl_sub| apply: comp_tclosS].
    move => -[x y] /(@tclos_iterP R x y) [n].
    case H3: (n == 0);first by move: H3 => /eqP ->;rewrite iter1 => H3;left.
    move: H3 => /neq0_lt0n H3;rewrite (iterSl R) => -[z /= [H1 H2]].
    by right;exists z;split;[|exists n].
  Qed.
  
  Lemma tclos_compK R:  (R.+ `;` R.+) `<=` R.+.
  Proof. 
    move => [x y] [z [/tclos_iterP [n1 H1] /tclos_iterP [n2 H2]]].
    by exists (n1.+1 + n2.+1);[exact | rewrite (iter_compose R n1.+1 n2.+1);exists z].
  Qed.
  
  Lemma tclosU_comp R: R.+ `|` (R.+ `;` R.+) = R.+.
  Proof. by rewrite predeqE => -[x y];split => [[? //| /tclos_compK ?//] | ?];left. Qed.
  
  Lemma tclosUr R: R `|` (R.+ `;` R) = R.+.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [H1| [z /= [/tclos_iterP [n1 H1] H3]]];
             first by apply: tcl_sub.
      by (exists n1.+2);[| rewrite (iter_compose1r R n1.+1);exists z].
    + move => /tclos_iterP [n].
      case H2: (n == 0); first by move: H2 => /eqP ->;rewrite iter1;left.
      move: H2 => /neq0_lt0n H2;rewrite (iter_compose1r R n) => -[z [H3 H4]].
      by right;exists z;split;[exists n|].
  Qed.
  
  (** * Reflexive Transitive Closure *)
  
  (* A proof with bigcup *)
  Lemma rtclosE R: R.* = 'Δ `|` R.+.
  Proof. 
    by rewrite /rtclos (bigcup_splitn 1) 
      -(@bigcup_mkord _ 1 (fun n => R^(n))) bigcup_iter1 bigcup_addn.
  Qed.

  Lemma rtclos_ind R S: transitive S -> reflexive S -> R `<=` S -> R.* `<=` S.
  Proof.
    move => Ht Hr H1 [x y] [n _]. 
    case H2: (n == 0);first by move: H2 => /eqP -> /deltaTP ->.
    by move: H2 => /neq0_lt0n H2;move: (iter_transS Ht H1 H2) => H3 /H3 ?.
  Qed.
  
  Lemma rtclos_trans R: transitive R.*.
  Proof.
    rewrite rtclosE => y x z [/deltaTP -> //| /tclos_iterP [n1 H1]].
    move => [/deltaTP <- //|/tclos_iterP [n2 H2]];first by right;(exists n1.+1).
    by right;exists (n1.+1 + n2.+1);[exact|rewrite iter_compose;exists y].
  Qed.
  
  Lemma rtclos_refl R: reflexive R.*.
  Proof. by rewrite rtclosE; move => x; left. Qed.
  
  Lemma rtclos_sub R: R `<=` R.*.
  Proof. by rewrite rtclosE;move => [x y] ?;right;exists 1;[|rewrite iter1]. Qed.
  
  (* coincide with mathematical def of closure  *)
  Lemma rtclos_smallest R: R.* = smallest [set S | reflexive S /\ transitive S] R. 
  Proof.
    rewrite rtclosE eqEsubset;split; first by 
      move => -[x y] [/deltaTP -> //| /tclos_iterP [n H2]] S' [[H3 H3'] H4];
             [|apply: (@iter_transS R S' H3' H4 n.+1)].
    rewrite -rtclosE; move => -[x y] H2.
      have: [set S | (reflexive S /\ transitive S) /\ R `<=` S] R.*
        by split;[split;[apply: rtclos_refl|apply: rtclos_trans]|apply: rtclos_sub].
      by move => /H2.
  Qed.
  
  Lemma rtclosV R: R.*^-1 = R^-1.* .
  Proof. by rewrite 2!rtclosE invU tclosV deltaTV. Qed.
  
  Lemma delta_rtclosS R X: Δ_(X) `<=` R.* .
  Proof. by rewrite rtclosE;apply: subset_trans;[apply: deltaTS|apply: subsetUl].  Qed.
  
  Lemma tclos_rtclosS R: R.+ `<=` R.*.
  Proof. by rewrite rtclosE;apply: subsetUr. Qed.
  
  Lemma rtclosS R S: R `<=` S -> R.* `<=` S.*.
  Proof. by move => H1;rewrite 2!rtclosE;apply/setUS/tclosS. Qed.
  
  Lemma DuT_eq_Tstar R:  'Δ `|` R.+ = R.*.  
  Proof. by rewrite rtclosE. Qed.
  
  Lemma comp_rtclosE R: R `;` R.* = R.+.
  Proof. by rewrite rtclosE compUr compx1 tclosUl. Qed.
  
  Lemma rtclos_compE R: R.* `;` R = R.+.
  Proof. by rewrite rtclosE compUl comp1x tclosUr. Qed.
    
  Definition iterU (T: Type) (R: relation T) n : relation T := [set xy | exists k, k < n.+1 /\ R^(k) xy].
  
  Lemma iterU0 R: iterU R 0 = 'Δ.
  Proof. by rewrite predeqE => -[x y];split => [[k] |/deltaTP ->];[rewrite ltnS leqn0 => -[/eqP -> H1]|exists 0]. Qed.

  Lemma iterUS R n: iterU R (n.+1) = 'Δ `|`  (R `;` (iterU R n)).
  Proof. 
    rewrite predeqE => -[x y]. split.
    + move => [k [H1 H2]].
      case H3: (k == 0). move: H3 => /eqP H3. rewrite H3 in H2. by left.
      move: H3 => /neq0_lt0n H3.
      have H4: k.-1.+1 = k by apply: ltn_predK H3. 
      move: H2; rewrite -H4 iterSl.
      move => [z [H5 H6]].
      right. exists z. split. by [].
      by (exists k.-1); split;[rewrite -H4 in H1|].
    + move => [H1 | [z [H1 [k [H2 H3]]]]];first by ( exists 0).
      by exists k.+1;split;[| rewrite iterSl;exists z].
  Qed.
  
  Lemma iterU_rtclosS R: forall (n : nat), (iterU R n) `<=` R.*.
  Proof.
    elim => [|n Hr];first by rewrite iterU0 => [[x y] ?];exists 0.
    rewrite iterUS  rtclosE;apply: setUS;move => -[x y] [z [? /Hr]].
    by rewrite rtclosE => -[/deltaTP /= <- | H2];[apply: tcl_sub| apply: comp_tclosS;exists z].
  Qed.
  
  Lemma rtclos_iterUP R (x y:T): R.* (x, y) -> exists (n:nat), (iterU R n) (x,y).
  Proof. by rewrite rtclosE => -[/deltaTP -> | [n H1 H2]];[(exists 0);rewrite iterU0| exists n;exists n].
  Qed.

  Lemma rtclos_iterP R (x y: T): R.* (x,y) -> exists n, R^(n) (x,y).
  Proof.
    move => h; case: (@rtclos_iterUP R x y h) => n.
    by rewrite /iterU /mkset => -[k [_ hk]]; exists k.
  Qed.
  
  (* transitive (reflexive closure) = (reflexive (transitive closure)) *)
  Lemma rclos_tclosE R: 'Δ `|` R.+ = ('Δ `|` R).+.
  Proof. 
    have H0: R `<=` 'Δ `|` R by apply: subsetUr.
    have H1: 'Δ `<=` 'Δ `|` R by apply: subsetUl.
    have H2: 'Δ `|` R `<=` ('Δ `|` R).+  by apply: tcl_sub.
    have H3: R `<=`  ('Δ `|` R).+ by apply: (subset_trans  H0 H2).
    have H4: 'Δ  `<=`  ('Δ `|` R).+ by apply: (subset_trans  H1 H2).
    have H5: reflexive ('Δ `|` R).+. move =>x; have: 'Δ (x,x) by [];apply:H4.
    have H6: transitive ('Δ `|` R).+ by apply: tclos_trans.
    have H8:'Δ `|` R `<=` ('Δ `|` R.+) by apply: setUS;apply: tcl_sub.
    have H7: transitive ('Δ `|` R.+) by rewrite -rtclosE;apply: rtclos_trans.
    rewrite eqEsubset;split.
    + by rewrite -rtclosE rtclos_smallest;apply: @smallest_sub. 
    + by rewrite tclosE;apply: @smallest_sub.
  Qed.

  (** * Reflexive and Transitive Closure *)
  Lemma rtclos_compE1 R S: R.* `;` S.* = ('Δ `|` R.+) `;` ('Δ `|` S.+ ).
  Proof. by rewrite -!rtclosE. Qed.
  
  Lemma rtclos_compE2 R S: R.* `;` S.* = 'Δ `|` R.+ `|` S.+ `|` (R.+ `;` S.+). 
  Proof.
    by rewrite !rtclosE
         !compUr !compUl deltaK comp1x compx1 setUA.
  Qed.

  Lemma rtclos_idem R: R.*.* = R.* .
  Proof.
    rewrite eqEsubset; split; last by apply: rtclos_sub.
    by apply: rtclos_ind; [apply: rtclos_trans | apply: rtclos_refl |].
  Qed.
  
  Lemma rtclos_ind_l R S U:
    S `<=` U -> (R `;` U) `<=` U -> (R.* `;` S) `<=` U.
  Proof.
  move => hS hRU [x y] [z [h1 h2]].
  case: (@rtclos_iterUP R x z h1) => n hn; clear h1; move: x hn h2.
  elim: n => [x | n ihn x].
  - by rewrite iterU0 => -[_ /= ->] hz; apply: hS.
  - rewrite iterUS => -[[_ /= ->] hz | [u [hu hun]] hz]; first by apply: hS.
    by apply: (hRU (x,y)); exists u; split => //; apply: (ihn u).
  Qed.

  (* parameterless variant: R.* <= Z whenever 'Δ <= Z and R ; Z <= Z *)
  Lemma rtclos_ind_l1 R S:
    'Δ `<=` S -> (R `;` S) `<=` S -> R.* `<=` S.
  Proof. by move => hD hRS; rewrite -[X in X `<=` _]compx1; apply: rtclos_ind_l. Qed.
  
  Lemma rtclosK R: R.* `;` R.* = R.*. 
  Proof. by rewrite rtclos_compE2 -setUA tclosU_comp -setUA setUid -rtclosE. Qed.

  Lemma denest R S: (R `|` S).* = R.* `;` (S `;` R.*).* .
  Proof.
  have hD (U: relation T) : 'Δ `<=` U.* by apply: delta_rtclosS.
  set Z := (R.* `;` (S `;` R.*).*).
  have hDZ : 'Δ `<=` Z
    by rewrite /Z -[X in X `<=` _]comp1x; apply: compSS; apply: hD.
  rewrite eqEsubset; split.
  - apply: rtclos_ind_l1 => //.
    rewrite compUl subUset;split.
    + rewrite /Z -compA; apply: compSl.
      by rewrite comp_rtclosE; apply: tclos_rtclosS.
    + rewrite /Z -compA.
      apply: (subset_trans (_ : _ `<=` (S `;` R.*).*)).
      * by rewrite comp_rtclosE; apply: tclos_rtclosS.
      * by rewrite -[X in X `<=` _]comp1x; apply: compSl; apply: hD.
  - have hR : R.* `<=` (R `|` S).*
      by apply: rtclosS; apply: subsetUl.
    have hS : (S `;` R.*) `<=` (R `|` S).*.
      rewrite -[X in _ `<=` X]rtclosK; apply: compSS => //.
      by apply: (subset_trans (@subsetUr _ R S)); apply: rtclos_sub.
    have hS2 : (S `;` R.*).* `<=` (R `|` S).*
      by rewrite -[X in _ `<=` X]rtclos_idem; apply: rtclosS.
    by rewrite /Z -[X in _ `<=` X]rtclosK; apply: compSS.
  Qed.
                
  (** * Foresets *)
  
  Lemma fsetT X: 'Δ#X = X.
  Proof. by rewrite predeqE => x;split =>[[x' [/deltaTP -> ?]] //| ?];exists x;rewrite deltaTP. Qed.
  
  Lemma fset_deltaE X Z: Δ_(Z)#X = Z `&` X.
  Proof. by rewrite /fset/delta predeqE/= => x;split => [[x' [[? <-] ?]] //| [? ?]];exists x. Qed.
  
  Lemma fset_deltaCE X Y: Δ_(Y.^c)#X = X `\` Y.
  Proof.
    rewrite /fset/delta/setC predeqE /= => x;split;first by move => [x' [[? <-] ?]].
    by move => [? ?];exists x.
  Qed.
  
  Lemma fsetS R S X: R `<=` S -> R#X `<=` S#X.
  Proof. by move => H x [y [? ?]];by exists y;split;[apply: H |]. Qed.
  
  Lemma fsetSr R X Y: X `<=` Y -> R#X `<=` R#Y.
  Proof. by move => H x [y [? ?]];exists y;split;[|apply: H]. Qed.
  
  Lemma set_inc2 X x: x \in X <->  [set x] `<=` X.
  Proof. by split => [/set_mem ? y /= -> // |];rewrite in_setE;apply. Qed.
  
  Lemma fset_comp R S X: S # (R # X) = (S `;` R) # X.
  Proof.
    rewrite /fset /compose /fset predeqE /=.
    move => x; split => [ [z [? [y [? ?]]]] | [ y [[z [? ?]] ?]]].
    by (exists y);split;[exists z;split|]. 
    by (exists z);split;[|exists y].
  Qed.
  
  Lemma fsetUl R S X: S#X `|` R#X = (S `|` R) # X.
  Proof.
    rewrite /fset /setU predeqE /= => x; split. 
    by move => [[y [? ?]] | [y [? ?]]];exists y;[split;[left|]|split;[right|]].
    by move => [y [[?|?] ?]];[left|right];exists y.
  Qed.

  Lemma Fset_s R x y: R#_(x) y <-> R (y,x).
  Proof. by split => [[y' [H1 /= <-] //] | ?];exists x. Qed.
  
  Lemma fsetUr R X Y: R#(X `|` Y) = (R#X) `|` (R#Y).
  Proof.
    rewrite /fset /setU predeqE /= => x; split. 
    by move => [z [? [?|?]]];[left|right];exists z.
    by move => [[y [? ?]]|[y [? ?]]];exists y;[split;[|left]|split;[|right]].
  Qed.

  Lemma FsetI R X Y: R#(X `&` Y) `<=` (R#X) `&` (R#Y).
  Proof.  by move => x [y [? [? ?]]];split;exists y. Qed.

  (* Foreset in extension *)
  Lemma fset_bigP R X x: (R#X) x <-> exists y, X y /\ R#_(y) x.
  Proof. by split => [[y [? ?]]|[y [+ [z [+ /= H3]]]]];[(exists y);rewrite Fset_s| rewrite H3;exists y]. Qed.
  
  Lemma fset1_compVP R S x y: (exists z, R#_(x) z /\ S#_(y) z) <-> (R^-1 `;` S) (x,y). 
  Proof. split.
    by move => [z [/fset_bigP [x' [/= -> /Fset_s ?]] /fset_bigP [y' [/= -> /Fset_s ?]]]];(exists z).
    by move => [z /= [H1 H2]];exists z;rewrite 2!Fset_s.
  Qed.

  Lemma fset1_refl R: forall (x:T), reflexive R -> R#_(x) x. 
  Proof. by move => x H;rewrite /fset /mkset;exists x.   Qed.
  
  Lemma fset1_rtclos R: forall (x:T), R.*#_(x) x. 
  Proof. by move => x; exists x;split;[apply: rtclos_refl |]. Qed.
  
  Lemma fset_restrict R X Y : X `<=` Y -> R#X = (R `;` Δ_(Y))# X.
  Proof.
    rewrite predeqE /= => H x.
    split => [[y [H1 H2]]|[y [[z [/= H1 /deltaE [_ <-]]] H4]]];last by (exists z).
    by (exists y);split;[exists y;split;[by [] |by split;[apply H|]]|]. 
  Qed.
  
  Lemma fset1P0 R: forall (x y:T), R (x, y) <-> R#_(y) x. 
  Proof. by move => x y ; split => [H1 | [z [H1 /= <-]]];[exists y |]. Qed.

  Lemma fset1_tclos R x y: R (x, y) -> R.+#_(y) x. 
  Proof. by move => ?;exists y;split;[exists 1;[|rewrite iter1]|]. Qed.
  
  Lemma fset1_tclos_step R: forall (x y:T), (exists (x1:T), R (x, x1) /\ R.+#_(y) x1) -> R.+#_(y) x. 
  Proof.
    move => x y' [x1 [H1 [y [[n /=H2' H2] <-]]]];exists y;split;last by exact. 
    by exists (n.+1);[|rewrite iterSl;exists x1].
  Qed.
  
  Lemma fset1_tclos_stepr R: forall (x y z:T), R.+#_(y) x /\ R (y, z) -> R.+#_(z) x. 
  Proof.
    move => x y z [[t [[n /= H1' H1] /= <-]] H3].
    by exists z;split;[exists (n.+1);[| rewrite iter_compose1r;exists t]|].
  Qed.
  
  Lemma fset1_tclosS R: forall (y z:T), R (y, z) -> ( R.+#_(y) `<=` R.+#_(z) ).
  Proof. by move => y z ? x ?;apply fset1_tclos_stepr with y. Qed.

  Lemma fset1_tclosSr R: forall (y z:T), y \in R.+#_(z) -> (R.+#_(y) `<=` R.+#_(z) ).
  Proof.
    move => y z /set_mem H1 t;move:H1;rewrite -3!fset1P0 => H1 H2.
    by apply: (tclos_trans H2 H1). 
  Qed.

  (** * Elements for Foreset Topology *)

  (** * fset and bigcup *)
  Lemma fset_bigcup R: forall (I: Type) (F : I -> set T),
      R#( \bigcup_ i (F i) ) =  \bigcup_ i (R# (F i)).
  Proof.
    move => I F;rewrite /fset predeqE => x;split.
    by move => [y [H1 [n Pn Fny]]]; exists n;[ | exists y].
    by move => [n Pn [y [H1 H2]]];exists y;split;[|exists n].
  Qed.
  
  (** * fset and bigcap *)
  Lemma fset_bigcapS R: forall (I: Type) (F : I -> set T),
      R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)).
  Proof.
    by move => I F x [y [H1 H2]];exists y; split;[| apply: H2]. 
  Qed.
  
  Lemma fset_stableU R: forall (I: Type) (F : I -> set T),
      (forall i, R#(F i) `<=` (F i)) -> R#(\bigcup_ i (F i)) `<=` (\bigcup_ i (F i)).
  Proof.
    by move => I F H1;rewrite fset_bigcup => x [n Pn Fn];exists n;[|apply: H1].
  Qed.

  Lemma fset_stableI R: forall (I: Type) (F : I -> set T),
      (forall i, R#(F i) `<=` (F i)) -> R#(\bigcap_ i (F i)) `<=` (\bigcap_ i (F i)).
  Proof.
    move => I F H1. 
    have H2: (\bigcap_ i R#(F i)) `<=` (\bigcap_ i (F i))
      by move => x H2 i /H2/H1 H3.
    have H3: R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)) by apply:fset_bigcapS.
    by apply: (subset_trans H3 H2).
  Qed.
  
  Lemma fset_stableI2 R: forall (A B: set T),
      R#A  `<=` A -> R#B  `<=` B -> R#(A `&` B)  `<=` A   `&` B.
  Proof.
    move => A B ? ?.
    have H1: (R#A) `&`  (R#B)  `<=`  A   `&` B by apply: setISS.
    apply: (subset_trans _ H1); apply: FsetI.
  Qed.
  
  Lemma Fset_0 R: R#set0 `<=` set0.
  Proof. by move => x [y [_ H1]]. Qed.

  Lemma fsetTS R: R#setT `<=` setT.
  Proof.  by []. Qed.

  (** * Ater sets *) 
  
  (* check that it coincide with usual definition *)
  Lemma asetE  R Y: (aset R Y) = [set x | exists (y: T), R (y,x) /\ Y y].
  Proof. by rewrite /aset/fset.  Qed.
  
  Lemma aset_bigcup R: forall (I: Type) (F : I -> set T),
      ( \bigcup_ i (F i) ):#R =  \bigcup_ i ((F i):#R).
  Proof.
    by move => I F;apply: fset_bigcup.
  Qed.

  Lemma aset_bigcapS R: forall (I: Type) (F : I -> set T),
      (\bigcap_ i (F i)):#R `<=`  \bigcap_ i ((F i):#R).
  Proof.
    by move => I F;apply: fset_bigcapS.
  Qed.

  Lemma aset_stableU R: forall (I: Type) (F : I -> set T),
      (forall i, (F i):#R `<=` (F i)) -> (\bigcup_ i (F i)):#R `<=` (\bigcup_ i (F i)).
  Proof.
    by move => I F H1;apply: fset_stableU.
  Qed.

  Lemma aset_stableI R: forall (I: Type) (F : I -> set T),
      (forall i, (F i):#R `<=` (F i)) -> (\bigcap_ i (F i)):#R `<=` (\bigcap_ i (F i)).
  Proof.
    by move => I F H1;apply: fset_stableI.
  Qed.
  
  Lemma aset_stableI2 R: forall (A B: set T),
      A:#R `<=` A -> B:#R `<=` B -> (A `&` B):#R  `<=` A `&` B.
  Proof.
    by move => A B ? ?;apply: fset_stableI2.
  Qed.
  
  Lemma aset0 R: set0:#R `<=` set0.
  Proof. by move => x [y [_ H1]]. Qed.
  
  Lemma asetTS R: setT:#R `<=` setT.
  Proof. by []. Qed.

  (** * Closures *) 
  
  Lemma clos1_refl R X: forall (x:T), Clos_(x | R, X) x.
  Proof. by move => x;exists x;split;[apply rtclos_refl|]. Qed.
  
  Lemma clos1P E W: forall (x y: T),  Clos_(x | E,W) y <-> (Δ_(W.^c) `;` E).* (y, x).
  Proof.
    move => x' y';split;first by move => [z [?  <-]].
    by move => ?;exists x';split.
  Qed.
  
  Lemma clos_bigP E W X x: Clos(X |E, W) x <-> exists y, X y /\ Clos_(y |E, W) x.
  Proof. by split; rewrite fset_bigP.  Qed.    
  
  Lemma closU E W X Y:  Clos(X `|` Y| E,W) = Clos(X| E,W) `|` Clos(Y| E,W).
  Proof. by rewrite fsetUr. Qed.
  
  Lemma clos1US E W : forall (X Y: set T) (x:T),
      X x -> Clos_(x| E,W) `<=` Clos(X `|` Y| E,W).
  Proof.
    move => X Y x' /asboolP/set_inc2 H1.
    have H2:  Clos_(x'|E,W) `<=` Clos(X | E,W) 
      by apply fsetSr.
    have H3:  Clos(X|E,W) `<=` Clos(X `|` Y|E,W)
      by apply fsetSr; apply subsetUl.
    by apply subset_trans with Clos(X|E,W).
  Qed.
  
  Lemma closUSl E W X Y: Clos(X| E,W) `<=` Clos(X `|` Y| E,W).
  Proof. by move => x; rewrite closU; left.  Qed.    
  
  Lemma closUSr E W X Y: Clos(X| E,W) `<=` Clos(Y `|` X| E,W).
  Proof. by move => x; rewrite closU; right. Qed.    
  
  Lemma clos_sub E W X: X `<=` W -> X `<=` Clos(X| E,W).
  Proof. by move => ? x ?;rewrite /fset /mkset;exists x;split;[apply rtclos_refl|].  Qed.    

  Lemma closU_subl E W X Y: X `<=` W -> X `<=` Clos(X `|` Y | E,W).
  Proof.
    move => H0.
    have H2: X `<=` Clos( X | E,W)  by apply:clos_sub.
    by apply: (subset_trans H2);apply: closUSl.
  Qed.

  Lemma closU_subr E W : forall (X Y: set T),
      Y `<=` W -> Y `<=` Clos(X `|` Y | E,W).
  Proof.
    move => X Y H0.
    have H2: Y `<=` Clos( Y | E,W)  by apply:clos_sub.
    by apply: (subset_trans H2);apply: closUSr.
  Qed.
  
  Lemma fset_deltaCU R X Y: 'Δ#X `|` R#Y = 'Δ#X `|` (Δ_(X.^c) `;` R)#Y.
  Proof. by  rewrite fsetT setUD -fset_deltaCE fset_comp. Qed.
  
  Lemma fset_iterU_deltaC R Y n: (iterU R n)#Y = (iterU ( Δ_(Y.^c) `;` R) n)#Y.
  Proof.
    elim:n => [ | n' H'];first by rewrite 2!iterU0.
    by rewrite 2!iterUS -2!fsetUl -[in RHS]fset_comp
            -[in RHS]H' [in RHS]fset_comp [in RHS]compA fset_deltaCU.
  Qed.
  
  Lemma fset_iterU_rtclosS R Y n: (iterU R n)#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
  Proof. by rewrite fset_iterU_deltaC;apply: fsetS;apply: iterU_rtclosS. Qed.
  
  Lemma fset_rtclos_deltaC R Y: (Δ_(Y.^c) `;` R).*#Y = R.*#Y.
  Proof.
    rewrite eqEsubset;split. 
    by apply: fsetS; apply: (rtclosS (@delta_compS _ Y.^c)).
    have E29_2:  R.*#Y `<=` (Δ_(Y.^c) `;` R).*#Y.
    move => x [z [H1 H2]];
           suff: exists n : nat, iterU R n (x, z); last by apply: rtclos_iterUP.
    by move => [n H3];(suff: (fset (iterU R n) Y) x; 
                      first by move => H; apply fset_iterU_rtclosS in H);
              exists z; split.
    by [].
  Qed.

  (* an other proof using  denest  *)
  Lemma fset_rtclos_deltaC_1 R Y: R.* `<=`  (Δ_(Y.^c) `;` R).* `;` ('Δ `|` Δ_(Y)`;` relT).
  Proof.
    have : R = 'Δ `;` R by rewrite comp1x.
    rewrite -{1}(setUv Y) setUC -deltaU compUl => H1.
    rewrite {1}H1 denest.
    apply:  compS; rewrite rtclosE; apply: setUS.
    rewrite compA (@tclos_deltal (R`;`(Δ_(Y.^c)`;`R).* ) Y).
    apply: compS.
    by apply: subrelT.
  Qed.

  Lemma fset_rtclos_deltaC' R Y: (Δ_(Y.^c) `;` R).*#Y = R.*#Y.
  Proof.
    rewrite eqEsubset;split.
    + move: (@fsetS (Δ_(Y.^c) `;` R).* R.* Y) => H1.
      by move: (@delta_compS R Y.^c) => /rtclosS/H1 H0.
    + have H1: ((Δ_(Y.^c) `;` R).* `;` ('Δ `|` Δ_(Y)`;` relT)) #Y `<=` Clos(Y|R,Y).
      {
        move => z.
        rewrite /fset /= => -[y [[y' [/= H2 [H3 | H3]]] H4]].
        ++ by rewrite deltaTP in H3;(exists y');split;[| rewrite H3 ].
           by exists y';split;[| move: H3 => [t /= [/deltaE [? _] _]]].
      }
      have H2:  R.*#Y `<=`  ((Δ_(Y.^c) `;` R).* `;` ('Δ `|` Δ_(Y)`;` relT))#Y
        by apply: fsetS;apply: fset_rtclos_deltaC_1.
      by pose proof (subset_trans H2 H1).
  Qed.
  
  (** *  Restriction of a relation to a subset *)

  Lemma restrictP R X (x y: T): 
    x \in X /\ y \in X -> (R (x,y) <-> (Δ_(X) `;` R `;` Δ_(X)) (x,y)).
  Proof.
    rewrite /compose /delta /mkset /=.
    move => [/set_mem H1 /set_mem H2];split=> [ H3 | [z [[t [[H3 ->] H4] [H5 <-]]]] //].
    by (exists y; split;[ exists x; split | ]).
  Qed.

  Lemma restrictPl R X (x y: T): x \in X -> (R (x,y) <-> (Δ_(X) `;` R) (x,y)).
  Proof. by move => /set_mem ?;split => [? | [z [[? /= ->] ?] ] //];(exists x; split). Qed.

  Definition Restrict R X :=  [set x | X x.1 /\ X x.2 /\ R x].
  
  (* equivalent expression with Dset *)
  Lemma restrict_subE R X: (Restrict R X) = (R |_(X)).
  Proof.
    rewrite predeqE => [[x y]].
    split => [[/= H1 [H2 H3]] | [z [[t [[/= H1 H'1] H2]] [/= H3 H'3]]]].
    by (exists y;split;[ exists x;split | ]).
    by split; [ | split; [rewrite -H'3 | rewrite H'1 -H'3]].
  Qed.
  
  Lemma delta_restrictT X: Δ_(X) = ('Δ |_(X)).
  Proof. by rewrite compx1 deltaK. Qed.

  Lemma delta_restrict X: Δ_(X) = (Δ_(X) |_(X)).
  Proof. by rewrite 2!deltaK. Qed.
  
  Lemma restrict_memP R X x y: (R |_(X)) (x,y) <-> X x /\ X y /\ R (x,y).
  Proof.
    by split => [[x' [[y' [/deltaE /= [? <-] ?]] /deltaE [? <-]]] //
               | [? [? ?]]];exists y;split;[exists x|].
  Qed.
  
  Lemma restrictK R X: (R |_(X)) |_(X) = R|_(X).
  Proof. by rewrite 2!compA deltaK -2!compA deltaK. Qed.
    
  Lemma tclos_restrict R X: (R |_(X)).+ = (R |_(X)).+ |_(X). 
  Proof. 
    by rewrite {1}compA  tclos_deltal -compA {1}tclos_deltar -compA.
  Qed.

  Lemma restrictU R S X: (R `|` S) |_(X) = (R |_(X)) `|` (S |_(X)).
  Proof.
    rewrite predeqE => -[x y];split. 
    by move => /restrict_memP [? [? [? | ?]]];[left|right];rewrite restrict_memP.
    by move => [|] /restrict_memP [? [? ?]];rewrite restrict_memP;split;[|split;[|left]| |split;[|right]].
  Qed.
  
  Lemma restrict_deltaUr R X: ('Δ `|` R|_(X))`;`Δ_(X) = ('Δ `|` R) |_(X).
  Proof. by rewrite compUl comp1x compA deltaK restrictU -delta_restrictT. Qed.
  
  Lemma restrict_deltaUl R X:  Δ_(X) `;` ('Δ `|` R|_(X)) = ('Δ `|` R) |_(X).
  Proof. by rewrite compUr compx1 -2!compA deltaK restrictU -delta_restrictT. Qed.
  
  Lemma restrict_deltaUK R X: ('Δ `|` R|_(X)) |_(X) = ('Δ `|` R) |_(X).
  Proof. by rewrite compA restrict_deltaUr -restrict_deltaUl -compA deltaK. Qed.
         
  Lemma restrict_iter_tclosS R S X: (forall n, R^(n.+1)|_(X) = S^(n.+1)|_(X)) -> R.+ |_(X) `<=` S.+ |_(X).
  Proof.
    move => H0  -[x y] /restrict_memP [H1 [H2 /tclos_iterP [n H3]]].
    have: R^(n.+1)|_(X) (x,y) by apply/restrict_memP. 
    rewrite (H0 n) => /restrict_memP [H1' [H2' H3']].
    by apply /restrict_memP;split;[|split;[|exists n.+1]].
  Qed.

  Lemma restrict_iter_tclosE R S X: (forall n, R^(n.+1)|_(X) = S^(n.+1)|_(X)) -> R.+ |_(X) = S.+ |_(X).
  Proof. by move => H0; rewrite eqEsubset; split; apply: restrict_iter_tclosS. Qed.
  
  Lemma restrict_iter_deltaU X R n: ('Δ `|` R|_(X))^(n.+1)|_(X) = (('Δ `|` R)|_(X))^(n.+1)|_(X).
    elim: n. by rewrite 2!iter1 restrict_deltaUK restrictK.
    move => n Hr.
    rewrite {1}iter_compose1r {1}compA {1}compA restrict_deltaUr.
    rewrite -[('Δ `|` R)|_(X) in LHS]restrictK -3!compA.
    rewrite Hr -[in Y in (_ `;` Y = _)]deltaK -compA.
    rewrite [(('Δ `|` R)|_(X))^(n.+1)|_(X)`;`('Δ `|` R)|_(X)`;`Δ_(X)]compA.
    rewrite [(('Δ `|` R)|_(X))^(n.+1)|_(X)`;`(('Δ `|` R)|_(X)`;`Δ_(X))]compA.
    rewrite [Δ_(X)`;`(('Δ `|` R)|_(X))^(n.+1)`;`(Δ_(X)`;`(('Δ `|` R)|_(X)`;`Δ_(X)))]compA.
    rewrite -[Δ_(X)`;`(('Δ `|` R)|_(X)`;`Δ_(X))]compA restrictK compA -iter_compose1r.
    exact.
  Qed. 
  
  Lemma restrict_tclos_deltaU X R: Δ_(X) `|` (R|_(X)).+ = (Δ_(X) `|` (R|_(X))).+.
  Proof. 
    rewrite [in LHS]tclos_restrict {1}delta_restrictT -restrictU.
    rewrite rclos_tclosE {5}delta_restrictT -restrictU  [in RHS]tclos_restrict.
    apply: restrict_iter_tclosE;apply: restrict_iter_deltaU.
  Qed.
  
  (* reflexive and transitive properties using relation equalities *)
  
  Lemma reflexive_rclosE R: reflexive R <-> R ='Δ  `|` R.
  Proof.
    split => [? | ->];last by move => ?;left.
    by rewrite eqEsubset;split =>[[? ?]|[? ?]];[move=> ?;right | move => [/deltaTP -> | ?]].
  Qed.

  Lemma transitive_iterS R: forall (n: nat), transitive R -> R^(n.+1) `<=` R.
  Proof.
    move => n H1.
    elim: n => [| n H2];first by rewrite iter1.
    rewrite -addn1 iter_compose iter1 => -[x z] -[y [/H2 /= H3 /= H4]].
      by apply: (H1 y x z). 
  Qed.
  
  Lemma transitive_tclosE R: transitive R <-> R = R.+.
  Proof. by split => [/@smallest_id H1 | ->];[rewrite tclosE H1|apply: tclos_trans]. Qed.
  
  Lemma rtclosE_refl_trans R: (reflexive R /\ transitive R) <-> R = R.*.
  Proof.
    split => [ | ->];last by by split;[apply: rtclos_refl R|apply: rtclos_trans].
    pose proof (@smallest_id _ (fun R => (reflexive R /\ transitive R)) R ) as H1.
    by move => /H1 H2; rewrite rtclos_smallest H2.
  Qed.
      
  (** * Asymmetric part of a relation *) 
  (* begin snippet asym:: no-out *)  
  Definition asym R: relation T := [set xy | R xy /\ ~ (R^-1 xy)].
  (* end snippet asym *)    

  Lemma asym_antisym R: antisymmetric (asym R).
  Proof. by move => x y [_ ?] [? _]. Qed.

  Lemma asym_irreflexive R: irreflexive (asym R).
  Proof. by move => x [? ?]. Qed.

  Lemma asym_asym R: asymmetric (asym R). 
  Proof. by rewrite (asym_antisymP (@asym_irreflexive R));apply: asym_antisym. Qed.
  
  Lemma asym_trans R: transitive R -> transitive (asym R).
  Proof.
    move => H0 y x z [H1 /= H1'] [H2 /= H2'];split => [ | /= H3].
    by apply: H0 H1 H2.
    by have: R (y,x) by apply: H0 H2 H3.
  Qed.
  
  Lemma asym_sporder R:  transitive R -> sporder (asym R).
  Proof.
    by move => ?;split;[apply: asym_irreflexive|apply: asym_trans].
  Qed.
  
  Lemma asymE R: asymmetric R <-> asym R = R.
  Proof.
    split => [Has | <-];last by apply: asym_asym.
    by rewrite predeqE => -[x y];split => [[_ ?]// | /[dup] ? /Has ?].
  Qed.
  
  Lemma asymP R: antisymmetric R /\ irreflexive R <-> asymmetric R.
  Proof.
    split => [[Has Hi] | /[dup] /asym_irr Hi /(asym_antisymP Hi) ? //].
    by rewrite (asym_antisymP Hi).
  Qed.
  
  Lemma asym_antisym_irrE R: antisymmetric R /\ irreflexive R <-> asym R = R.
  Proof. rewrite -asymE;apply:asymP. Qed.
  
  Lemma asymS R: (asym R) `<=` R.
  Proof. by move => [a b] [? _]. Qed.

  Lemma asymK R: asym (asym R) = (asym R).
  Proof. by move: (@asym_asym R) => /asymE. Qed.
  
  Lemma comp_asymS R: R.+ `;` asym(R.+) `<=` asym(R.+).
  Proof.
    move: asymS => /(_ R.+) H3 => [[x y] [z /= [H1 /[dup] H2 /H3 H4]]].
    split =>[| H5]; first by apply: (tclos_trans H1 H4).
    have H6: R.+ (y,z) by apply: (tclos_trans H5 H1).
    by move: H2 => [_ H2].
  Qed.
  
  Lemma asym_compS R: asym(R.+) `;` R.+ `<=`  asym(R.+).
  Proof.
    move: asymS => /(_ R.+) H3 => [[x y] [z /= [/[dup] H2 /H3 H4 H1]]].
    split =>[| H5]; first by apply: (tclos_trans H4 H1).
    have H6: R.+ (z,x) by apply: (tclos_trans H1 H5).
    by move: H2 => [_ H2 ].
  Qed.

  Lemma sporder_asymE R: sporder R -> (asym R.+) = R.
  Proof.
    by move => [Hi /[dup] Ht /transitive_tclosE <-];apply/asymE/sporder_asym.
  Qed.
  
  (** * Independent sets with respect to a relation *)
  
  Lemma indepS R S X: R `<=` S -> indep S X -> indep R X.
  Proof. by move => H1 H2 x y H3 H4 H5;move: (H2 x y H3 H4 H5) => ? /H1 ?. Qed.

  Lemma indep_symE R X: indep R X <-> indep (R `|` R^-1) X.
  Proof. 
    have H1:  R `<=` R `|` R^-1 by apply: subsetUl.
    split => [H2 x y P1 P2 P3 [H3| H3]|];last by apply: (indepS H1).
    by apply: (H2 x y _ _ _).
    have P3': y <> x by move => H5;rewrite H5 in P3.
    by apply: (H2 y x _ _ _).
  Qed.
  
  Lemma indepV R X: indep R X -> indep R^-1 X.
  Proof. 
    by move => H1;rewrite indep_symE inverseK setUC -indep_symE.
  Qed.
  
  Lemma indep_memP x y R X: x \in X -> y \in X -> ~ (x = y) -> indep R X 
                            -> ~ (( R `|` R^-1) (y,x)).
  Proof.
    move => H1 H2 H3 H4. 
    have H6: ~ (y = x) by move =>I1;rewrite I1 in H3.
    move => [ ? | ? ];first by move: H4 => /(_ y x H2 H1 H6).
    by move: H4 => /(_ x y H1 H2 H3).
  Qed.
  
  Lemma indepSr R X Y: X `<=` Y -> indep R Y -> indep R X.
  Proof. 
    move => H1 H2 x y /set_mem/H1/mem_set H3 /set_mem/H1/mem_set H4 H5.
    by move: (H2 x y H3 H4 H5).
  Qed.
  
  Lemma indep0 R: indep R set0.
  Proof. by move => x y /set_mem H3 _ _ _. Qed.
  
  Lemma indep1 R: forall (x: T), indep R [set x].
  Proof. by move => x x1 x2 /set_mem -> /set_mem -> ?. Qed.
  
  Lemma indepU R: forall X x,
      indep R X -> ~(x \in R#X) -> ~(x \in (X:#R)) -> indep R (X `|` [set x]).
  Proof.
    move => X x H2 H3 H4 x1 x2 /set_mem 
             [/mem_set H5 | /mem_set H5] /set_mem [/mem_set H6 |/mem_set H6] H7 H8.
    rewrite /indep in H2.
    + by apply: ((H2 x1 x2) H5 H6 H7 H8).
    + move: H6 H4 => /set_mem <- H4. 
      by have H9: x2 \in X:#R by rewrite inE;exists x1; rewrite inE in H5.
    + move: H5 H3 => /set_mem <- H3. 
      by have H9: x1 \in R#X by rewrite inE;exists x2;rewrite inE in H6.
    + by move: H5 H6 H7 => /set_mem -> /set_mem ->. 
  Qed.
  
  (** * Partition induced by an Equivalence Relation *)
  
  (* Définition de la classe d'équivalence de x *)
  Definition class_of R (x : T) := [set y: T| R (x,y)].

  Definition Quotient R := {E : set T| exists x : T, E = class_of R x }.

  (* Ensemble des classes d'équivalence (possiblement avec répétitions) *)
  Definition Classes R:= [set C | exists x:T, C = class_of R x].
  
  (* Lemme 1 : Chaque classe est non vide *)
  Lemma classes_neq0 R: equivalence R -> forall C, Classes R C -> (C != set0).
  Proof. by move => [R_ref _ _ ] C -[x0 ->];rewrite set0P;exists x0. Qed.
  
  (* Lemme 2 : Deux classes sont égales ou disjointes *)
  Lemma classes_disjoint R:
    equivalence R -> forall (x y: T), (exists z, R (x,z) /\ R (y,z)) -> class_of R x = class_of R y.
  Proof.
    move => [R_ref R_tr R_sy] x z [y [Rxy Rzy]].
    rewrite predeqE;move => t;split;rewrite/class_of/mkset => Hr.
    by pose proof (R_tr x z t (R_tr y z x Rzy (R_sy x y Rxy)) Hr).
    by pose proof (R_tr z x t (R_tr y x z Rxy (R_sy z y Rzy)) Hr).
  Qed.

  (* Lemme 3 : Toute l'union des classes couvre T *)
  Lemma classes_cover R: equivalence R -> forall x : T, exists C : set T, Classes R C /\ C x.
  Proof.
    move => [R_ref _ _] x; exists (class_of R x).
    by split;[rewrite /Classes/mkset;exists x;exact| rewrite /class_of/mkset].
  Qed.

  Lemma classes_bigcupT R:  equivalence R -> \bigcup_ (C in (Classes R)) (fun C  => C) C = setT.
  Proof.
    move => He;rewrite predeqE => x;split => [// | _].
    by move: (classes_cover He x) => [C [H1 H2]];  exists C.
  Qed.

  Lemma classes_eq_disjoint R (C C': set T): equivalence R ->
                                  C \in Classes R -> C' \in Classes R -> (exists z, C z /\ C' z) -> C = C'.
  Proof.
    move => He /set_mem [x ->] /set_mem [x' ->] [z H1].
    by apply: ((classes_disjoint He) x x');exists z.
  Qed.
  
  Lemma setI_neq0P (C C': set T):
    (C `&` C') != set0 <-> exists z, C z /\ C' z.
  Proof.  by rewrite set0P;split;move => [z [? ?]];exists z. Qed.

End Relation_Facts.

Section Restrict_to_subset.
  
  (** * Considering (R: relation S) with (S: set T) *)

  Context (T: eqType).
  Implicit Types (R S: relation T) (X: set T).

  (** some helpers to understand sval *)
  Lemma mem_sval X (v: X) : ((sval v) \in X).
  Proof. by rewrite inE; apply: set_valP. Qed.

  Lemma mem_svalP X v: (v \in X) -> exists v' : X, v = sval v'.
  Proof. by move => H0;exists (exist _ v H0). Qed.
  
  Definition restrict_sub (T: Type) (X:set T) (R: relation T): relation X := 
    [set xy : X*X | R ((sval xy.1),(sval xy.2))].
  
  Lemma restrict_subK R X: (@restrict_sub _ X R) = (@restrict_sub _ X (R |_(X))).
  Proof.
    rewrite /restrict_sub predeqE => -[x y] /= ; split; last first.
    by move => [z [[t [/deltaE /= [_ <-] H4]] /deltaE [_ <-]]].
    move => H1;exists (sval y);split;last by rewrite deltaE /=;split;[apply: set_valP|].
    by (exists (sval x));rewrite deltaE /=;split;[split;[apply: set_valP|]|].
  Qed.
  
  Definition extend (T: Type) (X:set T) (R: relation X) :=
    [set xy | exists x : X, exists y: X, xy.1 = (sval x) /\ xy.2 =(sval y) /\ R (x,y)].

  Lemma extend_restrictK X R: @extend _ X (@restrict_sub _ X R) = (R |_(X)).
  Proof.
    rewrite restrict_subK predeqE /restrict_sub => -[x y]; split.
    by move => [x' [y' /= [-> [-> H3]]]].
    move => /[dup] H0 [z [[t [/deltaE /= [/mem_set H1 H1'] H4]] /deltaE [/mem_set H2 H2']]].
    rewrite H2' in H2.
    move: (H1) (H2) => /mem_svalP [x' H1''] /mem_svalP [y' H2''].
    by exists x';exists y';rewrite /mkset -H1'' -H2''.  
  Qed.
  
  Lemma extendU X (R S: relation X): (extend R) `|` (extend S) = extend (R `|` S).
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [|] [x' [y' /= [H2 [H3 H4]]]].
      by (exists x';exists y');rewrite -H2 -H3 /=;split;[|split;[|left]].
      by (exists x';exists y');rewrite -H2 -H3 /=;split;[|split;[|right]].
    + move => [x' [y' /= [H2 [H3 [H4 | H4]]]]].
      by left;(exists x';exists y');rewrite -H2 -H3 /=. 
      by right;(exists x';exists y');rewrite -H2 -H3 /=. 
  Qed. 
  
  Lemma extend_comp X (R S: relation X): extend (R `;` S) = extend R `;` extend S.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [x' [y' /= [? [? [z' /= [? ?]]]]]].
      by exists (sval z');split;[exists x';exists z'| exists z';exists y'].
    + move => [z [[x' [z' /= [-> [-> H3]]]]] [z'' [y' /= [H4 [-> H6]]]]].
      exists x';exists y';split;[exact|split;[exact|]].
      by exists z';split;[| have ->: z' = z'' by apply: val_inj].
  Qed.
  
  Lemma extend_iter X R n: @extend _ X (@restrict_sub _ X R)^(n.+1) = (R |_(X))^(n.+1).
  Proof.
    elim: n => [| n Hn];first by rewrite !iter1 extend_restrictK.
    rewrite -addn1 (iter_compose (R|_(X)) n.+1 1) (iter_compose (restrict_sub R) n.+1 1).
    by rewrite extend_comp Hn !iter1 extend_restrictK.
  Qed.

  Lemma extend_tclos X R: @extend _ X (@restrict_sub _ X R).+ = (R |_(X)).+.
  Proof.
    rewrite predeqE => -[x y];split.
    + move => [x' [y' /= [? [? H3]]]]. 
      move: H3 => /(@tclos_iterP _ ((@restrict_sub _ X R)) x' y') [ n H3].
      by (exists n.+1);[| rewrite -extend_iter;(exists x';exists y')].
    + move => /(@tclos_iterP _ (R|_(X)) x y) [n H3];move: H3; rewrite -extend_iter. 
      by move => [x' [y']] H1;(exists x';exists y');move: H1 => [-> [-> /iterS_tclos ?]]. 
  Qed.

  Lemma restrict_subP R S X: (R |_(X)) = (S |_(X)) <-> (@restrict_sub _ X R) = (@restrict_sub _ X S).
  Proof.
    by split => [H|H];[rewrite (restrict_subK R) (restrict_subK S) H| rewrite -2!extend_restrictK H].
  Qed.
  
  Lemma restrict_extendK X (R:relation X): (@restrict_sub _ X (extend R)) = R.
  Proof.
    rewrite predeqE => -[x y]; split;last by (exists x;exists y).
    by move => [x' [y' /= [/val_inj <- [/val_inj <- ?]]]].
  Qed.
  
  Lemma restrict_deltaT X: ('Δ: relation X) = (@restrict_sub _ X 'Δ).
  Proof. 
    rewrite predeqE => -[x y];split;first by move => /@deltaTP ->. 
    by move => /deltaTP/= H1; rewrite deltaTP;apply: val_inj.
  Qed.
  
  Lemma restrict_subU X R S: (@restrict_sub _ X R) `|` (@restrict_sub _ X S) = (@restrict_sub _ X (R `|` S)).
  Proof. by rewrite predeqE => -[x y];split;move => [?|?];[left|right|left|right]. Qed.
  
  Lemma restrict_tclos_deltaUE X R: (Δ_(X) `|` (R|_(X)).+) = (Δ_(X) `|` (R|_(X))).+.
  Proof. 
    rewrite {4}delta_restrictT -restrictU.
    rewrite [in LHS]tclos_restrict {1}delta_restrictT -restrictU.
    rewrite -extend_tclos -extend_restrictK -restrict_subU -extend_tclos restrict_extendK
             -restrict_deltaT rclos_tclosE restrict_deltaT restrict_subU.
    by [].
  Qed.
  
End Restrict_to_subset.

Section Infinite_paths.
  (** * Definitions around infinite paths *)

  Context (T : Type).
  Implicit Types (T : Type) (R S: relation T) (A B: set T).
  
  (* total (or left total)  *) 
  (* begin snippet lefttotal:: no-out *)  
  Definition total_rel R := forall x, exists y, R (x,y).
  (* end snippet lefttotal *)
  
  Definition total_ex R := exists f : T -> T, forall x, R (x, f x). 
  
  (* using coercion to rel T and choice lemma on rel T *)
  Lemma total_totalexP R: total_rel R -> total_ex R.
  Proof.
    move => Htr.
    have /choice [f Rxfx] x: exists y, ((rel_of R): rel T) x y
        by move: Htr => /(_ x) [y Rxy]; exists y;apply/asboolP.
    by exists f => x; move: Rxfx => /(_ x)/asboolP. 
  Qed.
  
  Lemma totalP R: total_rel R <-> total_ex R.
  Proof. by split =>[| [f H1] x];[apply: total_totalexP | exists (f x)].  Qed.
  
  Definition total_rel'' (R: relation T) := 
    (forall x, exists f : nat -> T, f 0 = x /\ forall n, R ((f n),(f (S n)))).
  
  Lemma total_ex_fun R:  total_ex R -> total_rel'' R.
  Proof. 
    by move => [f H1] x; exists (fun n => ssrnat.iter n f x);rewrite /=.
  Qed.
  (* begin snippet iicfun:: no-out *)  
Definition iic_fun R f:= forall n, R ((f n),(f (S n))).
  (* end snippet iicfun *)  
  (* begin snippet iic:: no-out *)  
Definition iic R := exists f, iic_fun R f.
  (* end snippet iic *)
  
  (* begin snippet iicinj:: no-out *)  
Definition iic_inj R := 
  exists f, (forall n, R (f n,f (S n))) /\ injective f.
  (* end snippet iicinj *)  

  Lemma total_fun_iic R: (nonempty [set: T]) ->  total_rel'' R -> iic R. 
  Proof. by move => -[v0 H1] /(_ v0) [f [H2 H3]]; exists f. Qed.
  
  (** * total_iic as a lemma deduced from choice *)
  Lemma total_iic R: (nonempty [set: T]) ->  total_rel R -> iic R. 
  Proof.
    by move => H0 /totalP/total_ex_fun/(total_fun_iic H0) H1.
  Qed.
  
  (* begin snippet Rloop:: no-out *)    
  Definition rloop (R: relation T) := exists v, forall w,  R (v,w) -> R (w,v).
  (* end snippet Rloop *)
  
  Lemma rloop_fsetS v R:  (forall w,  R (v,w) -> R (w,v)) -> [set v]:#(R) `<=` R#([set v]).
  Proof.
    move => Rl w H1;move: Rl => /(_ w) H2.
    rewrite /fset;exists v;split;last by [].
    by apply/H2;move: H1;rewrite /aset Fset_s => H1.
  Qed.
  
  Lemma rloop_not_total R: (antisymmetric R /\ irreflexive R /\ rloop R) -> (~ (total_rel R)).
  Proof.
    move => [H1 [H1' [v H2]]].
    rewrite -existsNP; exists v; rewrite -forallNE => x /[dup] H3 /H2 H4.
    have H5: x = v by apply: H1.
    by move: H3; rewrite H5 => /H1'.
  Qed.
  
  Lemma not_total_ex R: (~ (total_rel R)) -> exists v, (forall x : T, ~ R (v, x)).
  Proof. by rewrite -existsNP => -[v H1];exists v;move: H1; rewrite -forallNE. Qed. 

  Lemma ex_rloop R: (exists v, (forall x : T, ~ R (v, x)))-> rloop R.
  Proof. by move => -[v H1];exists v => y /H1 H2. Qed. 

  Lemma not_rloop_total_asym R: ~ (rloop R) -> total_rel (asym R).
  Proof. 
    by rewrite -forallNE => H1 v;move: H1 => /(_ v)/existsNP [w /not_implyP H1];exists w.
  Qed.

  Lemma rloop_asym R: (rloop R) -> rloop (asym R).
  Proof.
    by move => [v H1];exists v => w [H2 H3];split;[apply: H1| move: H2 => /H1 H2].
  Qed.

  Lemma rloop_ex_asym R: (rloop R) -> exists v, (forall x : T, ~ ((asym R) (v, x))).
  Proof. by move => [v H1];exists v => w [/H1 H2 H3]. Qed.
  
  Lemma not_iic_rloop R: (nonempty [set: T]) -> ~ (iic (asym R)) -> (rloop R).
  Proof. by move => H0; apply contraPP => /not_rloop_total_asym/(total_iic H0) H1.  Qed.
  
  Lemma iicS R S: R `<=` S -> (iic R) -> (iic S).
  Proof.
    by move => Hsub [f H];exists f;move: H => + n =>/(_ n)/Hsub ?.
  Qed.
  
End Infinite_paths.


Section ZornRelation.
  (** * Zorn Lemma for relations : we use the Zorn Lemma from classical_sets *)
  (** * using rel_of to obtain a rel T relations from a relation T *)
  
  Context (T: Type).
  

  (* begin snippet chains:: no-out *)  
Definition chains (R: relation T) := 
  [set C: set T| forall (c1 c2: T), C c1 -> C c2
      ->  R (c1,c2) \/ R (c2,c1)].
  (* end snippet chains *)  

  Lemma zorn_rel (R: relation T) : 
    porder R
    -> (forall A : set T, chains R A -> exists t : T, forall s : T, A s -> R (s, t))
    -> exists t, forall s, R (t, s) -> s = t.
  Proof.
    move => [Hr Ha Ht] Htotal. 
    pose S:= (rel_of R).
    have RS_iff s t:  S s t <-> R (s,t) by split;rewrite /S/rel_of => /asboolP.
    have Sr t: S t t by rewrite asboolE;apply Hr.
    have Sa s t: S s t -> S t s -> s = t by rewrite 2!asboolE;apply Ha. 
    have St r s t: S r s -> S s t -> S r t by rewrite 3!asboolE;apply Ht.
    have HT A: total_on A (fun x x0 : T => S x x0) -> exists t : T, forall s : T, A s -> S s t.
    move => H1. 
    have H2 s t: A s -> A t -> R (s, t) \/ R (t, s) by rewrite -2!RS_iff; exact: H1.
    by move: H2 => /Htotal [t H2];(exists t => s);rewrite RS_iff;apply: H2.
    (* end have HT *)
    move: (@Zorn T S Sr St Sa HT) => [t Hz].
    by exists t => s;rewrite -RS_iff;apply: Hz.
  Qed.
  
End ZornRelation.

