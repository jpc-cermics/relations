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
(* Correspondance entre rel.v (relation T = set (T*T)) et la bibliothèque      *)
(* RelationAlgebra (hrel T T = T -> T -> Prop), afin de pouvoir utiliser les   *)
(* tactiques de décision ka, kat et hkat.                                      *)
(*                                                                             *)
(* Dictionnaire des opérations:                                                *)
(*                                                                             *)
(*   rel.v          RelationAlgebra                                            *)
(*   -----------------------------------------------------------------------   *)
(*   relation T     hrel T T         (T*T) -> Prop  /  T -> T -> Prop          *)
(*   R = S          R ≡ S     (weq)  égalité / équivalence extensionnelle      *)
(*   R `<=` S       R ≦ S     (leq)  inclusion                                 *)
(*   R `;` S        R ⋅ S     (dot)  composition                               *)
(*   'Δ             1         (one)  identité                                  *)
(*   'Δc            0         (bot)  relation vide                             *)
(*   set0           0         (bot)  relation vide                             *)
(*   setT           top       (top)  relation pleine                           *)
(*   R `|` S        R + S     (cup)  union                                     *)
(*   R `&` S        R ∩ S     (cap)  intersection                              *)
(*   R.^c           !R        (neg)  complémentaire                            *)
(*   R^-1           R°        (cnv)  converse                                  *)
(*   R.*            R^*       (str)  clôture réflexive-transitive              *)
(*   R.+            R^+       (itr)  clôture transitive                        *)
(*   Δ_(X)          [pset X]  (inj)  test KAT                                  *)
(*   Δ_(X.^c)       [!pset X]        test complémenté                          *)
(*   L_(X)          [pset X]⋅top                                               *)
(*   R_(X)          top⋅[pset X]                                               *)
(*   R |_(X)        [pset X]⋅R⋅[pset X]                                        *)
(*                                                                             *)
(* Ensembles (vus comme vecteurs, cf. [vec] et la section Vec):                *)
(*   set T          hrel T unit      relation hétérogène vers un singleton     *)
(*   X = Y          vec X ≡ vec Y                                              *)
(*   X `<=` Y       vec X ≦ vec Y                                              *)
(*   R#X            R ⋅ vec X        foreset                                   *)
(*   X:#R           R° ⋅ vec X       afterset                                  *)
(*   X `|` Y        vec X + vec Y                                              *)
(*   X `&` Y        vec X ∩ vec Y                                              *)
(*   set0 / setT    0 / top                                                    *)
(*                                                                             *)
(* Transport:                                                                  *)
(*   to_hrel R : hrel T T      de rel.v vers RelationAlgebra                   *)
(*   of_hrel H : relation T    de RelationAlgebra vers rel.v                   *)
(*   pset X    : dset T        de set T vers les tests (booléens) de KAT       *)
(*   vec X     : hrel T unit   de set T vers les vecteurs                      *)
(*                                                                             *)
(* Tactiques fournies:                                                         *)
(*   to_ra_goal : met le but sous forme RelationAlgebra.  Reconnaît R = S,     *)
(*                R `<=` S, reflexive R, symmetric R, transitive R, ainsi que  *)
(*                X = Y et X `<=` Y sur les ensembles (via vec)                *)
(*   to_ra      : idem, en transportant aussi les hypothèses                   *)
(*   rka        : to_ra_goal puis ka      (algèbre de Kleene)                  *)
(*   rkat       : to_ra_goal puis kat     (algèbre de Kleene avec tests)       *)
(*   rhkat      : to_ra      puis hkat    (idem, avec hypothèses de Hoare)     *)
(*   rlattice   : to_ra_goal puis lattice (treillis borné: `|`, `&`, set0, setT)*)
(*   rra        : to_ra_goal puis ra      (normalisation, buts plus faibles)   *)
(*   ra_cnv     : pousse le converse vers les atomes (cnvdot, cnvstr, ...)     *)
(*   rka_cnv    : to_ra_goal puis ra_cnv puis ka                               *)
(*   rkat_cnv   : to_ra_goal puis ra_cnv puis kat                              *)
(*                                                                             *)
(* Limites (cf. la section Limites en fin de fichier):                         *)
(*   - ka/kat/hkat ne décident pas les fragments contenant ^-1 (converse),     *)
(*     `&` (intersection), .^c (complément) ou setT (top).                     *)
(*   - pour le converse, ra_cnv le pousse vers les atomes (R° devient un       *)
(*     atome frais): rka_cnv/rkat_cnv sont alors corrects mais incomplets.     *)
(*     C'est suffisant en pratique (cf. paper_relations.v).                    *)
(*   - lattice ne décide que le fragment treillis borné, sans distributivité.  *)
(*   - hkat n'élimine que les hypothèses de Hoare (x ≡ 0, [c];p ≡ [c], ...);   *)
(*     une hypothèse de monotonie comme R `<=` S n'en fait pas partie.         *)
(*   - sur un but ensembliste (donc typé), hkat échoue d'emblée: il annonce    *)
(*     "typed hkat is not supported yet".  ka et kat, eux, acceptent le typé.  *)
(*                                                                             *)
(* Les autres tactiques de RelationAlgebra (ra_normalise, mrewrite, dual,      *)
(* solve_rmov, aac_rewrite, ...) s'emploient après to_ra_goal; elles sont      *)
(* recensées dans probe/tactiques-RA.md.                                       *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Warnings "-parsing -coercions -notation-incompatible-prefix".
From mathcomp Require Import all_boot order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
(* Export (et non Import): les clients de ce fichier ont besoin des instances *)
(* Proper de RelationAlgebra, sans lesquelles setoid_rewrite ne descend pas    *)
(* sous les opérations et la traduction s'arrête à la première passe.          *)
From RelationAlgebra Require Export kat normalisation rewriting kat_tac rel.
Set Warnings "parsing coercions notation-incompatible-prefix".

(* rel.v est chargé en dernier, et exporté: ses noms (relation, compose,      *)
(* iter, ...) doivent masquer chez les clients ceux de RelationAlgebra.rel et  *)
(* de Stdlib (Relation_Definitions.relation).  Importer rel_ra suffit donc,    *)
(* et doit se faire APRÈS les autres imports mathcomp.                         *)
From RL Require Export rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * Transport entre [relation T] et [hrel T T] *)

Definition to_hrel (T: Type) (R: relation T) : hrel T T := fun x y => R (x,y).
Definition of_hrel (T: Type) (H: hrel T T) : relation T := fun xy => H xy.1 xy.2.

(* injection of a set in boolean tests of KAT *)
Definition pset (T: Type) (X: set T) : dset T := fun x => `[< X x >].

(* un sous-ensemble vu comme "vecteur": une relation hétérogène vers un      *)
(* singleton.  Le monoïde de RelationAlgebra est une catégorie, et ka/kat    *)
(* acceptent les buts typés: on peut donc décider des égalités d'ensembles   *)
(* bâties sur les forsets/aftersets.  (hkat, lui, refuse le typé.)           *)
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

  (** inclusion et égalité *)

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

  (* versions orientées, utilisées par les tactiques *)
  Lemma to_hrel_leqW : to_hrel R ≦ to_hrel S -> R `<=` S.
  Proof. by rewrite to_hrel_leqE. Qed.

  Lemma to_hrel_weqW : to_hrel R ≡ to_hrel S -> R = S.
  Proof. by rewrite to_hrel_weqE. Qed.

  Lemma to_hrel_leqF : R `<=` S -> to_hrel R ≦ to_hrel S.
  Proof. by rewrite to_hrel_leqE. Qed.

  Lemma to_hrel_weqF : R = S -> to_hrel R ≡ to_hrel S.
  Proof. by rewrite to_hrel_weqE. Qed.

  (** prédicats de rel.v exprimés dans RelationAlgebra *)

  Lemma to_hrel_reflW : (1 ≦ to_hrel R)%ra -> reflexive R.
  Proof. by move => h x; exact: (h x x (erefl x)). Qed.

  Lemma to_hrel_symW : ((to_hrel R)° ≦ to_hrel R)%ra -> symmetric R.
  Proof. by move => h x y hxy; exact: (h y x hxy). Qed.

  Lemma to_hrel_transW : (to_hrel R ⋅ to_hrel R ≦ to_hrel R)%ra -> transitive R.
  Proof. by move => h y x z h1 h2; apply: (h x z); exists y. Qed.

End Transport.

(** * [to_hrel] est un morphisme pour toutes les opérations *)

Section Morphism.
  Variable (T: Type).
  Implicit Types (R S: relation T) (X Y: set T).

  (** structure de treillis *)

  Lemma to_hrel_setU R S : to_hrel (R `|` S) ≡ (to_hrel R + to_hrel S)%ra.
  Proof. by []. Qed.

  Lemma to_hrel_setI R S : to_hrel (R `&` S) ≡ (to_hrel R ∩ to_hrel S)%ra.
  Proof. by []. Qed.

  Lemma to_hrel_set0 : to_hrel (set0: relation T) ≡ (0%ra: hrel T T).
  Proof. by []. Qed.

  Lemma to_hrel_setT : to_hrel (setT: relation T) ≡ (top: hrel T T).
  Proof. by []. Qed.

  (* le complémentaire n'appartient pas au fragment décidé par ka/kat *)
  Lemma to_hrel_setC R : to_hrel (R.^c) ≡ (!(to_hrel R))%ra.
  Proof. by []. Qed.

  (** structure de monoïde *)

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

  (** clôtures *)

  Lemma to_hrel_RTclos R : to_hrel (R.*) ≡ ((to_hrel R)^*)%ra.
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

  Lemma to_hrel_Tclos R : to_hrel (R.+) ≡ ((to_hrel R)^+)%ra.
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

(** * Opérations sur les tests *)

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

(** * Converse: lois de RelationAlgebra spécialisées à [hrel]                *)

(* Les lois générales (cnvdot, cnvstr, ...) portent sur une structure         *)
(* inconnue; [rewrite ?cnvdot] déplie alors hrel_cnv en lambda et détruit le  *)
(* but.  On les spécialise donc à hrel, ce qui les rend utilisables par       *)
(* autorewrite.                                                              *)

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

  (* un test est auto-converse; absent de RelationAlgebra.  Énoncé sur un    *)
  (* test quelconque (et non sur pset X) pour attraper aussi les tests       *)
  (* composés [!p], [p ⊔ q], ...                                             *)
  Lemma hcnv_inj (p: dset T) : (([p])° ≡ [p])%ra.
  Proof. by move => x y; split => [[e h] | [e h]]; split; rewrite ?e ?(esym e). Qed.

End Cnv.

(** * Ensembles vus comme vecteurs                                           *)

(* [vec] est un morphisme du treillis des sous-ensembles, et transforme le   *)
(* foreset/afterset en composition.  C'est ce qui permet de décider par ka   *)
(* des égalités portant sur des ensembles et non sur des relations.          *)

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

  (** morphisme *)

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

End Vec.

(** * Tactiques *)

(* Deux passes: [hrel_morph] traduit la structure (et les deux cas           *)
(* particuliers 'Δ et 'Δc), puis [hrel_test] traduit les Δ_(X) restants en   *)
(* tests KAT. L'ordre importe: Δ_(setT) doit devenir 1 et non [pset setT].   *)

Create HintDb hrel_morph discriminated.
Create HintDb hrel_test discriminated.

#[export] Hint Rewrite
  to_hrel_compose to_hrel_setU to_hrel_setI to_hrel_inverse
  to_hrel_RTclos to_hrel_Tclos
  to_hrel_Delta to_hrel_DeltaC
  to_hrel_Lr to_hrel_Rr
  to_hrel_set0 to_hrel_setT : hrel_morph.

#[export] Hint Rewrite
  to_hrel_Delta_set to_hrel_DeltaC_set
  psetU psetI psetC psetT pset0 : hrel_test.

(* Les ensembles sont décomposés en premier: vec_setU doit passer avant      *)
(* vec_Fset, sinon vec (X `|` R#Y) reste bloqué et ka échoue sur un but      *)
(* tronqué.  autorewrite boucle, ce qu'une suite de [rewrite !] ne fait pas. *)
#[export] Hint Rewrite
  vec_Fset vec_Aset vec_setU vec_setI vec_set0 vec_setT : vec_morph.

(* met le but sous la forme [_ ≡ _] ou [_ ≦ _] dans RelationAlgebra *)
Ltac to_ra_goal :=
  intros;
  (apply: to_hrel_weqW || apply: to_hrel_leqW
   || apply: to_hrel_reflW || apply: to_hrel_symW || apply: to_hrel_transW
   || apply: vec_weqW || apply: vec_leqW
   || idtac);
  autorewrite with vec_morph;
  autorewrite with hrel_morph; autorewrite with hrel_test.

(* transporte également les hypothèses (nécessaire pour hkat) *)
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

(* pousse le converse vers les atomes: ka/kat voient alors R° comme un atome  *)
(* frais.  Correct mais incomplet (la théorie équationnelle de KA + converse   *)
(* n'est pas décidée par ces tactiques).                                       *)
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

  (** ** algèbre de Kleene: rka *)

  Goal (R `|` S).* = (R.* `;` S.*).* .
  Proof. by rka. Qed.

  Goal R.* `;` R.* = R.* .
  Proof. by rka. Qed.

  Goal (R `;` S).* `;` R = R `;` (S `;` R).* .
  Proof. by rka. Qed.

  Goal R.+ = R `;` R.* .
  Proof. by rka. Qed.

  Goal 'Δ `|` R.+ = R.* .
  Proof. by rka. Qed.

  Goal R.* `<=` (R `|` S).* .
  Proof. by rka. Qed.

  (** ** algèbre de Kleene avec tests: rkat *)

  Goal Δ_(X) `;` Δ_(X) = Δ_(X).
  Proof. by rkat. Qed.

  Goal (Δ_(X) `;` R).* `;` Δ_(X) = Δ_(X) `;` (R `;` Δ_(X)).* .
  Proof. by rkat. Qed.

  Goal Δ_(X) `;` Δ_(X.^c) = set0.
  Proof. by rkat. Qed.

  Goal Δ_(X `&` Y) = Δ_(X) `;` Δ_(Y).
  Proof. by rkat. Qed.

  Goal Δ_(X) `|` Δ_(X.^c) = 'Δ.
  Proof. by rkat. Qed.

  Goal Δ_(X) `;` R `<=` R.
  Proof. by rkat. Qed.

  Goal (R |_(X)).+ `<=` Δ_(X) `;` R.+ `;` Δ_(X).
  Proof. by rkat. Qed.

  (** ** hypothèses de Hoare: rhkat *)

  Goal R `;` S = set0 -> R `;` S `;` U = set0.
  Proof. by rhkat. Qed.

  Goal Δ_(X) `;` R = R `;` Δ_(X) -> Δ_(X) `;` R.* = R.* `;` Δ_(X).
  Proof. by rhkat. Qed.

  (** ** prédicats reflexive / symmetric / transitive *)

  Goal reflexive (R.*).
  Proof. by rka. Qed.

  Goal transitive (R.+).
  Proof. by rka. Qed.

  Goal symmetric (R `|` R^-1).
  Proof. by rka_cnv. Qed.

  Goal symmetric (Δ_(X) `;` R^-1 `;` R `;` Δ_(X)).
  Proof. by rka_cnv. Qed.

  (** ** ensembles (forsets / aftersets) : les mêmes tactiques *)

  Goal (R `;` S)#X = R#(S#X).
  Proof. by rka. Qed.

  Goal R.*#(R.*#X) = R.*#X.
  Proof. by rka. Qed.

  Goal R.*#X = X `|` R#(R.*#X).
  Proof. by rka. Qed.

  Goal (R `|` S).*#X = (R.* `;` S.*).*#X.
  Proof. by rka. Qed.

  Goal R#(X `|` Y) = R#X `|` R#Y.
  Proof. by rka. Qed.

  Goal R.+#X = R#(R.*#X).
  Proof. by rka. Qed.

  Goal R#X `<=` R.*#X.
  Proof. by rka. Qed.

  (* idempotence d'une clôture: la forme de Fset_CW / CBK_Clos *)
  Goal Clos(X|R,W) = Clos(Clos(X|R,W)|R,W).
  Proof. by rka. Qed.

  Goal (X:#R) = R^-1#X.
  Proof. by rka. Qed.

  (** ** treillis: rlattice *)

  Goal R `&` S `<=` R.
  Proof. by rlattice. Qed.

  Goal R `|` S = S `|` R.
  Proof. by rlattice. Qed.

End Tests.

(** * Exemples: lemmes de rel.v redémontrés en une ligne *)

Section Exemples.
  Variable (T: Type).
  Variables (R S: relation T) (X: set T).

  (* compA *)
  Goal (R `;` S) `;` R = R `;` (S `;` R).
  Proof. by rka. Qed.

  (* rtclosE *)
  Goal R.* = 'Δ `|` R.+ .
  Proof. by rka. Qed.

  (* rtclos_compE *)
  Goal R.* `;` R = R.+ .
  Proof. by rka. Qed.

  (* tclosUl *)
  Goal R `|` (R `;` R.+) = R.+ .
  Proof. by rka. Qed.

  (* tclosUr *)
  Goal R `|` (R.+ `;` R) = R.+ .
  Proof. by rka. Qed.

  (* tclosU_comp *)
  Goal R.+ `|` (R.+ `;` R.+) = R.+ .
  Proof. by rka. Qed.

  (* tclos_compK *)
  Goal (R.+ `;` R.+) `<=` R.+ .
  Proof. by rka. Qed.

  (* comp_tclosS / tclos_compS *)
  Goal (R `;` R.+) `<=` R.+ .
  Proof. by rka. Qed.

  Goal (R.+ `;` R) `<=` R.+ .
  Proof. by rka. Qed.

  (* dénestage.  La preuve directe à partir des seuls lemmes de rel.v fait   *)
  (* une quarantaine de lignes et réclame d'abord un principe d'induction    *)
  (* absent de rel.v (rtclos_ind exige la transitivité de la cible, qui est   *)
  (* ici le point dur): cf. rel1.v, rt_ind_l et denest.                      *)
  Goal (R `|` S).* = R.* `;` (S `;` R.*).* .
  Proof. by rka. Qed.

  Goal (R `|` S).* = (R.* `;` S).* `;` R.* .
  Proof. by rka. Qed.

  Goal (R `|` S).+ = R.* `;` (S `;` R.*).+ `|` R.+ .
  Proof. by rka. Qed.

End Exemples.

(** * Limites *)

(* Les buts ci-dessous sont hors des fragments décidés; les [Fail] documentent *)
(* précisément ce qui n'est pas automatisable par ces tactiques.               *)

Section Limites.
  Variable (T: Type).
  Variables (R S U: relation T) (X Y: set T).

  (* le converse n'est pas dans le fragment décidé par ka/kat, mais ra_cnv   *)
  (* le pousse vers les atomes, ce qui suffit en pratique                     *)
  Goal (R `;` S)^-1 = S^-1 `;` R^-1.
  Proof. Fail by rka. by rka_cnv. Qed.

  Goal R.*^-1 = R^-1.* .
  Proof. Fail by rka. by rka_cnv. Qed.

  Goal R.+^-1 = R^-1.+ .
  Proof. Fail by rka. by rka_cnv. Qed.

  Goal (Δ_(X) `;` R `;` Δ_(X))^-1 = Δ_(X) `;` R^-1 `;` Δ_(X).
  Proof. Fail by rkat. by rka_cnv. Qed.

  (* ra_cnv reste incomplet: R° traité comme un atome frais *)
  Goal R `<=` R.* `;` R^-1 `;` R.* -> True.
  Proof. by []. Qed.

  (* l'intersection n'est pas dans le fragment de ka/kat, mais le fragment *)
  (* treillis borné est traité par lattice *)
  Goal R `&` S `<=` R.
  Proof. Fail by rka. by rlattice. Qed.

  (* la distributivité n'est pas dans le fragment de lattice *)
  Goal (R `|` S) `&` U = (R `&` U) `|` (S `&` U).
  Proof. Fail by rlattice. by rewrite setIUl. Qed.

  (* top (setT, L_(X), R_(X)) n'est pas dans le fragment de ka/kat *)
  Goal L_(X) `;` R `<=` L_(X).
  Proof. Fail by rkat. Abort.

  (* sur les ensembles, hkat refuse le typé ("typed hkat is not supported") *)
  Goal R `;` S = set0 -> (R `;` S)#X = set0.
  Proof. Fail by rhkat. Abort.

  (* mélanger un test et une intersection d'ensembles sort du fragment *)
  Goal Δ_(X)#Y = X `&` Y.
  Proof. Fail by rkat. Abort.

  (* hkat n'élimine pas une hypothèse de monotonie *)
  Goal R `<=` S -> R.+ `<=` S.+ .
  Proof. Fail by rhkat. by apply: tclosS. Qed.

End Limites.
