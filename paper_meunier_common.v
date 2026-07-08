(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & datest) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".
From RL Require Import  seq1 seq2 rel.

From RL Require Import  paper_monochromatic_f. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Definition NotEmpty (T: Type) := (exists (v0:T), (v0 \in setT)).

Section CheckAsym. 
  (** * Import main result from paper_monochromatic_f *)
  Context (T : choiceType) (R: relation T).
  Hypothesis A1: (NotEmpty T).

  Import Asyminf2Inf(Asym2P5', allL_rc_asym).

  (* begin snippet infasym:: no-out *) 
  Lemma iic_asym_to_iic_inj:  (iic (Asym R.+)) -> (iic_inj R). 
  (* end snippet infasym *)  
  Proof. by apply: (@Asym2P5' T R A1). Qed.

  Lemma not_iic_inj_to_not_iic_asym: ~ (iic_inj R) -> ~ (iic (Asym R.+)).
  Proof. by move => ? /iic_asym_to_iic_inj ?. Qed.

End  CheckAsym. 

Module Infinite_paths.
  (** * iic_asym_injective:  iic (Asym R.+) -> iic_inj (Asym R.+) *) 

  Section iic_asym. 

    Variable (T : Type).
    Implicit Types (T : Type) (R: relation T) (A B: set T).
    
    #[local] Lemma iic_asym_L1 (f : nat -> T) R:
      (forall n, (Asym R.+) ((f n),(f (S n)))) -> 
      forall p n, 0 < p -> (Asym R.+) (f n, f (n + p)). 
    Proof.
      move => Hi. 
      elim => [// | p Hr n' _].
      case H2: (p == 0); first by move: H2 => /eqP ->;rewrite addn1;apply: Hi. 
      move: H2 =>  /neq0_lt0n /(Hr n') H2.
      have H4: transitive (Asym R.+) by apply: Asym_preserve_transitivity;apply: TclosT.
      have H5: Asym R.+ (f (n' + p), f (n' + p).+1) by apply: Hi.
      rewrite /transitive in H4.
      move: (H4 (f n') (f (n' + p)) (f (n'+p).+1) H2 H5).
      by rewrite -addn1 -[p.+1]addn1 addnA.
    Qed.
    
    #[local] Lemma iic_asym_L2 (f : nat -> T) R:
      (forall n, (Asym R.+) ((f n),(f (S n)))) -> 
      forall p n, 0 < p -> ~ (f n) = f (n + p). 
    Proof.
      by move => + p n H1 => /iic_asym_L1 /(_ p n H1) + H2;rewrite -H2; apply: Asym_irreflexive.
    Qed.
    
    #[local] Lemma iic_asym_L3 (f : nat -> T) R:
      (forall n, (Asym R.+) ((f n),(f (S n)))) -> injective f.
    Proof.
      have H0 n m: m < n -> exists p, p> 0 /\ n = m + p by move => H1;exists (n-m); lia.
      move => /iic_asym_L2 Hi p q;apply contraPP => H1.
      have [H2|H2]: (p < q \/ q < p) by lia.
      by pose proof (H0 q p H2) as [p' [H3 ->]]; apply: Hi.
      by move: (H0 p q H2) => [p' [H3 ->]];move: (Hi p' q H3);symmetry.
    Qed.
    
    Lemma iic_asym_injective R: iic (Asym R.+) -> iic_inj (Asym R.+).
    Proof. by move => [f /[dup] ? /iic_asym_L3  ?];exists f. Qed.

    Lemma sporder_iic_injective R: (sporder R) -> iic R -> iic_inj R.
    Proof. by move => /sporderEq <-;apply: iic_asym_injective. Qed.
    
    End iic_asym.
  
End Infinite_paths. 

Export Infinite_paths.
Arguments iic_asym_injective {T}.
Arguments sporder_iic_injective {T}.

Section Infinite_paths_X.
  (** * Assumptions on infinite paths *)
  (* should be move on rel.v *)

  Context (T : Type).
  Implicit Types (R: relation T) (X: set T).

  Lemma notiic_rloop_sub_L1 X (S: relation X):
    (exists (v0:T), (v0 \in X)) -> ~ (iic (Asym S)) -> (Rloop S).
  Proof. 
    have setTypeP: (exists x : X, x \in [set: X]) <-> (exists (t:T), (t \in X))
      by split => [[v ?] |[v H0]];[exists (sval v) | exists (exist _ v H0)];
                 rewrite inP;[apply: set_valP|].
    by move => /setTypeP H0; apply: notiic_rloop. 
  Qed. 
  
  Lemma notiic_rloop_sub_L2 X R:
    ~ (iic (Asym R)) -> (exists (v0:T), (v0 \in X)) -> (Rloop (@Restrict' T X R)).
  Proof.
    move => H1 H0.
    have H2: (iic (@Restrict' T X (Asym R))) -> (iic (Asym R))
      by move => [f // ?];exists (fun n => (sval (f n))). 
    have H3:  ~ (iic (Asym R)) -> ~ (iic (@Restrict' T X (Asym R)))
      by contra => -[f H4];apply: H2; by (exists f).
    by apply/(notiic_rloop_sub_L1 H0)/H3.
  Qed.
  
  (* notiic_rloop for a subset X *)
  Lemma notiic_rloop_sub X R:
    ~ (iic (Asym R)) ->(exists (v0:T), (v0 \in X))
    -> (exists (v:T), v \in X /\ forall w, w \in X -> R (v,w) -> R (w,v)).
  Proof.
    move => Ninf H0.
    move: (notiic_rloop_sub_L2 Ninf H0) => [v H1];exists (sval v).
    split=> [| w H2];first by rewrite inP;apply: set_valP.
    have [w' <-]: exists (w': X), (sval w') = w by (exists (exist _ w H2)).
    by move => ?;apply: H1.
  Qed.
  
End Infinite_paths_X.

Reserved Notation "A [<=] B" (at level 4, no associativity). 
Reserved Notation "A [<= R ] S" (at level 4, no associativity). 

(* begin snippet leset:: no-out *)    
Definition leSet T R: relation (set T) := 
  [set AB |forall (a:T), (a \in AB.1) -> exists b, b \in AB.2 /\ ( a = b \/ R (a,b)) ].

Notation "A [<= R ] B" := (leSet R (A,B)).
(* end snippet leset *)       

Definition leSet' T R: relation (set T) := [set AB | AB.1 `<=` ('Δ  `|` R)#AB.2]. 

Section Set_relation. 
  (** * A relation on sets induced by a relation on elements *)

  Context (T : eqType).
  Implicit Types (T : eqType) (R S: relation T) (A B: set T).
  
  Lemma lesetE R: leSet R = leSet' R. 
  Proof.
    rewrite predeqE => -[A B];split. 
    - move => H1 a /inP/H1 [b [/inP H2 [->| H3]]]; first by (exists b);split;[left|].
      by (exists b);split;[right|].
    - rewrite /leSet' /mkset /= -FsetUl Fset_D.
      move => H1 a /inP/H1 [/inP H2 | [b [H2 /inP H3]]].
      by (exists a); split;[ | left].
      by exists b; split;[ | right].
  Qed.

  (* begin snippet lesetI:: no-out *)   
  Lemma Ile R A B: A `<=` B -> A [<= R] B.
  (* end snippet lesetI *)
  Proof. by move => H1 /= a /inP/H1 ?;exists a;split;[rewrite inP|left]. Qed.

  Lemma leI R S: S `<=` R -> (leSet S)  `<=` (leSet R).
  Proof.
    move => H1;rewrite 2!lesetE => [[A B]] H2.
    by apply: subset_trans H2 _;apply: Fset_inc; apply: setUS.
  Qed.
  
End Set_relation.


Section Set_order. 
  (** * the previous relation [<= R] is an order relation on R-independent sets *)

  Context (T : eqType).
  Implicit Types (R S: relation T) (A B: set T).
  
  Axiom proof_irrelevance: forall (P : Prop) (p q : P), p = q.
  
  Section Util.
    (** ingredients *)
    Lemma le_trans_if_tr R: transitive R -> transitive (leSet R).
    Proof.
      rewrite lesetE => /Tclos_iff H0 A B C /= H1 H2.
      have : ('Δ  `|` R)#B `<=` ('Δ  `|` R)#(('Δ  `|` R)#C) by apply: Fset_inc1.
      rewrite Fset_comp H0 DuT_eq_Tstar compose_rt_rt -DuT_eq_Tstar -H0 => H3.
      by apply: subset_trans H1 H3.
    Qed.

    Lemma le_refl  R: reflexive (leSet R).
    Proof. by move => A r H1;exists r;split;[| left]. Qed.
    
    Lemma le_antisym_if_sp' R: 
      sporder R -> forall A B, (RelIndep R A) -> A [<= R] B -> B  [<= R] A -> A `<=` B.
    Proof.
      move => /[dup] -[_ Htr] /sporder_asym/AsymEq Asy A B H1 + +  a H4.
      rewrite -Asy => H2 H3.
      move: (H4) => /inP /H2 [b [/inP /= H5 [-> // | [H6 H6']]]]. 
      move: (H5) => /inP /H3 /= [c [/inP H8 H9]].
      case H10: (a == b ); first by move: H10 => /eqP ->.
      move: H10 => /eqP H10.
      case H12: (b == c).
      - move: H12 H8 => /eqP <- H8.
        by have: False by move: H4 H8 => /inP H4 /inP H8;apply: (H1 a b). 
      - move: H12 H9 => /eqP H12 [H9 // | [H9 H9']].
        case H13: (a == c); first by move: H13 H9' => /eqP <- H9'.
        pose proof Htr.
        have H14: R (a,c) by apply: Htr H6 H9.
        by have: False by move: H13 H4 H8 => /eqP H13 /inP H4 /inP H8; apply: (H1 a c). 
    Qed.
    
    Lemma le_antisym_if_sp R: 
      sporder R ->
      forall A B, (RelIndep R A) -> (RelIndep R B) 
             -> A [<= R] B -> B  [<= R] A -> A = B.
    Proof.
      move => Hsp A B H1 H2 H3 H4.
      by move: (le_antisym_if_sp' Hsp H1 H3 H4)
                 (le_antisym_if_sp' Hsp H2 H4 H3);rewrite eqEsubset.
    Qed.
  
  End Util.
  
  (* begin snippet lesetporder:: no-out *)   
  Lemma leSet2_porder R: 
    sporder R -> 
    @porder {S: set T| RelIndep R S} [set AB | (sval AB.1) [<= R] (sval AB.2)].
  (* end snippet lesetporder  *)   
  Proof.
    move => H_sp.
    split => [ [A ?] | [A Ha] [B Hb] H1 H2 | [A ?] [B ?] [C ?]].
    + (* reflexive *) by apply/le_refl.
    + (* antisymmetric *) 
      move: (le_antisym_if_sp H_sp Ha Hb H1 H2) => H5.
      subst A;apply: f_equal;apply: proof_irrelevance.
    + (* transitive *) by move: H_sp => [_ ?];apply/le_trans_if_tr.
  Qed.
  
End Set_order. 

