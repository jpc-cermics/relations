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
From mathcomp Require Import all_boot seq order boolp classical_sets. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".
From RL Require Import  seq1 seq2 rel.

From RL Require Import  paper_monochromatic_f. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section CheckAsym. 

  Context (T : choiceType) (R: relation T).
  Hypothesis A1: (exists (v0:T), (v0 \in setT)).

  Import Asyminf2Inf(Asym2P5', allL_rc_asym).
  
  Lemma check_asym:  (iic (Asym R.+)) -> (iic_inj R). 
    Proof. by apply: (@Asym2P5' T R A1). Qed.
End  CheckAsym. 


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
  
  Lemma Ile R A B: A `<=` B -> A [<= R] B.
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
  Implicit Types (T : eqType) (R S: relation T) (A B: set T).
  
  Axiom proof_irrelevance: forall (P : Prop) (p q : P), p = q.
  
  Section Util.
    (** ingredients *)
    Lemma le_trans_if_tr R: transitive R -> transitive (leSet R).
    Proof.
      rewrite lesetE => /clos_t_iff H0 A B C /= H1 H2.
      have : ('Δ  `|` R)#B `<=` ('Δ  `|` R)#(('Δ  `|` R)#C) by apply: Fset_inc1.
      rewrite Fset_comp H0 DuT_eq_Tstar compose_rt_rt -DuT_eq_Tstar -H0 => H3.
      by apply: subset_trans H1 H3.
    Qed.

    Lemma le_refl  R: reflexive (leSet R).
    Proof. by move => A r H1;exists r;split;[| left]. Qed.
    
    Lemma le_antisym_if_sp' R: 
      sporder R -> forall A B, (RelIndep R A) -> A [<= R] B -> B  [<= R] A -> A `<=` B.
    Proof.
      move => [Ir H0] A B H1 H2 H3 a H4.
      pose proof (sporder_antisym H0 Ir) as Asy.
      have H0': Asym R = R by rewrite -AsymE.
      move: H2 H3; rewrite -H0' => H2 H3.
      move: (H4) => /inP /H2 [b [/inP /= H5 [-> // | [H6 H6']]]]. 
      move: (H5) => /inP /H3 /= [c [/inP H8 H9]].
      case H10: (a == b ); first by move: H10 => /eqP ->.
      move: H10 => /eqP H10.
      case H12: (b == c).
      - move: H12 H8 => /eqP <- H8.
        by have: False by move: H4 H8 => /inP H4 /inP H8;apply: (H1 a b). 
      - move: H12 H9 => /eqP H12 [H9 // | [H9 H9']].
        case H13: (a == c); first by move: H13 H9' => /eqP <- H9'.
        have H14: R (a,c) by apply: H0 H6 H9.
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
  
  Lemma leSet2_porder R: 
    sporder R -> 
    @porder {S: set T| RelIndep R S} [set AB | (sval AB.1) [<= R] (sval AB.2)].
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

Section Infinite_paths.
  (** *  iic_asym_injective *) 

  Context (T : Type).
  Implicit Types (T : Type) (R S: relation T) (A B: set T).
  
  Lemma AsymInf_step1 (f : nat -> T) R:
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
  
  Lemma AsymInf_step2 (f : nat -> T) R:
    (forall n, (Asym R.+) ((f n),(f (S n)))) -> 
    forall p n, 0 < p -> ~ (f n) = f (n + p). 
  Proof.
    by move => + p n H1 => /AsymInf_step1 /(_ p n H1) + H2;rewrite -H2; apply: Asym_irreflexive.
  Qed.
  
  Lemma AsymInf (f : nat -> T) R:
    (forall n, (Asym R.+) ((f n),(f (S n)))) -> injective f.
  Proof.
    have H0 n m: m < n -> exists p, p> 0 /\ n = m + p by move => H1;exists (n-m); lia.
    move => /AsymInf_step2 Hi p q;apply contraPP => H1.
    have [H2|H2]: (p < q \/ q < p) by lia.
    by pose proof (H0 q p H2) as [p' [H3 ->]]; apply: Hi.
    by move: (H0 p q H2) => [p' [H3 ->]];move: (Hi p' q H3);symmetry.
  Qed.
  
  Lemma iic_asym_injective R: iic (Asym R.+) -> iic_inj (Asym R.+).
  Proof. by move => [f /[dup] H1 /AsymInf H2];exists f. Qed.
  
End Infinite_paths.

Section Infinite_paths_X.
  (** * Assumptions on infinite paths *)
  
  Context (T : Type).
  Implicit Types (T : Type) (R: relation T) (X: set T).

  Lemma setTypeP X: (exists v : X, v \in [set: X]) <-> (exists (v:T), (v \in X)).
  Proof.
    split => [[v H0] |[v H0]].
    by (exists (sval v));rewrite inP; apply: set_valP. 
    by (exists (exist _ v H0));rewrite inP.
  Qed.
  
  Lemma notiic_rloop_sub X (S: relation X):
    (exists (v0:T), (v0 \in X)) -> ~ (iic (Asym S)) -> (Rloop S).
  Proof. by move => /setTypeP H0; apply: notiic_rloop. Qed. 
  
  Lemma test67 X R: (iic (@Restrict' T X (Asym R))) -> (iic (Asym R)).
  Proof.  by move => [f // ?];exists (fun n => (sval (f n))). Qed.

  Lemma test68 X R:
    ~ (iic (Asym R)) -> (exists (v0:T), (v0 \in X)) -> (Rloop (@Restrict' T X R)).
  Proof.
    move => H1 H0.
    have H2:  ~ (iic (Asym R)) -> ~ (iic (@Restrict' T X (Asym R)))
      by apply contraPP;rewrite not_notE not_notE; apply: test67.
    move: H1 => /H2 H1.
    by apply: (notiic_rloop_sub H0 H1).
  Qed.
  
  Lemma test68' X R:
    ~ (iic (Asym R)) ->(exists (v0:T), (v0 \in X))
    -> (exists (v:T), v \in X /\ forall w, w \in X -> R (v,w) -> R (w,v)).
  Proof.
    move => Ninf H0.
    move: (test68 Ninf H0) => [v H1].
    exists (sval v).
    split; first  by rewrite inP; apply: set_valP.
    move => w H2.
    have [w' <-]: exists (w': X), (sval w') = w by exists (exist _ w H2). 
    move => H3.
    by apply: H1.
  Qed.
  
End Infinite_paths_X.

Section Paper. 
  (*  On Monochromatic Paths in Edge-Coulured Digraphs *)
  Variables (T:choiceType) (Eb Er: relation T).

  (** Mono (x,y): there exists a monochromatic oriented path from x to y *)
  (* begin snippet Mono:: no-out *)   
  Definition Mono :=  Eb.+ `|` Er.+.
  (* end snippet Mono *) 

  (* The set Scal as a subset of T *)
  (* begin snippet Scal:: no-out *) 
  Definition Scal := [ set S | RelIndep Mono S /\ S:#(Er.+) `<=` Mono#S /\  S != set0 ].
  (* end snippet Scal *) 
    
  (* The set Scal as a Type *)
  
  (* begin snippet SType:: no-out *)    
  Definition SType := {S: set T| RelIndep Mono S /\ S:#(Er.+) `<=` Mono#S  /\ S != set0}.
  (* end snippet SType *)  
  
  Definition Elt (C: set SType) := {x : T |exists (S: SType), S \in C /\ x \in (sval S)}.
  
  Lemma S2Scal: forall (S: SType), (sval S) \in Scal.
  Proof. by move => [S [H1 [H2 H3]]];rewrite inP. Qed.

  Lemma Scal2S: forall S, S \in Scal -> exists (S': SType), (sval S') = S.
  Proof.  by move => S /inP H1; exists (exist _ S H1). Qed.

  (* begin snippet leSetone:: no-out *)   
  Definition leSet1 (AB: SType*SType) :=
    leSet (Asym Eb.+) ((proj1_sig AB.1), (proj1_sig AB.2)).
  (* end snippet leSetone *)  
  
  (** * The relation on sets restricted to Stype subsets *)
  Notation "A [<=] B" := (leSet1 (A,B)).
  
  Section Scal_order. 
    
    Lemma sporderAst: sporder (Asym Eb.+).
    Proof.
      by split;[apply/Asym_irreflexive|apply/Asym_preserve_transitivity/TclosT].
    Qed.
    
    Lemma leSet1_transitive: @transitive SType leSet1.
    Proof. by move => [A ?] [B ?] [C ?]; 
                     apply/le_trans_if_tr/Asym_preserve_transitivity/TclosT. Qed.
    
    Lemma leSet1_reflexive: @reflexive SType leSet1.
    Proof. by move => [A ?];apply: le_refl. Qed.
    
    Lemma le_antisym_l1: forall A B, 
        (RelIndep Mono A) -> (RelIndep Mono B)
        -> A [<= (Asym Eb.+)] B -> B  [<= (Asym Eb.+)] A -> A = B.
    Proof.
      move => A B H1 H2 H1' H2'. 
      pose proof @AsymI T (Eb.+) as H3.
      have H4: Eb.+ `<=` Mono by apply: subsetUl.
      have H5: Asym Eb.+ `<=` Mono by apply: subset_trans (H3 Eb.+) H4.
      have H6: (RelIndep (Asym Eb.+) A) by apply: RelIndep_I H5 H1. 
      have H7: (RelIndep (Asym Eb.+) B) by apply: RelIndep_I H5 H2. 
      have H8: transitive (Asym Eb.+) 
        by apply: Asym_preserve_transitivity;apply: TclosT.
      have H9: irreflexive (Asym Eb.+) by apply Asym_irreflexive.
      have H10: sporder (Asym Eb.+) by exact. 
      by move : (le_antisym_if_sp H10 H6 H7 H1' H2').
    Qed.
    
    Lemma leSet1_antisymmetric: @antisymmetric SType leSet1.
    Proof. 
      move => [A Ha] [B Hb] H1 H2.
      move: (Ha) (Hb) => [Ha' Ha''] [Hb' Hb''].
      move: (le_antisym_l1 Ha' Hb' H1 H2) => H5.
      subst A. (** why I cannot use rewrite *)
      apply: f_equal.
      apply: proof_irrelevance.
    Qed.
    
    Lemma leSet1_porder: @porder SType leSet1. 
    Proof.
      pose proof sporderAst as H_sp.
      split => [ [A ?] | [A Ha] [B Hb] H1 H2 | [A ?] [B ?] [C ?]].
      + by apply/leSet1_reflexive.
      + by apply/leSet1_antisymmetric.
      + by apply/leSet1_transitive. 
    Qed.
    
  End Scal_order.

  Section SType_chains.
    (** * Chains in Stype *)

    (* begin snippet Chains:: no-out *)    
    Definition Chains := [set C: set SType| forall (c1 c2: SType),
          c1 \in C -> c2 \in C -> c1 [<=] c2 \/ c2 [<=] c1].
    (* end snippet Chains *)    
    
    Lemma Chains_is_total: forall (A : set SType),
        A \in Chains <-> total_on A (curry leSet1).
    Proof. split => [/inP H2 c1 c2 /inP ? /inP ?| H1]; first by apply: H2. 
           by apply/inP => c1 c2 /inP H2 /inP H3;apply: H1.
    Qed.
  
    Lemma Chains_Scal:  forall (C: set SType) S,
        C \in Chains -> S \in C -> Scal (sval S).
    Proof. by move => C [S [H1 [H2 H3]]] /inP H4 /inP H5. Qed.
  
    Lemma Elt_not_empty: forall (C: set SType), 
        C \in Chains -> C != set0 -> exists (S: SType), (S \in C /\ (exists x, x \in (sval S))).
    Proof.
      move => C H1 /notempty_exists [S H2];exists S;split;first by []. 
      by move: S H2 => [S' [H3 [H4 /notempty_exists H5]] /=] _.
    Qed.
    
  End SType_chains.

  Section Sinf_set.
    (** * Sinf C for a non empty Chain *)
    
    Variables  (C: set SType).
    Hypothesis Hc: C \in Chains. 
    Hypothesis Hne: C != set0.
    
    Definition Ec := Elt C.

    (* Set Sinf associated to a chain *)
    Definition Sinf := 
      [ set v: T | 
        exists S, (S \in C) /\ (v \in (sval S)) /\ (forall T, T \in C -> S [<=] T -> v \in (sval T))].
    
    (* A relation on the set Elt C, all the elements
       of T which are elements of a set in the chain C *)
    Definition RC:= [set xy:Ec*Ec |
                      ((sval xy.1) \in Sinf /\ xy.2 = xy.1)
                      \/ (~ ((sval xy.1) \in Sinf) /\ (Asym Eb.+) (sval xy.1, sval xy.2))].
    
    Lemma transitive_RC: transitive RC. 
    Proof.
      have H3: transitive (Asym Eb.+) by apply/Asym_preserve_transitivity/TclosT.
      by move => x y z [/= [H0 ->]| [H1 H1']] [ /= [H0' /= ->]| /= [H2 H2']]; 
                [left | right | right |right;split;[ | apply H3 with (sval y)]].
    Qed.
    
    Lemma ChnotE: exists _ : Elt C, True.
    Proof.
      move: (Elt_not_empty Hc Hne) => [S [H2 [x H3]]].
      have H4: exists (S: SType), S \in C /\ x \in (sval S) by (exists S).
      by exists (exist _ x H4).
    Qed.
    
    Lemma ChnotE_witness: Elt C.
    Proof. by apply: inhabited_witness; rewrite inhabitedE; apply: ChnotE. Qed.
    
    (* Sinf is a Mono-independent set *)
    Lemma Sinf_indep: RelIndep Mono Sinf.
    Proof.
      move: Hc => /inP H1 x y /inP H2 /inP H3 H4 /= H5.
      move: H2 H3 =>[S [H6 [/= H7 H8]]] [U [H6' [/= H7' H8']]].
      move: H8 H8' => /((_ U) H6') H8 /((_ S) H6) H8'.
      have [H9|H9]: S [<=] U \/ U [<=] S by apply: H1.
      - move: H9 H1 => /H8 H9 /inP H1.
        move: (Chains_Scal H1 H6') => [/(_ x y) H10 _].
        by apply: (H10 H9 H7' H4 H5).
      - move: H9 H1 => /H8' H9 /inP H1.
        move: (Chains_Scal H1 H6) => [/(_ x y) H10 _].
        by apply: (H10 H7 H9 H4 H5).
    Qed.
    
    Section Ec_seq. 
      (** *  the main result here is total_RC *) 

      Lemma Ec_seq1: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, S1 \in C /\ S [<=] S1 /\ ~ (s \in (sval S1)).
      Proof.
        move: Hc => H1 S s H2 H3. 
        apply contraPP;rewrite not_existsP 2!not_notE inP /Sinf => H4;exists S.
        split => [// | ];split => [// |A ? ?].
        by move: H4 => /(_ A) /not_andP [? //|/not_andP [// | /contrapT ?]].
      Qed.
      
      Lemma Ec_seq2: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, exists s1, S1 \in C /\ s1 \in (sval S1) /\ (Asym Eb.+) (s,s1).
      Proof.
        move: Hc => H1 S s H2 H3 H4.
        move: (Ec_seq1 H2 H3 H4) => [S1 [H5 [H6 H7]]].
        by move: ((H6 s) H3) => [s1 [H8 [H9 | H9]]];exists S1, s1;[rewrite -H9 in H8|].
      Qed.
      
      Lemma Ec_seq3: forall (s: Ec), 
          ~ ((sval s) \in Sinf) -> exists (s1: Ec), (Asym Eb.+) (sval s,sval s1).
      Proof.
        move => [s [S [H1 H2]]] H3.
        move: (Ec_seq2 H1 H2 H3) => [S1 [s1 [H4 [H5 H6]]]].
        have H7: exists (S: SType), S \in C /\ s1 \in (sval S) by (exists S1).
        by exists (exist _ s1 H7).
      Qed.
      
      Lemma total_RC: total_rel RC. 
      Proof.
        move => s.
        case H3: ((sval s) \in Sinf); first by (exists s); left.
        have H4: ~ ((sval s) \in Sinf) by move => H5;rewrite H5 in H3.
        move: (Ec_seq3 H4) => [s1 H5].
        by exists s1; right.
      Qed.
      
    End Ec_seq.
    
    Section XXX.

      Lemma test0_iic_RC: forall s, exists f : nat -> Ec, f 0 = s /\ forall n, RC ((f n),(f (S n))).  
      Proof. 
        by move: total_RC => /total_rel_iff H1;apply: total_rel'_to_total_rel''. 
      Qed.
      
      Lemma test1_RC:forall s, forall f, f 0=s /\ (forall n, RC ((f n),(f (S n)))) 
                               -> (forall n, ~ (sval (f n)) \in Sinf)
                               -> (forall n, (Asym Eb.+) (sval (f n), sval(f (S n)))).
      Proof. 
        by move => s f + + n => [[H0 /(_ n) [/=[H1 H1'] | /= [H1 H1']]]] /(_ n) H2.
      Qed.
      
      Lemma test3_RC: ~ (iic (Asym Eb.+)) -> 
                      forall s, exists f, (f 0=s /\ (forall n, RC ((f n),(f (S n)))))
                                /\ ~ (forall n, ~ (sval (f n)) \in Sinf).
      Proof.
        move => H1; move: test0_iic_RC => + s => /(_ s) [f H2].
        exists f; split => [// | H4]. 
        have H5:  iic (Asym Eb.+)
          by exists (fun n => (sval (f n)));move: test1_RC => /(_ s f) H6;apply: H6. 
               exact.
      Qed.
      
      Lemma test4_RC: ~ (iic (Asym Eb.+)) ->
                      forall s, exists f, (f 0=s /\ (forall n, RC ((f n),(f (S n)))))
                                /\ exists n, (sval (f n)) \in Sinf.
      Proof.
        move => H1; move: (test3_RC H1) => + s => /(_ s) [f [H2 /not_existsP [n H3]]].
        exists f;split;[ exact| exists n; exact].
      Qed.

      Lemma transitiveN_RC: forall f, 
          (forall n, RC ((f n),(f (S n)))) -> (forall n, n > 1 -> RC (f 0, f n)).
      Proof.
        move => f H1;elim => [// | n Hn H2 ].
        case H3: (1 < n). 
        + have H4: RC (f 0, f n) by apply: Hn;rewrite H3.
          by move : (transitive_RC H4 (H1 n)).
        + case H5: (n == 0); first by move: H5 => /eqP ->; apply: H1.
          case H6: (n == 1); first by move: H6 => /eqP ->;move: (transitive_RC (H1 0) (H1 1)).
          have H7: ~ (n <= 1) by rewrite leq_eqVlt H6 ltnS leqn0 H5.  
          by rewrite leqNgt H3 in H7.
      Qed.
      
      Lemma Util: forall n, ~ (n = 0) /\ ~ (n = 1) ->  n > 1. 
      Proof.
        move => n [/eqP H1 /eqP H2]. 
        have: n >= 0 by []; rewrite  leq_eqVlt => /orP [/eqP H3 // | ].
        by move: H3 H1 => H3; rewrite -H3. 
        rewrite leq_eqVlt => /orP [/eqP H4 | H4 //].
        by move: H2; by rewrite -H4.
      Qed.
      
      Lemma test_yy: ~ (iic (Asym Eb.+)) ->
                     forall s, exists f, f 0=s /\ (exists n, (sval (f n)) \in Sinf /\ RC ((f 0), (f n))).
      Proof.
        move => H1; move: (test4_RC H1) => + s => /(_ s) [f [[H2 H3] [n H4]]].
        exists f. split;first by [].
        case H5: (sval (f 0) \in Sinf).
        + exists 0. split.  by []. left. by [].
        + have H6: ~ (n = 0). move => H6. rewrite H6 in H4. by rewrite H5 in H4.
          case H7: (sval (f 1) \in Sinf).
          ++ by (exists 1).
          ++ exists n. 
             have H8: ~ (n = 1). move => H8. rewrite H8 in H4. by rewrite H7 in H4.
             have H9: n > 1 by apply Util.
             move: (transitiveN_RC H3) => /(_ n) H10.
             split. by []. by apply: H10.           
      Qed.

      Lemma ChooseRC5:~ (iic (Asym Eb.+))
            -> forall (s:Ec), (sval s \in Sinf) \/ exists s',  s' \in Sinf /\ (Asym Eb.+) (sval s, s').
      Proof. 
        move => H1; move: (test_yy H1) => + s => /(_ s) [f [H2 [n [H3 H3']]]].
        case H4: (sval (f 0) \in Sinf ). by left; rewrite -H2 H4.
        right. exists (sval (f n)). split. by []. 
        rewrite -H2. 
        move: H3' => [/= [H3' _] | /= [H5 H6]].
        by rewrite H4 in H3'.
        by [].
      Qed.

      Lemma ChooseRC6:~ (iic (Asym Eb.+)) -> forall (S: SType), (S \in C) -> (sval S) [<= (Asym Eb.+)] Sinf.
      Proof. 
        move => H1 S H2 s /= H3.
        have H4: exists (S: SType), S \in C /\ s \in (sval S) by (exists S).
        move: (ChooseRC5 H1 (exist _ s H4)) => /= [H5 | [s' [H5 H6]]].
        by (exists s);split;[|left].
        by (exists s');split;[|right].
      Qed.
      
    End XXX.
    
    (** * The Assumptions we use: weaker than the original paper assumptions *)
    (* begin snippet Assumptions:: no-out *)    
    Hypothesis A1: (exists (v0:T), (v0 \in setT)).
    Hypothesis A3: ~ (iic (Asym Er.+)).
    Hypothesis A4: ~ (iic (Asym Eb.+)).
    (* end snippet Assumptions *)    
    
    (* begin snippet Scalnotempty:: no-out *) 
    Lemma Scal_not_empty: exists v, Scal [set v].
    (* end snippet Scalnotempty *)
    Proof.
      have: Rloop Er.+ by apply: notiic_rloop.
      move => [v H1]; exists v.
      have H2': Er.+ `<=` Mono by apply: subsetUr.
      split;first by rewrite /RelIndep;move => x y /inP /= -> /inP /= ->.
      split;first by move => t [y [/= H3 H4]];move: H3; rewrite H4 /= => /H1/H2' H3;exists v.
      by rewrite -notempty_exists;(exists v);rewrite inP.
    Qed.
    
    Lemma SType_not_empty: (@setT SType) != set0.
    Proof.
      rewrite -notempty_exists;move: Scal_not_empty => [v H2].
      by exists (exist _ [set v] H2);rewrite inP.
    Qed.
    
    Lemma Sinf_not_empty: Sinf != set0.
    Proof.
      move: ChnotE => [s _];rewrite -notempty_exists.
      by move: (ChooseRC5 A4 s) => [H1 | [s' [H1 _]]];[exists (sval s) | exists s'].
    Qed.
    
    Lemma Sinf_ScalP: Sinf:#(Er.+) `<=` Mono#Sinf.
    Proof.
      move: Hc => H1 y [s [ H2 H3]].
      move: (H3) => [S [H4 [H5 H6]]].
      move: (Chains_Scal H1 H4) => [H7 [H8 H9]].
      have H13: y \in Er.+^-1#(sval S)
          by rewrite inP /Fset;exists s;split;[exact | rewrite -inP].
      move: H13 => /inP/H8 [t [H13 H14]]. 
      case H15: (t \in Sinf); first by (exists t); split;[ exact | rewrite -inP].
      have H16: (s <> t) by move => H17;rewrite -inP H17 in H3;rewrite H3 in H15.
      have H17: ~ ( Er.+ (y,t)). 
      move => H18.
      have H19: Mono (s,t) by right; apply: (TclosT H2 H18).
      move: H7 => /(_ s t) H7.
      move: H14 => /inP H14.
      by move: (H7 H5 H14 H16).
      have H18: (Eb.+ (y,t)) by move: H13 => [H13 | H13]. 
      have H19: (sval S) [<= (Asym Eb.+)] Sinf by apply: ChooseRC6. 
      move: H14 => /inP/H19 [tinf [/= H20 [H21 | [H21 H22]]]].
      + by rewrite -H21 in H20;rewrite H20 in H15. 
      + by exists tinf;split;[ left;apply: (TclosT H18 H21) | rewrite -inP].
    Qed.
    
    Lemma Sinf_Scal: Sinf \in Scal. 
    Proof.
      rewrite inP;split;[apply: Sinf_indep|split;[apply: Sinf_ScalP|apply: Sinf_not_empty]].
    Qed.
    
    Lemma Sinf_final: exists Si, forall (S: SType), C S -> S [<=] Si.
    Proof.
      move: Sinf_Scal => /inP H2;exists (exist _ Sinf H2);move => S /inP H3. 
      by apply: ChooseRC6.
    Qed.

  End Sinf_set.

  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  Hypothesis A3: ~ (iic (Asym Er.+)).
  Hypothesis A4: ~ (iic (Asym Eb.+)).
  
  
  (** * we are now able to use Zorn Lemma *)
  (** Zorn lemma  in mathcomp-analysis.1.3.1 
   * has changed and requires R to be (R : rel T) as oposed to (R: T -> T -> Prop) in 
   * previous version. Thus we have to convert (curry leSet1) to rel T and adapt the proof.
   **)
    
  Lemma SmaxZ_new: exists Sm, forall S, (fun x y => `[< (curry leSet1) x y >]) Sm S -> S = Sm.
  Proof.
    apply: Zorn.
    move => t; rewrite asboolE; by apply leSet1_reflexive.
    move => r s t; rewrite 3!asboolE; by apply leSet1_transitive.
    move => s t;rewrite 2!asboolE; by apply leSet1_antisymmetric.
    move => A. 
    rewrite /total_on => H2.
    have H3: total_on A (curry leSet1). 
    move => s t H5 H6. 
    have H7:`[< curry leSet1 s t >] \/ `[< curry leSet1 t s >] by apply H2. 
    by rewrite 2!asboolE in H7.     
    case H1: (A != set0).
    pose proof Sinf_final.
    move: H3 => /Chains_is_total H3. apply Sinf_final in H3.
    move: H3 => [Si H3].
    exists Si. move => S /H3 H4. by rewrite asboolE.
    by [].
    by [].
    move: H1 => /negP/contrapT/eqP H1. 
    move: (SType_not_empty A1 A3) => /notempty_exists [Sm Ht].
    by exists Sm; move => S; rewrite H1 -inP in_set0. 
  Qed.
  
  Lemma SmaxZ: exists Sm, forall S, (curry leSet1) Sm S -> S = Sm.
  Proof.
    move: SmaxZ_new => [Sm H1];exists Sm. move => S.
    move: H1 => /(_ S) H1; by rewrite asboolE in H1.
  Qed.
  
  (** * back to set T *)
  Lemma Exists_Smax: exists Sm, Sm \in Scal /\ forall T, T \in Scal -> Sm [<= (Asym Eb.+)] T -> T = Sm.
  Proof.
    move: SmaxZ => [Sm H1];exists (sval Sm); split; first by  apply: S2Scal.
    by move => S /Scal2S [S' <-] H3; f_equal;by apply H1.
  Qed.
  
  Section Maximal. 

    (** * We show that the maximal set is the independent set we search *)
    Variable (Sm: set T).
    
    Definition IsMaximal (S: set T):= 
      S \in Scal /\ forall T, T \in Scal -> S [<= (Asym Eb.+)] T -> S = T.
  
    Definition Sx:= [set y | ~ (y \in Sm) /\ ~ (y \in Mono#Sm)].

    Definition Tm x:= [set y | y \in Sm /\ ~ (Eb.+ (y,x))].

    Lemma TmI: forall x, Tm x `<=` Sm.
    Proof. by move => x y [/inP H2 _]. Qed.

    Lemma fact1: forall x y, y \in Sm -> ~(y \in (Tm x)) -> Eb.+ (y,x).
    Proof. by move => x y H3;rewrite inP not_andE => [[? // | /contrapT ? //]]. Qed.
    
    Lemma Sb1': forall x z, z \in Sm `\` (Tm x) -> Eb.+ (z,x).
    Proof. by move => x z /inP [/inP H3 /inP H4]; apply: (fact1 H3 H4). Qed.
    
    Definition Sxm x := forall y, y \in Sx -> Er.+(x,y) -> Er.+(y,x).
    
    (* A consequence of A3 *)
    Lemma Sx_1: (exists (x:T), (x \in Sx)) -> (exists (x:T), x \in Sx /\ Sxm x).
    Proof.
      by move => H1; move: (test68' A3 H1) => H2.
    Qed.
    
    Lemma fact: IsMaximal Sm -> (forall t, t\in Sm:#(Er.+) -> t \in Mono#Sm).
    Proof. by move => Smax t H3;move: Smax H3 => [/inP [_ [H8 _]] _] /inP/H8 H3;rewrite inP. Qed.
    
    Lemma fact2: IsMaximal Sm -> (forall x, RelIndep Mono (Tm x)).
    Proof.
      move => Smax x x1 x2 /inP [H3 _] /inP [H4 _] H5 H6;move: Smax => [/inP [H7 _] _].
      by move: ((H7 x1 x2) H3 H4 H5 H6).
    Qed.
    
    Lemma fact3: forall x, (x \in Sx) -> ~(x \in Mono#(Tm x)).
    Proof.
      move => x /inP [H2 H2'] H3;move: TmI => /(_ x)/Fset_inc1 => /(_ Mono) H4.
      by have: x \in Mono#Sm by move: H3;rewrite inP => /H4 -/inP H3.
    Qed.

    Lemma fact4: IsMaximal Sm -> (forall x, (x \in Sx) -> ~(x \in (Tm x):#Mono)).
    Proof.
      move => Smax x /inP [_ H2'] /inP [x1 [H5 [H3 H3']]]. 
      move: (H5) => [H5' // | /= H5'] .
      move: Smax => [/inP [_ [H6 _]] _].
      have H7: x \in Sm:#(Er.+) by rewrite inP;exists x1;rewrite inP in H3.
      by move: H7 => /inP/H6 -/inP H7.
    Qed.

    Lemma fact5: IsMaximal Sm -> (forall x, x \in Sx -> RelIndep Mono ((Tm x) `|` [set x])).
    Proof.
      by move => Smax x H2;apply:  RelIndep_U;[apply: fact2|apply: fact3|apply: fact4].
    Qed.
    
    Lemma fact6: forall x, x \in Sx -> Sm [<= (Asym Eb.+)] ((Tm x) `|` [set x]).
      move => x H2 x1 /= H3.
      case H4: (x1 \in Tm x).
      by (exists x1);split;[rewrite inP;left;rewrite -inP| left].
      exists x;split; first by rewrite inP;right. 
      right. 
      move: H2 H4 => /inP [_ H2'] /negP H4.
      
      move: (fact1 H3 H4) => H5.
      split => [// | H6].
      by have: x \in Mono#Sm by rewrite inP;(exists x1);split;[left|rewrite -inP].
    Qed.
    
    Lemma fact7: forall x, x \in Sx -> Sm = ((Tm x) `|` [set x]) -> False.
    Proof.
      by move => x /inP [H2 _] H3;have: x \in Sm by rewrite H3 inP; right.
    Qed.
    
    Lemma fact8: IsMaximal Sm -> (forall x, x \in Sx -> ~ (((Tm x) `|` [set x]) \in Scal)).
    Proof.
      move => Smax x H2 H3; move: (fact6 H2) Smax => H4 [H5 H6].
      have: Sm = ((Tm x) `|` [set x]) by apply: H6.
      by apply: (fact7 H2).
    Qed.
    
    Lemma fact9:  IsMaximal Sm -> 
                  (forall x, (x \in Sx) -> 
                      exists y, y \in (((Tm x) `|` [set x]):#(Er.+))
                               /\ ~ (y \in Mono#((Tm x) `|` [set x]))).
    Proof.
      move => Smax x H2.
      move: (fact8 Smax H2) => /inP /not_andP [H3 | /not_andP [H3 | H3]].  
      by move: (fact5 Smax H2).
      by move: H3 => /existsNP [y /not_implyP [/inP H3 /inP H4]];exists y.
      
      have H4: exists y, y \in (Tm x `|` [set x]) by (exists x);rewrite inP; right.
      have H5: Tm x `|` [set x] = set0 by rewrite -empty_iff;move => H6.
      move: H4;rewrite H5 => [[z H4]].
      by rewrite in_set0 in H4.
    Qed.
    
    Lemma FsetlU: forall x X Y (R: relation T), x \in R#X -> x \in R#(X `|` Y).
    Proof.
      move => x X Y R /inP H2.
      have H3: R#X `<=`  R#(X `|` Y) by apply: Fset_inc1; apply: subsetUl.
      by move: H2 => /H3/inP H2. 
    Qed.
    
    Lemma FsetUO: forall x X Y (R: relation T), 
        x \in R#(X `|` Y) -> x \in R#X \/ x \in R#Y.
    Proof.
      by move => x X Y R;rewrite FsetUr => /inP [ /inP H1 | /inP H1];[left | right].
    Qed.
    
    Lemma FsetDI: forall x X Y (R: relation T), 
        x \in R#(X `\` Y) -> x \in R#X.
    Proof.
      move => x X Y R /inP H2.
      have H3: R#(X `\` Y) `<=` R#(X) by apply: Fset_inc1;rewrite setDE; apply: subIsetl.
      by move: H2 => /H3 H2;rewrite inP.
    Qed.
    
    (** strangely it is not necessary to separate the two cases 
        Sm = (Tm x) or Sm <> (Tm x) *)

    Lemma fact11:  IsMaximal Sm -> (forall x, x \in Sx -> Sxm x -> Sm = (Tm x) -> False).
    Proof.
      move => Smax x H2 H2' H3.
      have H6: ~ (x \in Sm:#Mono) by move: (fact4 Smax H2); rewrite -H3.
      have H7: ~ (x \in Mono#Sm) by move: (fact3 H2); rewrite -H3.
      have [y [H8 H9]]:
        (exists y, y \in (Sm `|` [set x]):#(Er.+) /\ ~ (y \in Mono#(Sm `|` [set x])))
        by rewrite H3; apply: fact9.
      have H10: ~ (y \in Sm:#Er.+)
        by move => H11;(have H12: y \in Mono#Sm by apply: fact);
                  (have H13: y \in Mono#(Sm `|` [set x]) by apply: FsetlU).
      have H11: y \in [set x]:#Er.+.
      move: H8 => /FsetUO [H8 | H8]; last by [].
      have: y \in Mono#(Sm). 
      by rewrite -FsetUl inP;right;rewrite -inP.
      have: y \in Mono#(Sm`|` [set x]) by apply: FsetlU.
      by [].
      (* end of H11 *)
      have H12: Er.+ (x,y) by move: H11; rewrite inP /Aset/Fset => [[z [H11 <-]]].
      
      have H13: ~ (y \in Sm) 
        by (move => H14;
                   (have: x \in Mono#Sm by rewrite inP;
                    exists y;split;[right| rewrite -inP])).
      have H14: y \in Sx by rewrite inP;split;[| move => /(FsetlU [set x]) H15].
      have H15: Er.+ (y,x) by apply: H2'. 
      
      have H16: y \in Mono#([set x]) 
          by rewrite -FsetUl inP; right; rewrite -Fset_t0.
      have H17: y \in Mono#(Sm `|` [set x]) by rewrite setUC FsetlU.
      by [].
    Qed.

    Lemma fact12_1: forall x, (x \in Sx) -> (Tm x) `|` (Sm `\` (Tm x)) = Sm.
    Proof.
      move => x H2.
      have H3: (Sm `&` (Tm x)) = (Tm x) by rewrite setIC setIidPl;apply: TmI.
      have H4: ((Sm `&` (Tm x)) `|` (Sm `\` (Tm x)) = Sm) by rewrite setUIDK.
      by rewrite H3 in H4.
    Qed.
    
    Lemma fact12: IsMaximal Sm -> 
                  (forall x, x \in Sx -> Sxm x -> (exists z, z \in Sm /\ ~(z\in (Tm x))) -> False).
    Proof.
      move => Smax x H2 H3 [z [H4 H5]].
      move: (fact9 Smax H2) => [y [/FsetUO [H6|H6] H7]].
      - (* y \in Er.+.-1#(Tm x) *)
        have H8: y \in Er.+^-1#Sm
            by move: TmI => /(_ x)/Fset_inc1 => /(_ Er.+^-1) H9;
                                              move: H6; rewrite inP => /H9 H6;rewrite inP.
        have H9: y \in Mono#Sm by apply: fact.
        move: (fact12_1 H2) => H12.
        move: H9;rewrite -H12 => /FsetUO [H9 | H9].
        by have H13:  y \in Mono#(Tm x `|` [set x]) by apply: FsetlU.
        move: H9;rewrite -FsetUl inP => [[H9 | H9]].
        + move: H9 => [t [H13 /inP H14]].
          move: H14 => /Sb1' H14.
          have H15: Eb.+ (y,x) by apply: (TclosT H13 H14).
          have H16: y \in Mono#_(x)
              by rewrite -FsetUl inP;left;rewrite -Fset_t0.
          have H17: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC; apply: FsetlU.
          by [].
        + (* T -R-> y -R-> S \ (Tm x) contredit indep  *)
          move: H6 => /inP [z1 [H13 H14]].
          move: H9 => [z2 [H15 H16]].
          have H17: Er.+ (z1, z2) by apply: TclosT H13 H15.
          have H17': Mono (z1,z2) by right.
          
          (* montrer que z1 et z2 sont differents et dans Sm *)
          have H19: z1 <> z2.
          move => H20.
          have H21: ~(z2 \in (Tm x)) by apply subDsetr in H16; move => /inP H21.
          by move: H14; rewrite H20 => /inP H14.

          move: H14 => /TmI H14.
          apply subDsetl in H16.
          move: Smax => [/inP [ISm _] _].
          move: ISm => /(_ z1 z2) ISm.
          move: H16 H14 => /inP H16 /inP H14.
          have H22: ~( Mono(z1,z2)) by apply: (ISm H14 H16 H19).
          by [].
      - (* x -R-> y est contradictoire *)
        move: H6; rewrite inP -Fset_t0 /inverse /= => H6.
        have H8: ~(y \in Mono#Sm).
        rewrite -FsetUl => /inP [H9 | H9].
        + (* de H9 on a aussi Eb.+#(Sm\ T) y car ~ (y -M-> T) 
         on en deduit que y -B-> x quicontredit 5 *)
          move: (fact12_1 H2) H9 => <- /inP/FsetUO [H9 | H9].
          by have H11: y \in Mono#(Tm x `|` [set x])
              by apply: FsetlU;rewrite -FsetUl inP;left;rewrite -inP.
          move: H9; rewrite inP => [[z1 [H10 /inP H11]]].
          move: (Sb1' H11) => H12.
          have H13: Eb.+ (y,x) by apply: (TclosT H10 H12).
          have H14: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -FsetUl inP;
            left;rewrite -Fset_t0.
          by [].
        + (* ici y-R-> S et x-R-> y => x -R-> S contredit def de x *)
          move: H9 => [z1 [H9 H10]].
          have H11: x \in Mono#Sm
              by rewrite inP;exists z1;split;[right;apply: (TclosT H6 H9) |].
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H8 *)
          have H13: ~ (y \in Sm).
          move => H14.
          have H15: x \in Mono#Sm. 
          rewrite inP.
          exists y;split. 
          by right. by rewrite -inP.
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H13 *)
          have H14: y \in Sx. by rewrite inP;split.        
          
          rewrite /Sxm in H3.
          have H15: Er.+ (y, x). apply: ((H3 y) H14 H6). 
          have H16: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -FsetUl inP;
            right;rewrite -Fset_t0.
          by [].
    Qed.
    
    Lemma fact12': IsMaximal Sm -> (forall x, x \in Sx -> Sxm x -> False).
    Proof.
      move => Smax x H2 H3.
      move: (fact9 Smax H2) => [y [/FsetUO [H6|H6] H7]].
      - (* y \in Er.+.-1#(Tm x) *)
        have H8: y \in Er.+^-1#Sm
            by move: TmI => /(_ x)/Fset_inc1 
             => /(_ Er.+^-1) H9;
               move: H6; rewrite inP => /H9 H6;rewrite inP.
        have H9: y \in Mono#Sm by apply: fact.
        move: (fact12_1 H2) => H12.
        move: H9;rewrite -H12 => /FsetUO [H9 | H9].
        by have H13:  y \in Mono#(Tm x `|` [set x]) by apply: FsetlU.
        move: H9;rewrite -FsetUl inP => [[H9 | H9]].
        + move: H9 => [t [H13 /inP H14]].
          move: H14 => /Sb1' H14.
          have H15: Eb.+ (y,x) by apply: (TclosT H13 H14).
          have H16: y \in Mono#_(x)
              by rewrite -FsetUl inP;left;rewrite -Fset_t0.
          have H17: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC; apply: FsetlU.
          by [].
        + (* T -R-> y -R-> S \ (Tm x) contredit indep  *)
          move: H6 => /inP [z1 [H13 H14]].
          move: H9 => [z2 [H15 H16]].
          have H17: Er.+ (z1, z2) by apply: TclosT H13 H15.
          have H17': Mono (z1,z2) by right.
          
          (* montrer que z1 et z2 sont differents et dans Sm *)
          have H19: z1 <> z2.
          move => H20.
          have H21: ~(z2 \in (Tm x)) by apply subDsetr in H16; move => /inP H21.
          by move: H14; rewrite H20 => /inP H14.

          move: H14 => /TmI H14.
          apply subDsetl in H16.
          move: Smax => [/inP [ISm _] _].
          move: ISm => /(_ z1 z2) ISm.
          move: H16 H14 => /inP H16 /inP H14.
          have H22: ~( Mono(z1,z2)) by apply: (ISm H14 H16 H19).
          by [].
      - (* x -R-> y est contradictoire *)
        move: H6; rewrite inP -Fset_t0 /inverse /= => H6.
        have H8: ~(y \in Mono#Sm).
        rewrite -FsetUl => /inP [H9 | H9].
        + (* de H9 on a aussi Eb.+#(Sm\ T) y car ~ (y -M-> T) 
         on en deduit que y -B-> x quicontredit 5 *)
          move: (fact12_1 H2) H9 => <- /inP/FsetUO [H9 | H9].
          by have H11: y \in Mono#(Tm x `|` [set x])
              by apply: FsetlU;rewrite -FsetUl inP;left;rewrite -inP.
          move: H9; rewrite inP => [[z1 [H10 /inP H11]]].
          move: (Sb1' H11) => H12.
          have H13: Eb.+ (y,x) by apply: (TclosT H10 H12).
          have H14: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -FsetUl inP;
            left;rewrite -Fset_t0.
          by [].
        + (* ici y-R-> S et x-R-> y => x -R-> S contredit def de x *)
          move: H9 => [z1 [H9 H10]].
          have H11: x \in Mono#Sm
              by rewrite inP;exists z1;split;[right;apply: (TclosT H6 H9) |].
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H8 *)
          have H13: ~ (y \in Sm).
          move => H14.
          have H15: x \in Mono#Sm. 
          rewrite inP.
          exists y;split. 
          by right. by rewrite -inP.
          by move: H2; rewrite inP => [[_ H13]].
          (** end of H13 *)
          have H14: y \in Sx. by rewrite inP;split.        
          
          rewrite /Sxm in H3.
          have H15: Er.+ (y, x). apply: ((H3 y) H14 H6). 
          have H16: y \in Mono#(Tm x `|` [set x])
              by rewrite setUC;apply: FsetlU;rewrite -FsetUl inP;
            right;rewrite -Fset_t0.
          by [].
    Qed.

    Lemma fact13: IsMaximal Sm -> ~(exists x, x \in Sx).
    Proof.
      by move => H0 /Sx_1 [v [H1 H2]];apply: (fact12' H0 H1 H2).
    Qed.

    Lemma fact14: IsMaximal Sm -> (forall x, ~ (x\in Sm) -> (x \in Mono#Sm)).
    Proof.
      move => Smax x H1. 
      move: (fact13 Smax) => /forallNP /(_ x) H2.
      have H3: ~ (x \in Sx) <-> (x \in Sm) \/ (x \in Mono#Sm) by rewrite inP not_andE 2!not_notP.
      by move: H2 => /H3 [H2 | H2].
    Qed.
    
  End Maximal. 
  
  Theorem Final: exists (Sm: set T), forall x, ~ (x\in Sm) -> (x \in Mono#Sm). 
    Proof.
      move: Exists_Smax => [Sm [H1 H2]]. 
      have H3: IsMaximal Sm 
        by split => [// |U H3 H4];have ->: U = Sm by apply: H2 H3 H4.
      by exists Sm; move => x; apply: fact14.
    Qed.
    
End Paper.
