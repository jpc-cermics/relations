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

From RL Require Import  paper_monochromatic_f paper_meunier_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Paper. 
  (*  abstract version *)
  Variables (T:choiceType) (R B O: relation T).
  
  Definition M' := B `|` R.
  
  Definition Scal := [set S| RelIndep M' S /\ S:#(R) `<=` M'#S/\S != set0 ].
  
  Definition SType := {S | RelIndep M' S /\ S:#(R) `<=` M'#S/\S != set0}.

  Definition Elt (C: set SType) := {x : T |exists (S: SType), S \in C /\ x \in (sval S)}.
  
  Lemma S2Scal: forall (S: SType), (sval S) \in Scal.
  Proof. by move => [S [H1 [H2 H3]]];rewrite inE. Qed.

  Lemma Scal2S: forall S, S \in Scal -> exists (S': SType), (sval S') = S.
  Proof. by move => S /inP H1; exists (exist _ S H1). Qed.

  Lemma ScalProp: forall S S1,
      RelIndep M' S -> S1 `<=` S -> (S1:#(R) `<=` M'#S <-> forall y, ~ (y \in S) -> y \in S1:#(R) -> y \in  M'#S).
  Proof.
    move => S S1 H1 H1';split => [H2 y _ /inP/H2/inP H4 //| H2 y H3].
    case H5: (y \in S);last first.
    + apply/inP/H2. by rewrite H5. by apply/inP.
    + move: H3. rewrite /Aset => -[y' [H6 H7]].      
      rewrite /RelIndep in H1.
      case H8: (y == y').
      ++ move: H8 => /eqP H8; have H9: M'(y,y) by rewrite -H8 in H6;rewrite /M';right.
         by move: H7 => /H1' H7;(exists y);rewrite -H8 in H7.
      ++ move: H8 H7 => /eqP H8 /inP H7.
         have H9:  y' <> y by move => H10;rewrite H10 in H8.
         move: H7 => /inP/H1'/inP H7.
         move: (H1 y' y H7 H5 H9) => H10.
         by have H11: M' (y', y) by rewrite /M;right.
  Qed.

  Lemma ScalProp1: forall S,
      RelIndep M' S -> (S:#(R) `<=` M'#S <-> forall y, ~ (y \in S) -> y \in S:#(R) -> y \in  M'#S).
  Proof. move => S H1; apply: (ScalProp H1 (@subset_refl T S)).  Qed.
  
  (** * The relation on sets restricted to Stype subsets *)
  Definition leSet1 (AB: SType*SType) :=
    leSet O ((sval AB.1), (sval AB.2)).
  Notation "A [<=] B" := (leSet1 (A,B)).
    
  Section Scal_order. 
        
    Lemma leSet1_transitive: sporder O -> @transitive SType leSet1.
    Proof. by move => [? ?] [X ?] [Y ?] [Z ?];apply/le_trans_if_tr. Qed.
           
    Lemma leSet1_reflexive: @reflexive _ leSet1.
    Proof. by move => [A ?];apply: le_refl. Qed.
    
    Lemma le_antisym_l1: forall A B, 
        sporder O -> O  `<=` M' `|` M'^-1 ->  (RelIndep M' A) -> (RelIndep M' B)
        -> A [<= O] B -> B  [<= O] A -> A = B.
    Proof.
      move => X Y H1 H3 /RelIndep_Is H4 /RelIndep_Is H5. 
      apply/le_antisym_if_sp. exact.
      by apply/(@RelIndep_I T O (M' `|` M'^-1) X H3 H4).
      by apply/(@RelIndep_I T O (M' `|` M'^-1) Y H3 H5).
    Qed.
    
    Lemma leSet1_antisymmetric: sporder O -> O `<=` M' `|` M'^-1 -> @antisymmetric _ leSet1.
    Proof. 
      move => H1 H2 [X [Hx Hx']] [Y [Hy Hy']] H3 H4.
      move: (le_antisym_l1 H1 H2 Hx Hy H3 H4) => H5.
      subst X. (** why I cannot use rewrite *)
      apply: f_equal.
      apply: proof_irrelevance.
    Qed.
    
    Lemma leSet1_porder: sporder O -> O  `<=`  M' `|` M'^-1 -> @porder _ leSet1. 
    Proof.
      move => ? ?; split. 
      + by apply/leSet1_reflexive.
      + by apply/leSet1_antisymmetric.
      + by apply/leSet1_transitive. 
    Qed.
    
  End Scal_order.

  Section Sinf_set.
    (** * Sinf C for (C: set SType) and C != set0 *)
    
    Variables  (C: set SType).
    Hypothesis Hne: C != set0.
    
    (* Set Sinf associated to a chain C *)
    (* begin snippet Sinf:: no-out *)   
    Definition Sinf := 
      [ set v: T | 
        exists S, (S \in C) /\ (v \in (sval S)) /\
               (forall T, T \in C -> S [<=] T -> v \in (sval T))].
    (* end snippet Sinf *)   

    (* A relation on the set Elt C, all the elements
       of T which are elements of a set in C *)
    (* begin snippet RC:: no-out *)   
    Definition RC:= [set xy: (Elt C)*(Elt C) |
                      ((sval xy.1) \in Sinf /\ xy.2 = xy.1)
                      \/ (~ ((sval xy.1) \in Sinf) /\
                           O (sval xy.1, sval xy.2))].
    (* end snippet RC*)   
        
    Lemma transitive_RC:  sporder O -> transitive RC. 
    Proof.
      move => [_ H3].
      by move => x y z [/= [H0 ->]| [H1 H1']] [ /= [H0' /= ->]| /= [H2 H2']]; 
                [left | right | right |right;split;[ | apply H3 with (sval y)]].
    Qed.

    (** * Elt C  is not empty *)
    (* begin snippet Eltnotempty:: no-out *)   
    Lemma Elt_not_empty: exists _ : Elt C, True.
    (* end snippet Eltnotempty *)   
    Proof.
      have: exists (S: SType), S \in C /\ (exists x, x \in (sval S)).
      move: Hne => /notempty_exists [S H2];exists S;split;first by []. 
      by move: S H2 => [S' [H3 [H4 /notempty_exists H5]] /=] _.
            
      move => [S [? [x ?]]].
      have H4: exists (S: SType), S \in C /\ x \in (sval S) by (exists S).
      by exists (exist _ x H4).
    Qed.
    
    Section total_RC. 
      (** *  the main result here is total_RC *) 

      Lemma total_RC_L1: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, S1 \in C /\ S [<=] S1 /\ ~ (s \in (sval S1)).
      Proof.
        move => S s H2 H3. 
        apply contraPP;rewrite not_existsP 2!not_notE inE /Sinf => H4;exists S.
        split => [// | ];split => [// |A ? ?].
        by move: H4 => /(_ A) /not_andP [? //|/not_andP [// | /contrapT ?]].
      Qed.
      
      Lemma total_RC_L2: forall (S: SType) (s:T), 
          (S \in C) -> (s \in (sval S)) -> ( ~ (s \in Sinf)) 
          -> exists S1, exists s1, S1 \in C /\ s1 \in (sval S1) /\ O (s,s1).
      Proof.
        move => S s H2 H3 H4.
        move: (total_RC_L1 H2 H3 H4) => [S1 [H5 [H6 H7]]].
        by move: ((H6 s) H3) => [s1 [H8 [H9 | H9]]];exists S1, s1;[rewrite -H9 in H8|].
      Qed.
      
      Lemma total_RC_L3: forall (s: Elt C), 
          ~ ((sval s) \in Sinf) -> exists (s1: Elt C), O (sval s,sval s1).
      Proof.
        move => [s [S [H1 H2]]] H3.
        move: (total_RC_L2 H1 H2 H3) => [S1 [s1 [H4 [H5 H6]]]].
        have H7: exists (S: SType), S \in C /\ s1 \in (sval S) by (exists S1).
        by exists (exist _ s1 H7).
      Qed.
      
      (* begin snippet totalRC:: no-out *)    
      Lemma total_RC: total_rel RC. 
      (* end snippet totalRC *)    
      Proof.
        move => s.
        case H3: ((sval s) \in Sinf); first by (exists s); left.
        have H4: ~ ((sval s) \in Sinf) by move => H5;rewrite H5 in H3.
        move: (total_RC_L3 H4) => [s1 H5].
        by exists s1; right.
      Qed.

      Lemma iic_RC: (iic RC).
      Proof.
        apply DC; last by apply: total_RC.
        move: Elt_not_empty => [x _];exists x;by apply/inP.
      Qed.
      
    End total_RC. 
        
    Lemma Elt_not_empty_witness: Elt C.
    Proof. by apply: inhabited_witness; rewrite inhabitedE; apply: Elt_not_empty. Qed.
    
    Section total_RC_to_iic.
      (** consequence of the fact that RC is total *)

      Implicit Type (f: nat -> Elt C) (s: Elt C).
        
      Lemma total_RC_P1 s f: 
        f 0=s /\ (forall n, RC ((f n),(f (S n)))) 
        -> (forall n, ~ (sval (f n)) \in Sinf) -> iic O. 
      Proof. 
        move => H1 H2;exists (fun n => (sval (f n))) => n.
        by move: H1 H2 => [H0 /(_ n) [/=[H1 H1'] | /= [H1 H1']]] /(_ n) H2.
      Qed.
      
      Lemma total_RC_P2:
        ~ (iic O)
        -> forall s, exists f, (f 0=s /\ (forall n, RC ((f n),(f (S n)))))
                    /\ exists n, (sval (f n)) \in Sinf.
      Proof. 
        move: total_RC => /total_rel_iff /total_rel'_to_total_rel'' H1.
        move: H1 => + H2 s => /(_ s) [f H3].
        exists f;split;[exact | apply/not_existsP]. 
        by move: H3 => /total_RC_P1 H3;move => /H3 H4.
      Qed.
      
      Lemma transitiveN_RC f:  
        sporder O -> (forall n, RC ((f n),(f (S n))))   -> (forall n, n > 1 -> RC (f 0, f n)).
      Proof.
        move => H0 H1;elim => [// | n Hn H2 ].
        case H3: (1 < n). 
        + have H4: RC (f 0, f n) by apply: Hn;rewrite H3.
          by move : (transitive_RC H0 H4 (H1 n)).
        + case H5: (n == 0); first by move: H5 => /eqP ->;apply: H1.
          case H6: (n == 1); first by move: H6 => /eqP ->;move: (transitive_RC H0 (H1 0) (H1 1)).
          have H7: ~ (n <= 1) by rewrite leq_eqVlt H6 ltnS leqn0 H5.  
          by rewrite leqNgt H3 in H7.
      Qed.
      
      (* begin snippet totalRCPTr:: no-out *)    
      Lemma total_RC_P3:
        sporder O ->  ~ (iic O) ->
        forall s, exists f, f 0=s /\ (exists n, (sval (f n)) \in Sinf /\ RC ((f 0), (f n))).
      (* end snippet totalRCPTr *)
      Proof.
        move => H0 H1; move: (total_RC_P2 H1) => + s => /(_ s) [f [[H2 H3] [n H4]]].
        exists f;split;first exact.
        case H5: (sval (f 0) \in Sinf);first by (exists 0);split;[ | left].
        have H6: ~ (n = 0) by move => H7;rewrite H7 H5 in H4. 
        case H7: (sval (f 1) \in Sinf);first by (exists 1).
        exists n. 
        have H8: ~ (n = 1) by move => H8;rewrite H8 H7 in H4.
        have H9: n > 1 by lia. 
        move: (transitiveN_RC H0 H3) => /(_ n) H10.
        by split;[| apply: H10].
      Qed.

      (* begin snippet ChooseRCCi:: no-out *)    
      Lemma ChooseRC5:sporder O -> ~ (iic O)
            -> forall (s: Elt C), (sval s \in Sinf) \/ 
                        exists (s':T), (s' \in Sinf) /\ O (sval s, s').
      (* end snippet ChooseRCCi *)    
      Proof. 
        move => H0 H1; move: (total_RC_P3 H0 H1) => + s => /(_ s) [f [H2 [n [H3 H3']]]].
        case H4: (sval (f 0) \in Sinf); first by left;rewrite -H2 H4.
        right;exists (sval (f n));split;first exact. 
        rewrite -H2. 
        by move: H3' => [/= [H3' _] | /= [H5 H6]//];rewrite H4 in H3'.
      Qed.

      (* begin snippet ChooseRCSi:: no-out *)    
      Lemma ChooseRC6:sporder O -> ~ (iic O)
            -> forall (S: SType), (S \in C) -> (sval S) [<= O] Sinf.
      (* end snippet ChooseRCSi *) 
      Proof. 
        move => H0 H1 S H2 s /= H3.
        have H4: exists (S: SType), S \in C /\ s \in (sval S) by (exists S).
        move: (ChooseRC5 H0 H1 (exist _ s H4)) => /= [H5 | [s' [H5 H6]]].
        by (exists s);split;[|left].
        by (exists s');split;[|right].
      Qed.
      
    End total_RC_to_iic.
    
  End Sinf_set.
  
  Section SType_chains.
    (** * set (C: set SType) which are in Chains *)
    
    Implicit Type (C: set SType).
    
    (* begin snippet Chains:: no-out *)    
    Definition ChainsB := @Chains SType leSet1. 
    (* end snippet Chains *)    
    
    Lemma Chains_is_total C: C \in ChainsB <-> total_on C (curry leSet1).
    Proof. split => [/inP H2 c1 c2 ? ?| H1];first by apply: H2. 
           by apply/inP => c1 c2 ? ?;apply: H1.
    Qed.
    
    Lemma Chains_Scal C S: C \in ChainsB -> S \in C -> Scal (sval S).
    Proof. by move: S => [S [H1 [H2 H3]]] /inP H4 /inP H5. Qed.
    
  End SType_chains.
  
  Section Sinf_chains.
    (** * Sinf when C is a non empty Chain *)
    
    Variables  (C: set SType).
    Hypothesis Hc: C \in ChainsB. 
    Hypothesis Hne: C != set0.
        
    (* Sinf is a M'ono-independent set when C is a chain *)
    Lemma Sinf_indep: RelIndep M' (Sinf C).
    Proof.
      move: Hc => /inP H1 x y /inP H2 /inP H3 H4 /= H5.
      move: H2 H3 =>[S [/[dup] H6 /inP P6 [/= H7 H8]]]
                     [U [/[dup] H6' /inP P6' [/= H7' H8']]].
      move: H8 H8' => /((_ U) H6') H8 /((_ S) H6) H8'.
      have [H9|H9]: S [<=] U \/ U [<=] S by apply: H1.
      - move: H9 H1 => /H8 H9 /inP H1.
        move: (Chains_Scal H1 H6') => [/(_ x y) H10 _].
        by apply: (H10 H9 H7' H4 H5).
      - move: H9 H1 => /H8' H9 /inP H1.
        move: (Chains_Scal H1 H6) => [/(_ x y) H10 _].
        by apply: (H10 H7 H9 H4 H5).
    Qed.
    
    (* begin snippet Scalnotempty:: no-out *) 
    Lemma Scal_not_empty (A1: Assumption1 T) (A2: Assumption2 R):
      exists v, Scal [set v].
    (* end snippet Scalnotempty *)
    Proof.
      have: Rloop R by apply: notiic_rloop.
      move => [v H1]; exists v.
      have H2':  R `<=` M' by rewrite /M';apply: subsetUr.
      split;first by rewrite /RelIndep;move => x y /inP /= -> /inP /= ->.
      split;first by move => t [y [/= H3 H4]];move: H3; rewrite H4 /= => /H1/H2' H3;exists v.
      by rewrite -notempty_exists;(exists v);rewrite inE.
    Qed.
    
    Lemma SType_not_empty (A1: Assumption1 T) (A2: Assumption2 R):
      (@setT SType) != set0.
    Proof.
      rewrite -notempty_exists;move: (Scal_not_empty A1 A2) => [v H2].
      by exists (exist _ [set v] H2);rewrite inE.
    Qed.
    
    Lemma Sinf_not_empty (A3: Assumption3 O) (A4: Assumption4 O):
      (Sinf C) != set0.
    Proof.
      move: (@Elt_not_empty C Hne) => [s _];rewrite -notempty_exists.
      by move: (@ChooseRC5 C Hne A4 A3 s) => [H1 | [s' [H1 _]]];[exists (sval s) | exists s'].
    Qed.
    
    (* begin snippet SinfScalP:: no-out *)    
    Lemma Sinf_ScalP (A2: Assumption2 R) (A3: Assumption3 O) 
      (A4: Assumption4 O) (A5:Assumption5 O M') (A9: Assumption9 R B O M'):
      (Sinf C):#(R) `<=` M'#(Sinf C).
     (* end snippet SinfScalP *)
    Proof.
      move: Hc => H1 y [x [B1 H3]].
      move: (H3) => [X [H4 [H5 H6]]].
      move: (Chains_Scal H1 H4) => [H7 [H8 H9]].
      move: (EM (y \in (Sinf C))) => [ H9' | H9'].
      + (* we eliminate the case y \in Sinf C *)
        move: H3 => /inP H3. 
        move: (Sinf_indep H3 H9') => H10.
        move: (EM (x = y)) H3 => [H11 | H11] /inP H3.
        by (exists x);(have H12: M'(y,x) by right;move: B1;rewrite H11).
        by move: H11 => /H10 H11;(have H12: M'(x,y) by right).
      + (* now  ~ y \in Sinf C *)
        have B2: ~ (x = y) by move => I1;rewrite -I1 inE in H9'.
        move: (EM (M' (y,x))) => [? | B3];first by (exists x).
        have H10: (sval X):#R y by (exists x);split;[ |rewrite -inE].
        move: H10 => /H8 [x' [B4 /inP H11]].
        
        move: (EM (x' \in (Sinf C))) => [/inP ? | B5];first by (exists x').
        (* now x' not in Sinf C *)
        have B6: ~ (x = x') by move => I1; move: H3;rewrite I1 => /inP H3. 
        have B3': ~ (y = x')
          by move => I1;rewrite I1 in B1;
                    (have I3: M' (x,x') by right);move: (H7 x x' H5 H11 B6).
        
        have H12: (sval X) [<= O] (Sinf C)  by apply: ChooseRC6. 
        move: (H11) => /H12 [y' [/= B7 [H21 | B8]]].  
        by rewrite -H21 in B7.
        
        move: (EM (x' = y')) B4 => [-> | B3''] B4.
        by (exists y'); rewrite inE in B7. 
        
        have P11': ~ ((M' `|` M'^-1) (x',x))
          by pose proof (@RelIndep_E _ x x' M' _ H5 H11 B6 H7).
        
        move: (EM (x = y')) B8 => [<- /A5 B10 //| B9 /[dup] B8 /A5 B10].
        
        have P1: ~ (x = y) by apply: B2.
        have P2: ~ (x = x') by apply: B6. 
        have P3: ~ (x = y') by apply: B9.
        have P4: ~ (y = x') by apply: B3'.
        have P5: ~ (x' = y') by apply: B3''.
        have P6: ~ (y' = y) by  move => I1; by rewrite I1 in B7.
        have P7: R (x, y) by apply: B1.
        have P8: M' (y, x') by apply: B4.
        have P9: O (x',y') by apply: B8.
        have P10: ~ M' (y, x) by apply: B3.
        have P11: ~ ((M' `|` M'^-1) (x',x)) by apply: P11'.
        have P12: ~ ((M' `|` M'^-1) (y',x))
          by move: H3 => /inP H3;
                        pose proof (@RelIndep_E _ x y' M' _ H3 B7 P3 (Sinf_indep)).
        
        exists y'. split. by apply: (A9 x y x' y' P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12). by rewrite -inE.
    Qed.
    
    (* begin snippet SinfScal:: no-out *)    
    Lemma Sinf_Scal (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
      (A5:Assumption5 O M') (A9: Assumption9 R B O M'):
      (Sinf C) \in Scal. 
    (* end snippet SinfScal *)
    Proof.
      by rewrite inE;split;[apply: Sinf_indep|split;[apply: Sinf_ScalP|apply: Sinf_not_empty]].
    Qed.
    
    Lemma Sinf_final (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)   (A5:Assumption5 O M') (A9: Assumption9 R B O M'):
      exists Si, forall (S: SType), C S -> S [<=] Si.
    Proof.
      move: (Sinf_Scal A2 A3 A4 A5 A9) => /inP H2;exists (exist _ (Sinf C) H2);move => S /inP H3. 
      by apply: ChooseRC6.
    Qed.

  End Sinf_chains.
    
  (** * existence of Smax with Zorn Lemma for type SType *)
  (* begin snippet SmaxSType:: no-out *)    
  Lemma Smax_SType
    (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O) (A5: Assumption5 O M')
    (A9: Assumption9 R B O M'):
    exists Sm, forall S, Sm [<=] S -> S = Sm.
  (* end snippet SmaxSType *)
  Proof.
    apply: (@Zorn_relation SType leSet1 (leSet1_porder A4 A5)) => C.
    move: (@Sinf_final C) => H2 /inP H3.
    move: H3 => {}/H2 H3.
    case H4: ( C != set0 ); first by apply: (H3 H4 A2 A3 A4 A5 A9).
    move: H4 => /negP/contrapT/eqP H4. 
    move: (SType_not_empty A1 A2) => /notempty_exists [Sm Ht].
    by exists Sm; move => S; rewrite H4 -inE in_set0. 
  Qed.
  
  (** * existence of Smax in set T *)
  (* begin snippet SmaxE:: no-out *)    
  Lemma Smax_Scal 
    (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O) (A5: Assumption5 O M')
    (A9: Assumption9 R B O M'):
    exists Sm, Sm \in Scal /\ forall T, T \in Scal -> Sm [<= O] T -> T = Sm.
  (* end snippet SmaxE *)    
  Proof.
    move: (Smax_SType A1 A2 A3 A4 A5 A9) => [Sm H1];exists (sval Sm); split; first by  apply: S2Scal.
    by move => S /Scal2S [S' <-] H3; f_equal;by apply H1.
  Qed.

  (** * existence of Smax in set T *)
  (* begin snippet IsMaximal:: no-out *)  
  Definition IsMaximal (S: set T):= 
      S \in Scal /\ forall T, T \in Scal -> S [<= O] T -> T = S.
  (* end snippet IsMaximal:: no-out *)  
  (* begin snippet Smax:: no-out *)    
  Lemma Smax (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
    (A5: Assumption5 O M') (A9: Assumption9 R B O M'):
    exists Sm, IsMaximal Sm.
  (* end snippet Smax *)    
  Proof. by move: (Smax_Scal A1 A2 A3 A4 A5 A9) => [Sm HH];exists Sm. Qed.
  
  Lemma main_lemma X 
    (A2: Assumption2 R) (A6: Assumption6 B M' O) (A7: Assumption7 R B M') 
    (A8: Assumption8 R B M') :
    IsMaximal X -> Mabsorbant R B X.
  Proof.
    contra; move => H1 /inP H2. 
    have H3: Non_Mabsorbant R B X. move: H1 => [y H1] H3. exists y. rewrite inE.
    split. by []. rewrite notin_setE in H3. by rewrite inE.
    move: (extend A2 A6 A7 A8 H2 H3) => [X' [/inP H4 [H5 [x' [H6 H7]]]]].
    exists X'. by []. split. by [].
    apply /eqP => /seteqP [H8 H9].
    by move: H6 => /inP/H8/inP H6.
  Qed.
  
  Implicit Type (S X: set T).
  
  (** * The Assumptions we use: weaker than the original paper assumptions *)
  (* begin snippet MainTh:: no-out *)    
  Theorem G_SSW
    (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
    (A5: Assumption5 O M') (A6: Assumption6 B M' O) (A7: Assumption7 R B M') (A8: Assumption8 R B M')
    (A9: Assumption9 R B O M'):
    exists X, RelIndep M' X /\  X != set0 /\  forall x, ~ (x\in X) -> (x \in M'#X). 
  (* end snippet MainTh:: no-out *)    
  Proof.
    move: (Smax A1 A2 A3 A4 A5 A9) => [Sm H1].
    move: (main_lemma A2 A6 A7 A8 H1) => H2.
    move: H1 => [/inP [H1 [H4 H5]] H3].
    by exists Sm. 
  Qed.
  
End Paper.

Module SSWext.
  (** * Extended SSW Theorem *)
  Parameter (T:choiceType) (Eb Er: relation T).

  Definition R := Er.+. 
  Definition B := Eb.+. 
  Definition O := (Asym B). 

  Definition SSW_1:= (NotEmpty T).
  Definition SSW_2:= ~ (iic (Asym R)).
  Definition SSW_3:= ~ (iic (Asym B)).
  
  Lemma R_trans: transitive R.
  Proof. by apply: (@TclosT _ Er). Qed.

  Lemma B_trans: transitive B.
  Proof. by apply: (@TclosT _ Eb). Qed.
  
  Lemma L4: (Assumption4 O). 
  Proof. by apply: (@Asym_sporder _ B);apply: TclosT. Qed.
  
  Lemma L5: (Assumption5 O (M R B)).
  Proof. 
    have H1: O `<=` M' R B
      by apply: (@subset_trans _ B _ _ (@AsymI _ B)
                   (@subsetUl _ B R)).
    by pose proof (@subset_trans _ _ O _  H1 (@subsetUl _ (M' R B) (M' R B)^-1)).
  Qed.
  
  Lemma L6: (Assumption6 B (M R B) O).
  Proof. move => x y [? ?];split;first exact.
         move => ?; by have: M' R B (y, x) by left.
  Qed.

  Lemma L7: (Assumption7 R B (M R B)).
  Proof. 
    move => x x' y y' H1 H2 [H3|H3] H4 H5 H6 H7 H8 H9.
    by left;apply: (B_trans H3 H4).
    by have: M' R B (x,x') by right;apply: (R_trans H2 H3).
  Qed.
  
  Lemma L8: (Assumption8 R B (M R B)).
  Proof. 
    move => x' y y' B0 B0' B0'' H1 [H2| H2] H3 [H4 H5].
    by left;apply: (B_trans H2 H3).
    by have H11: M' R B (y,x') by right;apply: (R_trans H1 H2).
  Qed.
  
  Lemma L9: (Assumption9 R B O (M R B)).
  Proof. 
    move =>  x y x' y' P0 P1 P2 P3 P4 P5 H1 [H2|H2] H3 H4 H5 H6.
    by move: H3 => /(@AsymI _ B) H3;left;apply: (B_trans H2 H3).
    by have: (M' R B `|` (M' R B)^-1) (x',x) by right;right;apply: (R_trans H1 H2).
  Qed.
  
  Theorem SSWext
    (A1: SSW_1) (A2: SSW_2) (A3: SSW_3):
    exists X, RelIndep (M' R B) X /\  X != set0 /\  forall x, ~ (x\in X) -> (x \in (M' R B)#X). 
  (* end snippet MainTh:: no-out *)    
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 L4 L5 L6 L7 L8 L9).
  Qed.
  
End SSWext.

Module ABkernels.
  (** * The case of AB kernels  *)
  Parameter (T:choiceType) (A1 A2: relation T).

  Definition R := A1.
  Definition B := A2.
  Definition O := (Asym B). 

  Definition AB_1:= (NotEmpty T).
  Definition AB_2:= ~ (iic (Asym R)).
  Definition AB_3:= ~ (iic (Asym B)).
  Definition AB_4:= transitive R.
  Definition AB_5:= transitive B.

  Lemma L4 (A5: AB_5) : (Assumption4 O). 
  Proof. by apply: (@Asym_sporder _ B). Qed.
  
  Lemma L5: (Assumption5 O (M R B)).
  Proof. 
    have H1: O `<=` M R B
      by apply: (@subset_trans _ B _ _ (@AsymI _ B)
                   (@subsetUl _ B R)).
    by pose proof (@subset_trans _ _ O _  H1 (@subsetUl _ (M R B) (M R B)^-1)).
  Qed.
  
  Lemma L6: (Assumption6 B (M R B) O).
  Proof. move => x y [? ?];split;first exact.
         move => ?; by have: M R B (y, x) by left.
  Qed.

  Lemma L7 (A4: AB_4) (A5: AB_5): (Assumption7 R B (M R B)).
  Proof. 
    move => x x' y y' H1 H2 [H3|H3] H4 H5 H6 H7 H8 H9.
    by left;apply: (A5 y' x' y H3 H4).
    by have: M R B (x,x') by right;apply: (A4 x y' x' H2 H3).
  Qed.
  
  Lemma L8 (A4: AB_4) (A5: AB_5): (Assumption8 R B (M R B)).
  Proof. 
    move => x' y y' B0 B0' B0'' H1 [H2| H2] H3 [H4 H5].
    by left;apply: (A5 y' x' y H2 H3).
    by have H11: M R B (y,x') by right;apply: (A4 y y' x' H1 H2).
  Qed.
  
  Lemma L9(A4: AB_4) (A5: AB_5) : (Assumption9 R B O (M R B)). 
  Proof. 
    move =>  x y x' y' P0 P1 P2 P3 P4 P5 H1 [H2|H2] H3 H4 H5 H6.
    by move: H3 => /(@AsymI _ B) H3;left;apply: (A5 y x' y' H2 H3).
    by have: (M R B `|` (M R B)^-1) (x',x) by right;right;apply: (A4 x y x' H1 H2).
  Qed.

  Theorem SSWext
    (A1: AB_1) (A2: AB_2) (A3: AB_3) (A4: AB_4) (A5: AB_5):
    exists X, RelIndep (M R B) X /\  X != set0 /\  forall x, ~ (x\in X) -> (x \in (M R B)#X). 
  (* end snippet MainTh:: no-out *)    
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 (L4 A5) L5 L6 (L7 A4 A5)
                     (L8 A4 A5) (L9 A4 A5)).
  Qed.
  
End ABkernels.


Module MeunierLanglois. 
  Parameter (T:choiceType) (R B: relation T).

  Definition O := [set xy | (Asym B) (xy.1, xy.2) /\  ~ R (xy.2,xy.1)].
  Definition AB_1:= (NotEmpty T).
  Definition AB_2:= ~ (iic (Asym R)).
  Definition AB_3:= ~ (iic (Asym B)).
  Definition AB_4:=  forall x y z, 
      ~ (y = x) -> ~ (y = z) -> ~ (z = x)       
      -> R (x,y) -> R (y,z) -> R (x,z) \/ ( B (y,x) /\ B (z,x) ).
  
  Definition AB_5:=  forall x y z, 
      ~ (x = y) -> ~ (z = y) -> ~ (z = x)       
      -> B (x,y) -> B (y,z) -> B (x,z) \/ ( R (z,x) /\ R (z,y) ).
  
  Definition AB_6:=  forall x y z, 
      B (x,y) -> ~ (B^-1 (x,y)) -> ~ (R (y,x)) 
      -> B (y,z) -> ~ (B^-1 (y,z)) -> ~ (R (z,y))
      -> B (x,z) /\ ~ (B^-1 (x,z)) /\ ~ (R (z,x)).
  
  Lemma L3 (A3: AB_3): (Assumption3 O).
  Proof.
    move: A3. contra => -[f H].
    by exists f;move => n;move: H => /(_ n) [/= H1 _].
  Qed.
  
  Lemma L4 (A5: AB_5) (A6: AB_6) : (Assumption4 O). 
  Proof. 
    split. 
    + move => x [/= H1 _].
      by pose proof (@Asym_irreflexive T B x). 
    + move => x y z [/= [H1 H1'] H2] [/= [H3 H3'] H4].
      move: (A6 x y z H1 H1' H2 H3 H3' H4) => [H5 [H6 H7]].
      by split. 
  Qed.
  
  Lemma L5: (Assumption5 O (M R B)).
  Proof. by move => [x y] [[/= ? _] _];left;left.  Qed.
  
  Lemma L6: (Assumption6 B (M R B) O).
  Proof.
    move => x y [H1 H2].
    split. 
    split. by []. move => /= H3.
    by have H4:  M R B (y, x) by left.
    move => /= H3.
    by have H4:  M R B (y, x) by right. 
  Qed.
  
  Lemma L7 (A4: AB_4) (A5: AB_5): (Assumption7 R B (M R B)).
  Proof. 
    move => x x' y y' H1 H2 [H3|H3] H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
    + left;move: (A5  y' x' y H12 H14 H10 H3 H4) => [? // | [_ H10']]. 
      (have H11': M R B(y,x') by right);by move : H6 => -[_ ?].
    + move: (A4 x y' x' H11 H12 H1 H2 H3) => [H10' | [_ H10']].
      by (have H11': M R B(x, x') by right). 
      by (have H11': M R B(x', x) by left).
  Qed.
  
  Lemma L8 (A4: AB_4) (A5: AB_5): (Assumption8 R B (M R B)).
  Proof. 
    move => x' y y' P0 P0' P0'' H1 [H2| H2] H3 [H4 H5].
    + left;move: (A5 y' x' y P0 P0'' P0' H2 H3) => [? // | [_ H6]].
      by have H11: M R B(y,x') by right.
    + have H6: y' <> y by move => I7;rewrite I7 in P0'.
      have H7: x' <> y by move => I7;rewrite I7 in P0''.
      
      move: (A4 y y' x' H6 P0 H7 H1 H2) => [H6' | [H6' _]].
      by have H11: M R B(y,x') by right.
      by left.
  Qed.
  
  Lemma L9 (A4: AB_4) (A5: AB_5) : (Assumption9 R B O (M R B)).
  Proof. 
    move =>  x y x' y' P0 P1 P2 P3 P4 P5 H1 [H2|H2] [[/= H3 /=H3'] /=H3''] H4 H5 H6.
    + have P4': ~ (y' = x') by move => I1;rewrite I1 in P4.
      move: (A5 y x' y' P3 P4' P5 H2 H3) => [? | [_ ?] //];first by left.
    + have P0': ~ (y = x) by move => I1;rewrite I1 in P0.
      have P1': ~ (x' = x) by move => I1;rewrite I1 in P1.
      move: (A4 x y x' P0' P3 P1' H1 H2) => [? | [? _]].
      by have: (M R B (x', x) \/ (M R B)^-1 (x', x)) by right;right.
      by have: M R B (y,x) by left.
  Qed.
  
  Theorem MLinf
    (A1: AB_1) (A2: AB_2) (A3: AB_3) (A4: AB_4) (A5: AB_5) (A6: AB_6):
    exists X, RelIndep (M R B) X /\  X != set0 /\  forall x, ~ (x\in X) -> (x \in (M R B)#X). 
  (* end snippet MainTh:: no-out *)    
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 (L3 A3) (L4 A5 A6) 
                  L5 L6 (L7 A4 A5) (L8 A4 A5) (L9 A4 A5)).
  Qed.
  
End MeunierLanglois. 

Module BlidiaEngel.
    
  (* O is an orientation:  Asym, irreflexive relation *)
  (* D irreflexive D est inclue dans O `|` O^-1 *)
  (* O is acycliq *)
  Section test.
  
  Parameter (T:choiceType) (O D: relation T).
  
  Definition R := D `&` O^-1. 
  Definition B := D `&` O. 
  
  Context (OD: O `|` O^-1 = (M R B) `|` (M R B)^-1).
  
  Definition AB_1:= (NotEmpty T).
  Definition AB_2:= ~ (iic R).
  Definition AB_3:= ~ (iic B).
  
  Definition AB_4:=  forall x y z t, 
      ~ (y = x) -> ~ (y = z) -> ~ (z = x) -> ~ (z = t)
      -> ~ (z = y) ->  ~ (y = t) -> ~ (x = t)
      -> O (x,y) -> (O (y,z) \/ O (z,y)) -> O (t,z) 
      -> O (x,z) \/ O (z,x) \/ O (y,t) \/ O (t,y) \/ O (x,t) \/ O (t,x).
  
  Definition AB_5:=  forall x y z, 
      ~ (x = y) -> ~ (z = y) -> ~ (z = x)       
      -> O (x,y) -> O (y,z) -> O (z,x)
      -> (O (y,x) /\ O (z,y)).

  (* O and D are both directions of a same graph *)

  Lemma haveA5: ( O  `<=` (M R B) `|` (M R B)^-1).
  Proof. by rewrite -OD;apply: subsetUl. Qed.
  
  Lemma haveA6: forall x y, B (x,y) /\ ~ ((M R B) (y, x)) -> O (x,y).
  Proof. by move => x y [[_ Hb] _]. Qed.
  
  Theorem BE 
    (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
    (A7: Assumption7 R B (M R B)) (A8: Assumption8 R B (M R B))
    (A9: Assumption9 R B O (M R B)):
    exists X, RelIndep (M R B) X /\  X != set0 /\  forall x, ~ (x\in X) -> (x \in (M R B)#X). 
  (* end snippet MainTh:: no-out *)    
  Proof.
    move: (Smax A1 A2 A3 A4 haveA5 A9) => [Sm H1].
    move: (main_lemma A2 haveA6 A7 A8 H1) => H2.
    move: H1 => [/inP [H1 [H4 H5]] H3].
    by exists Sm. 
  Qed.

  End test.
  
End BlidiaEngel.

Module Champetier.
  
  (* O is an orientation:  Asym, irreflexive relation *)
  (* D irreflexive D est inclue dans O `|` O^-1 *)
  
  (* ZZZ O is Transitive *)
  
  Parameter (T:choiceType) (O D: relation T).
  
  Definition C := O.
  Definition R := D `&` O^-1. 
  Definition B := D `&` O. 

  Definition AB_1:= (NotEmpty T).
  Definition AB_2:= ~ (iic R).
  Definition AB_3:= ~ (iic B).
  
  Definition AB_5:=  forall x y z, 
      ~ (x = y) -> ~ (z = y) -> ~ (z = x)       
      -> O (x,y) -> O (y,z) -> O (z,x)
      -> (O (y,x) /\ O (z,y)).
  
End Champetier.

