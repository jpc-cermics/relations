(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & datest)*)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The main result here is the last lemma of the file: Asym2P5'                 *)
(** * Under assumption Hypothesis A1: (exists (v0:T), (v0 \in setT))               *)
(** *    if there is an infinite path for the relation (Asym R.+)                  *)
(** *   then there is an infinite path for the relation R.                         *)
(** *   By infinite path, we mean here that all the visited vertices are distincts.*)
(** *   More formally,                                                             *)
(** *                                                                              *)
(** *   exists f: nat -> T, (forall n, (Asym R.+) ((f n), (f n.+1)))               *)
(** *   => exists h: nat -> T, (forall n, R ((h n), (h n.+1))) /\ injective h.     *)
(** *                                                                              *)
(** *   Note that f is automatically injective.                                    *)
(** *                                                                              *)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import rel seq1 seq2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Hn4.
  (** * some Lemmata around infinite outward R-path *) 
  
  Variables (T: eqType) (R: relation T).
  Implicit Types (st: seq T) (x y s z:T).
  
  Lemma allL_rc_asym st y z: z \in st -> (rcons st y) [L\in] R -> R.+ (z, y).
  Proof.
    by move => H1 /(@Lift_in_F T R) H2;move: (allset_in H1 H2) => /inP ?;rewrite Fset_t0.
  Qed.
  
  Lemma allL_c_asym st x y: y \in st -> (x::st) [L\in] R -> R.+ (x, y).
  Proof.
    by move => H1 /(@Lift_in_A _ R) H3;move: (allset_in H1 H3);rewrite /Aset inP -Fset_t0.  
  Qed.
  
  Lemma allL_asym_l1 st x y: allL R st x y -> ~ R.+ (y, last x st) -> (Asym R.+) (x, y).
  Proof.
    move => H1 H2;split => [|H3];first by apply: (allL_to_clos_t H1).
    case H4: (st == [::]); first by move: H4 H2 => /eqP -> /= ?. 
    move: H4 => /eqP/(@last_in T) => /(_ x) H4.
    have H5: (last x st) \in (rcons st y) by rewrite in_rcons;apply/orP;left. 
    move: (allL_c_asym H5 H1) => H6. 
    by have: R.+ (y, last x st) by apply: TclosT H3 H6.
  Qed.

  Lemma allL_asym_r1 st x y: allL R st x y -> ~ R.+ (head y st,x) -> (Asym R.+) (x, y).
  Proof.
    move => H1 H2;split => [|H3];first by apply: (allL_to_clos_t H1). 
    case H4: (st == [::]);first by move: H4 H2 => /eqP -> /= ?.
    move: H4 => /eqP/(@head0 T) => /(_ y) H4.
    have H5: (head y st) \in (x::st) by rewrite in_cons;apply/orP;right.
    move: (allL_rc_asym H5 H1) => H6. 
    by have: R.+ (head y st,x) by apply: TclosT H6 H3.
  Qed.
  
  Lemma allL_asym_l st x s y:  s \in st -> allL R st x y -> ~ R.+ (y, last x st) 
                               -> (Asym R.+) (s, y).
  Proof.
    move => H1 H4 H5;move: (allL_take_drop H1 H4) => [_ H1'].
    split; first by move: (allL_to_clos_t H1') => H6.
    case H3: (s == (last x st)); first by move: H3 => /eqP ->.
    have H6: ~ ( s = (last x st)) by move => H7; rewrite -H7 eq_refl in H3.
    pose proof (allL_belast H1 H6 H4) as H7.
    by move => H8;have H9: R.+ (y, last x st) by apply: (TclosT H8 H7).
  Qed.
  
  Lemma allL_asym_r st x s y: s \in st -> allL R st x y -> ~ R.+ (head y st, x) 
                              -> (Asym R.+) (x, s).
  Proof.
    move => H1 H4 H5;move: (allL_take_drop H1 H4) => [H1' _].
    split;first by move: (allL_to_clos_t H1').
    case H3: (s == (head y st)); first by move: H3 => /eqP ->.
    have H6: ~ ( s = (head y st))  by move => H7; rewrite -H7 eq_refl in H3.
    pose proof (allL_behead H1 H6 H4) as H7.
    by move => H8;have H9: R.+ (head y st,x) by apply: (TclosT H7 H8).
  Qed.
  
  Lemma allL_asym_lr st st' x s y s' z: 
    s \in st -> allL R st x y -> ~ R.+ (y, last x st) 
    -> s' \in st'  -> allL R st' y z
    -> (Asym R.+) (s, s').
  Proof.
    move => H1 H3 H4 H5 H6;move: (allL_asym_l H1 H3 H4) => H7.
    have H8: s' \in (rcons st' z) by rewrite in_rcons H5 orTb. 
    pose proof (allL_c_asym H8 H6) as H9. 
    have H10: (Asym(R.+) `;` R.+) (s,s') by (exists y).
    by move: H10 => /AsymIncr H10.
  Qed.
  
  Lemma allL_asym_rl st st' x s y s' z:
      s \in st -> allL R st x y 
      -> s' \in st' -> allL R st' y z -> ~ R.+ (head z st', y) 
      -> (Asym R.+) (s, s').
  Proof.
    move => H1 H2 H3 H5 H6;move: (allL_asym_r H3 H5 H6) => H7.
    have H8: s \in (x::st) by rewrite in_cons H1 orbT. 
    pose proof (allL_rc_asym H8 H2) as H9. 
    have H10: (R.+  `;` Asym(R.+)) (s,s') by (exists y).
    by move: H10 => /AsymIncl H10.
  Qed.
  
  Lemma allL_asym_xx st x s z: 
    s \in st -> ~ (z = s) -> allL R st x z -> ~ R.+ (z, s)
    -> (Asym R.+) (x,z).
  Proof.
    elim: st x s z => [// | y st Hr x s z].
    rewrite in_cons => /orP [/eqP -> | H1] H2.
    + rewrite allL_c => /andP [/inP H3 H4] H5. 
      split.
      ++ pose proof (allL_to_clos_t H4) as H6.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         by pose proof TclosT H7 H6.
      ++ move => H6.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         by pose proof TclosT H6 H7.
    + rewrite allL_c => /andP [/inP H3 H4] H5. 
      split.
      ++ pose proof (allL_to_clos_t H4) as H6.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         by pose proof TclosT H7 H6.      
      ++ pose proof (Hr y s z) H1 H2 H4 H5 as [H8 H9].
         move => H10.
         have H7: R.+ (x, y) by apply: iter1_inc_clos_trans.
         have H11: R.+ (z,y) by apply: TclosT H10 H7.
         exact.
  Qed.
  
  Lemma uniq_asym2: forall x stl y str z,
      allLu R stl x y -> ~ R.+ (y, last x stl) -> allLu R str y z 
      -> (forall s, s \in str -> s \in stl -> False).
  Proof.
    move => x stl y str z [H1 H2] H3 [H4 H5].
    move: H2 => /uniq_crc [K1 [K2 [K3 K4]]].
    move: H5 => /uniq_crc [J1 [J2 [J3 J4]]].
    move => s H9 H10.
    pose proof allL_asym_lr H10 H1 H3 H9 H4 as H12. 
    by pose proof Asym_irreflexive H12.
  Qed.
  
  Lemma allL2_fact: forall yl (stlr: seq T) yr str z,
      allLu R stlr yl yr -> allLu R str yr z 
      -> ~ R.+ (z, yr) -> ~ R.+ (head z str, yr)
      -> ~ ( z \in stlr)  /\ ~ (yl = z).
  Proof.
    move => yl stlr yr str z H1 H2 H3 H4.
    move: H1 => [H1 /uniq_crc  [J1 [J2 _]]].
    move: H2 => [H2 /uniq_crc  [K1 [K2 _]]].
    have H5: forall s, s \in stlr -> ~(s = yr)
        by move => s H6 H7; rewrite H7 in H6.
    split. 
    + move => /[dup] H6 /H5 H7.
      have H8: R.+ (z, yr) 
        by pose proof (allset_in H6 (Lift_in_F (allL_Lift_in_rc H1)));
        rewrite Fset_t0 -inP.
      exact.
    + (* Asym composition is Asym *) 
      by move: H1 => + H6;rewrite H6 => /(@allL_to_clos_t T) H1.
  Qed.
  
  Lemma RedBackL: forall (st:seq T) (x y:T),
      allLu R st x y -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          subseq st' st (* subseq (rcons st' y') (rcons st y) *)
          /\ uniq (x::(rcons st' y'))       
          /\ st' [\in] R.+#_(x) 
          /\ (x::(rcons st' y')) [L\in] R 
          /\ ~ (R.+ (y',x))
          /\ (y = y' \/ R.+ (y',y))
          /\ ~ (R.+ (y',(last x st'))).
  Proof.
    have H0: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim.
    elim/last_ind => [x y [H1 H2] | st z Hr x y [H1 H1'] H2];
                    first by (exists [::], y);have H3: y = y \/ R.+ (y, y) by left.
    case H3: ((z,x) \in R.+).
    - exists (rcons st z); exists y.
      have H4: (rcons st z) [\in] R.+#_(x).
      move: H1; rewrite Lift_crc Lift_rcrc allset_cons allset_rcons => [[_ [H1 _]]].
      rewrite allset_rcons.
      split;first by apply Lift_in_FF with z;[|rewrite inP -Fset_t0 -inP H3].
      by rewrite -Fset_t0 -inP H3.
      (* end of H4 *)
      have H5: y = y \/ R.+ (y, y) by left.
      move: H3 => /inP H3.
      have H6: ~ R.+ (y, last x (rcons st z))
        by rewrite last_rcons; move => H7;have H8: R.+ (y,x) by apply: TclosT H7 H3.
      exact. 
    - rewrite Lift_crc Lift_rcrc allset_cons allset_rcons in H1.
      move: (H1); rewrite H0 => [[H10 [H10' H10'']]].
      have H5: (x :: rcons st z) [L\in] R by rewrite Lift_crc allset_cons.
      have H13: subseq (rcons st z) (rcons (rcons st z) y) by apply: subseq_rcons. 
      have H14: uniq (x :: rcons st z) by apply: (uniq_subseq H1' H13).
      have H5': allLu R st x z by split.
      apply Hr in H5'; last by move => /inP H6; rewrite H6 in H3.
      move: H5' => [st' [y' [H5'' [H5' [H6 [H7 [H8 [H9 H9']]]]]]]].
      (* have H11: subseq (rcons st' y') (rcons (rcons st z) y)
        by apply subseq_trans with (rcons st z);[ | apply subseq_rcons]. *)
      have H11: subseq st' (rcons st z) by apply/subseq_trans/subseq_rcons.
      (exists st', y'); move: H9 => [H9 | H9].
      by have H12: (y = y' \/ R.+ (y', y)) by right;rewrite -H9;apply: TclosSu.
      by have H12: (y = y' \/ R.+ (y', y)) by right;apply TclosT with z;[ |apply: TclosSu].
  Qed.

  (* utility lemma *)
  Lemma RedBackR: forall (st:seq T) (y z:T),
      (y::(rcons st z)) [L\in] R
      -> uniq (y::(rcons st z)) 
      -> ~ ( R.+ (z,y))
      -> exists st', exists y',
          subseq st' st (* (y'::st') (y::st)  *)
          /\ uniq (y'::(rcons st' z))       
          /\ st' [\in] (z)_:#R.+ 
          /\ (y'::(rcons st' z)) [L\in] R 
          /\ ~ (R.+ (z,y'))
          /\ (y = y' \/ R.+ (y,y'))
          /\ ~ (R.+ ((head z st'),y')).
  Proof.
    elim => [y z H1 H2| y1 st Hr y z H1 H1' H2];
             first by (exists [::], y);have H3: y = y \/ R.+ (y, y) by left.
    case H3: ((z,y1) \in R.+).
    - exists (y1::st); exists y.
      have H4: (y1::st) [\in] (z)_:#R.+.
      move: H1;rewrite Lift_crc Lift_rcc allset_cons allset_rcons => [[_ [H1 _]]].
      rewrite allset_cons.
      split;first by rewrite  /Aset -Fset_t0 /inverse /= -inP H3.
      by apply Lift_in_AA with y1;[|rewrite inP /Aset -Fset_t0 /inverse /= -inP H3].
      (* end of H4 *)
      have H5: y = y \/ R.+ (y, y) by left.
      move: H3 => /inP H3.
      have H6: ~ R.+ (head z (y1 :: st), y)
        by move => /= H7;have H8: R.+ (z,y) by apply: TclosT H3 H7.
      exact.
    - rewrite Lift_crc Lift_rcc allset_cons allset_rcons in H1.
      move: (H1) => [H10 [H10' H10'']].
      have H5: (y1 :: rcons st z) [L\in] R 
        by rewrite -rcons_cons Lift_rcc allset_rcons.
      apply Hr in H5; last by move => /inP H6; rewrite H6 in H3.
      move: H5 => [st' [z' [H5 [H5' [H6 [H7 [H8 [H9 H9']]]]]]]].
      (*  have H11: subseq (z'::st') (y::(y1::st)).
      by apply subseq_trans with (y1::st);[| apply subseq_cons]. *)
      have H11: subseq st' (y1 :: st) by apply/subseq_trans/subseq_cons.
      (exists st', z'); move: H9 => [H9 | H9].
      by have H12: (y = z' \/ R.+ (y, z')) by right; rewrite -H9; apply: TclosSu.
      by have H12: (y = z' \/ R.+ (y, z')) by right;apply TclosT with y1;[apply: TclosSu|].
      by move: H1'; rewrite cons_uniq rcons_cons => /andP [_ H1'].
  Qed.
  
  Lemma RedBackLR: forall (x y z:T) (stl: seq T),
      allLu R stl x y -> ~ R.+ (y,x) -> (Asym R.+) (y,z) 
      -> exists stl', exists yl, exists str', exists yr, exists stlr,
          ((yl = yr) \/ (allLu R stlr yl yr))
          /\ subseq stl' stl (* (rcons stl' yl) (rcons stl y)  *)
          /\ allLu R stl' x yl 
          /\ ~ (R.+ (yl,x))
          /\ ~ (R.+ (yl,(last x stl')))
          /\ allLu R str' yr z
          /\ ~ (R.+ (z,yr))
          /\ ~ (R.+ ((head z str'),yr)).
  Proof.
    move => x y z stl [H1 H2] H3 /TCP_uniq1 [[str [H4 H5]] H6].
    pose proof (RedBackL (conj H1 H2) H3) as [stl' [yl [H7' H7]]].
    pose proof (RedBackR H4 H5 H6) as [str' [yr [_ H8]]].
    exists stl';exists yl;exists str';exists yr.
    move: H7 => [L1 [L2 [L3 [L4 [L5 L6]]]]].
    move: H8 => [M1 [M2 [M3 [M4 [M5 M6]]]]].
    
    have: (yl = yr) \/  R.+ (yl, yr).
    by move: L5 M5 => [<- | H16] [<- | H17];
                  [left | right | right | right;apply TclosT with y].
    
    move => [? | ?]; first by (exists [::]);split;[left |]. 
    case H17: (yl == yr);move: H17 => /eqP H17;first by (exists [::]);split;[ left|].
    have: R.+ (yl, yr) /\  yl <> yr by exact.
    rewrite TCP_uniq'' => -[strl [? ?]];exists strl.
    by split;[right|].
  Qed.
  
  Lemma uniq_util: forall yl stlr yr str1 z,
      uniq (yl :: rcons stlr yr) -> uniq (yr :: rcons str1 z)
      -> ( forall s : T, s <> z -> s \in stlr -> s \in str1 -> False)
      -> ~ (yl \in str1) -> ~ (z \in stlr) -> ~ (yl = z)
      -> uniq ((yl :: stlr) ++ yr :: rcons str1 z).
  Proof.
    move => yl stlr yr str z H1 H2 H3 H4' H5' H6'.
    move: (H2);rewrite cons_uniq rcons_uniq => /andP [_ /andP [/negP H4 _]].
    
    have H5: forall s, s \in str -> ~ (s = z)
        by move => s H6 H7;rewrite -H7 in H4.

    have H6: ( forall s : T, s \in stlr -> s \in str -> False)
      by move: H3 H5 => + + s H6 H7 
         => /(_ s) H3 /(_ s) H5; pose proof (H3 (H5 H7) H6 H7).

    have H7: uniq (yl :: stlr)
      by move: H1;rewrite -rcons_cons rcons_uniq => /andP [_ H1].

    move: H1 => /uniq_crc [J1 [J2 [J3 J4]]].
    move: (H2) => /uniq_crc [K1 [K2 [K3 K4]]].
    

    have H8: forall s, s = yr -> s = yl -> False by move => s H1 H2';rewrite -H1 -H2' in J4. 
    have H9: forall s, s \in rcons str z -> s = yl -> False
          by move => s H1 H2';move: H1;
                    rewrite in_rcons => /orP [H1 |/eqP H1];[rewrite H2' in H1|rewrite -H2' -H1 in H6'].
    have H10: forall s, s = yr -> s \in stlr -> False by move => s H1 H2';rewrite H1 in H2'.
    have H11: forall s, s \in rcons str z -> s \in stlr -> False
            by move => s H1 H2';move: H1;
                      rewrite in_rcons => /orP [H1 |/eqP H1];
                                         [pose proof (H6 s H2' H1)|rewrite H1 in H2'].
    
    have H12: forall s, s \in yl :: stlr -> s \in yr :: rcons str z -> False
            by move => s;rewrite in_cons => /orP [/eqP H13 | H13] /orP [/eqP H14 | H14];
                                          [apply: (H8 s)| apply: (H9 s)|apply: (H10 s)|apply: (H11 s)].
    
    by pose proof (uniq_cat H7 H2 H12).
  Qed.

  Lemma RedBackLR2:  forall (x y z:T) (stl: seq T),
      allLu R stl x y -> ~ R.+ (y,x) -> (Asym R.+) (y,z) 
      -> exists stl', exists yl, exists (stlr: seq T), exists yr, exists str',
          ((yl = yr /\ (forall s, s \in stl' -> s \in str' -> False)
            /\ subseq stl' stl (* subseq (rcons stl' yl) (rcons stl y)  *)
            /\ allLu R stl' x yl /\ ~ (R.+ (yl,(last x stl')))
            /\ allLu R str' yr z /\ ~ (R.+ ((head z str'),yr))
           )
           \/
             ( 
               subseq stl' stl (* subseq (rcons stl' yl) (rcons stl y)  *)
               /\allLu R stl' x yl /\ ~ (R.+ (yl,(last x stl')))
               /\ allLu R ((rcons stlr yr) ++ str') yl z
               /\ (exists s, s \in (rcons stlr yr ++ str') /\ ~ R.+ (z,s))
             )
           \/ 
             (
               subseq stl' stl (* subseq (rcons stl' yl) (rcons stl y)  *)
               /\ allLu R stl' x yl /\ ~ (R.+ (yl,(last x stl')))
               /\ allLu R (drop (index yl str').+1 str') yl z
               /\  ~ R.+ (z, yl)
               /\ uniq (stl' ++ drop (index yl str').+1 str')
             )
           ).
  Proof.
    move => x y z stl H1 H1' H2.
    move: (RedBackLR H1 H1' H2) => [stl1 [yl [str1 [yr [stlr H7]]]]].
    
    move: H7=> [[H15 | [H15 H16]] [H7' [H7 [H8 [H10 [H11 [H13 H14]]]]]]].
    + exists stl1; exists yl; exists stlr; exists yr; exists str1. 
      move: H7' H7 H8 H10; rewrite H15 => H7' H7 H8 H10.
      have H16: (forall s : T, s \in stl1 -> s \in str1 -> False) 
        by move => s H17 H18;apply/(uniq_asym2 H7 H10 H11);[apply/H18|apply/H17].
      by left. 
    + exists stl1; exists yl; exists stlr; exists yr; exists str1. 
      case H17: (yl \in str1); last first.
      (* first case *)
       ++ move: H17 => /negP K4.
          have K1: (allLu R stlr yl yr) by split.
          pose proof allL2_fact K1 H11 H13 H14 as [K2 K3].
          
          have H21: forall s : T, s <> z -> s \in stlr -> s \in str1 -> False.
          move: H11 => [H11 H11'] s H18 H19 H20.
          (** * ZZZZ H18 non used *)
          by pose proof (allL_asym_rl H19 H15 H20 H11 H14) as [H notH]. 
      
          have H17: allL R ((rcons stlr yr) ++ str1) yl z.
          by move: H11 => [H11' H11'']; by rewrite allL_cat; apply/andP. 
      
          have H18: uniq (rcons stlr yr)
            by move: H16; rewrite cons_uniq => /andP [_ ?]. 

          have H19: uniq str1
            by move: H11 => [_ ];rewrite cons_uniq rcons_uniq => /andP [_ /andP [_ ?]].
      
          have P1: uniq ((yl :: stlr) ++ yr :: rcons str1 z)
            by move: H11 => [H11 H11'];apply: (uniq_util H16 H11' H21).
          
          have H20: uniq (yl::(rcons ((rcons stlr yr) ++ str1) z))
            by move: P1; rewrite cat_cons -rcons_cons -rcons_cat -cat_rcons. 

          have H22: allLu R ((rcons stlr yr) ++ str1) yl z
            by split.

          have H23: exists s, s \in (rcons stlr yr ++ str1) /\ ~ R.+ (z,s).
          exists yr; split; last by [].
          by rewrite mem_cat;apply/orP;left;rewrite in_rcons;apply/orP;right;apply/eqP.
          
          by right;left.
          
       ++ move: H11 => [/[dup] H11 /(@allL_to_clos_t T) H11' /uniq_crc [J1 [J2 [J3 J4]]]].
          move: (H15) => /(@allL_to_clos_t T) H15'.
          have H12: ~ (yl =z) by move => H12;rewrite H12 in H15'.
      
          have H20: ~ (R.+ (z, yl)) 
            by move => H21; have H22: R.+ (z,yr) by apply: (TclosT H21 H15').
          
          pose proof allL_take_drop H17 H11 as [_ H21]. 
          
          have H22: subseq (drop (index yl str1).+1 str1) str1 by apply: drop_subseq.
          have H23: ~ yr \in drop (index yl str1).+1 str1 by apply: notin_subseq H22 J1.
          have H24: uniq (drop (index yl str1).+1 str1) by apply: subseq_uniq H22 J3.
          have H25: uniq (yl::(drop (index yl str1).+1 str1))
            by rewrite cons_uniq H24 andbT;apply: drop_notin. 
          have H26: uniq (yl::(rcons (drop (index yl str1).+1 str1) z)).
          rewrite -rcons_cons rcons_uniq H25 andbT. 
          rewrite in_cons. apply/orP.  move => [/eqP H27 | H27];first by rewrite H27 in H12.
          by pose proof in_subseq H22 H27. 
          
          have H27:  allLu R (drop (index yl str1).+1 str1) yl z by split.
            
          right;right.
          split. by []. split. by []. split. by []. split. by [].
          
          move: (H7) => [H7'' /uniq_crc [K1 [K2 [K3 K4]]]].
      
          have H28: (forall s : T, s \in stl1 -> s \in drop (index yl str1).+1 str1 -> False).
          move => s H29 H28. 
          have H30: s \in str1 by pose proof (in_subseq H22 H28).
           have H32: (s \in (rcons stlr yr) ++ str1)
            by rewrite mem_cat; apply/orP; right.
          
          have H33: allL R ((rcons stlr yr) ++ str1) yl z
            by rewrite allL_cat; apply/andP. 
          by pose proof (allL_asym_lr H29 H7'' H10 H32 H33) as [H notH].
          (* end of H28 *)
          
          by pose proof (uniq_cat K3 H24 H28).
  Qed.
  
  (** * The main Lemma of this section *)
  Lemma Asym2P x y z stl: 
    allLu R stl x y -> ~ R.+ (y,x) -> (Asym R.+) (y,z) 
    -> exists stl', exists y', exists str',
        subseq stl' stl 
        /\ allLu R stl' x y' /\ ~ R.+ (y',x)
        /\ allLu R str' y' z /\ ~ R.+ (z, y')
        /\ uniq (stl' ++ str').
  Proof.
    move => H1 H1' H2.
    move: (RedBackLR2 H1 H1' H2) => [stl1 [yl [str1 [yr [stlr H7]]]]].
    move: H7 => [[H7 [H8 [H9' [H9 [H10 [H11 H12]]]]]] | ]. 
    + exists stl1;exists yl;exists stlr.
      have H13:  uniq (stl1 ++ stlr)
        by move: H9 H11 => [_ /uniq_crc [K1 [K2 [K3 K4]]]] [_ /uniq_crc [J1 [J2 [J3 J4]]]];
                          pose proof (uniq_cat K3 J3 H8).
      
      have: (~ R.+ (head z stlr, yl) \/ (exists s : T, s \in stlr /\ ~ R.+ (z, s)))
        by left;rewrite H7.
      
      have H14: (Asym R.+) (x, yl)
        by move: H9 => [H9 _];move: (allL_asym_l1 H9 H10).
      
      have H16: ~ R.+ (z, yl) 
        by move: H11 => [H11 H11'];
                       pose proof allL_asym_r1 H11 H12 as [H17 H18];rewrite H7.
      
      have H17: ~ R.+ (yl,x)
        by move: H9 => [H9 _];pose proof allL_asym_l1 H9 H10 as [H18 H19].
      
      by rewrite -H7 in H11.
    + 
      move => [[H7'' [H7 [H9 ] [H11 H11']]] |].
      ++ exists stl1;exists yl;exists(rcons str1 yr ++ stlr).
         move: (H7) (H11)  => [H7' H8] [H9' H10].
         have H12: forall s, s \in stl1 -> s \in (rcons str1 yr ++ stlr) -> False.
         move => s H13 H14. 
         by move: (allL_asym_lr H13 H7' H9 H14 H9') => [H notH].
         
         move: H8 => /uniq_crc [_ [_ [H8 _]]].
         move: H10 => /uniq_crc [_ [_ [H10 _]]].
         
         have H10': uniq (stl1 ++ rcons str1 yr ++ stlr) by pose proof (uniq_cat H8 H10 H12).
         
         have H16: ~ R.+ (z, yl).
         move: H11' => [s [K1 K2]].
         move: H11 => [H11 H11''].
         move: H11'' => /uniq_crc [_ [J2 _]].
         have H14: ~ (z = s) by move => H15; rewrite H15 in J2.
         pose proof allL_asym_xx K1 H14 H11 K2 as [_ H16]. 
         exact.
      
         have H15: (~ R.+ (head z (rcons str1 yr ++ stlr), yl) \/
                      (exists s : T, s \in rcons str1 yr ++ stlr /\ ~ R.+ (z, s)))
           by right.
         
         have H17: ~ R.+ (yl,x)
           by pose proof allL_asym_l1 H7' H9 as [H18 H19].
         
         exact.
      ++ move => [H7'' [H7 [H8 [H9 [H10 H11]]]]].
         exists stl1;exists yl;exists(drop (index yl stlr).+1 stlr).
         move: H7 => [H7 H7'].
         have H12: ~ R.+ (yl, x) by pose proof (allL_asym_l1 H7 H8) as [_ H'].
         exact.
  Qed.

End Hn4.

Section Hn0.
  (** * some Lemmata around Axiom of choice *) 
  
  Variables (T T':choiceType) (R: set T) (R': set (T*T')).
  
  Hypothesis Au0: (exists (v0:T'), (v0 \in [set: T'])).
  Hypothesis Au1: forall (t: T), R t -> exists z, R' (t,z).
  
  Lemma Au1_P1: forall (t: T),
    exists z, z \in [set u| (R t /\ R' (t,u)) \/ ~ R t].
  Proof. 
    move => t. 
    case H1: (t \in R).
    + move: H1 => /inP H1;move: t H1 => t /[dup] H1 /Au1 [z H1'].
      by exists z;rewrite inP;left;split.
    + move: Au0 => [v0 Au0'].
      by exists v0; rewrite inP; right;move => /inP H2;rewrite H1 in H2.
  Qed.
  
  Lemma Au1_P3 (t: T): R t -> R' (t,xchoose (Au1_P1 t)).
  Proof.
    have H0: xchoose (Au1_P1 t) \in [set u| (R t /\ R' (t,u)) \/ ~ R t]
      by apply: xchooseP.
    by move: H0 => /inP [[_ ?] //| ? //].
  Qed.
  
  Lemma Au1_G: exists (g: T -> T'), forall t, R t -> R' (t,g(t)).
  Proof. by exists (fun t => xchoose (Au1_P1 t)); apply: Au1_P3. Qed.
  
End Hn0.

Section Hn2. 
  (* apply Hn0 to allLu *)
  Variables (T:choiceType) (R: relation T). 
  
  Lemma choose_Rseq: exists (g: T*T -> seq T), forall xy, 
      (Asym R.+) xy -> allLu R (g xy) xy.1 xy.2.
  Proof.
    have Au0: (exists (v0: seq T), (v0 \in [set: seq T]))
      by (exists [::]);rewrite inP.
    pose R' :=[set xyz: (T*T)*(seq T)| allLu R xyz.2 xyz.1.1 xyz.1.2].
    have Au1: forall (xy:T*T), (Asym R.+) xy -> exists z, R' (xy,z)
          by move => [x y] /TCP_uniq1 [[st H3] _];exists st.
    by move: (Au1_G Au0 Au1) => [g H1]; exists g. 
  Qed.
  
End Hn2.

Section Infinite_path. 
  
  Variables (T:choiceType) (R: relation T). 

  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  Definition T2 : Type := (seq T)*T*(seq T)*nat.

  Fixpoint iterh (h: T2 -> T2) (p0:T2) n : T2 := 
    match n with 
    | 0 => p0
    | S n => h (iterh h p0 n)
    end.
  
  Definition Re1 (f: nat -> T) :=
    [set p: T2 | exists (stl: seq T) (x:T) (str:seq T) n,
        p = (stl,x,str,n) /\ uniq (stl ++ str) 
        /\ allLu R str x (f n.+1) /\ ~ R.+ (f n.+1,x)].
  
  Definition Re2 (f: nat -> T) := 
    [set p: T2*T2 | exists stl x str n stl' y' str' n',
      p.1 = (stl, x, str,n) /\ p.2 = (stl', y', str',n')
      /\ n' = n.+1
      /\ allLu R stl' x y' /\ ~ R.+ (y',x) 
      /\ uniq (stl' ++ str')
      /\ allLu R str' y' (f n.+2) /\ ~ R.+ (f n.+2,y')
      /\ uniq (stl ++ stl')].
  
  Lemma Re2_to_Re1: forall (f: nat -> T) (p q: T2), Re2 f (p,q) -> Re1 f q.
  Proof.
    move => f p q -[stl [x [str [n [stl' [x' [str' [n' [/= _ [-> [H1 H2]]]]]]]]]]].
    move: H2 => [H2 [H3 [H4 [H5 [H6 H7]]]]].
    exists stl'; exists x';exists str';exists n'.
    rewrite H1.
    exact. 
  Qed.
  
  Lemma ARR':exists (v: T2), (v \in [set: T2]).
  Proof. by move: A1 => [v0 _];exists ([::],v0,[::],0);rewrite inP. Qed.
  
  Lemma Asym2P1: 
    (iic (Asym R.+)) -> 
    exists f : nat -> T, exists g: T*T -> seq T, 
      (allLu R (g (f 0,f 1)) (f 0) (f 1) /\ ~ R.+ (f 1, f 0))
      /\ forall (p : T2), Re1 f p -> exists (t: T2), Re2 f (p,t).
  Proof.
    move: (@choose_Rseq T R) => [g H0] [f Hn];exists f;exists g.
    split; first by split;[apply: H0 | move: Hn => /(_ 0) [_ Hn]].
    move => [[stl0 x0] str0] [stl [x [str [n [-> [H1 [H2 H3]]]]]]].
    move: (Hn) => /(_ n.+1) Hn'.
    pose proof (Asym2P H2 H3 Hn') as [stl' [y' [str' [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
    have H10:  uniq (stl ++ stl') by apply: (uniq_subseq' H1 H4).
    by exists (stl',y', str',n.+1);exists stl; exists x; exists str;exists n; exists stl'; exists y'; exists str'; exists n.+1.
  Qed.
  
  Lemma Asym2P3: 
    (iic (Asym R.+)) -> exists f : nat -> T, 
      (exists (p0: T2), Re1 f p0) 
      /\ exists h: T2 -> T2, forall (p : T2), Re1 f p -> Re2 f (p,h p).
  Proof.
    move => /Asym2P1 [f [g [[[H2' H3'] H4'] H1]]]; exists f. 
    have H5': uniq (g (f 0,f 1))
      by move: H3';rewrite cons_uniq rcons_uniq => /andP [_ /andP [_ ] ].
    split;first by (exists ([::],f 0,g (f 0,f 1),0);exists [::]; exists (f 0); exists (g (f 0,f 1)); exists 0).
    pose proof (@Au1_G T2 T2 (Re1 f) (Re2 f) ARR' H1) as [h H2].
    by exists h.
  Qed.
  
  Lemma Asym2P4: 
    (iic (Asym R.+)) -> exists f : nat -> T, exists h: T2 -> T2, exists (p0: T2),
        Re1 f p0 /\ (forall n, Re2 f (iterh h p0 n, iterh h p0 n.+1)).
  Proof.
    move => /Asym2P3 [f [[p0 H0] [h H1]]]. 
    exists f;exists h;exists p0;split;first by []. 
    elim => [ | n /Re2_to_Re1 Hn]; first by rewrite /iterh; apply: H1.
    by apply: H1.
  Qed.
  
  Lemma Asym2P5: 
    (iic (Asym R.+)) -> exists k: nat -> T, exists l: nat -> seq T,
        forall n, allLu R (l n) (k n) (k n.+1) /\ ~ R.+ (k n.+1, k n)
             /\ uniq ((l n) ++ (l n.+1)).
  Proof.
    move => /Asym2P4 [f [h [p0 [H0 H1]]]].
    exists (fun n => (iterh h p0 n).1.1.2);exists (fun n => (iterh h p0 n.+1).1.1.1).
    move => n;move: H1 => /[dup] /(_ n.+1) H1 /(_ n) H2. 
    move: H2 => [stl [x [str [n1 [stl' [x' [str' [n1' /= [J1 [J2 [_ [H4 [H5 _]]]]]]]]]]]]].
    move: H1 => [stl1 [x1 [str1 [n11 [stl1' [x1' [str1' [n11' /= [K1 [K2 [_ HH']]]]]]]]]]].
    move: HH' => [_ [_ [_ [_ [_ H9']]]]].
    by split;[rewrite J2 J1|split;[rewrite J2 J1|rewrite K2 K1]].
  Qed.

End Infinite_path. 

(** What is done here: 
    given a path (f 0) -> (g 0) -> (f 1) -> g(1) -> f(2) in a graph 
    defined by a relation R, where the function f and g are given.
    for each i, (f i) is a node in T and (g i) is a sequence in T (giving a path).
    We want to build a function val such that the path is given by 
    (val 0) -> (val 1) -> (val 2) -> .....
    Moreover, using properties of f and g with respect to the relation R, 
    we want to prove that val is injective. 
*)

Section val_construction.

  (** utilities *)
  Context (T:eqType) (f: nat -> T) (g: nat -> seq T).
  
  Section prelude.
    (** utilities *)
    Context (p: nat -> nat).
    
    Definition csum (n : nat) : nat:=
      let fix loop m := if m is i.+1 then (loop i) + (p i).+1 else 0 in loop n.
    
    Lemma csumP n: (csum n.+1) = (csum n) + (p n).+1.
    Proof. by []. Qed.

    Lemma csum_strict_inc n: csum n < csum n.+1.
    Proof. rewrite /= ;by lia. Qed.

    Lemma csum_gt_id n : csum n >= n.
    Proof. elim: n => [// |n Hr];apply: (leq_ltn_trans Hr (csum_strict_inc n)). Qed.
    
    Lemma csum_inc  n m : n < m -> csum n < csum  m.
    Proof. 
      elim: m n => [n // | m' Hn n H1]. 
      case H2: (n == m');first by move: H2 => /eqP ->;apply: csum_strict_inc.
      move: H1;rewrite leq_eqVlt => /orP [H3 | H3];first by lia.
      have /Hn H4: n < m' by lia.
      have H5:  csum n <= csum m' by lia. 
      by rewrite csumP;apply: (leq_ltn_trans H5 _);lia.
    Qed.
    
    Lemma csum_inc1 n m: n <= m -> csum n <= csum m.
    Proof. 
      by move => ?;case H2: (n == m);[move: H2 => /eqP ->|apply/ltnW/csum_inc;lia].
    Qed.
    
    Lemma csum_up  n: exists k, n < csum k.
    Proof.
      by  (exists n.+1);apply: (leq_ltn_trans (csum_gt_id n) (csum_strict_inc n)).
    Qed.
    
    Definition csumI n:= (ex_minn (csum_up n)).-1.

    Lemma exists_sandwich n:
      (csum (csumI n)) <= n < csum (csumI n).+1.
    Proof.
      pose j:= (ex_minn (csum_up n)).-1; rewrite /csumI -/j. 
      case H1: (n <= p 0).
      + have H2: (ex_minn (csum_up n)).-1 = 0
          by case: ex_minnP => m _ /(_ 1);rewrite /csum add0n ltnS H1;lia.
        by rewrite /j H2 /= add0n ltnS H1.
      + move: H1;rewrite leqNgt => /negP/negP H1.
        pose  k0 := (ex_minn (csum_up n)).
        have H2: ~(0 = k0) 
          by rewrite /k0;case: ex_minnP  => k H3 ?;move => H5;rewrite -H5 in H3.
        have H3: 0 < k0 by lia.
        have H4: k0.-1.+1 = k0 by lia.
        move: H3 H4;rewrite /j /k0;case: ex_minnP => // k H3 H5 H6 ->. 
        rewrite H3 andbT. 
        have: n < csum  k.-1 -> False by move => /H5 H4; lia.
        by lia.
    Qed.
    
    Lemma uniq_sandwich n j k:
      ((csum j) <= n < csum j.+1) -> ((csum k) <= n < csum k.+1) ->  j = k.
    Proof.
      move => H1 H2.
      case H3: ( j == k);first by move: H3 => /eqP ->.
      case H4: (j < k).
      + have H6: csum j.+1 <= csum k by apply: csum_inc1.
        have H7: n < n by lia.  
        by have H8: false by rewrite -(ltnn n).
      + have H5: k < j by lia.
        have H6: csum k.+1 <= csum j by apply: csum_inc1.
        have H7: n < n by lia.  
        by have H8: false by rewrite -(ltnn n).
    Qed.
    
    Lemma incr_sandwich n j: (csumI n) < j -> n <= (csum j).
    Proof.
      move: (exists_sandwich n) => /andP [H1 H2] H3.
      have H4: csum (csumI n).+1 <= csum j by apply: csum_inc1.
      by lia.
    Qed.
    
    Lemma incr_sandwich1 n j: (csum j) < n -> j <= (csumI n).
    Proof. contra. apply: incr_sandwich.
    Qed.
    
    Lemma csumI0 n j: ((csum j) <= n < csum j.+1) -> (csumI n) = j.
    Proof.
      move => H1;pose proof (exists_sandwich n) as H2.
      by apply: (@uniq_sandwich n (csumI n) j).
    Qed.
    
    Lemma csumI0' n j: ((csum j) < n < csum j.+1) -> (n - (csum j)).-1 < (p j).
    Proof. by rewrite csumP => H1;lia. Qed.

    Lemma csumI1 n j: ((csum j) <= n < csum j.+1)
                      -> if (n.+1 < csum j.+1) then (csumI n.+1) = j
                        else (csumI n.+1) = j.+1. 
    Proof.
      move => /andP [H1 H2].
      case H3: (n.+1 < csum j.+1).
      + have H4: (csum j) <= n.+1 < (csum j.+1) by lia.
        pose proof (exists_sandwich n.+1) as H5.
        by apply: (@uniq_sandwich n.+1 (csumI n.+1) j).
      + have H6': n.+1 = csum j.+1 by lia.
        by apply: csumI0; rewrite H6' [csum j.+2]csumP; lia.
    Qed.

    Lemma csumI1' n j: n= (csum j) -> (n.+1 < csum j.+1) = false -> (p j)=0.
    Proof.
      move => H1 H2.
      have H3: n < csum j.+1 by rewrite H1;apply: csum_inc.
      have: n.+1 = csum j.+1 by lia.
      by rewrite csumP -H1;lia.
    Qed.
    
    Lemma csumI2 n: if (n.+1 < csum (csumI n).+1) then (csumI n.+1) = (csumI n) 
                    else (csumI n.+1) = (csumI n).+1.
    Proof. by  move: (exists_sandwich n) => /csumI1. Qed.
    
    Lemma csumI3 n: n.+1 = csum (csumI n).+1 -> (csumI n.+1) = (csumI n).+1.
    Proof.
      by move: (csumI2 n) => + H1;have ->: (n.+1 < csum (csumI n).+1) = false by lia.
    Qed.

    Definition decode n := (csumI n, n - (csum (csumI n))).

    Lemma decodeP n j: ((csum j) <= n < csum j.+1) -> (decode n)= (j, n -(csum j)).
    Proof. by move => /(@csumI0 n j) <-. Qed.
    
    Lemma decode_next n j k: 
      (decode n) = (j,k) 
      -> (decode n.+1) = if (n.+1 < csum j.+1) then (j, k.+1) else (j.+1,0).
    Proof.
      rewrite /decode => -[H1 H2].
      pose proof (exists_sandwich n) as H3.
      move: H2 H3;rewrite H1 => H2 /[dup] /andP [H3 H3'] /csumI1. 
      case H4: (n.+1 < csum j.+1). 
      + move => ->. 
        by have ->: n.+1 - csum j = k.+1 by lia. 
      + move => ->.
        case H5: (n.+1 == csum j.+1);last by lia.
        by move: H5 => /eqP H5;rewrite -H5 subnn.
    Qed.
    
    (** unused: we just use decode 
        Definition encode (rc : nat * nat) : nat := (csum rc.1 + rc.2).
     *)

  End prelude.
  
  Section val_def_and_properties.

    (** we specialize previous section to the case when p is (fun n' => (size (g n')) *)
    Definition p := (fun n => (size (g n))).

    (** unused: we just use decode 
        Definition encode' (g : nat -> seq T) (rc : nat * nat) : nat := encode (fun n' => (size (g n'))) rc.
    *)

    Definition val n := 
      let (row,col):= decode p n in 
      if col == 0 then (f row) else nth (f row.+1) (g row) col.-1.

    Lemma valP n j: ((csum p j) <= n < csum p j.+1)
                     -> val n = (if n - csum p j == 0
                                then f j
                                else nth (f j.+1) (g j) (n - csum p j).-1).
    Proof. by move => /(@csumI0 p n j) H1; rewrite  /val /decode H1. Qed.

    Lemma valP' n j z: ((csum p j) <= n < csum p j.+1)
                       -> val n = nth z ((f j)::(rcons (g j) (f j.+1))) (n - csum p j).
    Proof. 
      move => /[dup] H1 /valP.
      case H2: (n - csum p j == 0);first by move: H2 => /eqP -> /=.
      have H3: csum p j < n by lia.
      move: H1;rewrite csumP [(p j)]/p => [H1 H1'].
      have H6: 0 < n - csum p j <=  (size (g j)) by lia.
      case H7: (n - csum p j == (size (g j))).
      by move: H7 H1' => /eqP ->;rewrite nth_L1 => ->;apply: nth_dv; lia.
      have H8:  0 < n - csum p j <  (size (g j)) by lia.
      rewrite (@nth_L2 T (g j) (f j) (f j.+1) z (n -csum p j) H8) H1'.
      by apply: nth_dv; lia.
    Qed.
    
    Lemma valP'' n j: n = (csum p j) -> val n = (f j).
    Proof.
      move => H1.
      have H2: ((csum p j) <= n < csum p j.+1) by rewrite csumP H1;lia.
      by move: H2 => /(@valP' n j (f j.+1));rewrite H1 subnn /=.
    Qed.

    Lemma valP''' n j: ((csum p j) < n < csum p j.+1) -> (val n) \in (g j).
    Proof.
      move => H1;have /(@valP n j):((csum p j) <= n < csum p j.+1) by lia.
      have ->: (n - csum p j == 0) = false by lia.
      move => H2.
      apply/nthP.
      exists (n - csum p j).-1. 
      by move: H1;rewrite csumP [(p j)]/p => /andP [H1 H1'];lia.
      by rewrite H2.
    Qed.

    Lemma valP4 n j: (csum p j) < n -> exists j', (j <= j') /\ ((val n) \in (g j') \/ (val n) = (f j')).
    Proof.
      move => H1.
      move: (@exists_sandwich p n) => H2.
      pose proof (@incr_sandwich1 p n j H1) as H3. 
      exists (csumI p n);split;first exact. 
      case H4: (n == csum p (csumI p n)). 
      by move: H4 => /eqP/valP'' H4;right.
      by (have /valP''' H5: csum p (csumI p n) < n < csum p (csumI p n).+1 by lia);left.
    Qed.
    
    Section val_path.

      Lemma allL2val (R: relation T): 
        (forall n, allL R (g n) (f n) (f n.+1)) -> forall n, R ((val n), (val n.+1)).
      Proof.
        move => H1 n.
        move: (@exists_sandwich p n) => H2.
        pose j:= (csumI p n);rewrite -/j in H2.
        pose proof (@allL_nth' T R (g j) (f j) (f j.+1) (f j.+1)) as H3.
        move: H1 => /(_ j) {}/H3 /(_ (n -csum p j)) H1.
        have H3: n - csum p j <= size (g j) by rewrite csumP [(p j)]/p in H2; lia.
        move: H3 => /H1.
        move: (H2) => /(@valP' n j (f j.+1)) <-.
        case H3: (n.+1 < csum p j.+1). 
        + have H2': csum p j <= n.+1 < csum p j.+1 by lia.
          have H4: (n.+1 - csum p j) = (n - csum p j).+1 by lia.
          by move: H2' => /(@valP' n.+1 j (f j.+1));rewrite H4 => <-.
        + have H4: n.+1 = csum p j.+1 by lia.
          have H5: (n - csum p j).+1 = csum p j.+1 -csum p j by lia.
          have H6: (n - csum p j).+1 = (p j).+1 by rewrite csumP in H5;lia.
          rewrite H6 [(p j)]/p nth_L1'.
          have H7: csum p j.+1 <= n.+1 < csum p j.+2
            by apply/andP;split;rewrite H4;[|apply: csum_strict_inc].
          pose proof (@valP' n.+1 j.+1 (f j.+1) H7) as H8.
          by rewrite H8 H4 subnn /=.
      Qed.
      
    End val_path.

    Section val_injective.

    Lemma Asym2P12 (R: relation T):
      (forall n, allLu R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> ( forall n, forall n', n < n' -> ~ R.+ (f n', f n)).
    Proof.
      move => H0 n.
      elim => [// | n' Hr H1].
      case H2: (n < n'); 
        last by (have <-: n = n' by lia);move: H0 => /(_ n) [_ [? _]].
      move: H2 => /Hr H2 H3.
      move: H0 => /(_ n') [[+ _] _] => /(@allL_to_clos_t T) H4.
      by pose proof (@TclosT T R (f n') (f n'.+1) _ H4 H3).
    Qed.
    
    Lemma Asym2P9 (R: relation T): 
      (forall n, allL R (g n) (f n) (f n.+1)) 
      -> ( forall n, forall n', n < n' -> R.+ ((f n), (f n'))).
    Proof.
      move => H0 n;elim => [//| n' Hr H1].
      move: H0 => /(_ n') /(@allL_to_clos_t T R) H0.
      case H2: (n < n');first by move: H2 => /Hr H2;apply: (@TclosT T R (f n) (f n') _).
      by have /eqP ->: (n == n') by lia.
    Qed.

    Lemma Asym2P10 (R: relation T): 
      (forall n, allLu R (g n) (f n) (f n.+1)) 
      -> ( forall n, forall n', forall x, n <= n' -> x \in (g n') -> R.+ ((f n), x)).
    Proof.
      move => H0 n n' x H1' H2. 
      case H0': (n == n' ); last first.
      + have H1: ( n < n') by lia.
        have H1'': (forall n, allL R (g n) (f n) (f n.+1))
          by move: H0 => + n1 => /(_ n1) [H0 _].
        move: H1'' => /Asym2P9/(_ n n' H1) H3.
        move: H0 => /(_ n') [H4 _].
        pose proof (@allL_to_clos_t_left T _ _ _ _ x H2 H4). 
        by apply: (@TclosT T R (f n) (f n') _).
      + move: H0' => /eqP ->.
        move: H0 => /(_ n') [H0 _].
        by pose proof (@allL_to_clos_t_left T R (g n') (f n') (f n'.+1) x H2 H0). 
    Qed.
    
    Lemma Asym2P11 (R: relation T): 
      (forall n, allL R (g n) (f n) (f n.+1)) 
      -> ( forall n, forall n', forall x, n < n' -> x \in (g n) -> R.+ (x, (f n'))).
    Proof.
      move => H0 n n' x H1 H2. 
      case H3: (n.+1 < n').
      + move: H3 => /(@Asym2P9 R H0) H3.
        move: H0 => /(_ n) H4.
        pose proof (@allL_to_clos_t_right T _ _ _ _ x H2 H4). 
        by apply: (@TclosT T R x (f n.+1) _).
      + have /eqP <-: (n.+1 == n') by lia.
        move: H0 => /(_ n) H4.
        by pose proof (@allL_to_clos_t_right T _ _ _ _ x H2 H4). 
    Qed.
    
    Lemma Asym2P6 (R: relation T) z n: 
      allL R (g n) (f n) (f n.+1)
      <-> forall j, j <= size (g n) ->
             R ((nth z ((f n)::(rcons (g n) (f n.+1))) j),
                 (nth z ((f n)::(rcons (g n) (f n.+1))) j.+1)).
    Proof. by rewrite (@allL_nth' T R (g n) (f n) (f n.+1) z). Qed.

    
    Lemma Asym2P6' (R: relation T):
      (forall n, allLu R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> ( forall n, forall n', n < n' -> uniq ((g n) ++ (g n'))).
    Proof.
      move => H0 n n' H1.
      move: (H0) => /[dup] /(_ n) [[H2 H3] [H4 H5]] /(_ n') [[H6 H7] [H8 H9]].
      case C1: (n' == n.+1);first by move: C1 => /eqP ->. 
      have H10: n.+1 < n' by lia.
      move: H3 H7;rewrite 2!uniq_crc => -[_ [_ [H3 _]]] -[_ [_ [H7 _]]].
      rewrite uniq_catE H3 H7;split;[exact |split;[exact|]].
      move => x H11 H12.
      pose proof (@allL_to_clos_t_left T _ _ _ _ x H12 H6) as T0.
      pose proof (@allL_to_clos_t_right T _ _ _ _ x H11 H2) as T1.    
      have H13: R.+ (f n', f n.+1) by apply: (@TclosT T R _ _ _ T0 T1).
      by pose proof (@Asym2P12 R H0 _ _ H10).
    Qed.
    
    Lemma allL2valu (R: relation T): 
      (forall n, @allLu T R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> forall n, forall n', n < n' -> (val n) = (val n') -> False.
    Proof.
      move => H1 n n' H2 H3.
      move: (@exists_sandwich p n) => H4.
      pose j:= (csumI p n);rewrite -/j in H4.
      case H5: (n' < csum p j.+1).
      + (* n and n' are in the same interval csum p j <= . < csum p j.+1 *)
        move: H1 => /(_ j) [[H6 H6'] [H7 H8]].
        move: (H4) => /(@valP' n j (f j.+1)) H9.
        have H4':  csum p j <= n' < csum p j.+1 by lia.
        move: (H4') => /(@valP' n' j (f j.+1)) H9'.
        move: H3;rewrite H9 H9'.
        pose proof (@uniq_nth3 T (f j :: rcons (g j) (f j.+1)) (f j.+1)) as H10.
        move: H6' => {}/H10 /(_ (n - csum p j) (n' - csum p j)) H6'.
        have H10: n - csum p j < n' - csum p j  by lia.
        have H11: n' - csum p j < size (f j :: rcons (g j) (f j.+1))
          by rewrite /= size_rcons;rewrite csumP [(p j)]/p in H5; lia.
        move: H10 => /H6' H10.
        move: H11 => /H10 H11.
        by move => H12;rewrite H12 in H11.
      + (* csum p j <= n < csum p j.+1 and csum p j.+1 <= n' *)
        case H5': (n' == csum p j.+1).
        ++ move: H1 => /(_ j) [[H6 H6'] [H7 H8]].
           move: (H4) => /(@valP' n j (f j.+1)) H9.
           move: H5' => /eqP/[dup] H5' /(@valP''  n' j.+1).
           pose proof (@uniq_nth3 T (f j :: rcons (g j) (f j.+1)) (f j.+1)) as H10.
           move: H6' => {}/H10 /(_ (n - csum p j) (n' - csum p j)) H6'.
           have H10: n - csum p j < n' - csum p j  by lia.
           have H11: n' - csum p j < size (f j :: rcons (g j) (f j.+1))
             by rewrite /= size_rcons H5' csumP [(p j)]/p;lia. 
           move: H10 => {}/H6' H10.
           move: H11 => {}/H10 H11 H12.
           move: H11;rewrite H5' csumP [(p j)]/p.
           have ->: (csum p j + (size (g j)).+1 - csum p j) = (size (g j)).+1 by lia.
           by rewrite  nth_L1' -H9 -H12 H3.
        ++ (* now csum p j <= n < csum p j.+1 and csum p j.+1 < n' *)
          have H6: csum p j.+1 < n' by lia.
          move: (@valP4 _ _ H6) => [j' [H7 [H8 | H8]]].
          +++ (* val n' \in g j' *) 
            case H9: (n == csum p j).
            ++++ (** val n = f j and val n' \in g j' *)
              move: H9 => /eqP/valP'' H9.
              have H10:  forall n : nat, allLu R (g n) (f n) (f n.+1)
                  by move: H1 => + n1 => /(_ n1) [H1 _].
              pose proof (@Asym2P10 R H10 j' j' (val n') (leqnn j') H8) as H11.
              move: H11;rewrite -H3 H9 => H11.
              by pose proof (@Asym2P12 R H1 j j' H7).
            ++++ (** val n = g j and val n' = g j' *)
              have H10:  csum p j < n < csum p j.+1 by lia.
              move: H10 => /valP''' H10. 
              move: H1 => /(@Asym2P6') /(_ j j' H7) /uniq_catE [_ [_ H1]].
              apply: H1. apply: H10. rewrite H3. apply: H8.
          +++ (** val n' = f j' *)
            case H9: (n == csum p j).
            ++++  (** val n= (f j) et val n'= (f j') *)
              move: H9 => /eqP/valP'' H9.
              pose proof (@Asym2P12 R H1 j j' H7) as H10.
              move: H10;rewrite -H8 -H9 -H3 => H10.
              have H11: (forall n, allL R (g n) (f n) (f n.+1))
                by move: H1 => + n1 => /(_ n1) [[H1 _] _].
              pose proof (@Asym2P9 R H11 j j' H7) as H12.
              move: H12; rewrite  -H8 -H9 -H3 => H12.
              exact.
            ++++ (** val n= (g j) et val n'= (f j') *)
              have H10:  csum p j < n < csum p j.+1 by lia.
                 move: H10 => /valP''' H10. 
                 move: (H1) => /(_ j) [[H01 H1'] _].
                 case H12: (j' == j.+1). 
                 +++++ move: H12 => /eqP H12.
                 rewrite H12 -H3 in H8.
                 move: H1' => /(@uniqE T (g j) (f j) (f j.+1) (val n)) [_ [H1' _]].
                 move: H1' => /(_ (index (val n) (g j))) H1'.
                 rewrite nth_index in H1'.
                 move: (H10); rewrite -index_mem => /H1'.
                 by rewrite -H8.
                 exact.
                 +++++ 
                 pose proof (@allL_to_clos_t_right T R (g j) (f j) (f j.+1) (val n) H10 H01) as H11. 
                 move: H11;rewrite H3 H8 => H11.
                 have H13: j.+1 < j' by lia.
                 pose proof (@Asym2P12 R H1 _ _ H13).
                 exact.
    Qed.

    Lemma is_inj: 
      (forall n, forall n', n < n' -> (val n) = (val n') -> False) -> injective val.
    Proof.
      move => H1 n n' H2.
      case H3: ((n < n') || (n' < n));
        first by move: H3 => /orP [/H1 /[!H2] ? |/H1 /[!H2] ?] //.
      lia.
    Qed.
    
    Lemma allL2val_inj (R: relation T): 
      (forall n, @allLu T R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> injective val. 
    Proof. by move => /allL2valu H1;apply: is_inj. Qed.
    
    End val_injective .

  End val_def_and_properties.

End val_construction.


Section main_result.

  Variables (T:choiceType) (R: relation T).

  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  
  Lemma Asym2P5': (iic (Asym R.+)) -> (iic_inj R). 
  Proof.
    move => /(@Asym2P5 T R A1) [k [l H1]]. 
    move: (H1) => /allL2val_inj ?.
    have H2: (forall n, allL R (l n) (k n) (k n.+1)) 
      by move: H1 => + n => /(_ n) [[? _] _].
    move: H2 => /allL2val ?. 
    by exists (val k l).
  Qed.
  
End main_result.


