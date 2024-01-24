(* -*- Encoding : utf-8 -*- *)
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

From RL Require Import  seq1 ssrel rel. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(* Notation used 
 * st is a sequence of elements of Type T
 * Variables (st: seq T).
 * stt is a sequence of elements of the product Type T*T 
 * Variables (stt: seq (T*T)).
 * On veut manipuler des relations sur T et des relations sur T*T 
 * Variables (R_T: relation T)
 * Variables (R_T2: relation T*T)
 *)

Reserved Notation "p [\in] X" (at level 4, no associativity). 
(* begin snippet all_notation:: no-out *)  
Notation "p [\in] X" := (all (fun x => x \in X) p). 
(* end snippet all_notation *)  

Section Types.
  (** * Needed Types *)
  Variables (T O: Type).
  Definition Eo (Z: Type) := prod (prod T T) Z.

End Types.

Section allset2.
  (** * allset for a product type (T *T) *)

  Variables (T: Type).
  
  Lemma allset_inv: forall (E: relation T) (spa: seq (T * T)), 
      spa [\in] E <-> (map (fun tt => (tt.2,tt.1)) spa) [\in] E.-1. 
  Proof.
    move => E;elim => [ // | [x y] spa Hr].
    by rewrite map_cons !allset_cons Hr.
  Qed.
  
  Lemma allset_Rr: forall (X: set T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] R_(X) <-> (rcons p y) [\in] X.
  Proof.
    move => X x y p.
    elim: p x. 
    - rewrite /= /Rr; split => [/andP [/inP H1 _] | /andP [/inP H1 _]].
      by rewrite /mkset /= in H1;apply mem_set in H1;rewrite H1.
      by apply/andP;split;[ apply/inP;rewrite /mkset /= |].
    - move => z p Hr x; rewrite rcons_cons Lift_c 2!allset_cons.
      split => [ [? /Hr ?] // | [? ?]].
      by split;[| apply Hr].
  Qed.

  Lemma allset_Lr: forall (X: set T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] L_(X) <-> (x::p) [\in] X.
  Proof.
    move => X x y p.
    elim: p x. 
    - rewrite /= /Lr; split => [/andP [/inP H1 _] | /andP [/inP H1 _]].
      by rewrite /mkset /= in H1;apply mem_set in H1;rewrite H1.
      by apply/andP;split;[ apply/inP;rewrite /mkset /= |].
    - move => z p Hr x; rewrite rcons_cons Lift_c 2!allset_cons.
      split => [ [? /Hr ?] // | [? ?]].
      by split;[| apply Hr].
  Qed.
  
  Lemma allset_Dl: forall (X: set T) (E: relation T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] (Δ_(X)`;`E) -> (x::p) [\in] X.
  Proof.
    by move => X E x y p;rewrite DeltaLco allset_I => /andP [/allset_Lr H1 _].
  Qed.

  Lemma allset_Dr: forall (X: set T) (E: relation T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] (E`;`Δ_(X)) -> (rcons p y) [\in] X.
  Proof.
    by move => X E x y p;rewrite DeltaRco allset_I => /andP [_ /allset_Rr H1].
  Qed.

End allset2.

Section allset_Lifted.
  (** *  all on a lifted sequence  *)
  
  Variables (T: Type).
  Definition allL (E: relation T) (p: seq T) (x y:T) := 
    (Lift (x::(rcons p y))) [\in] E.
  
  Lemma allL0 : forall (E: relation T) (x y : T),
      allL E [::] x y = ((x,y) \in E).
  Proof.
    by move => E x y;rewrite /allL Lift_c /andP /= andbT. 
  Qed.

  Lemma allL0' : forall (E: relation T) (x y : T),
      allL E [::] x y <-> E (x,y).
  Proof.
    by move => E x y;rewrite allL0;split=> [/set_mem H1 // | /inP H1]. 
  Qed.
  
  Lemma allL_c: forall (E: relation T) (p: seq T) (x y z: T),
      allL E (z::p) x y <-> ((x, z) \in E) && allL E p z y.
  Proof.
    by move => E p x y z;split;[rewrite /allL rcons_cons Lift_c allset_cons |].
  Qed.

  Lemma allL_rc: forall (E: relation T) (p: seq T) (x y z: T),
      allL E (rcons p z) x y <-> ((z,y) \in E) && allL E p x z.
  Proof.
    move => E p x y z;split.
    by rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons;move => [-> /inP ->].
    by move => /andP [/inP ? ?];rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.
  
  Lemma allL_cat: forall (E: relation T) (p q: seq T) (x y z: T),
      allL E ((rcons p y) ++ q) x z <-> allL E p x y && allL E q y z.
  Proof.
    move => E p q x y z.
    rewrite /allL cat_rcons rcons_cat rcons_cons -cat_rcons Lift_cat_crc allset_cat.
    by split => [ [? ?] | /andP [? ?]];[apply/andP |].
  Qed.
  
  Lemma allL_subset: forall (E R: relation T) (p: seq T) (x y: T),
      (E `<=` R) -> allL E p x y -> allL R p x y.
  Proof.
    by move => E R p x y H1 H2;apply allset_subset with E.
  Qed.
  
  Lemma allL_WS_iff: forall (E: relation T) (W:set T) (p: seq T) (x y: T),
      allL (Δ_(W.^c) `;` E) p x y <-> all (fun x => x \in W.^c) (x::p) && allL E p x y.
  Proof.
    move => E W p x y.
    have H1: (L_(W.^c) `&` E) `<=` E by apply intersectionSr.
    have H2: (L_(W.^c) `&` E) `<=` L_(W.^c) by apply intersectionSl.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaLco /allL allset_I.
    by split => /andP [/allset_Lr H5 H6];[apply /andP | apply /andP].
  Qed.
  
  Lemma allL_SW_iff: forall (E: relation T) (W:set T) (p: seq T) (x y: T),
      allL (E `;` Δ_(W.^c)) p x y <-> all (fun x => x \in W.^c) (rcons p y) && allL E p x y.
  Proof.
    move => E W p x y.
    have H1: (E `&` L_(W.^c)) `<=` E by apply intersectionSl.
    have H2: (E `&` L_(W.^c)) `<=` L_(W.^c) by apply intersectionSr.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaRco /allL allset_I; split => /andP [H5 H6]. 
    by rewrite allset_Rr in H6; apply /andP; split. 
    by apply /andP; split;[| rewrite allset_Rr].
  Qed.
  
  Lemma allL_rev: forall (E: relation T) (p: seq T) (x y: T),
      allL E p x y <->  allL E.-1 (rev p) y x.
  Proof.
    move => E p x y. 
    have H1: (y :: rcons (rev p) x) = rev (x::(rcons p y)) by rewrite rev_cons rev_rcons -rcons_cons.
    by rewrite /allL allset_rev allset_inv H1 Lift_rev.
  Qed.
  
  Lemma allL_All: forall (E: relation T) (p: seq T) (x y: T),
      allL E p x y -> all (fun x => x \in (E.+)#_(y)) (x::p).
  Proof.
    move => E p x y.
    elim: p x. 
    by move => x;rewrite /allL /= => /andP [/inP H1 _];apply /andP;split;[apply mem_set;apply Fset_t1|].
    move => z p Hr x;rewrite allL_c => /andP [/inP H1 /Hr H2].
    move: (H2);rewrite allset_cons => [[H3 H4]].
    by rewrite allset_cons;split;[ apply Fset_t2; exists z |].
  Qed.
  
End allset_Lifted.

Section Edge_paths.
  (** * (edge) paths equivalent definitions with the help of all and Lift  *) 
    
  Variables (T: Type).
  
  (* The definition of (edge) paths of length greater or equal to one *)
  
  (* begin snippet EPath1:: no-out *) 
  Definition EPath1 (E: relation T):=[set p: seq T| (Lift p) [\in] E /\ size(p) >= 2].
  (* end snippet EPath1 *)

  (* an equivalent definition not using the lift operation *)
  Inductive EPath (E: relation T): seq T -> Prop :=
  | pp_void : EPath E [::]
  | pp_two (x: T) (ep: seq T) : 
    EPath E ep ->
    ep = [::] \/ (exists (y: T), exists (ep1: seq T), ep = [::y & ep1] /\ E (x,y))
    -> EPath E ([:: x & ep]).
  
  Definition EPath1' (E: relation T) := [set p: seq T | EPath E p /\ size(p) >= 2].
  
  Section EPath1_EPath1'.

    (* intermediate Lemma *)
    Lemma Epath_equiv_rc_: forall (E:relation T) (p: seq T) (x y: T),
        (Lift (x::(rcons p y))) [\in] E <-> EPath E (x::(rcons p y)).
    Proof.
      split.
      - elim: p x y => [ //= x y /andP [/inP H2 _] | z p Hr x y ].
        by apply pp_two;[ apply pp_two;[constructor | left] | right; exists y, [::]].
        rewrite rcons_cons Lift_c allset_cons andC;
            by move => [H1 H2];apply pp_two;[ apply Hr | right; exists z, (rcons p y)].
      - move => H.
        elim/EPath_ind: H => [// | x' y' ep H1 [-> // | [y1 [ep1 [H2 H3]]]]].
        by rewrite H2 in H1 *; rewrite Lift_c allset_cons //.
    Qed.
    
    Lemma Epath_equiv: forall (E:relation T) (p: seq T),
        (Lift p ) [\in] E <-> EPath E p.
    Proof.
      move => E p.
      (* we use seq_cases to explore the three cases *)
      pose proof seq_cases p as [H1 | [[x' H1] | [x' [y' [q H1]]]]];rewrite H1.
      by split => H;[apply pp_void | ].
      by split => H;[apply pp_two;[apply pp_void | left] | ].
      by rewrite Epath_equiv_rc_.
    Qed.
    
    Lemma Epath_eq: forall (E:relation T),  EPath1 E = EPath1' E.
    Proof.
      move => E.
      rewrite /EPath1 /EPath1' /mkset predeqE => p.
      split => [[H1 H2] | [H1 H2]].
      by split;[rewrite -Epath_equiv |].
      by split;[rewrite Epath_equiv  |].
    Qed.

  End EPath1_EPath1'.

End Edge_paths.

Section Lift2.
  (** * Multiple definitions of edge paths *) 
  
  Variables (T: Type).

  (* A relation on (T*T) (Ch for Chain) *)
  (* begin snippet Chrel:: no-out *)  
  Definition Chrel  := [set ppa : (T * T)*(T * T) | (ppa.1).2 = (ppa.2).1].
  (* end snippet Chrel *)  

  Lemma Chrel_eq: forall (pa1 pa2: (T*T)), Chrel (pa1,pa2) <-> pa1.2 = pa2.1.
  Proof. by []. Qed.
  
  Lemma Lift_Lift: forall (p:seq T), (Lift (Lift p)) [\in] Chrel. 
  Proof.
    move => p. 
    pose proof seq_cases p as [H1 | [[x H1] | [q [x [y H1]]]]].
    (* p = [::] *) by rewrite H1. 
    (* p = [::x] *) by rewrite H1. 
    (* p = x::(rcons q y) *)
    have H2: size(p) > 1 by rewrite H1 /= size_rcons.
    move: H2 => /seq_cc [q1 [x1 [x2 ->]]].
    elim: q1 x1 x2 => [ x' y' // | y' p' Hr z' x'].
    by rewrite 3!Lift_c allset_cons -Lift_c;split;[ |apply Hr].
  Qed.

  Lemma Lift_Chrel_n_imp: forall (n: nat) (spa : seq (T*T)),
      size(spa)= n.+2 -> (Lift spa) [\in] Chrel -> exists p: seq T, Lift p = spa.
  Proof.
    elim => [// | n Hr].
    - move => spa H1 H2.
      rewrite seq_rcrc0 in H1;move: H1 => [[x1 x2] [[y1 y2] H3]].
      move: H2; rewrite H3 allL0' /Chrel /mkset => /= [->].
      by (exists [::x1;y1;y2]).
    - move => spa H1 H2.
      have H4: size(spa) > 1 by rewrite H1.
      pose proof seq_cc H4 as [q [[x1 x2] [[y1 y2] H5]]].
      move: H2; rewrite H5 Lift_c allset_cons => [[H6 H7]].
      move: H6; rewrite /Chrel /mkset /= => ->.
      have H8: size [::(y1, y2) & q] = n.+2
        by rewrite H5 /= -addn1 -[in RHS]addn1 in H1; apply addIn in H1.
      apply Hr in H7;last by [].
      move: H7 => [p1 H7].
      have H10: size(p1) > 1 by rewrite -Lift_sz2 H7.  
      pose proof seq_cc H10 as [q3 [x3 [y3 H11]]].
      exists [::x1,x3,y3& q3].
      rewrite Lift_c -H11 H7. 
      by have -> : x3 = y1 by move: H7; rewrite H11 Lift_c => [[H7]]. 
  Qed.
  
  Lemma Lift_Chrel_n_iff: forall (n: nat) (spa : seq (T*T)),
      size(spa)= n.+2 -> ((Lift spa) [\in] Chrel <-> exists p: seq T, Lift p = spa).
  Proof.
    move => n spa H1;split;first by apply Lift_Chrel_n_imp with n.
    by move => [p <-]; apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel_gt1: forall (spa : seq (T*T)),
      size(spa) > 1 -> ((Lift spa) [\in] Chrel <-> exists p: seq T, Lift p = spa).
  Proof.
    move => spa H1.
    have H0: forall (n : nat), 1 < n -> n = n.-2.+2
        by elim => [// | [// |n _ H2 ]];
                  pose proof ltn_predK H2;rewrite -H;apply succn_inj.
    have H2: (size(spa)).-2 >= 0 by [].
    split => [H3 | [p <-]].
    by apply Lift_Chrel_n_imp with (size(spa)).-2;[apply H0 |].
    by apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel: forall (spa : seq (T*T)),
      ((Lift spa) [\in] Chrel <-> exists p: seq T, Lift p = spa).
  Proof.
    elim => [ | [x y] spa _ ];first by split => ?;[(exists [::]) |].
    elim: spa => [ | [z t] spa _]; first by split => [H2 | [p H2]];[(exists [::x;y])|].
    by apply Lift_Chrel_gt1.
  Qed.
  (* begin snippet Lift_lemma:: no-out *)  
  Lemma Lift_lemma:  image [set s | True] (@Lift T) 
                     = preimage (@Lift (T*T)) [set spa| spa [\in] Chrel].
  (* end snippet Lift_lemma *)  
  Proof. 
    rewrite /image /preimage /mkset predeqE => spa.
    by split => [[x _ <-] | /Lift_Chrel [p H1]];[ apply Lift_Lift | exists p].
  Qed.

  (* begin snippet Lift_lemma2:: no-out *)  
  Definition Im (n: nat):= image [set s | size(s)>n] (@Lift T).
  Definition Im1 (n: nat):= [set sp| exists p: seq T, Lift p = sp /\ size(p)>n].
  Definition Pre (n: nat):= 
    preimage (@Lift (T*T)) [set sp| sp [\in] Chrel /\ size(sp)> n].
  Definition Pre1 (n: nat):= [set sp| (Lift sp) [\in] Chrel /\ size(sp)>n].
  (* end snippet Lift_lemma2 *)  

  Lemma Lift_lemma2: (Im 2) = (Pre 0).
  Proof. 
    rewrite /Im /Pre /image /preimage /mkset predeqE => spa.
    split => [[x H1 <-] | [/Lift_Chrel [p H1] H2]]. 
    by split;[apply Lift_Lift | move: H1; rewrite 2!Lift_szn].
    by exists p;[rewrite -2!Lift_szn H1 |].
  Qed.

  Lemma Lift_lemma3: (Im 2) = (Im1 2).
  Proof. 
    rewrite /Im /Im1 /image /mkset predeqE => spa.
    by split => [[p H1 H2]|[p [H1 H2]]];(exists p).
  Qed.
    
  Lemma Lift_lemma4: (Pre 0) = (Pre1 1).
  Proof. 
    by rewrite /Pre /Pre1 /preimage /mkset predeqE => spa;rewrite Lift_szn.
  Qed.
  
  (* begin snippet EPath2new:: no-out *) 
  Definition P_ge_1 (E: relation T):=
    [set spa | spa [\in] E /\ (Lift spa) [\in] Chrel /\ size(spa) > 0].
  (* end snippet EPath2new *)
  
  (* begin snippet EPath3new:: no-out *) 
  Definition P_ge_1' (E: relation T):=
    [set spa | spa [\in] E /\ (exists p, (Lift p) =spa /\ size(p) > 1)].
  (* end snippet EPath3new *)
  
  (* begin snippet EPath2inter:: no-out *) 
  Lemma P_ge_1_lemma: forall (E: relation T), 
      P_ge_1 E = [set spa | spa [\in] E] 
                   `&` [set spa | (Lift spa)  [\in] Chrel /\ size(spa) > 0].
  (* end snippet EPath2inter *)
  Proof. by move => E;rewrite /P_ge_1 /setI /mkset predeqE => spa. Qed.

  Lemma P_ge_1'_lemma: forall (E: relation T), 
      P_ge_1' E =[set spa | spa [\in] E] `&` [set spa | (exists p, (Lift p) =spa /\ size(p) > 1)].
  Proof. by move => E;rewrite /P_ge_1 /setI /mkset predeqE => spa. Qed.
  
  Lemma P_equiv: forall (E: relation T), P_ge_1 E = P_ge_1' E.
  Proof.
    move => E;rewrite /P_ge_1 /P_ge_1' /setI /mkset predeqE => spa.
    split. 
    move => [H1 [/Lift_Chrel [p H2] H3]].
    split. by []. exists p. split. by []. by rewrite -Lift_sz2 H2.
    move => [H1 [p [H2 H3]]].
    split. by []. split. rewrite Lift_Chrel. by exists p. by rewrite -H2  Lift_sz2.
  Qed.
  
End Lift2.

Section LiftO2.
  (** * Multiple definitions of extended oriented edge paths *) 
  
  Variables (T: Type).

  Fixpoint pairp (st: seq(T*T)) (so: seq (O*O)): seq((T*O)*(T*O)):= 
    match st, so with 
    | t::st, o::so => ((t.1,o.1),(t.2,o.2))::(pairp st so)
    | t::st, [::] =>  ((t.1,P),(t.2,P))::(pairp st [::])
    |  _ , _ => [::]
    end.

  Fixpoint unpairp (sto: seq((T*O)*(T*O))) : seq(T*T)*seq(O*O):=
    match sto with 
    | x::sto => ((x.1.1,x.2.1)::((unpairp sto).1),(x.1.2,x.2.2)::((unpairp sto).2))
    | [::] => ([::],[::])
    end.
  
  Lemma unpairp_sz: forall (sto: seq((T*O)*(T*O))),
      size(unpairp sto).1 = size(sto) 
      /\ size(unpairp sto).2 = size(sto).
  Proof.
    by elim => [// | x sto [H1 H2]];rewrite /unpairp /= H1 H2.
  Qed.
  
  Lemma unpairp_right: forall (sto: seq((T*O)*(T*O))),
      pairp (unpairp sto).1 (unpairp sto).2 = sto.
  Proof.
    by elim => [// | [[t1 o1] [t2 o2]] sto Hrt];rewrite /= Hrt.
  Qed.
  
  Lemma Lift_LiftO__: forall (st:seq T) (so:seq O), 
      size(st) = size (so)
      -> (Lift (pair st so)) = pairp (Lift st) (Lift so).
  Proof.
    elim => [ // | t st Hr]. 
    - elim => [ // | o so Ho H1].
      rewrite pair_cc.
      elim: st Hr Ho H1 => [// | t' st' Hr'].
      elim: so Hr' => [ // | o' so' Ho' H1'] Hr' H2 H3.
      rewrite pair_cc Lift_c -pair_cc.
      rewrite Lift_c Lift_c /pairp -/pairp.
      f_equal.
      apply Hr'.
      by move: H3; rewrite /= => /succn_inj H3.
  Qed.
  
  Definition Prel (R: relation (T)) := [set p : (T*O)*(T*O) | R (p.1.1,p.2.1)].
  
  Lemma XX: forall (R: relation T) (st: seq(T*T)) (so: seq (O*O)),
      (pairp st so) [\in] (Prel R) <-> st [\in] R.
  Proof.
    move => R.
    elim => [// | [t1 t2] st Hr so].
    elim: so => [ |  [o1 o2] so Ho ].
    + rewrite /pairp -/pairp;split. 
      by rewrite allset_cons /Prel => [[/= H1 /Hr ->]];rewrite andbT mem_set.
      by rewrite allset_cons => [[H1 /Hr H2]];rewrite allset_cons /=;split.
    + rewrite /pairp allset_cons -/pairp /=.
      split => [ [H1 /Hr ->] | /andP [/inP H1 /Hr H2] ]. 
      by rewrite andbT mem_set.
      by split.
  Qed.

End  LiftO2.

Section LiftO3.
  (** * Multiple definitions of extended oriented edge paths *) 
  Variable (T:Type).

  Definition O_rev (o:O) := match o with | P => N | N => P end.
  
  (* begin snippet Oedge:: no-out *)  
  Definition Oedge (E: relation T): set (T*T*O) :=
    fun (oe: T*T*O) => match oe with | (e,P) => E e | (e,N) => E.-1 e end.
  (* end snippet Oedge *)

  Lemma Oedge_rev: forall (E: relation T) (x y: T),
      Oedge E (x,y,P) = Oedge E (y,x,N).
  Proof.
    by move => E x y.
  Qed.
  
  Lemma Oedge_inv: forall (E: relation T) (x y: T) (o:O),
      Oedge E (x,y,o) = Oedge E.-1 (x,y, O_rev o).
  Proof.
    by move => E x y; elim. 
  Qed.
  
  Definition ChrelO := [set ppa: (T*T*O)*(T*T*O) | (ppa.1.1).2 = (ppa.2.1).1].
  
  Lemma ChrelO_as_Prel: ChrelO = Prel (@Chrel T).
  Proof. by []. Qed.
  
  Lemma Lift_LiftO_gt1: forall (st:seq T) (so:seq O), 
      size(st)> 1 /\ size(st) = size(so)+1
      -> (Lift (LiftO st so)) = pairp (Lift (Lift st)) (Lift so).
  Proof.
    move => st so [H1 H2].
    rewrite /LiftO.
    apply Lift_LiftO__.
    pose proof (Lift_sz H1) as H3.
    by rewrite H3 H2 addn1 subn1. 
  Qed.

  Lemma Lift_LiftO_eq1: forall (st:seq T) (so:seq O), 
      size(st)= 1 /\ size(st) = size(so)+1
      -> (Lift (LiftO st so)) = pairp (Lift (Lift st)) (Lift so).
  Proof.
    move => st so [H1 H2].
    move: (H1);rewrite seq_1 => [[x H3]].
    have H4: size so =0. by rewrite H1 addn1 in H2;apply succn_inj. 
    apply size0nil in H4.
    by rewrite H3 H4 /=.
  Qed.
  
  Lemma Lift_LiftO_gtO: forall (st:seq T) (so:seq O), 
      size(st)> 0 /\ size(st) = size(so)+1
      -> (Lift (LiftO st so)) = pairp (Lift (Lift st)) (Lift so).
  Proof.
    move => st so.
    pose proof seq_cases st as [H1 | [[t H1] | [q [t [v H1]]]]].
    by rewrite H1.
    by move => [_ H2];apply Lift_LiftO_eq1;split;[rewrite H1|].
    by move => [H2 H3];apply Lift_LiftO_gt1;split;[rewrite H1 /= size_rcons|].
  Qed.
 
  Lemma Lift_LiftO: forall (st:seq T) (so:seq O), 
      size(st)> 0 /\ size(st) = size(so)+1
      -> (Lift (LiftO st so)) [\in] ChrelO. 
  Proof.
    move => st so [H1 H2].
    rewrite ChrelO_as_Prel Lift_LiftO_gtO. 
    apply XX.
    apply Lift_Lift.
    by [].
  Qed.
  
  Definition pair_tt_o:= (@pair_ (T*T) O P).
  Definition unpair_tt_o:= (@unpair (T*T) O).
  
  Lemma YY: forall (sto: seq(T*T*O)),
      pair_tt_o (unpair_tt_o sto).1 (unpair_tt_o sto).2 = sto.
  Proof.
    by move => sto;apply unpair_right.
  Qed.
  
  Lemma Lift_ChrelO: forall (sto: seq(T*T*O)),
      (Lift sto) [\in] ChrelO -> (Lift (unpair_tt_o sto).1) [\in] (@Chrel T).
  Proof.
    elim => [ // | tto sto Hr].
    elim: sto tto Hr => [ [t1 t2 o1] _ // | [[t1' t2'] o1'] sto Hr [[t1 t2] o1] H1 H2].
    move: H2;rewrite Lift_c allset_cons=> [[H2 H3]].
    rewrite /unpair_tt_o /unpair Lift_c allset_cons.
    by split;[ | apply H1].
  Qed.

  Lemma Lift_ChrelO1: forall (sto: seq(T*T*O)),
      size(sto) > 0 /\ (Lift sto) [\in] ChrelO 
      -> exists p: seq T, size(p) = size(sto)+1 /\ Lift p = (unpair_tt_o sto).1.
  Proof.
    move => sto [H0 H1].
    have H2:  (Lift (unpair_tt_o sto).1) [\in] (@Chrel T) by apply Lift_ChrelO.
    move: H2;rewrite Lift_Chrel => [[p H3]].
    exists p. 
    split; last by [].
    have H2: size(Lift p)= size(sto) by rewrite -[RHS]unpair_sz1 H3.
    have H4: size(p) > 1 by rewrite -Lift_sz2 H2.
    have H5: size(p) = size (Lift p) +1 by apply Lift_sz3;rewrite H2.
    by rewrite H5 H2. 
  Qed.
  
  Lemma Lift_ChrelO2: forall (sto: seq(T*T*O)),
    size(sto) > 0 /\  (Lift sto) [\in] ChrelO -> 
    exists p: seq T,exists so: seq O, 
      size(p) = size(sto)+1 /\ size(p)=size(so) +1 /\ LiftO p so = sto.
  Proof.
    move => sto H1.
    pose proof Lift_ChrelO1 H1 as [p [H2 H3]].
    move: H1 => [H0 H1].
    have H4: size p > 1 by rewrite H2 addn1.
    exists p; exists (unpair_tt_o sto).2.
    rewrite -unpair_sz. 
    split. by []. split. 
    rewrite -H3.
    rewrite [in RHS]Lift_sz. 
    rewrite subn1 addn1.
    pose proof (ltn_predK H4) as H5.
    by rewrite H5.
    by [].
    rewrite /LiftO H3. 
    apply YY.
  Qed.

  Lemma Lift_ChrelO3: forall (sto: seq(T*T*O)),
    (exists p: seq T,exists so: seq O,0 < size p /\ size p = size so + 1 /\ LiftO p so = sto)
    -> (Lift sto) [\in] ChrelO.
  Proof.
    move => sto [p [so [H1 [H2 <-]]]].
    by apply Lift_LiftO.
  Qed.

  (* begin snippet U_ge_1:: no-out *) 
  Definition U_ge_1 (E: relation T):=
    [set sto | sto [\in] (Oedge E) /\  size(sto) > 0 /\ 
                 (Lift sto) [\in] ChrelO].
  (* end snippet U_ge_1 *)
  
  (* begin snippet U_ge_1p:: no-out *) 
  Definition U_ge_1' (E: relation T):=
    [set sto | sto [\in] (Oedge E) /\ (exists p, exists so, size p > 1 /\ size p = size so + 1 /\ (LiftO p so) =sto)].
  (* end snippet U_ge_1p *)
  
  Lemma U_equiv: forall (E: relation T), U_ge_1 E = U_ge_1' E.
  Proof.
    move => E;rewrite /U_ge_1 /U_ge_1' /setI /mkset predeqE => spa.
    split. 
    - move => [H1 H2].
      split; first by []. 
      pose proof (Lift_ChrelO2 H2) as [p [so [H3 [H4 H5]]]].
      move: H2 => [H2 H2'].
      by (exists p);(exists so);split;[rewrite H3 addn1|].
    - move => [H1 [p [so [H2 [H3 H4]]]]].
      split. by [].
      split. 
      by rewrite -H4 /LiftO pair_sz Lift_sz2.
      rewrite -H4. apply Lift_LiftO.
      split. by apply ltn_trans with 1.
      by []. 
  Qed.

  Lemma ChrelO_eq: forall (x y z t: T) (o1 o2:O),
      ChrelO ((x,y,o1), (z,t,o2)) <-> y = z.
  Proof. by []. Qed.

  (* begin snippet D_U:: no-out *) 
  Definition D_U (R E: relation T):=
    [set spa | spa [\in] (Oedge E) /\
                 (exists p, exists x,exists y,exists o, (LiftO (x::(rcons p y)) o) = spa /\ R (x,y))].
  (* end snippet D_U *)

End LiftO3.

Section PathRel.
  (** * transitive closure and paths
   * the main result here is that the relation in AxA obtained 
   * by fun (x y : T) => (exists (p: seq T), AllL E p x y)
   * is the relation E.+ the transitive closure of E 
   *)

  Variables (T: Type) (E: relation T).
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel_n (E: relation T) (n:nat) :=
    [set x | (exists (p: seq T), size(p)=n /\ allL E p x.1 x.2)].

  (* composition and existence of paths coincide *)
  Lemma Itern_iff_PathReln : forall (n:nat), E^(n.+1) =  PathRel_n E n.
  Proof.
    elim => [ | n' H].
    - rewrite /iter /PathRel_n Delta_idem_l /mkset predeqE => [[x y]].
      split => [ H | ].
      by (exists [::]); rewrite allL0' /=.
      by move => [p [/size0nil -> /allL0' H2]].
    - rewrite -add1n iter_compose H /iter Delta_idem_l /mkset predeqE => [[x y]].
      split => [[z [/= /inP H1 [p [H2 /= H3]]]] |[p [H1 H2]]];
                first by (exists (z::p));rewrite -H2 allL_c H3 andbT H1. 
      elim: p H1 H2 => [ // | z p' _ H1].
      move: H1;rewrite /size -/size -/addn1 => /succn_inj H1.
      rewrite allL_c /= => [/andP [/inP H2 H3]].
      by exists z;split;[ | exists p'].
  Qed.
  
  (* R.+ =  PathRel R *)
  (* begin snippet TCP:: no-out *)  
  Lemma TCP: E.+ = [set vp | exists p, (Lift (vp.1::(rcons p vp.2))) [\in] E].
  (* end snippet TCP *)  
  Proof.
    rewrite /mkset predeqE => [[x y]].
    split => [H1 | [p H1]].
    - apply clos_t_iterk in H1.
      move: H1 => [n H1].
      rewrite  Itern_iff_PathReln /PathRel_n in H1.
      move: H1 => [p [H1 H2]].
      by (exists p).
    - have H2:  PathRel_n E (size p) (x, y) by (exists p).
      rewrite -Itern_iff_PathReln in H2.
      by apply iterk_inc_clos_trans in H2.
  Qed.

End PathRel.

Section PathRel_Examples.
  (* Applications *)
  
  Variables (T: Type) (E: relation T) (W: set T).

  Lemma clos_t_to_paths_l : forall (x y: T),
      (Δ_(W.^c) `;` E).+ (x, y) ->
      (exists (p: seq T), all (fun x => x \in W.^c) (x::p) /\ allL E p x y
                     /\ all (fun x => x \in ((Δ_(W.^c) `;` E).+)#_(y)) (x::p)).
  Proof.
    move => x y; rewrite {1}TCP; move => [p /= H1]; exists p.
    move: (H1) => /allL_WS_iff/andP [H2 H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP H1 H1'].
    by rewrite -allset_consb H1 H1' andbT.
  Qed.
  
  Lemma clos_t_to_paths_r : forall (x y: T),
      (E `;` Δ_(W.^c)).+ (x, y) ->
      (exists (p: seq T), (all (fun z => z \in W.^c) (rcons p y) /\ allL E p x y)
                     /\ all (fun z => z \in ((Δ_(W.^c) `;` E.-1).+)#_(x)) (y::(rev p))).
  Proof.
    move => x y; rewrite {1}TCP; move  => [p H1]; exists p.
    rewrite allL_rev inverse_compose DeltaE_inverse /= in H1.
    move: (H1) => /allL_WS_iff/andP /= [/andP [/inP H2 H3] H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP /= H1 H1'].
    by rewrite H1 H1' andbT allL_rev H2' allset_rcons allset_rev H3. 
  Qed.
  
End PathRel_Examples.

Section Active_relation.
  (** * relation on EO where EO = (AxA)xO
   * this section is to be merged with previous stuffs 
   *)
  
  Variables (T: Type).
  
  (* Active as a relation on Eo) *)
  (* begin snippet ActiveOe:: no-out *)  
  Definition ActiveOe (W: set T) (E: relation T) := 
    [set oe : (T*T*O) * (T*T*O) | 
      Oedge E oe.1 /\ Oedge E oe.2 /\ (ChrelO oe)
      /\ match (oe.1.2,oe.2.2, oe.1.1.2) with 
        | (P,P,v) => W.^c v
        | (N,N,v) => W.^c v
        | (N,P,v) => W.^c v
        | (P,N,v) => (Fset E.* W) v
        end].
  (* end snippet ActiveOe *)  

  Lemma ActiveOe_Oedge: forall (W: set T) (E: relation T) (eo : (T*T*O) * (T*T*O)),
      (ActiveOe W E) eo -> Oedge E eo.1 /\ Oedge E eo.2.
  Proof.
    by move => W E eo [H1 [H2 _]].
  Qed.

  Lemma ActiveOe_Compose: forall (W: set T) (E: relation T) (eo : (T*T*O) * (T*T*O)),
      eo \in (ActiveOe W E) -> ChrelO eo. 
  Proof.
    by move => W E eo /inP [_ [_ [H3 _]]].
  Qed.
  
  Lemma ActiveOe_o: forall (W: set T) (E: relation T) (x y z: T) (o:O),
      (ActiveOe W E) ((x,y,o),(y,z,o)) <-> (Oedge E (x,y,o)) /\ (Oedge E (y,z,o)) /\ W.^c y.
  Proof.
    move => W E x y z o;rewrite /ActiveOe /mkset /ChrelO /=.
    case: o.
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
  Qed.
  
  Lemma ActiveOeT: forall (W: set T) (E: relation T) (x u v z t: T) (o1 o2 o3 o4:O),
      (Fset E.* W) x 
      /\ ActiveOe W E ((u,x,o1), (x,v,o2)) /\ ActiveOe W E ((z,x,o3), (x,t,o4))
      -> ActiveOe W E ((u,x,o1), (x,t,o4)).
  Proof.
    move => W E x u v z t o1 o2 o3 o4.
    case: o1;case: o2; case:o3; case:o4;
      by move => [H0 [[H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]]].
  Qed.
  
  Lemma ActiveOe_rev: forall (W:set T) (E: relation T) (e1 e2: (T * T)) (o:O),
      (ActiveOe W E).-1 ((e1,o), (e2,o)) <-> ActiveOe W E.-1 ((e2,O_rev o), (e1,O_rev o)).
  Proof.
    by move => W E [x1 y1] [x2 y2] o; case: o. 
  Qed.

End Active_relation.

Section Active_paths. 
  (** * Active paths  *)
  Variables (T: Type) (W: set T) (E: relation T).
  (* orientation  *)
  Definition EO := (T * T * O)%type.
  
  (* Active is now almost expressed as a transitive closure 
   * on an lifted space (A * A) * O as it uses AllL *)
  (* begin snippet Aeop:: no-out *)  
  Definition Active_path
    (W: set T) (E: relation T) (p: seq EO) (x y: T) :=
    match p with 
    | [::] => x = y 
    | [::eo1] => eo1.1.1 = x /\  eo1.1.2 = y /\  Oedge E eo1 
    | eo1 :: [:: eo2 & p]
      => eo1.1.1 = x /\ (last eo2 p).1.2 = y 
        /\ allL (ActiveOe W E) (belast eo2 p) eo1 (last eo2 p)
    end.
  (* end snippet Aeop *)
  
  Definition R_o (o:O):= match o with | P => E | N=> E.-1 end.

  Lemma R_o': forall (o:O) (xy: T*T),
      R_o o xy <-> match o with | P => E xy | N=> E.-1 xy end.
  Proof.
    by move => o xy; case: o.
  Qed.

  (** increase active path by left addition *)
  Lemma Active_path_cc: forall (p: seq EO) (eo1 eo2:  EO) (y: T),
      Active_path W E [:: eo1, eo2 & p] eo1.1.1 y
      <-> Active_path W E [:: eo2 & p] eo2.1.1 y /\ ActiveOe W E (eo1, eo2).
  Proof.
    elim => [ | eo3 p _] eo1 eo2 y. 
    - split.
      + by move => [_ [/= -> /allL0' H3]];move: (H3) => /ActiveOe_Oedge [_ H4].
      + by move => [[_ [<- H3]] /inP H4] /=; rewrite allL0.
    - split.
      by move => [H2 [/= H3 /= /allL_c/andP [/inP H4 H5]]] //.  
      by move => [[_ [H3 H4]] /inP H5] /=;
                  rewrite allL_c;split;[| split;[| apply /andP]].
  Qed.
  
  Lemma Active_path_cc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E [:: eo1, eo2 & p] x y -> 
      x = eo1.1.1 /\ y = (last eo2 p).1.2.
  Proof.
    by move => p eo1 eo2 x y [H1 [H2 _]].
  Qed. 
  
  Lemma Active_path_cc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E [:: eo1, eo2 & p] x y -> ActiveOe W E (eo1, eo2) .
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_cc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_cc [_ H1].
  Qed.
  
  Lemma Active_path_crc: forall  (p: seq EO) (eo1 eo2:  EO),
      Active_path W E (eo1::(rcons p eo2)) eo1.1.1 eo2.1.2
      <-> allL (ActiveOe W E) p eo1 eo2.
  Proof.
    elim => [ | eo p H1] eo1 eo2;
           first by split;[move => [_ [_ /= H2]] |move => H1;split;[ |split]].
    split; rewrite rcons_cons.
    move => /Active_path_cc [H2 /inP H3]. 
    by rewrite allL_c; apply/andP; split;[ | apply H1].
    by move => H2;split;[ | split;[ rewrite last_rcons | rewrite belast_rcons last_rcons]].
  Qed.
  
  Lemma Active_path_crc_ht: forall  (p: seq EO) (eo1 eo2: EO) (x y: T),
      Active_path W E (eo1::(rcons p eo2)) x y -> eo1.1.1 = x /\  eo2.1.2 = y.
  Proof.
    move => p eo1 eo2 x y;rewrite headI;move => [H1 [H2 _]].
    by elim: p H2 => [ //= | a p _ //=]; rewrite last_rcons.
  Qed.
  
  Lemma Active_path_crc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E (eo1::(rcons p eo2)) x y
      -> ActiveOe W E (eo1, (head eo2 p)) /\ ActiveOe W E ((last eo1 p), eo2).
  Proof.
    elim => [eo1 eo2 x y [_ [/= _ /allL0' H4]] // | eo3 p H1 eo1 eo2 x y].
    rewrite rcons_cons. move => H2.
    pose proof Active_path_cc_ht H2 as [H3 H4].
    pose proof Active_path_cc_a H2 as H5.
    move: H2;rewrite H3 Active_path_cc;move => [H6 H7].
    apply H1 in H6 as [H6 H8].
    by split;[ | rewrite last_cons].
  Qed.
  
  Lemma Active_path_rcrc: forall (p: seq EO) (eo1 eo2:  EO),
      Active_path W E (rcons (rcons p eo1) eo2) (head eo1 p).1.1 eo2.1.2
      <-> Active_path W E (rcons p eo1) (head eo1 p).1.1 eo1.1.2
        /\ ActiveOe W E (eo1, eo2).
  Proof.
    elim => [ | eo p H1] eo1 eo2.
    - split. 
      by move => [_ [_ /= /allL0' H3]];move: (H3) => /ActiveOe_Oedge [H4 _ /=].
      by move => [_ H2] /=;rewrite allL0'. 
    - 
      rewrite !rcons_cons.
    rewrite Active_path_crc.
    split. 
    move => /allL_rc/andP [/inP H2 H3].
    by rewrite Active_path_crc.
    rewrite Active_path_crc. move => [H2 /inP H3].
    rewrite allL_rc. 
    by apply/andP.
  Qed.

  Lemma Active_path_rcrc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E (rcons (rcons p eo1) eo2) x y 
      -> x = (head eo1 p).1.1 /\ y= eo2.1.2.
  Proof.
    elim => [ | eo p H1] eo1 eo2 x y; first by move => [H1 [H2 _]]; split.
    by rewrite !rcons_cons => /Active_path_crc_ht [H2 H3].
  Qed.

  Lemma Active_path_rcrc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E (rcons (rcons p eo1) eo2) x y 
      -> ActiveOe W E (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_rcrc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_rcrc [_ H1].
  Qed.

  Lemma Active_path_rc_hto: forall (p: seq EO) (eo1:  EO) (x y: T),
      Active_path W E (rcons p eo1) x y ->
      x = (head eo1 p).1.1 /\ y = eo1.1.2 
      /\ Oedge E eo1 /\ Oedge E (head eo1 p).
  Proof.
    elim => [eo1 x y [H2 [H3 H4]] // | eo2 p _ eo1 x y H1]. 
    by pose proof Active_path_crc_ht H1 as [H2 H3];
    pose proof Active_path_crc_a H1 as [[H4 _] [_ [H8 _]]].
  Qed.
  
  Lemma Active_path_c_hto: forall (p: seq EO) (eo1:  EO) (x y: T),
      Active_path W E (eo1::p) x y -> 
      x = eo1.1.1 /\ y = (last eo1 p).1.2
      /\ Oedge E eo1 /\ Oedge E (last eo1 p).
  Proof.
    elim => [eo1 x y [H1 [H2 H3]] // | eo2 p _ eo1 x y H1]. 
    pose proof Active_path_cc_ht H1 as [H2 H3];
      pose proof Active_path_cc_a H1 as [H4 [H5 _]]. 
    rewrite lastI in H1.
    by pose proof Active_path_rc_hto H1 as [_ [_ [H8 _]]].
  Qed.
    
  Lemma Active_path_split: forall (p q: seq EO) (eop eoq:  EO) (x y: T),
      Active_path W E ((rcons p eop)++ eoq::q) x y
      -> Active_path W E (rcons p eop) x eop.1.2
        /\ Active_path W E (eoq::q) eoq.1.1 y
        /\ ActiveOe W E (eop, eoq).
  Proof.
    elim => [ q eop eoq x y // | z p Hr q eop eoq x y ].
    - rewrite cat_rcons cat0s => H1.
      pose proof Active_path_cc_ht H1 as [H2 _].
      pose proof Active_path_cc_a H1 as [H3 _].
      by move: H1; rewrite H2 Active_path_cc; move => [H4 H5];split.
    - elim/last_ind: q Hr eop eoq x y.
      + move => _ eop eoq x y.
        rewrite -cat_rcons cats0 => H1.
        pose proof Active_path_rcrc_ht H1 as [H2 H3].
        move: H1; rewrite H2 H3 Active_path_rcrc; move => [H4 H5]. 
        by pose proof H5 as [H6 [H7 _]].
      + move => q1 t _ H1 eo1 eo2 x y H3.
        rewrite rcons_cons cat_cons -rcons_cons -rcons_cat in H3.
        pose proof Active_path_crc_ht H3 as [H4 H5].
        move: H3; rewrite -H4 -H5.
        move => /Active_path_crc /allL_cat/andP [H6 /allL_c/andP [/inP H7 H8]]. 
        by rewrite rcons_cons Active_path_crc Active_path_crc.
  Qed.
  
  Lemma Active_path_cat: forall (p q: seq EO) (eop eoq :EO) (x y z: T),
      ActiveOe W E (eop, eoq)
      /\ Active_path W E (rcons p eop) x y 
      /\ Active_path W E (eoq::q) y z
      -> Active_path W E (rcons p eop++ eoq::q) x z.
  Proof.
    elim. 
    - move => q eop eoq x y z [H1 [H2 H3]].
      have -> : rcons [::] eop ++ eoq :: q = [:: eop, eoq & q] by [].
      pose proof Active_path_rc_hto H2 as [H4 _].
      pose proof Active_path_c_hto H3 as [H6 _].
      by rewrite H4 Active_path_cc -H6.
    - move => eo1 p1 Hr q eop eoq x y z [H1 [H2 H3]]. 
      rewrite rcons_cons cat_cons.
      rewrite rcons_cons in H2.
      elim/last_ind: q Hr H1 H2 H3.
      + move => _ /inP H1 H2 H3.
        pose proof Active_path_crc_ht H2 as [H4 H5].
        have [H7 H8]: y = eoq.1.1 /\ z = eoq.1.2 by move: H3 => [H3 [H3' _]].
        rewrite -H4 -H5 Active_path_crc in H2.
        rewrite cats1 -H4 H8 Active_path_crc allL_rc. 
        by apply/andP.
      + move => q1 eoq1 _ _ /inP H2 H3 H4.
        pose proof Active_path_crc_ht H3 as [H5 H6].
        pose proof Active_path_crc_ht H4 as [H7 H8].
        rewrite -H5-H6 Active_path_crc in H3.
        rewrite -H7 -H8 Active_path_crc in H4.
        rewrite -rcons_cons -{1}cat_rcons -/rcons -rcons_cat.
        rewrite -H5 -H8 Active_path_crc allL_cat. 
        apply/andP. rewrite allL_rc.
        split. by apply/andP. by [].
  Qed.

  Lemma Active_path_iff: forall (p q: seq EO) (eop eoq :EO) (x y z: T),
      ActiveOe W E (eop, eoq)
      /\ Active_path W E (rcons p eop) x y 
      /\ Active_path W E (eoq::q) y z
      <-> Active_path W E (rcons p eop++ eoq::q) x z /\ y= eop.1.2.
  Proof.
    move => p q eop eoq x y z.
    split => [ [H1 [H2 H3]] | [H1 H2]].
    - pose proof Active_path_rc_hto H2 as [_ [H4 _]].
      by split;[apply Active_path_cat with y | ].
    - pose proof Active_path_split H1 as [H3 [H4 H5]].
      pose proof H5 as [_ [H7 [H8 _]]].
      by split;[ | split;[rewrite H2 | rewrite H2 H8]].
  Qed.
  
  Lemma Active_path_cat': forall (p q: seq EO) (x y z: T),
      (exists (p' q': seq EO), exists (eop eoq: EO),
          p = rcons p' eop /\ q = eoq::q' /\  ActiveOe W E (eop, eoq))
      /\ Active_path W E p x y 
      /\ Active_path W E q y z
      -> Active_path W E (p++q) x z.
  Proof.
    move => p q x y z [[p1 [q1 [eop [eoq [H1 [H2 H3]]]]]] [H4 H5]].
    by rewrite H1 H2; apply Active_path_cat with y; rewrite -H1 -H2.
  Qed.

  
  Section Active_path_unique. 

    (** * If there exists an active path from x to y there exists a walk from x to y
        we just prove that when a variable is repeated twice we can shorten the
        active path * to prove the general property, we have maybe to switch from
        Type to eqType to use unique * in seq ?  *)
    
    Lemma Oedge_Fset:  forall (u v: T), Oedge E (u,v, P) /\ E.*#W v -> E.*#W u.
    Proof.
      move => u v [H1 H2]. 
      move: H2 => [w [H2 H3]].
      have H4: (E `;` E.* ) (u,w) by (exists v).
      have H5:  (E.+ `<=` E.*) by apply clos_t_clos_rt.
      have H6: E.* (u, w) by rewrite r_clos_rt_clos_t in H4 ;apply H5 in H4.
      by (exists w).
    Qed.
  
    Lemma Active_path_Fset:  forall (p: seq T) (x y: T),
        Active_path W E ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ E.*#W (last y p) -> E.*#W x. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        move => x y [[_ [_ H2]] H3].
        by apply Oedge_Fset with y.
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc. 
        move => [[H1 H2] H3].
        have H4: E.*#W y by apply Hr with z.
        move: H2 => [H2 _].
        by apply Oedge_Fset with y.
    Qed.
    
    Lemma Active_path_Fset':  forall (p: seq T) (x y: T),
        Active_path W E ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ E.*#W (last y p) -> E.*#W y. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        by move => x y [[_ [_ H2]] H3].
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc.
        move => [[H1 H2] H3].
        have H4: E.*#W z by apply Hr with y.
        move: H2 => [_ [H2 _]].
        by apply Oedge_Fset with z.
    Qed.
    
    Lemma Active_path_shorten_L1: forall (p: seq EO) (x y z u v w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,v,N)) (v,w,N))] x w
        -> exists (q: seq T), Active_path W E (Lifto [::x,y & q] P) x (last y q) 
                        /\ (Fset E.* W) (last y q).
    Proof. 
      elim => [x y z u v w| ].
      - rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons Active_path_rcrc.
        have -> : [:: (x, y, P); (y, z, P)] = rcons [:: (x, y, P)]  (y, z, P) by [].
        rewrite Active_path_rcrc /head.
        move => [[H1 [H'2 [H'3 [/ChrelO_eq H'4 H'5]]]] [H3 [H4 [_ H6]]]].
        by (exists [::z]).
      - move => [[t s] o] p Hr x y z u v w.
        rewrite rcons_cons rcons_cons Active_path_cc.
        elim: p Hr.
        + move => Hr [H1 H2].
          move: (H1); rewrite Active_path_cc => [[_ [_ [_ [/ChrelO_eq H3 _]]]]];
                                               rewrite <- H3 in *.
          elim: o H1 => [ /Hr [q [H1 H4]] | ].
          ++ exists [:: z & q].
             by rewrite Lifto_c Lifto_c Active_path_cc -Lifto_c /last_cons. 
          ++ exists [::z].
             move: H1 => /Active_path_cc [H1 [_ [_ [_ H7]]]]. 
             move: (H2) => [H2' [H2'' _]].
             rewrite !Lifto_c Active_path_cc -Lifto_c /last.
             by split.
        + move => [[a b] o2] p _ H1 H2.
          move: (H2);rewrite Active_path_cc rcons_cons rcons_cons;
            move => [[_ [_ [_ [/ChrelO_eq H6 _]]]] _].
          rewrite <- H6 in *; clear H6.
          elim: o H2 => [[H2 H3] | ].
          ++ apply H1 in H2;move:H2 => [q H2].
             exists [::z].
             move: H2;rewrite Lifto_c => [[H2 H4]].
             rewrite /Lifto /Lift /pair_o.
             rewrite Active_path_cc last_cons /last.
             move: (H3) => [H5 [H6 _]].
             specialize Active_path_Fset' with q y z => H7.
             by split;[split | apply H7].
          ++ move => [H2 H3].
             pose proof H2 as H5.
             rewrite Active_path_cc in H2.
             rewrite Active_path_crc in H2.
             move: H2 => [H2 [_ [_ [_ H8 ]]]].
             exists [::z];rewrite last_cons /last.
             split. 
             by rewrite /= allL0'.
             by [].
    Qed.
    
    Lemma Active_path_shorten_L2: forall (p: seq EO) (x y z u w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> E.*#W y. 
    Proof. 
      move => p x y z u w H1.
      pose proof Active_path_shorten_L1 H1 as [q H2].
      rewrite Lifto_c in H2.
      by apply  Active_path_Fset' in H2.
    Qed.

    Lemma Active_path_shorten_L3: forall (p: seq EO) (x y z u w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> ActiveOe W E ((x,y,P), (y,w,N)).
    Proof. 
      move => p x y z u w H1.
      move: (H1) => /Active_path_shorten_L2 H2.
      pose proof Active_path_cc_a H1 as [H3 _].
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a [_ [H4 _]].
      by [].
    Qed.
    
    (* the only complex case is (o1 o2 o3 o4)= ( P P N N) which was is treated 
       in the previous lemmata *) 
    Lemma Active_path_shorten: forall (p: seq EO) (x y z u w: T) (o1 o2 o3 o4:O) ,
        Active_path W E [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe W E ((x,y,o1), (y,w,o4)).
    Proof. 
      move => p x y z u w o1 o2 o3 o4 H1. 
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a [_ [H2 [_ H3]]].
      move: o1 o2 o3 o4 H1 H2 H3.
      case; case; case; case;
        move => H1 H2 H3;
               pose proof Active_path_cc_a H1 as [H4 [_ [_ H5]]];
               move: H5 => //= H5;move: H3 => //= H3.
      by apply Active_path_shorten_L3 with p z u.
    Qed.
    
  End Active_path_unique. 
   
End Active_paths.   

Section Active. 
  (** * The Active relation as a relation on AxA *)

  Variables (T: Type). 

  (* begin snippet Active:: no-out *)  
  Definition Active (W: set T) (E: relation T) (x y: T) :=
   (exists (p: seq (T*T*O)), Active_path W E p x y).

  Definition D_separated  (W: set T) (E: relation T) (x y: T) := 
    ~(Active W E x y).
  (* end snippet Active *)  

  Lemma Deployment_to_Active_path:
    forall (W: set T) (E: relation T) (p: seq T) (x y: T) (o:O),
      ( all (fun x => x \in W.^c) p /\ allL (R_o E o) p x y )
        <-> Active_path W E (Lifto (x::(rcons p y)) o) x y.
  Proof.
    split.
    + elim: p x y => [x y [_ /allL0' /R_o' _] // | ]. 
      move => x1 p _ x y. 
      rewrite allset_consb allL_c. 
      move => [ /andP [H2 H'2] /andP [/inP H3 H4]].
      rewrite Lifto_crc Lifto_rcc Active_path_crc /=. 
      elim: p x x1 H3 H2 H'2 H4 => [x x1 H3 /inP H1 _ /allL0' H4 // | ].  
      ++ by rewrite allL0 /=; apply mem_set; split;case: o H3 H4 => /R_o' H3 /R_o' H4.
      ++ move => z p H1 x1 x H3 /inP H2 /allset_cons [H4 H4'] /allL_c/andP [/inP H5 H6] /=. 
         rewrite Lifto_c allL_c;apply /andP;split; last first. 
         by apply: (H1 x z H5 _ H4' H6); apply mem_set. 
         clear H1 H6;apply mem_set;rewrite ActiveOe_o /Oedge.
         by case: o H3 H5 => /R_o' H3 /R_o' H5. 
    + elim: p x y;
        first by move => x y //= [_ [_ H]];
                        split; elim: o H => H;[ | | apply /allL0'/R_o' | apply /allL0'/R_o'].
      
      move => z p H1 x y; rewrite Lift_o_cons;elim: p x y H1. 
      move => x y H1 /Active_path_cc [H2 [H3 [H4 [H5 H6]]]]. 
      elim: o H1 H2 H3 H4 H5 H6 => /= H1 H2 H3 H4 H5 H6.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      (* size p >= 2 *)
      move => t p _ x y H2;rewrite Lift_o_cons;move => /Active_path_cc [/H2 [H3 H5] H4].
      split.
        rewrite allset_cons andC. 
          split;[ | move: H4 => [_ [_ [_ H4]]]].
        by elim: o H2 H4 H5 => _ H4 H5.
        by elim: o H2 H4 H5 => _ /= H4 H5.
        rewrite allL_c H5 andbT.
        by elim: o H2 H4 H5 => _ [/= /inP H4 _] _ /=.
  Qed.
  
  Lemma Deployment_to_Active: forall (W: set T) (E: relation T) (p: seq T) (x y: T),
      (all (fun x => x \in W.^c) p /\ allL E p x y) -> Active W E x y.
  Proof.
    move => W E p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) P); apply Deployment_to_Active_path;split.
  Qed.

  Lemma Deployment_inv_to_Active: forall (W: set T) (E: relation T) (p: seq T) (x y: T),
      (all (fun x => x \in W.^c) p /\ allL E.-1 p x y) -> Active W E x y.
  Proof.
    move => W E p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) N); apply Deployment_to_Active_path;split.
  Qed.

End Active. 


Section Wip.
  (** * test to check how to prove that active path can be chosen uniq *)

  (* we use eqType here *)
  Variables (T: eqType).
  
  Lemma trunck_seq: forall (x: T) (p: seq T),
      ((x \in p) /\ exists (p1:seq T) , x \notin p1 /\ exists p2, (p= p1 ++ (x::p2)))
      \/ ~ (x \in p).
  Proof.
    move => x' p.
    elim: p => [ | x p [[H1 [p1 [H2 [p2 H3]]]] | H1] ].
    - by right.
    - left; split;first by rewrite in_cons H1 orbT.
      case Hx: (x'== x). 
      + by move: Hx => /eqP <-;(exists [::]);split;[|exists p].
      + by exists(x::p1);split;[rewrite in_cons Hx H2 | (exists p2); rewrite H3].
            - case Hx: (x'== x);last by right;rewrite in_cons Hx /=.
              left;split;first by rewrite in_cons Hx /=.
              by exists[::]; split;[ | exists p; move: Hx => /eqP ->].
  Qed.

  (* general property of seq *)
  Lemma trunck_seq_rev: forall (x: T) (p: seq T),
      ((x \in p) /\ exists (p1 p2:seq T), x \notin p2 /\ p= p1 ++ (x::p2))
      \/ ~ (x \in p).
  Admitted.
  
  (* P is compatible with truncation *)
  Axiom trunck_seq_P: forall (x: T) (p p1 p2: seq T) (P: T -> (seq T) -> Prop),
      P x p -> p = p1 ++ (x::p2) -> P x p2.
  
  (* existence with uniq *)
  Lemma P_uniq: forall (x: T) (p: seq T) (P: T-> (seq T) -> Prop),
      P x p -> exists (p2:seq T), x \notin p2 /\ P x p2.
  Proof.
    move => x p P H1.
    case Hx: (x \in p); last first.
    by (exists p);split;[rewrite Hx /= |].
    pose proof trunck_seq_rev x p as [[_ [p1 [p2 [H3 H4]]]] | H2].
    - exists p2. split. by []. by apply: (trunck_seq_P H1 H4).
    - by [].
  Qed.
           
End Wip.

