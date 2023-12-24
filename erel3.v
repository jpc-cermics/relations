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

From RL Require Import  ssrel rel. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Types.
  (** * Needed Types *)
  Variables (A: Type).
  Variables (O: Type).
  Definition T2 (T: Type) := (prod T T).
  Definition he (a: T2 A):= let (x,y):= a in x.
  Definition ta (a: T2 A):= let (x,y):= a in y.

  Definition Eo (T: Type) (Z: Type) := prod (prod T T) Z.
  Definition Oe_o (oe: Eo A O) := let (x,o) := oe in o.
  Definition Oe_h (oe: Eo A O) := let (x,o) := oe in let (h,t):=x in h.
  Definition Oe_t (oe: Eo A O) := let (x,o) := oe in let (h,t):=x in t.

End Types.

Section Utilities.

  Variables (A: Type).

  Lemma seq_rc: forall (p: seq A), 
      (0 < size p) -> exists (q:seq A) (x:A), p = (rcons q x).
  Proof.
    by elim => [ // | x p Hr H1];exists (belast x p), (last x p);rewrite lastI.
  Qed.
  
  Lemma seq_rcrc: forall (p: seq A), 
      1 < size p -> exists (q:seq A) (x y:A), p = (rcons (rcons q x) y).
  Proof.
    move => p H1.
    have H2: 0 < size p by apply leq_ltn_trans with 1.  
    pose proof seq_rc H2 as [q [x H3]].
    have H4: 0 < size q by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_rc H4 as [r [z H5]].
    by exists r,z,x;rewrite H3 H5.
  Qed.

  Lemma seq_rcrc0: forall (p: seq A), 
      size p = 2 -> exists (x y:A), p = [::x;y].
  Proof.
    move => p H1.
    have H2: 1 < size p by rewrite -H1.
    pose proof seq_rcrc H2 as [q [x [y H3]]].
    move: H1;rewrite H3 size_rcons size_rcons => /eqP H1.
    have /nilP H4: size q == 0 by [].
    by exists x,y;rewrite H4.
  Qed.

End Utilities.

Section Wip.
  (** * test to check how to prove that active path can be chosen uniq *)

  (* we use eqType here *)
  Variables (A: eqType).
  
  Lemma trunck_seq: forall (x: A) (p: seq A),
      ((x \in p) /\ exists (p1:seq A) , x \notin p1 /\ exists p2, (p= p1 ++ (x::p2)))
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
  Lemma trunck_seq_rev: forall (x: A) (p: seq A),
      ((x \in p) /\ exists (p1 p2:seq A), x \notin p2 /\ p= p1 ++ (x::p2))
      \/ ~ (x \in p).
  Admitted.
  
  (* P is compatible with truncation *)
  Axiom trunck_seq_P: forall (x: A) (p p1 p2: seq A) (P: A -> (seq A) -> Prop),
      P x p -> p = p1 ++ (x::p2) -> P x p2.
  
  (* existence with uniq *)
  Lemma P_uniq: forall (x: A) (p: seq A) (P: A-> (seq A) -> Prop),
      P x p -> exists (p2:seq A), x \notin p2 /\ P x p2.
  Proof.
    move => x p P H1.
    case Hx: (x \in p); last first.
    by (exists p);split;[rewrite Hx /= |].
    pose proof trunck_seq_rev x p as [[_ [p1 [p2 [H3 H4]]]] | H2].
    - exists p2. split. by []. by apply: (trunck_seq_P H1 H4).
    - by [].
  Qed.
           
End Wip.

Section All.
  (** * all the elements of a sequence belong to a set
   * very similar to all (in seq.v) except that we use Prop here not bool.
   *)

  Variables (A: Type). 
  
  (* True if all the elements of p are in X *)
  Fixpoint All (X: set A) (p: seq A) := 
    match p with 
    | [::] => True
    | x1::p1 => All X p1 /\ X x1
    end.

  Notation "p [∈] X" := (All X p) (at level 4, no associativity).

  Lemma All_cons: forall (X: set A) (p: seq A) (x:A),
      ((x::p) [∈]  X)  <->  p [∈] X /\ X x.
  Proof.
    move => X p x.
    by split;[elim : p x => [ x // | y p H1 x [H2 H2']];split;[ apply H1 |] | ].
  Qed.

  Check All.

  (* using a boolean version *)
  Lemma All_iff_all: forall (X: set A) (p: seq A), 
      (p [∈]  X) <-> all (fun x => x \in X) p.
  Proof.
    move => X p;split.
    - elim:p => [? // | x p H1 /All_cons [/H1 H2 H3] //].
      rewrite -in_setE /= in H3. 
      rewrite /all H3 /=.
      by apply H2.
    - elim:p => [? // | x p H1]. 
      by rewrite All_cons /all => /andP [? /H1 ?];split;[|rewrite -in_setE].
  Qed.
  
  Lemma All_eq_all: forall (X: set A) (p: seq A), 
      (p [∈]  X) = all (fun x => x \in X) p.
  Proof.
    by move => X p;rewrite propeqP;apply  All_iff_all.
  Qed.

  Lemma All_eq_all': forall (X: set A) (p: seq A), 
      (p [∈]  X) = all (fun x => x \in X) p.
  Proof.
    move => X. 
    elim => [ | x p H1]; first by rewrite /All trueE.
    rewrite propeqP;split => [ /All_cons [H2 /inP H3] | /andP [/inP H2 H3]].
    by rewrite /all H3 /= -H1.
    by rewrite All_cons;split;[rewrite H1|].
  Qed.
  
  Lemma All_subset: forall (X Y: set A) (p: seq A),
      (X `<=` Y)%classic ->  (p [∈]  X) -> (p [∈] Y).
  Proof.
    move => X Y; elim => [ // | x p1]. 
    by move => H1 H2 /All_cons [? ?];rewrite All_cons;split; [apply: H1| apply: H2].
  Qed.
  
  Lemma All_rcons: forall (X: set A) (p: seq A) (x:A),
      All X (rcons p x) <->  All X p /\ X x.
  Proof.
    move => X;elim => [// | x' p H1 x];split.
    by rewrite rcons_cons; move => [/H1 [? ?] ?];split;[split | ].
    by move => [[? ?] ?];rewrite rcons_cons;split;[apply H1|].
  Qed. 
  
  Lemma All_rev: forall (X: set A) (p: seq A),
      All X p <->  All X (rev p).
  Proof.
    move => X.
    have H1: forall (p':seq A), All X p' ->  All X (rev p')
        by elim => [// | x' p H1 [? ?]];
                  rewrite rev_cons All_rcons; split;[ apply H1 | ].
    by split => [ | ?];[ apply H1 | rewrite -[p]revK; apply H1].
  Qed. 

  Lemma All_cat: forall (X: set A) (p q: seq A),
      All X (p++q) <->  All X p /\ All X q.
  Proof.
    split. 
    by elim: p q => [q // | x p Hr q [/Hr [H1 H2] H3]]. 
    by elim: p q => [q [_ H1] //| x p Hr q [/All_cons [H1 H2] H3]];
                   rewrite cat_cons All_cons;split;[apply Hr | ].
  Qed. 
  
End All.

Section Seq_lift. 
  (** * from seq: A to seq: A*A
   * some properties of p in seq A are easier to verify on the lifted
   * sequence Lift p or on the Lift^2 p sequence. 
   *)
    
  Variables (A: Type).

  Definition h (a:T2 A):= let (x,y):= a in x.
  Definition l (a:T2 A):= let (x,y):= a in y.
  Definition pair_rev (a:T2 A):=  let (x,y):= a in (y,x).

  Lemma AllS_inv: forall (S: relation A) (spa: seq (T2 A)), 
      All S spa <-> All S.-1 (map pair_rev spa).
  Proof.
    move => S;elim => [ // | [x y] spa Hr].
    by rewrite map_cons !All_cons Hr.
  Qed.
  
  (* Ppath form sequence of nodes *)
  Fixpoint Lift (p: seq A): seq (T2 A) := 
    match p with 
    | x :: [:: y & p] as p1 => (x,y)::(Lift p1)
    | _ => @nil (prod A A)
    end.

  Section Lift_seq_props.
    
    Lemma Lift_c: forall  (p:seq A) (x y:A),
        Lift [::x,y & p] = [::(x,y) & Lift [::y & p]].
    Proof.
      by move => p x y; split.
    Qed.
    
    Lemma Lift_crc: forall  (p:seq A) (x y:A),
        Lift (x::(rcons p y)) = (x,(head y p))::(Lift (rcons p y)).
    Proof.
      by move => p x y; rewrite headI Lift_c. 
    Qed.
    
    Lemma Lift_rcrc: forall  (p:seq A) (x y:A),
        Lift (rcons (rcons p x) y) =  rcons (Lift (rcons p x)) (x,y).
    Proof.
      have H1: forall (q: seq A) (x' y':A), head y' (rcons q x') = head x' q by elim. 
      elim => [ x y // | z p Hr x y ].
      rewrite [in RHS]rcons_cons [in RHS]Lift_crc [in RHS]rcons_cons -[in RHS]Hr.
      by rewrite ![in LHS]rcons_cons [in LHS]Lift_crc H1. 
    Qed.
    
    Lemma Lift_rcc: forall (p:seq A) (x y:A),
        Lift (rcons (x::p) y) = rcons (Lift (x::p)) (last x p,y).
    Proof.
      by move => p x y;rewrite lastI Lift_rcrc.
    Qed.
    
    Lemma Lift_last: forall (p:seq A) (x y:A),
        last (x, head y p) (Lift (rcons p y)) = (last x p, y).
    Proof.
      by elim/last_ind => [x y // | p z Hr x y ];rewrite Lift_rcrc !last_rcons.
    Qed.

    Lemma Lift_head: forall (p:seq A) (x y:A),
        head (x, last y p) (Lift (x::p)) = (x,head y p).
    Proof.
      have H1: forall (q: seq A) (x' y':A), head y' (rcons q x') = head x' q by elim. 
      by elim/last_ind => [x y // | p z Hr x y ];rewrite Lift_crc H1 last_rcons.
    Qed.
    
    Lemma Lift_cat_rc: forall (p q:seq A) (y z:A),
        Lift ((rcons p y) ++ (rcons q z)) =
          Lift (rcons p y) ++ Lift (y::rcons q z).
    Proof.
      have H1: forall (q: seq A) (x' y':A), head y' (rcons q x') = head x' q by elim. 
      elim => [q y z // | t p Hr q y z].
      rewrite rcons_cons cat_cons -rcons_cat Lift_crc rcons_cat Hr. 
      have H2: head z (rcons p y ++ q) = head y p
        by elim/last_ind: q y z => [y z | q z' Hr' y z];
                                  [rewrite cats0 H1 | rewrite -rcons_cat H1 Hr'].
      by rewrite H2 -cat_cons -Lift_crc.
    Qed.
    
    Lemma Lift_cat_crc: forall (p q:seq A) (x y z:A),
        Lift (x::(rcons p y) ++ (rcons q z)) =
          Lift(x::(rcons p y)) ++ Lift (y::rcons q z).
    Proof.
      elim => [q x y z // | t p Hr q x y z].
      by rewrite Lift_crc [in RHS]cat_cons -Lift_cat_rc.
    Qed.
 
    Lemma Lift_rev: forall (p:seq A), 
        Lift (rev p) = map pair_rev (rev (Lift p)). 
    Proof.
      elim => [// | x p Hr ];elim: p x Hr => [// | x' p _ x H1].
      by rewrite rev_cons rev_cons Lift_rcrc 
         -rev_cons H1 Lift_c rev_cons map_rcons /pair_rev.
    Qed.
    
    (** Left inverse of Lift when p is not the nil list *)
    Fixpoint UnLift (p: seq (T2 A)) (x:A):= 
      match p with 
      | [::] => [::x]
      | [::(x,y) & p1 ] => [::x & UnLift p1 y]
      end.

    Lemma UnLift_c: forall (p: seq (T2 A)) (x y z:A),
        UnLift ((x, y) :: p) z = [::x & UnLift p y].
    Proof.
      by [].
    Qed.

    (** sanity check *)
    Lemma Lift_inv: forall (p : seq A) (x y:A),
        UnLift (Lift [::x,y & p]) x = [::x,y & p].
    Proof.
      by elim => [// | y p Hr x' x];rewrite Lift_c UnLift_c Hr.
    Qed.

    Lemma Lift_inv1: forall (p : seq A) (x y:A),
        UnLift (Lift (x::(rcons p y))) x = (x::(rcons p y)).
    Proof.
      by elim => [// | y p Hr x' x];rewrite Lift_c UnLift_c Hr.
    Qed.
    
    Lemma Lift_inv2: forall (p : seq A) (x:A),
        p <> [::] ->  UnLift (Lift p) (head x p) = p.
    Proof.
      elim => [ // | y p _ x _]. 
      elim: p x y => [ //= | z p  Hr x y].
      by rewrite Lift_c UnLift_c Hr.
    Qed.
    
  End Lift_seq_props.

  Definition SeqRel (S: relation A) (p: seq A) := All S (Lift p).
  
  Definition Path (S: relation A) (x y:A) (p: seq A) := SeqRel S (x::(rcons p y)).
  
  (** * The elements of P^n(A,E) (1a) of the paper are the 
   *  sequences q in A*A such that there exists x,y,p such that 
   *  q= Lift (x::rcons p y) satisfying AllS S q.
   *  
   *  We have two ways to see that q is a chain of size >=1. 
   *  q = Lift (x::rcons p y) or [ size q = 1 /\ Lift q satisfy AllS Compose]
   *
   * 
   * a sequence q in A*A of size > 0 is a chain if it is obtained 
   * as q Lift (x::(rcons p y))
   * or if performing a new Lift which gives a sequence in (A*A)^2 
   * the lifted sequence satisfy All Compose 
   * this is explored in next Section 
   *)
  
  (* Check that successive elements of a sequence are related by a Relation
   * without lifting the sequence. 
   * Then we prove that AllS S (Lift p ) <-> Chain S p.
   *)
  
  Inductive ChainI (S: relation A): seq (A) -> Prop :=
  | pp_void : ChainI S [::]
  | pp_two (x:A) (ep: seq A) : 
    ChainI S ep ->
    ep = [::] \/ (exists (y:A), exists (ep1: seq A), ep = [::y & ep1] /\ S (x,y))
    -> ChainI S ([:: x & ep]).
  
  Lemma ChainI_2: forall (S:relation A) (p: seq A) (x y:A),
      All S (Lift (x::(rcons p y))) <-> ChainI S (x::(rcons p y)).
  Proof.
    split.
    - elim: p x y => [ //= x y | z p Hr x y ].
      + move => [_ H2].
        by apply pp_two;[ apply pp_two;[constructor | left] | right; exists y, [::]].
      + rewrite rcons_cons Lift_c All_cons;
        by move => [H1 H2];apply pp_two;[ apply Hr | right; exists z, (rcons p y)].
    - move => H.
      elim/ChainI_ind: H => [// | x' y' ep H1 [-> // | [y1 [ep1 [H2 H3]]]]].
      by rewrite H2 in H1 *; rewrite Lift_c //.
  Qed.
  
  Lemma Chain_equiv: forall (S:relation A) (p: seq A),
      All S (Lift p ) <-> ChainI S p.
  Proof.
    move => S.
    have Chain_0: All S (Lift [::]) <-> ChainI S [::] 
      by split => H;[apply pp_void | ].
    have Chain_1: forall (z:A), All S (Lift ([::z])) <-> ChainI S [::z]
        by split => H;[ apply pp_two;[apply pp_void | left] | ].
    split;match goal with 
          | _ => elim: p => [|x p ];[|elim: p => [H1 | y p _ H1 ]];
                          try rewrite lastI;apply (Chain_0 , Chain_1, ChainI_2)
          end.
  Qed.
  
  (* (x :: (rcons p y)) is a path for the relation S or the graph (A,S) *)
  Fixpoint ChainF (S: relation A) (p: seq A) (x y: A) :=
    match p with
    | [::] => S (x, y)
    | x1::p1 => S (x, x1) /\ ChainF S p1 x1 y
    end.
  
  (* utility *)
  Lemma ChainF_c: forall (S: relation A) (p: seq A) (x y z: A),
      ChainF S (z::p) x y <->  S (x, z) /\ ChainF S p z y.
  Proof.
    by move => S p x y z; split;move => [H1 H2];[split| ].
  Qed.
  
  (** what is the link between a Ppath and Deployment path ? *) 
  Lemma ChainF_AllS: forall (S: relation A) (p: seq A) (x y: A), 
      ChainF S p x y <-> All S (Lift (x::(rcons p y))).
  Proof. 
    move => S p x y;split.
    elim: p x y => [ // | z p H1] x y /ChainF_c [H2 H3].
    by rewrite rcons_cons Lift_c All_cons;split;[apply H1 | ].
    elim: p x y => [ |x p H1 ] z y; first by move => [_ H1].
    rewrite rcons_cons Lift_c All_cons ChainF_c. 
    by move => [H2 H3];split; [ | apply H1].
  Qed.
  
End Seq_lift.

Section Lift2.
  (** using twice Lifted sequences or just Chain on lifted equences *)
  
  Variables (A: Type).
  Definition Lift2 := @Lift (T2 A).

  Definition ComposeAA  := 
    [set ppa : (T2 A)*(T2 A) | (ppa.1).2 = (ppa.2).1]%classic.

  (** sanity check *)
  Lemma Ppath_from_nodes_iff: forall (p:seq A) (x y:A),
      ChainI ComposeAA  (Lift [::x, y & p]).
  Proof.
    elim => [ x y | y p Hr z x];first by constructor;constructor.
    by rewrite Lift_c;apply pp_two;[ | right; exists (x,y), (Lift [::y &p])].
  Qed.

  Lemma Ppath_from_nodes_iff': forall (p:seq A) (x y:A),
      ChainI ComposeAA  (Lift [::x, y & p]).
  Proof.
    move => p x y.
    rewrite -Chain_equiv.
    elim: p x y => [ x y // | y p Hr z x].
    elim: p x y Hr => [ x y // | y p Hr' z' x H1].
    rewrite Lift_c Lift_c Lift_c Lift_c All_cons  -Lift_c  -Lift_c.
    split. apply H1.
    by [].
  Qed.
  
End Lift2.

Section Seq_liftO. 
  (** * from (seq: A) (seq:O) to seq: A *A * O *)
  
  Variables (A: Type).
  (* orientation  *)
  Inductive O := | P | N.
  Definition O_rev (o:O) := match o with | P => N | N => P end.
  
  (* Oedge as a subset of (prod A A) O) *)
  Definition Oedge (S: relation A) :=
    fun (oe: Eo A O) =>
      match Oe_o oe with
      | P => S ((Oe_h oe), (Oe_t oe))
      | N => S.-1 ((Oe_h oe), (Oe_t oe))
      end.
  
  Lemma Oedge_rev: forall (S: relation A) (x y:A),
      Oedge S (x,y,P) = Oedge S (y,x,N).
  Proof.
    by move => S x y.
  Qed.
  
  Lemma Oedge_inv: forall (S: relation A) (x y:A) (o:O),
      Oedge S (x,y,o) = Oedge S.-1 (x,y, O_rev o).
  Proof.
    by move => S x y; elim. 
  Qed.
  
  Fixpoint pair (spa: seq (T2 A)) (so: seq O):= 
    match spa, so with 
    | pa::spa, o::so => (pa,o)::(pair spa so)
    | pa::spa, [::] => (pa,P)::(pair spa [::])
    |  _ , _ => @nil (Eo A O)
    end.

  Lemma pair_c: forall (spa: seq (T2 A)) (so: seq O) (pa: T2 A),
      pair (pa::spa) so = (pa,head P so )::(pair spa (behead so)).
  Proof.
    elim => [ so pa // | pa1 spa Hr so pa ]; first by elim: so => [// | o so _ //].
    elim: so => [// | o so _ ].
    have -> : pair [:: pa, pa1 & spa] (o :: so) = (pa,o)::(pair [::pa1 & spa] so) by [].
    by rewrite Hr.
  Qed.

  Lemma pair_cat: forall (p q: seq (T2 A)) (sop soq: seq O),
      size sop = size p ->
      pair (p++q) (sop++soq) = (pair p sop) ++ (pair q soq).
  Proof.
    elim => [ q sop soq /eqP //= /nilP -> //= | ].
    move => a p Hr q sop soq H1.
    elim: sop H1 Hr => [// | so1 sop H1 H2 H3].
    rewrite cat_cons cat_cons pair_c //=.
    have H4: size sop = size p. by rewrite /size in H2; apply succn_inj.
    have -> : pair (p ++ q) (sop ++ soq) = pair p sop ++ pair q soq 
      by apply H3.
    by [].
  Qed.
  
  Fixpoint unpair_A (spao: seq (Eo A O)) :=
    match spao with 
    | [::] => [::]
    | (pa,o)::spao => (pa)::(unpair_A spao)
    end.

  Lemma unpair_A_c: forall (spao: seq (Eo A O)) (pa: T2 A) (o: O),
      unpair_A ((pa,o)::spao) = pa::(unpair_A spao).
  Proof.
    by [].
  Qed.
  
  Lemma pair_invl: forall (spa: seq (T2 A)) (so: seq O),
      unpair_A (pair spa so) = spa.
  Proof.
    elim => [// | pa spa Hr so].
    elim: so Hr => [ Hr // | o so _ Hr ];
                  match goal with _ => by rewrite pair_c unpair_A_c Hr end.
  Qed.
  
  Fixpoint unpair_O (spao: seq (Eo A O)) :=
    match spao with 
    | [::] => [::]
    | (pa,o)::spao => o::(unpair_O spao)
    end.

  Fixpoint pair_o (spa: seq (T2 A)) (o: O):= 
    match spa with
    | [::] => @nil (Eo A O)
    | pa::spa => (pa,o)::(pair_o spa o)
    end.
    
  Lemma pair_o_c: forall (spa: seq (T2 A)) (o: O) (aa:T2 A),
        pair_o (aa::spa) o = (aa,o)::(pair_o spa o).
  Proof.
    by [].
  Qed.

  Lemma pair_o_rc: forall (spa: seq (T2 A)) (o: O) (aa:T2 A),
        pair_o (rcons spa aa) o = rcons (pair_o spa o) (aa, o).
  Proof.
    by elim => [// | aa1 p Hr] o aa; rewrite rcons_cons //= Hr.
  Qed.

  Lemma pair_o_last: forall (spa: seq (T2 A)) (o: O) (aa:T2 A),
     last (aa,o) (pair_o spa o) = ((last aa spa), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_head: forall (spa: seq (T2 A)) (o: O) (aa:T2 A),
     head (aa,o) (pair_o spa o) = ((head aa spa), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  (** pair_o as  pair *)
  Lemma pair_o_iff: forall (spa: seq (T2 A)) (o: O),
      pair_o spa o = pair spa (nseq (size spa) o).
  Proof.
    by elim => [ // | pa spa Hr o ];rewrite pair_c pair_o_c Hr.
  Qed.

    
  Definition LiftO (sa: seq A) (so: seq O) := pair (Lift sa) so.
  Definition Lifto (sa: seq A) (o: O) := pair_o (Lift sa) o.
  
  Section LiftO_seq_props.
    
    Lemma LiftO_c: forall  (p:seq A) (so: seq O) (x y:A) (o:O),
        LiftO [::x,y & p] [::o & so]= [::(x,y,o) & LiftO [::y & p] so].
    Proof.
      by move => p x y;split.
    Qed.
    
    Lemma LiftO_crc: forall (p:seq A) (so: seq O) (x y:A) (o:O),
        LiftO (x::(rcons p y)) [::o & so] 
        = (x,(head y p),o)::(LiftO (rcons p y) so).
    Proof.
      by move => p so x y o;rewrite headI LiftO_c. 
    Qed.
    
    Definition UnLiftO_A (p: seq (Eo A O)) (x:A) := UnLift (unpair_A p) x.
    
    Definition UnLiftO_O (p: seq (Eo A O)) := unpair_O p.
    
    Lemma UnLiftO_A_c: forall (p: seq (Eo A O)) (x y:A) (o:O),
        UnLiftO_A ((x, y, o) :: p) x = [::x & UnLiftO_A p y].
    Proof.
      by [].
    Qed.
    
    Lemma LiftO_A_inv: forall (p : seq A) (so: seq O) (x y:A) (o:O),
        UnLiftO_A (LiftO [::x,y & p] [::o & so]) x = [::x,y & p].
    Proof.
      by move => p so x y o;rewrite /LiftO /UnLiftO_A pair_invl Lift_inv.
    Qed.

    Lemma LiftO_A_inv1: forall (p : seq A) (so: seq O) (x y:A) (o:O),
        UnLiftO_A (LiftO (x::(rcons p y)) [::o & so]) x = (x::(rcons p y)).
    Proof.
      by move => p so x y o;rewrite /LiftO /UnLiftO_A pair_invl Lift_inv1.
    Qed.
    
    Lemma LiftO_A_inv2: forall (p : seq A) (so: seq O) (x y:A) (o:O),
        p <> [::] -> UnLiftO_A (LiftO p so) (head x p) = p.
    Proof.
      by move => p so x y o H1;rewrite /LiftO /UnLiftO_A pair_invl Lift_inv2.
    Qed.
    
  End LiftO_seq_props.
  
  (** Lifto properties herited from Lift *) 
  Lemma Lifto_c: forall (p:seq A) (o:O) (x y:A),
      Lifto [::x, y & p] o = (x,y,o)::(Lifto [::y & p] o).
  Proof.
    by [].
  Qed.

  Lemma Lifto_crc: forall (p:seq A) (o:O) (x y:A),
      Lifto (x::(rcons p y)) o = (x,(head y p),o)::(Lifto (rcons p y) o).
  Proof.
    by move => p o x y; rewrite /Lifto Lift_crc. 
  Qed.
    
  Lemma Lifto_rcc: forall (p:seq A) (o:O) (x y:A),
      Lifto (rcons (x::p) y) o = rcons (Lifto (x::p) o) (last x p,y,o).
  Proof.
    by move => p o x y; rewrite /Lifto lastI Lift_rcrc pair_o_rc.
  Qed.
  
  Lemma Lifto_rcrc: forall (p:seq A) (o:O) (x y:A),
      Lifto (rcons (rcons p x) y) o =  rcons (Lifto (rcons p x) o) (x,y,o).
  Proof.
    by move => p o x y;rewrite /Lifto Lift_rcrc pair_o_rc. 
  Qed.
  
  Lemma Lifto_last: forall (p:seq A) (o:O) (y z:A),
      last (z, y ,o) (Lifto (rcons p y) o) = (last z p, y,o).
  Proof.
    elim/last_ind => [o y z // | p t Hr o y z].
    by rewrite /Lifto Lift_rcrc pair_o_last !last_rcons.
  Qed.

  Lemma Lifto_last1: forall (p:seq A) (o:O) ( y z:A),
      last (z, head y p,o) (Lifto (rcons p y) o) = (last z p, y,o).
  Proof.
    elim/last_ind => [o y z // | p t Hr o y z].
    by rewrite /Lifto Lift_rcrc pair_o_last !last_rcons.
  Qed.
  
  Lemma Lifto_head: forall (p:seq A) (o:O) (x z:A),
      head (x, z ,o) (Lifto (x::p) o) = (x, head z p, o).
  Proof.
    have H1: forall (q: seq A) (x' y':A), head y' (rcons q x') = head x' q by elim. 
    elim/last_ind => [o x y // | p t Hr o x z].
    by rewrite /Lifto Lift_crc H1. 
  Qed.

  Lemma Lifto_head1: forall (p:seq A) (o:O) (x z:A),
      head (last x p, z ,o) (Lifto (x::p) o) = (x, head z p, o).
  Proof.
    have H1: forall (q: seq A) (x' y':A), head y' (rcons q x') = head x' q by elim. 
    elim/last_ind => [o x y // | p t Hr o x z].
    by rewrite /Lifto Lift_crc H1. 
  Qed.
  
  Lemma Lift_o_cons: forall (p:seq A) (o:O) (x y z:A),
      Lifto (x::(rcons (z::p) y)) o = (x,z,o)::(Lifto (z::(rcons p y)) o).
  Proof.
    move => p o x y z;rewrite Lifto_crc //.
  Qed.
  
  Lemma Lift_o_start_end: forall (p q: seq A) (x y t:A),
      exists (x' y':A) (r: seq (Eo A O)), 
        ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P))
        = (x,x',N)::(rcons r (y',y,P)).
  Proof.
    elim => [ |x' p Hr q ].
    - elim/last_ind => [x y t | q z Hr x y t]; first by (exists t,t,[::]).
      (exists t,z, (Lifto (t::(rcons q z)) P)).
      by rewrite //= -!rcons_cons Lifto_rcrc !rcons_cons. 
    - elim/last_ind: q x' p Hr => [x p Hr x' y t |q x1 Hr x2 p H1 x y t ].
      + specialize Hr with [::] x y t as [x1 [y1 [r H1]]].
        by (exists x, y1, ((x, x1, N)::r));rewrite //= H1.
      + exists x2, x1, ((Lifto (x2::(rcons p t)) N) ++ (Lifto (t::(rcons q x1)) P)).
        by rewrite rcons_cons Lifto_c -!rcons_cons Lifto_rcrc -rcons_cat.
  Qed.
  
  (** XXX écrire les deux autres *) 
  Lemma Lifto_inv1: forall (p: seq A) (x y:A),
      UnLiftO_A (Lifto (x::(rcons p y)) N) x = x::(rcons p y).
  Proof.
    by move => p x y;rewrite /Lifto /UnLiftO_A pair_o_iff pair_invl Lift_inv1.
  Qed.

  Lemma Lifto_inv3: forall (p q: seq A) (x y t:A),
      UnLiftO_A ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P )) x =
        x :: rcons (rcons p t ++ q) y.
  Proof.
    move => p q x y t;rewrite /Lifto /UnLiftO_A. 
    rewrite !pair_o_iff -pair_cat.
    by rewrite pair_invl -Lift_cat_crc -rcons_cat Lift_inv1.
    by rewrite size_nseq.
  Qed.

  (* subset of AxAxO induced by a relation and orientation *)
  
  Definition AllOS (S: relation A) (seo: seq (Eo A O)) := All (Oedge S) seo.
  
  Definition SeqORel (S: relation A) (sa: seq A) (so:seq O) := AllOS S (LiftO sa so).

  (** * We obtain all the extended path joining x to y in the graph (T,S) *)
  Definition EoPath (S: relation A) (x y:A) (sa: seq A) (so:seq O):=
    SeqORel S (x::(rcons sa y)) so.

  (** * The elements of union_[n>=1] U^n(A,E) (2c) of the paper are the 
   *  sequences q in A*A*O such that there exists x,y,p and so such that 
   *  q= LiftO (x::rcons p y) so satisfying AllOS S q.
   *  
   *  We have two ways to see that q is a chain of size >=1. 
   *  q = Lift (x::rcons p y) or [ size q = 1 /\ Lift q satisfy AllS Compose
   *)
    
End Seq_liftO.

Section DeploymentPath.
  (** * Ici on regarde Deployment paths from x to y for a relation 
   * et on voit que c'est un AllS pour un Lift 
   * ce qui fait que la discussion au dessus doit s'appliquer 
   * Il faut voir avec quelle équivalence les preuves sont les + simples.
   *)
  
  Variables (A: Type).
          
  (* (x :: (rcons p y)) is a path for the relation S or the graph (A,S) *)
  Fixpoint Deployment_path (S: relation A) (p: seq A) (x y: A) :=
    match p with
    | [::] => S (x, y)
    | x1::p1 => S (x, x1) /\ Deployment_path S p1 x1 y
    end.

  (* utility *)
  Lemma Dpe: forall (S: relation A) (p: seq A) (x y z: A),
      Deployment_path S (z::p) x y <->  S (x, z) /\ Deployment_path S p z y.
  Proof.
    by move => S p x y z; split;move => [H1 H2];[split| ].
  Qed.

  (** what is the link between a Ppath and Deployment path ? *) 
  Lemma Dpe_AllS: forall (S: relation A) (p: seq A) (x y: A), 
      Deployment_path S p x y <-> All S (Lift (x::(rcons p y))).
  Proof. 
    move => S p x y;split.
    elim: p x y => [ // | z p H1] x y /Dpe [H2 H3].
    by rewrite rcons_cons Lift_c All_cons;split;[apply H1 | ].
    elim: p x y => [ |x p H1 ] z y; first by move => [_ H1].
    rewrite rcons_cons Lift_c All_cons Dpe. 
    by move => [H2 H3];split; [ | apply H1].
  Qed.
  
  (* utility *)
  Lemma Dpe_rev: forall (S: relation A) (p: seq A) (x y z: A),
      Deployment_path S (rcons p z) x y <->  S (z, y) /\ Deployment_path S p x z.
  Proof.
    move => S p x y z; split.
    - elim: p x y z => [ x y z [H1 H2] // | z' p H1 x y z ].
      rewrite rcons_cons => /Dpe [H2 /H1 [H3 H4]].
      by split;[ | split].
    - elim: p x y z => [ x y z [H1 H2] // | z' p H1 x y z ].
      rewrite rcons_cons; move => [H2 /Dpe [H3 H4]].
      by split;[ | apply H1;split].
  Qed.
  
  (* concatenate deployment paths
   * note that ((rcons p y) ++ q) = p ++ y::q) by cat_rcons
   *)
  
  Lemma Deployment_path_cat: forall (S: relation A) (p q: seq A) (x y z: A),
      Deployment_path S ((rcons p y) ++ q) x z
      <-> Deployment_path S p x y /\ Deployment_path S q y z.
  Proof.
    split;move: p q x y z.
    - elim => [ q x y z // |  t p Hr q u v w].
      rewrite rcons_cons cat_cons.
      move => /Dpe [H1 H2].
      have [H3 H4]: Deployment_path S p t v /\ Deployment_path S q v w by apply Hr.
      by split;[ split| ].
    - elim => [q x y z //= H1 |  z' p H1].
      elim => [x y z [/Dpe [H2 H3] //= H4] | t q1 H2 x y z [/Dpe [H3 H'3] /Dpe [H4 H'4]]].
      by split;[ | rewrite cats0 Dpe_rev; split].
      by rewrite rcons_cons cat_cons;split;[ |apply H1;split;[ | split]].
  Qed.
  
  (** shorter proof with AllS *)
  Lemma Deployment_path_cat': forall (S: relation A) (p q: seq A) (x y z: A),
      Deployment_path S ((rcons p y) ++ q) x z
      <-> Deployment_path S p x y /\ Deployment_path S q y z.
  Proof.
    move => S p q x y z.
    by rewrite !Dpe_AllS -All_cat -Lift_cat_crc rcons_cat.
  Qed.
  
  Lemma  Deployment_path_incl: forall (S T: relation A) (p: seq A) (x y: A),
      (S `<=` T)%classic -> Deployment_path S p x y -> Deployment_path T p x y.
  Proof.
    move => S T.
    elim => [x y H1 H2 | z p H1 x y H2 /Dpe [H3 H4]]; first by apply H1.
    by split;[apply H2 |apply H1].
  Qed.     
  
  Lemma  Deployment_path_incl': forall (S T: relation A) (p: seq A) (x y: A),
      (S `<=` T)%classic -> Deployment_path S p x y -> Deployment_path T p x y.
  Proof.
    move => S T p x y H1.
    by rewrite !Dpe_AllS ;apply All_subset.
  Qed.     
  
  Lemma  Deployment_path_WS_iff: forall (S: relation A) (W:set A) (p: seq A) (x y: A),
      Deployment_path (Δ_(W.^c) `;` S) p x y <-> All W.^c (x::p) /\ Deployment_path S p x y.
  Proof.
    move => S W p x y.
    have Hp: (Δ_(W.^c) `;` S `<=` S)%classic by apply DeltaCsubset.
    split.
    - elim: p x y.
      + by move => x y [z [[/= H1 <-] H3]] //. 
      + move => z p  H1 x y /Dpe [[x' [[H4 H5] H6]] H7]. 
        rewrite All_cons Dpe.
        apply H1 in H7.
        move: H7 => [H7 H8].
        by split;[ split;[ |]
                 | split;[rewrite /= in H5; rewrite H5 |]].
    -  elim:p x y=> [x y // [[_ H1] /= H2] | z p H1 x y [/All_cons [H2 H'2] /Dpe [H3 H4]]].
       by (exists x); split;[split;[|] |].
       by apply Dpe;split;[(exists x);split;[split;[|] |] | apply H1].
  Qed.
  
  Lemma  Deployment_path_SW_iff: forall (S: relation A) (W:set A) (p: seq A) (x y: A),
      Deployment_path (S `;` Δ_(W.^c)) p x y 
      <-> All W.^c (rcons p y) /\ Deployment_path S p x y.
  Proof.
    move => S W p x y.
    have Hp: (S `;` Δ_(W.^c) `<=` S)%classic by apply DeltaCsubsetl.
    split.
    - elim: p x y.
      + by move => x y [z [H3 [/= H1 <-]]] //. 
      + move => z p  H1 x y /Dpe [[x' [H6 [H4 H5]]] H7]. 
        rewrite All_cons Dpe.
        apply H1 in H7.
        move: H7 => [H7 H8].
        rewrite /= in H4 H5 H6.
        by split;[ split;[ | rewrite -H5]
                 | split;[ rewrite -H5 |]].
    -  elim:p x y=> [x y // [[_ H1] /= H2] | z p H1 x y [/All_cons [H2 H'2] /Dpe [H3 H4]]].
       by (exists y);split;[ |split;[ |]].
       by apply Dpe;split;[(exists z);split;[ | split;[|]] | apply H1].
  Qed.
  
  Lemma  Deployment_path_rev: forall (S: relation A) (p: seq A) (x y: A),
      Deployment_path S p x y <->  Deployment_path S.-1 (rev p) y x.
  Proof.
    have H1: forall (S': relation A) (p': seq A) (x' y': A),
        Deployment_path S' p' x' y' ->  Deployment_path S'.-1 (rev p') y' x'
        by move => S;elim => [ x y //|z p1 H1 x y /Dpe [H3 H4]];
                           rewrite  rev_cons Dpe_rev /inverse;
                             by split;[ | apply H1].
    move => S p x y; split => [H2 | H2 ].
    by apply H1.
    by rewrite -[p]revK -[S]inverse_inverse;apply H1.
  Qed.     

  (** Other proof with AllS *)
  Lemma  Deployment_path_rev': forall (S: relation A) (p: seq A) (x y: A),
      Deployment_path S p x y <->  Deployment_path S.-1 (rev p) y x.
  Proof.
    split;rewrite !Dpe_AllS;move => H1.
    by rewrite -rev_cons -rev_rcons Lift_rev -AllS_inv All_rev revK rcons_cons.  
    by rewrite AllS_inv All_rev -map_rev -rcons_cons -Lift_rev rev_rcons rev_cons.
  Qed.     
  
  Lemma Deployment_path_All: forall (S: relation A) (p: seq A) (x y: A),
      Deployment_path S p x y -> All (S.+)#_(y) (x::p).
  Proof.
    move => S.
    elim => [  x y /= H1 | z p Hr x y /Dpe [H1 H2]];
           first by split;[ | apply Fset_t1].
    split; first by apply Hr. 
    apply Fset_t2;exists z;split. 
    by [].
    by have [H3 H3']: All S.+#_(y) (z :: p) by apply Hr.
  Qed.
  
End DeploymentPath.

Section PathRel.
  (** * transitive closure and paths
   * the main result here is that the relation in AxA obtained 
   * by fun (x y :A) => (exists (p: seq A), Deployment_path S p x y)
   * is the relation S.+ the transitive closure of S 
   *)

  Variables (A: Type) (S: relation A).
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel_n (S: relation A) (n:nat) :=
    [set x | (exists (p: seq A), size(p)=n /\ Deployment_path S p x.1 x.2)]%classic.

  (* composition and existence of paths coincide *)
  Lemma Itern_iff_PathReln : forall (n:nat), S^(n.+1) =  PathRel_n S n.
  Proof.
    elim => [ | n' H].
    - rewrite /iter /PathRel_n Delta_idem_l /mkset predeqE => [[x y]].
      split => [ H | ].
      by (exists [::]).
      by move => [p [/size0nil -> H2]].
    - rewrite -add1n iter_compose H /iter Delta_idem_l /mkset predeqE => [[x y]].
      split => [[z [H1 [p [H2 H3]]]] |[p [H1 H2]]];
              first by (exists (z::p));rewrite -H2.
      elim: p H1 H2 => [ // | z p' _ H1].
      rewrite /size -/size -/addn1 in H1. 
      apply succn_inj in H1.
      rewrite /Deployment_path -/Deployment_path. 
      move => [H2 H3].
      by exists z;split;[ | (exists p');split].
  Qed.
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel (S: relation A) := 
    [set x | (exists (p: seq A), Deployment_path S p x.1 x.2)]%classic.
  
  (* R.+ =  PathRel R *)
  Lemma clos_t_iff_PathRel: S.+ =  PathRel S.
  Proof.
    rewrite /mkset predeqE => [[x y]].
    split => [H1 | [p H1]].
    - apply clos_t_iterk in H1.
      move: H1 => [n H1].
      rewrite  Itern_iff_PathReln /PathRel_n in H1.
      move: H1 => [p [H1 H2]].
      by (exists p).
    - have H2:  PathRel_n S (size p) (x, y) by (exists p).
      rewrite -Itern_iff_PathReln in H2.
      by apply iterk_inc_clos_trans in H2.
  Qed.

End PathRel.

Section PathRel_Examples.
  (* Applications *)
  
  Variables (A: Type) (S: relation A) (W: set A).

  Lemma clos_t_to_paths_l : forall (x y:A),
      (Δ_(W.^c) `;` S).+ (x, y) ->
      (exists (p: seq A), (All W.^c (x::p) /\ Deployment_path S p x y)
                     /\ All ((Δ_(W.^c) `;` S).+)#_(y) (x::p)).
  Proof.
    move => x y; rewrite {1}clos_t_iff_PathRel; move  => [p H]; exists p.
    by split;[apply Deployment_path_WS_iff | apply Deployment_path_All].
  Qed.
  
  Lemma clos_t_to_paths_r : forall (x y:A),
      (S `;` Δ_(W.^c)).+ (x, y) ->
      (exists (p: seq A), (All W.^c (rcons p y) /\ Deployment_path S p x y)
                     /\ All ((Δ_(W.^c) `;` S.-1).+)#_(x) (y::(rev p))).
  Proof.
    move => x y; rewrite {1}clos_t_iff_PathRel; move  => [p H]; exists p.
    split.
    by apply Deployment_path_SW_iff. 
    by rewrite Deployment_path_rev inverse_compose DeltaE_inverse in H;
    apply Deployment_path_All.
  Qed.
  
End PathRel_Examples.

Section Path_in_prod_A_A.
  (** * paths in prod A A THIS SECTION IS OBSOLETE 
   *  i.e. replaces by previous stuffs 
   *)
  Variables (A: Type).
  
  (* Ppath form sequence of nodes *)
  Fixpoint Ppath_from_nodes (p: seq A) := 
    match p with 
    | x :: [:: y & p] as p1 => (x,y)::(Ppath_from_nodes p1)
    | _ => @nil (prod A A)
    end.
  
  Lemma Ppath_from_nodes_eq: forall  (p:seq A) (x y:A),
      Ppath_from_nodes [::x,y & p] = [::(x,y) & Ppath_from_nodes [::y & p]].
  Proof.
    by move => p x y;split;elim: p x y;move => x y //=;move => z p Hr x1 y1 //= H1.
  Qed.
  
  Fixpoint Ppath_to_nodes (p: seq (T2 A)) (x:A):= 
    match p with 
    | [::] => [::x]
    | [::(x,y) & p1 ] => [::x & Ppath_to_nodes p1 y]
    end.
  
  Lemma Ppath_to_nodes_eq: forall (p: seq (T2 A)) (x y:A),
      Ppath_to_nodes ((x, y) :: p) x = [::x & Ppath_to_nodes p y].
  Proof.
    by [].
  Qed.
  
  Lemma Nodes_to_nodes: forall (p : seq A) (x y:A),
      Ppath_to_nodes (Ppath_from_nodes [::x,y & p]) x = [::x,y & p].
  Proof.
    elim => [// | y p Hr x' x].
    by rewrite Ppath_from_nodes_eq Ppath_to_nodes_eq Hr.
  Qed.

End Path_in_prod_A_A.

Section Active_relation.
  (** * relation on EO where EO = (AxA)xO
   * this section is to be merged with previous stuffs 
   *)
  Variables (A: Type).
  
  (* A relation on  (Eo) *)
  Definition ComposeOe' (oe1 oe2: Eo A O):= (Oe_t oe1)= (Oe_h oe2).

  Definition ComposeOe := 
    [set eo : (Eo A O) * (Eo A O) | (Oe_t eo.1)= (Oe_h eo.2)]%classic.
  
  Lemma ComposeOe_eq: forall (x y z t:A) (o1 o2:O),
      ComposeOe ((x,y,o1), (z,t,o2)) <-> y = z.
  Proof. by []. Qed.
         

  (* Active as a relation on Eo) *)
  Definition ActiveOe (W: set A) (S: relation A) := 
    [set oe : (Eo A O) * (Eo A O) | 
      Oedge S oe.1 /\ Oedge S oe.2 /\ (ComposeOe oe)
      /\ match ((Oe_o  oe.1),(Oe_o oe.2)) with
        | (P,P) => W.^c  (Oe_t oe.1)
        | (N,N) => W.^c  (Oe_t oe.1)
        | (N,P) => W.^c (Oe_t oe.1) 
        | (P,N) =>  (Fset S.* W) (Oe_t oe.1)
        end]%classic.
  
  Lemma ActiveOeT: forall (W: set A) (S: relation A) (x u v z t:A) (o1 o2 o3 o4:O),
      (Fset S.* W) x 
      /\ ActiveOe W S ((u,x,o1), (x,v,o2)) /\ ActiveOe W S ((z,x,o3), (x,t,o4))
      -> ActiveOe W S ((u,x,o1), (x,t,o4)).
  Proof.
    move => W S x u v z t o1 o2 o3 o4.
    case: o1;case: o2; case:o3; case:o4;
      by move => [H0 [[H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]]].
  Qed.
  
  Lemma ActiveOe_rev: forall (W:set A) (S: relation A) (e1 e2: (T2 A)) (o:O),
      (ActiveOe W S).-1 ((e1,o), (e2,o)) <-> ActiveOe W S.-1 ((e2,O_rev o), (e1,O_rev o)).
  Proof.
    by move => W S [x1 y1] [x2 y2] o; case: o. 
  Qed.

End Active_relation.

Section Active_paths. 
  (** * Active paths  *)
  Variables (A: Type) (W: set A) (S: relation A).
  (* orientation  *)
  Definition EO := Eo A O.
  
  (* Active is now almost expressed as a transitive closure 
   * on an lifted space (A * A) * O as it uses Deployment_path *)
  Definition Active_path
    (W: set A) (S: relation A) (p: seq EO) (x y:A) :=
    match p with 
    | [::] => x = y 
    | [::eo1] => (Oe_h eo1) = x /\  (Oe_t eo1) = y /\  Oedge S eo1 
    | eo1 :: [:: eo2 & p]
      => (Oe_h eo1) = x /\ (Oe_t (last eo2 p)) = y 
        /\ Deployment_path (ActiveOe W S) (belast eo2 p) eo1 (last eo2 p)
    end.
  
  Definition R_o (S: relation A) (o:O):= match o with | P => S | N=> S.-1 end.

  (** increase active path by left addition *)
  Lemma Active_path_cc: forall (p: seq EO) (eo1 eo2:  EO) (y:A),
      Active_path W S [:: eo1, eo2 & p] (Oe_h eo1) y
      <-> Active_path W S [:: eo2 & p] (Oe_h eo2) y /\ ActiveOe W S (eo1, eo2).
  Proof.
    elim => [ | eo3 p H1] eo1 eo2 y. 
    - split.
      by move => [H1 [H2 [H3 [H4 [H5 H6]]]]];split;[ split |].
      by move => [[H1 [H2 H3]] H4].
    - clear H1; split.
      move => [H2 [H3 /Dpe [H4 H4']]].
      by split;[split;[ | split] | ].
      by move =>  [[H2 [H3 H4]] H5].
  Qed.
  
  Lemma Active_path_cc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y:A),
      Active_path W S [:: eo1, eo2 & p] x y -> 
      x = Oe_h eo1 /\ y = Oe_t (last eo2 p).
  Proof.
    by move => p eo1 eo2 x y [H1 [H2 _]].
  Qed. 
  
  Lemma Active_path_cc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y:A),
      Active_path W S [:: eo1, eo2 & p] x y -> ActiveOe W S (eo1, eo2) .
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_cc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_cc [_ H1].
  Qed.
  
  Lemma Active_path_crc: forall  (p: seq EO) (eo1 eo2:  EO),
      Active_path W S (eo1::(rcons p eo2)) (Oe_h eo1) (Oe_t eo2)
      <-> Deployment_path (ActiveOe W S) p eo1 eo2.
  Proof.
    elim => [ | eo p H1] eo1 eo2;
           first by split;[move => [_ [_ /= H2]] |move => H1;split;[ |split]].
    split; rewrite rcons_cons.
    by move => /Active_path_cc [H2 H3];split; [ | apply H1].
    by move => H2;split;[ | split;[ rewrite last_rcons | rewrite belast_rcons last_rcons]].
  Qed.
  
  Lemma Active_path_crc_ht: forall  (p: seq EO) (eo1 eo2: EO) (x y:A),
      Active_path W S (eo1::(rcons p eo2)) x y -> Oe_h eo1 = x /\  Oe_t eo2 = y.
  Proof.
    move => p eo1 eo2 x y;rewrite headI;move => [H1 [H2 _]].
    by elim: p H2 => [ //= | a p _ //=]; rewrite last_rcons.
  Qed.
  
  Lemma Active_path_crc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y:A),
      Active_path W S (eo1::(rcons p eo2)) x y
      -> ActiveOe W S (eo1, (head eo2 p)) /\ ActiveOe W S ((last eo1 p), eo2).
  Proof.
    elim => [eo1 eo2 x y [H2 [H3 H4]] // | eo3 p H1 eo1 eo2 x y].
    rewrite rcons_cons; move => H2.
    pose proof Active_path_cc_ht H2 as [H3 H4].
    pose proof Active_path_cc_a H2 as H5.
    move: H2;rewrite H3 Active_path_cc;move => [H6 H7].
    apply H1 in H6 as [H6 H8].
    by split;[ | rewrite last_cons].
  Qed.
  
  Lemma Active_path_rcrc: forall (p: seq EO) (eo1 eo2:  EO),
      Active_path W S (rcons (rcons p eo1) eo2) (Oe_h (head eo1 p)) (Oe_t eo2)
      <-> Active_path W S (rcons p eo1) (Oe_h (head eo1 p)) (Oe_t eo1) 
        /\ ActiveOe W S (eo1, eo2).
  Proof.
    elim => [ | eo p H1] eo1 eo2.
    split. by move => [_ [_ [H3 H4]]].  by move => [H1 H2]; split.
    rewrite !rcons_cons.
    rewrite Active_path_crc.
    split. 
    move => /Dpe_rev [H2 H3].
    by rewrite Active_path_crc.
    rewrite Active_path_crc. move => [H2 H3].
    by rewrite Dpe_rev. 
  Qed.

  Lemma Active_path_rcrc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y:A),
      Active_path W S (rcons (rcons p eo1) eo2) x y 
      -> x = (Oe_h (head eo1 p)) /\ y= (Oe_t eo2).
  Proof.
    elim => [ | eo p H1] eo1 eo2 x y; first by move => [H1 [H2 _]]; split.
    by rewrite !rcons_cons => /Active_path_crc_ht [H2 H3].
  Qed.

  Lemma Active_path_rcrc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y:A),
      Active_path W S (rcons (rcons p eo1) eo2) x y 
      -> ActiveOe W S (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_rcrc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_rcrc [_ H1].
  Qed.

  Lemma Active_path_rc_hto: forall (p: seq EO) (eo1:  EO) (x y:A),
      Active_path W S (rcons p eo1) x y ->
      x = Oe_h (head eo1 p) /\ y = Oe_t eo1 
      /\ Oedge S eo1 /\ Oedge S (head eo1 p).
  Proof.
    elim => [eo1 x y [H2 [H3 H4]] // | eo2 p _ eo1 x y H1]. 
    by pose proof Active_path_crc_ht H1 as [H2 H3];
    pose proof Active_path_crc_a H1 as [[H4 _] [_ [H8 _]]].
  Qed.
  
  Lemma Active_path_c_hto: forall (p: seq EO) (eo1:  EO) (x y:A),
      Active_path W S (eo1::p) x y -> 
      x = Oe_h eo1 /\ y = Oe_t (last eo1 p) 
      /\ Oedge S eo1 /\ Oedge S (last eo1 p).
  Proof.
    elim => [eo1 x y [H1 [H2 H3]] // | eo2 p _ eo1 x y H1]. 
    pose proof Active_path_cc_ht H1 as [H2 H3];
      pose proof Active_path_cc_a H1 as [H4 [H5 _]]. 
    rewrite lastI in H1.
    by pose proof Active_path_rc_hto H1 as [_ [_ [H8 _]]].
  Qed.
    
  Lemma Active_path_split: forall (p q: seq EO) (eop eoq:  EO) (x y: A),
      Active_path W S ((rcons p eop)++ eoq::q) x y
      -> Active_path W S (rcons p eop) x (Oe_t eop)
        /\ Active_path W S (eoq::q) (Oe_h eoq) y
        /\ ActiveOe W S (eop, eoq).
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
        move => /Active_path_crc /Deployment_path_cat [H6 /Dpe [H7 H8]].
        by rewrite rcons_cons Active_path_crc Active_path_crc.
  Qed.
  
  Lemma Active_path_cat: forall (p q: seq EO) (eop eoq :EO) (x y z:A),
      ActiveOe W S (eop, eoq)
      /\ Active_path W S (rcons p eop) x y 
      /\ Active_path W S (eoq::q) y z
      -> Active_path W S (rcons p eop++ eoq::q) x z.
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
      + move => _ H1 H2 H3.
        pose proof Active_path_crc_ht H2 as [H4 H5].
        have [H7 H8]: y = Oe_h eoq /\ z = Oe_t eoq by move: H3 => [H3 [H3' _]].
        rewrite -H4 -H5 Active_path_crc in H2.
        by rewrite cats1 -H4 H8 Active_path_crc Dpe_rev.
      + move => q1 eoq1 _ _ H2 H3 H4.
        pose proof Active_path_crc_ht H3 as [H5 H6].
        pose proof Active_path_crc_ht H4 as [H7 H8].
        rewrite -H5-H6 Active_path_crc in H3.
        rewrite -H7 -H8 Active_path_crc in H4.
        rewrite -rcons_cons -{1}cat_rcons -/rcons -rcons_cat.
        by rewrite -H5 -H8 Active_path_crc Deployment_path_cat Dpe_rev.
  Qed.

  Lemma Active_path_iff: forall (p q: seq EO) (eop eoq :EO) (x y z:A),
      ActiveOe W S (eop, eoq)
      /\ Active_path W S (rcons p eop) x y 
      /\ Active_path W S (eoq::q) y z
      <-> Active_path W S (rcons p eop++ eoq::q) x z /\ y= Oe_t eop.
  Proof.
    move => p q eop eoq x y z.
    split => [ [H1 [H2 H3]] | [H1 H2]].
    - pose proof Active_path_rc_hto H2 as [_ [H4 _]].
      by split;[apply Active_path_cat with y | ].
    - pose proof Active_path_split H1 as [H3 [H4 H5]].
      pose proof H5 as [_ [H7 [H8 _]]].
      by split;[ | split;[rewrite H2 | rewrite H2 H8]].
  Qed.
  
  Lemma Active_path_cat': forall (p q: seq EO) (x y z: A),
      (exists (p' q': seq EO), exists (eop eoq: EO),
          p = rcons p' eop /\ q = eoq::q' /\  ActiveOe W S (eop, eoq))
      /\ Active_path W S p x y 
      /\ Active_path W S q y z
      -> Active_path W S (p++q) x z.
  Proof.
    move => p q x y z [[p1 [q1 [eop [eoq [H1 [H2 H3]]]]]] [H4 H5]].
    by rewrite H1 H2; apply Active_path_cat with y; rewrite -H1 -H2.
  Qed.

  
  Section Active_path_unique. 

    (** * If there exists an active path from x to y there exists a walk from x to y
        we just prove that when a variable is repeated twice we can shorten the
        active path * to prove the general property, we have maybe to switch from
        Type to eqType to use unique * in seq ?  *)
    
    Lemma Oedge_Fset:  forall (u v:A), Oedge S (u,v, P) /\ S.*#W v -> S.*#W u.
    Proof.
      move => u v [H1 H2]. 
      move: H2 => [w [H2 H3]].
      have H4: (S `;` S.* ) (u,w) by (exists v).
      have H5:  (S.+ `<=` S.*)%classic by apply clos_t_clos_rt.
      have H6: S.* (u, w) by rewrite r_clos_rt_clos_t in H4 ;apply H5 in H4.
      by (exists w).
    Qed.
  
    Lemma Active_path_Fset:  forall (p: seq A) (x y: A),
        Active_path W S ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ S.*#W (last y p) -> S.*#W x. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        move => x y [[_ [_ H2]] H3].
        by apply Oedge_Fset with y.
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc /Oe_h.
        move => [[H1 H2] H3].
        have H4: S.*#W y by apply Hr with z.
        move: H2 => [H2 _].
        by apply Oedge_Fset with y.
    Qed.
    
    Lemma Active_path_Fset':  forall (p: seq A) (x y: A),
        Active_path W S ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ S.*#W (last y p) -> S.*#W y. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        by move => x y [[_ [_ H2]] H3].
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc /Oe_h.
        move => [[H1 H2] H3].
        have H4: S.*#W z by apply Hr with y.
        move: H2 => [_ [H2 _]].
        by apply Oedge_Fset with z.
    Qed.
    
    Lemma Active_path_shorten_L1: forall (p: seq EO) (x y z u v w: A),
        Active_path W S [::(x,y,P),(y,z,P) & (rcons (rcons p (u,v,N)) (v,w,N))] x w
        -> exists (q: seq A), Active_path W S (Lifto [::x,y & q] P) x (last y q) 
                        /\ (Fset S.* W) (last y q).
    Proof. 
      elim => [x y z u v w| ].
      - rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons Active_path_rcrc.
        have -> : [:: (x, y, P); (y, z, P)] = rcons [:: (x, y, P)]  (y, z, P) by [].
        rewrite Active_path_rcrc /head /Oe_h /Oe_t. 
        move => [[H1 [H'2 [H'3 [/ComposeOe_eq H'4 H'5]]]] [H3 [H4 [_ H6]]]].
        by (exists [::z]).
      - move => [[t s] o] p Hr x y z u v w.
        rewrite rcons_cons rcons_cons Active_path_cc /Oe_h.
        elim: p Hr.
        + move => Hr [H1 H2].
          move: (H1); rewrite Active_path_cc => [[_ [_ [_ [/ComposeOe_eq H3 _]]]]];
                                               rewrite <- H3 in *.
          elim: o H1 => [ /Hr [q [H1 H4]] | ].
          ++ exists [:: z & q].
             by rewrite Lifto_c Lifto_c Active_path_cc -Lifto_c /Oe_h /last_cons. 
          ++ exists [::z].
             move: H1 => /Active_path_cc [H1 [_ [_ [_ H7]]]]. 
             move: (H2) => [H2' [H2'' _]].
             rewrite !Lifto_c Active_path_cc -Lifto_c /Oe_h /last.
             by split.
        + move => [[a b] o2] p _ H1 H2.
          move: (H2);rewrite Active_path_cc rcons_cons rcons_cons /Oe_h;
            move => [[_ [_ [_ [/ComposeOe_eq H6 _]]]] _].
          rewrite <- H6 in *; clear H6.
          elim: o H2 => [[H2 H3] | ].
          ++ apply H1 in H2;move:H2 => [q H2].
             exists [::z].
             move: H2;rewrite Lifto_c => [[H2 H4]].
             rewrite /Lifto /Lift /pair_o.
             rewrite Active_path_cc /Oe_h last_cons /last.
             move: (H3) => [H5 [H6 _]].
             specialize Active_path_Fset' with q y z => H7.
             by split;[split | apply H7].
          ++ move => [H2 H3].
             pose proof H2 as H5.
             rewrite Active_path_cc in H2.
             rewrite Active_path_crc in H2.
             move: H2 => [H2 [_ [_ [_ H8]]]].
             exists [::z];rewrite last_cons /last.
             by split. 
    Qed.
    
    Lemma Active_path_shorten_L2: forall (p: seq EO) (x y z u w: A),
        Active_path W S [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> S.*#W y. 
    Proof. 
      move => p x y z u w H1.
      pose proof Active_path_shorten_L1 H1 as [q H2].
      rewrite Lifto_c in H2.
      by apply  Active_path_Fset' in H2.
    Qed.

    Lemma Active_path_shorten_L3: forall (p: seq EO) (x y z u w: A),
        Active_path W S [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> ActiveOe W S ((x,y,P), (y,w,N)).
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
    Lemma Active_path_shorten: forall (p: seq EO) (x y z u w: A) (o1 o2 o3 o4:O) ,
        Active_path W S [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe W S ((x,y,o1), (y,w,o4)).
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

  Variables (A: Type). 
  
  Definition Active (W: set A) (S: relation A) (x y:A) :=
   (exists (p: seq (Eo A O)), Active_path W S p x y).

  Definition D_separated  (W: set A) (S: relation A) (x y:A) := 
    ~(Active W S x y).
  
  Lemma Deployment_to_Active_path:
    forall (W: set A) (S: relation A) (p: seq A) (x y:A) (o:O),
      ( All W.^c p /\ Deployment_path (R_o S o) p x y )
        <-> Active_path W S (Lifto (x::(rcons p y)) o ) x y.
  Proof.
    split.
    + elim: p x y => [x y [_ H1] | x1 p H1 x y [/All_cons [H2 H'2] /Dpe [H3 H4]]];
                    first by split;[ | split]; elim: o H1 => H1.
      elim: p H1 H2 H4 => [ _ H2 H4 // | z p _ H2 H5 /Dpe [H6 H7] ];
                         first by elim: o H3 H4 => H3 H4.
      by apply Active_path_cc;split;[ apply H2 | ];elim: o H2 H3 H6 H7 => H2 H3 H6 H7.
    + elim: p x y;first (* size p = 1 *) by move => x y //= [_ [_ H]];split; elim: o H => H.
      move => z p H1 x y; rewrite Lift_o_cons;elim: p x y H1. 
             (* size p = 2 *)
      move => x y H1 /Active_path_cc [H2 [H3 [H4 [H5 H6]]]]. 
      elim: o H1 H2 H3 H4 H5 H6 => /= H1 H2 H3 H4 H5 H6.
      split. split. by []. by rewrite /setC in H6. by[].
      split. split. by []. by rewrite /setC in H6. by[].
      (* size p >= 2 *)
      move => t p H1 x y H2;rewrite Lift_o_cons;move => /Active_path_cc [/H2 [H3 H5] H4].
      split.
        rewrite All_cons;split;[ | move: H4 => [_ [_ [_ H4]]]].
        elim: o H1 H2 H4 H5 => H1 H2 H4 H5.
        by [].
        by [].
        elim: o H1 H2 H4 H5 => H1 H2 /= H4 H5.
        by [].
        by [].
        
        by rewrite Dpe;split;[move: H4 => [H4 _] | ];elim: o H1 H2 H4 H5 => H1 H2 H4 H5.
  Qed.
  
  Lemma Deployment_to_Active: forall (W: set A) (S: relation A) (p: seq A) (x y:A),
      (All W.^c p /\ Deployment_path S p x y) -> Active W S x y.
  Proof.
    move => W S p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) P); apply Deployment_to_Active_path;split.
  Qed.

  Lemma Deployment_inv_to_Active: forall (W: set A) (S: relation A) (p: seq A) (x y:A),
      (All W.^c p /\ Deployment_path S.-1 p x y) -> Active W S x y.
  Proof.
    move => W S p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) N); apply Deployment_to_Active_path;split.
  Qed.

End Active. 
