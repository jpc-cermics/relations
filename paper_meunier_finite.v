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
(* Some results for finite binary relations over a finType T                  *)
(******************************************************************************)

From HB Require Import structures.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order finset boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".
From RL Require Import  seq1 seq2 rel paper_meunier_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope. (* we can use %classic *)
Local Open Scope set_scope. (* we can use %SET *)

Definition fin_relation (T: finType) := {set (T * T)}.
Notation "{ 'relation' T }" := (fin_relation T) (format "{ 'relation'  T }"): type_scope.

Module leSet_choice.
  (** * an increasing selection lemma *)

  Section leSet_choice_sec.

    Context {T:choiceType} (R: relation T) (f : nat -> set T).
  Context (A0: (NotEmpty T)) (A1: forall n, (f n) [<= R] (f n.+1)).
    
    Definition R'' (p1: nat*T) := 
      [set p | ((p.2 \in (f p.1) /\ (p1.2 \in (f p1.1) /\ (p1.2 = p.2 \/ R (p1.2,p.2)))) 
               \/ ~(p1.2 \in (f p1.1))) /\ p.1 = p1.1.+1 ]%classic.

    #[local] Lemma Au1_P2 (p1: nat*T): exists p, p \in R'' p1.
    Proof. 
      move: A1 =>/(_ p1.1) Hp1.
      case H1: (p1.2 \in (f p1.1)).
      by move: (H1) => /Hp1 [s2 /= [? ?]];(exists (p1.1.+1,s2));
                      rewrite inE;split;[left|].
      by move: A0 H1 => [v0 ?] /negP ?;exists (p1.1.+1,v0);rewrite inE;split;[right|].
    Qed.

    #[local] Lemma Au1_G2: exists (j: nat*T -> nat*T),
      forall p, p.2 \in (f p.1) -> ((j p).2 \in (f (j p).1) /\ (p.2 = (j p).2 \/ R (p.2,(j p).2)))
                             /\ (j p).1 = p.1.+1.
    Proof.
      exists (fun t => xchoose (Au1_P2 t)).
      move => p1.
      have H0: xchoose (Au1_P2 p1) \in R'' p1 by apply: xchooseP.
      by move: H0 => /inP /= [[[? [_ ?]] _ // |? ? //] ?].
    Qed.

    #[local] Lemma Au1_G3:
      exists (k: nat -> (T -> T)),
      forall n, forall s, s \in (f n) -> ((k n s) \in (f n.+1) /\ (s = (k n s) \/ R (s,(k n s)))).
    Proof.
      move: Au1_G2 => [j H1].
      exists (fun k => (fun s => (j (k,s)).2)).
      move => n s.
      move: H1 => /(_ (n,s))/= H1. 
      move => /H1 /= [+ H2].
      by rewrite H2.
    Qed.
    
    #[local] Fixpoint kiter (k: nat-> (T -> T)) n :=
      if n is n'.+1 then (k n) \o kiter k n' else (k 0).

    #[local]Lemma kiterP1 (k: nat -> (T -> T)) (s:T) (A:set T):
      s\in A -> (forall n s', s' \in A -> (k n s') \in A) -> (forall n, (kiter k n s) \in A).
    Proof. by move => H0 Hn;elim => [| n Hr/=];apply: Hn. Qed.

    #[local] Lemma kiterP2 (k: nat -> (T -> T)) s:
      (forall n, forall s, s \in (f n) -> (k n s) \in (f n.+1) /\ (s = (k n s) \/ R (s,(k n s))))
      -> s \in (f 0)
      -> forall n, (kiter k n s) \in (f n.+1).
    Proof.
      move => Hn H0;elim;first by move: Hn => /(_ 0 s H0) [? _].
      by move => n' Hr;move: Hn => /(_ n'.+1 _ Hr) => -[? _].
    Qed.
    
    #[local] Lemma kiterP3 (k: nat -> (T -> T)) s:
      (forall n, forall s, s \in (f n) -> (k n s) \in (f n.+1) /\ (s = (k n s) \/ R (s,(k n s))))
      -> s \in (f 0)
      -> forall n, (kiter k n s) = (kiter k n.+1 s) \/ R ((kiter k n s),(kiter k n.+1 s)).
    Proof.
      move => Hn H0;elim.
      by move: (@kiterP2 k s Hn H0 0) => /Hn [_ ?].
      by move => n Hr;move: (@kiterP2 k s Hn H0 n.+1) => /Hn [_ ?].
    Qed.
    
    (* this is the main lemma *)
    Lemma choose_inc_seq:
      forall s, s\in (f 0) -> exists (h1: nat -> T), 
          (forall n, (h1 n) \in (f n.+1)) /\ (forall n, (h1 n)=(h1 n.+1) \/ R (h1 n, h1 n.+1)).
    Proof.
      move => s H0;move: Au1_G3 => [k H1].
      exists (fun n => (kiter k n s)).
      by split;[apply:  kiterP2| apply: kiterP3].
    Qed.
    
  End leSet_choice_sec.
  
End leSet_choice.

Export leSet_choice.


Definition Diff {T: Type} (SS: T*T) := ~ ( SS.1 = SS.2).
Definition Inc {T: Type} (SS: (set T)*(set T)) := SS.1 `<=` SS.2.
Definition strictInc {T: Type} (SS: (set T)*(set T)) :=
  SS.1 `<=` SS.2 /\ ~ ( SS.1 = SS.2).

Module seq_leSet_choice.

  Section seq_leSet.
    Context {T:choiceType} (U R: relation T) (S: set T) (Sq: seq (set T)).
    Context (A0: (NotEmpty T)).
    Context (A1: @allL (set T) (leSet R) Sq S S).
    Context (A2: @allL (set T) Diff Sq S S).
    (** en theorie c'est un [\in] *) 
    (** mais en pratique il faut montrer que c'est equivalent a *)
    Context (A3: forall n, preKernel U R (nth S (S::Sq) n)).
    
    Implicit Types (sq: seq T) (s: T).

    Definition f (n : nat) := nth S (S::Sq) (n %% size (S::Sq)).

    (** * properties of f *)
    
    Lemma f_periodic n: f (n + (size (S::Sq))) = f n.
    Proof. by rewrite /f (modnDr n (size (S::Sq))). Qed.

    Lemma f_periodic' k n: f (n + k*(size (S::Sq))) = f n.
    Proof.
      elim: k n => [n |k Hk n];first by rewrite mul0n addn0.
      rewrite mulSnr.
      have ->: n + (k * size (S :: Sq) + size (S :: Sq)) = 
                 (n + (k * size (S :: Sq)) + size (S :: Sq)) by lia.
      by rewrite f_periodic Hk. 
    Qed.

    Lemma f_tosmall n: f n = f (n %% size (S :: Sq)).
    Proof.
      by rewrite {1}(divn_eq n (size (S :: Sq))) addnC f_periodic'.
    Qed.
    
    Lemma f_inc n: (f n) [<= R] (f n.+1).
    Proof.
      move: (@allL_nth' (set T) (leSet R) Sq S S S) A1 => H1 /H1 /(_ (n %% size (S::Sq))) H2.
      have H3: n %% size (S :: Sq) < size (S::Sq)
        by rewrite  ltn_pmod.
      have: n %% size (S :: Sq) <= size (Sq) by [].
      move => /H2 H4.
      clear H1 H2.
      rewrite -rcons_cons nth_rcons H3 nth_rcons in H4.
      have H7: f (n %% size (S :: Sq)).+1 = f (n.+1)
        by rewrite -addn1 f_tosmall (modnDml n 1 (size (S :: Sq))) -f_tosmall addn1.
      have H9: f ( (n + 1) %% size (S :: Sq)) = f (n.+1)
        by rewrite -(f_tosmall (n + 1)) addn1.
      
      case H5: ((n %% size (S :: Sq)).+1 == size (S :: Sq)).
      + move: H5 => /eqP  H5.
        rewrite H5 ltnn eq_refl in H4.
        have H6: (f n) [<=R] S. by [].
        have -> : f(n.+1) = S
          by rewrite -H7 H5 -[size _]add0n f_periodic /f mod0n /=. 
        exact.
      + have H6: (n %% size (S :: Sq)).+1 < size (S :: Sq) by lia.
        rewrite H6 in H4. 
        have H8: (f n) [<=R] (nth S (S :: Sq) (n %% size (S :: Sq)).+1) 
                  by [].
        have H10: (n %% size (S :: Sq) + 1) %% size (S :: Sq) = (n %% size (S :: Sq) + 1)
          by apply: modn_small;lia.

        rewrite -addn1 -H10 in H8. 
        have H11: (f n) [<=R] (f (n %% size (S :: Sq) + 1)) by [].
        by rewrite addn1 H7 in H11.
    Qed.
    
    Lemma f_prekernel n: preKernel U R (f n).
    Proof. by move: (A3) => /(_ (n %% size (S :: Sq))) H1.
    Qed.
    
    (** * existence of j and aj such that aj \in (f j) and ~ (aj \in (f j.+1)) *)
    
    Lemma Inc_Tr : transitive (@Inc T).
    Proof. by move => A B C;apply: subset_trans. Qed.
    
    Lemma allL_Tr (Rset: relation (set T)): 
      0 < size Sq -> @allL (set T) Rset Sq S S -> transitive Rset 
      -> forall S', (S' \in Sq) -> (Rset (S, S')) /\ (Rset (S',S)).
    Proof.
      move => H1 H2 /Tclos_iff H3 S' H4. 
      move: (@allL_to_Tclos_left _ Rset Sq S S S' H4 H2). 
      move: (@allL_to_Tclos_right _ Rset Sq S S S' H4 H2). 
      by rewrite -H3.
    Qed.

    Lemma size_Sq_sp : 0 < size Sq.
    Proof.
      move: A2;contra;rewrite leqn0 => /eqP/size0nil H1.
      by move: A2;rewrite H1 allL0 inE notin_setE.  
    Qed.

    Lemma DiffE: 
      exists j, j <= (size Sq) 
           /\ exists aj, aj \in (nth S (S::(rcons Sq S)) j)
                   /\ ~( aj \in (nth S (S::(rcons Sq S)) j.+1)).
    Proof.
      move: size_Sq_sp => H1;move: A2;rewrite (@allL_nth' (set T) Diff Sq S S S).
      contra => H2.
      have H4: allL Inc Sq S S
        by rewrite (@allL_nth' (set T));move => j Hs b /inP/(H2 j Hs b)/inP.
      have H6: forall S', S' \in Sq -> S = S'.
      move => S' Hs;move: (@allL_Tr Inc H1 H4 Inc_Tr S' Hs).
      by rewrite eqEsubset.
      by exists 0;[lia | rewrite /= // nth_rcons H1;apply: H6;apply: mem_nth].
    Qed.
    
    Lemma DiffE': 
      exists j, j <= (size Sq) /\ exists aj, aj \in (f j) /\ ~( aj \in (f j.+1)).
    Proof.
      move: DiffE  => [j [H1 [aj]]].
      rewrite -rcons_cons 2!nth_rcons. 
      have ->: j < (size Sq).+1 by lia.
      case H2: (j.+1 < size (S :: Sq)).
      + move => HH.
        exists j. split. by [].
        exists aj.
        have H3: j %% size (S :: Sq) = j 
          by apply: modn_small; lia. 
        have H4: j.+1  %% size (S :: Sq) = j.+1
          by  apply: modn_small; lia. 
        move: HH. rewrite -{1}H3 -{1}H4 => -[H5 H6].
        by split.
      + have H1': j.+1 <= size (S::Sq). rewrite /=;lia.
        have H2': j.+1 = (size (S::Sq)). by lia.
        rewrite -H2' eq_refl => -[H3 H4].
        have H5: j %% size (S :: Sq) = j 
          by apply: modn_small;rewrite /=; lia. 
        exists j.
        split. by [].
        exists aj.
        rewrite -H5 in H3.
        split. by [].
        have H7: f (j %% size (S :: Sq)).+1 = f (j.+1)
          by rewrite -addn1 f_tosmall (modnDml j 1 (size (S :: Sq))) -f_tosmall addn1.
        have H9: f ( (j + 1) %% size (S :: Sq)) = f (j.+1)
          by rewrite -(f_tosmall (j + 1)) addn1.
        have HH : f(j.+1) = S.
        rewrite H2'.
        have H10: size (S :: Sq) = 0 + size (S :: Sq) by rewrite add0n.
        by rewrite H10 f_periodic /=.
        by rewrite HH.
    Qed.


    (** * using a j offset on f *)

    Lemma exists_g: exists g: nat -> set T, exists a,
        a \in (g 0) /\ ~ (a \in (g 1)) /\ forall n, ((g n) [<= R] (g n.+1) /\ preKernel U R (g n)).
    Proof.
      move: DiffE' => [j [_ [a [H1 H2]]]].
      move: f_prekernel => H4.
      exists (fun n => (f (j + n))); exists a.
      rewrite addn0 addn1.
      split;[exact | split;[exact |]].
      move => n;move: f_inc => /(_ (j + n));rewrite -addn1 => H3.
      by rewrite -addn1 addnA.
    Qed.
    
    Lemma exists_h : exists g: nat -> set T, exists h : nat -> T,
        (forall n, (g n) [<= R] (g n.+1) /\ preKernel U R (g n))
        /\ (forall n, (h n) \in (g n)) /\  ~ ((h 0) \in (g 1)).
    Proof.
      move: exists_g => [g [a [H1 [H2 H3]]]].
      exists g. 
      have H4: forall n, exists z : T, z \in g n
          by move => n;move: H3 => /(_ n) [_ [_ [_ /notempty_exists ?]]].
      exists (fun t => if (t== 0) then a else xchoose (H4 t)).
      split;first exact.
      split;last by rewrite eq_refl.
      move => n.
      case H5: (n == 0);first by move: H5 => /eqP ->.
      apply: xchooseP.
    Qed.

    Lemma seq_not (h: nat -> T) (A : set T): 
      ~ (h 0) \in A -> (exists k, (h k) \in A) -> exists j, ~ (h j) \in A /\ (h j.+1) \in A.
    Proof.
      move => H0 [k Hk];elim: k Hk => [// | n Hr Hl].
      by case H1: ((h n) \in A);[move: H1 => /Hr H1 |exists n;rewrite H1 Hl].
    Qed.

    Definition Ig (g: nat -> set T) := [set x | forall n, x \in (g n)]%classic.

    Lemma exists_hP (g: nat -> set T) ( h : nat -> T):
        (forall n, (g n) [<= R] (g n.+1) /\ preKernel U R (g n))
        /\ (forall n, (h n) \in (g n)) /\  ~ ((h 0) \in (g 1))
        -> ~(exists n, (h n) \in (Ig g)).
    Proof.
      move => [H1 [H2 H3]] /[dup] H4' [n' H4].
      have H5:  ~ ( h 0 \in (Ig g)) by move => /inP /(_ 1) HH.
      move: (seq_not H5 H4') => [j [H6 H7]].
      
      have H8:  h j.+1 \in (g j) by move: H7 => /inP/(_ j).
      have H9:  h j \in (g j) by apply: H2.
      have H10: ~ ( h j = h j.+1)
        by move => He;rewrite He in H6.
      move: H1 => /(_ j) [HRj [Hindep _]].
      move: Hindep => /(_ (h j) (h j.+1) H9 H8 H10) HnotR.
      move: HRj => /(_ (h j)) /= HRj.
      move: H9 => /HRj H9.
      
      rewrite /leSet /= in HRj.
      
      rewrite /RelIndep. 
    Admitted.
    
  End seq_leSet.

End seq_leSet_choice.

Export seq_leSet_choice.
(*
Section test.
  
  Context (T: choiceType) (S S1 S2: set T).
  Let Sq : seq (set T) := [:: S1;S2].
  
  Compute (nth S (S::Sq) (size Sq).+1).
  Compute (f S Sq 0).
  Compute (f S Sq 1).
  Compute (f S Sq 2).
  Compute (f S Sq 3).
  Compute (f S Sq (size (S::Sq))).

End test. 
*)

Section FinsetToClassical.
  (** * from {set T} to (set T) classicals_sets and finTYpe *) 
  (** * from fin_relation {set T} to relation {set T} *)
  
  Variable (T : finType).
  Implicit Types (A B : {set T}) (x: T).
  
  Definition set_of_fin A : set T := [set x | x \in A ].
  Notation "[ ':set:' A ]" := (set_of_fin A) (format "[ ':set:'  A ]").
  (* Coercion set_of_fin : set_of >-> set. *)
  
  (* reverse conversion which works for finType *)
  Definition fin_of_set (A: set T) : {set T} := [set x in A]. 
  Notation "[:fin: A ]" := (fin_of_set A).    
  
  Lemma in_set_of_fin A x: x \in [:set: A] <-> x \in A.
  Proof.  by rewrite /set_of_fin in_setE. Qed.
  
  Lemma in_fin_of_set (A: set T) x: x \in [:fin: A] <-> x \in A.
  Proof. by split => [H | H];[by rewrite inE in H | rewrite inE]. Qed.
  
  Lemma in_finP A x: reflect (x \in [:set: A]) (x \in A).
  Proof.  by apply: (iffP idP);move/in_set_of_fin. Qed.
  
  Lemma fin_setInvol (A: {set T}): [:fin: [:set: A]] = A.
  Proof. 
    apply/setP => x; case H1: (x \in A).
    + by move: H1 => /in_set_of_fin/in_fin_of_set ->.
    + move: H1 => /negP/in_set_of_fin/in_fin_of_set H1.
      by case H2: (x \in [:fin:[:set:A]]).
  Qed.
  
  Lemma set_finInvol (A: set T): [:set: [:fin: A]] = A.
  Proof. 
    rewrite predeqE => x. 
    split => [/inP/in_set_of_fin/in_fin_of_set/inP // | /inP H1].
    by rewrite -inP in_set_of_fin in_fin_of_set.
  Qed.
  
  Lemma set_of_fin0 : [:set: finset.set0] = set0.
  Proof.
    rewrite predeqE => x.
    split;rewrite -in_setE;last by rewrite in_set0.
    by move => /in_set_of_fin;rewrite finset.in_set0. 
  Qed.
  
  Lemma set_of_finU A B: 
    [:set: (A :|: B)] = [:set: A] `|` [:set: B].
  Proof.
    rewrite predeqE => x.
    rewrite -[set_of_fin _ x]in_setE -[(_ `|` _) x]in_setE.
    rewrite in_set_of_fin finset.in_setU.
    split.
    by move => /orP [? | ?];apply/inP;[left| right];apply/inP/in_finP.
    by move/inP => [/inP/in_finP -> |/inP/in_finP ->];[rewrite orTb| rewrite orbT].
  Qed.

  (** * aller voir 
  Definition in_set T (A : set T) : pred T := (fun x => `[<A x>]).
Canonical set_predType T := @PredType T (set T) (@in_set T).

Lemma in_setE T (A : set T) x : x \in A = A x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Definition inE := (inE, in_setE).
  *) 

  Lemma set_of_finI A B : 
    set_of_fin (A :&: B) = (set_of_fin A) `&` (set_of_fin B).
  Proof.
    rewrite predeqE => x.
    rewrite -[set_of_fin _ x]in_setE -[(_ `&` _) x]in_setE.
    rewrite in_set_of_fin finset.in_setI.
    split;last by move => /inP [/inP/in_finP -> /inP/in_finP ->].
    move => /andP [/in_finP ? /in_finP ?].
    by rewrite inP;split;by rewrite -inP.
  Qed.
  
  Lemma set_of_fin_inj: injective set_of_fin.
  Proof.
    move => A B;rewrite predeqE -setP => /[swap] x /(_ x) H1.
    case H2: (x \in A);first by move/in_finP: H2 => /inP/H1/inP/in_finP ->.
    case H3: (x \in B);last exact.
    by move/in_finP: H3 H2 => /inP/H1/inP/in_finP ->.
  Qed.

  Lemma set_of_sfin v:  [:set: [set v]] = [set v]%classic.
  Proof.
    rewrite predeqE => x. 
    split;first by rewrite -inP in_set_of_fin inE => /eqP ->.
    by move => ->;rewrite -inP in_set_of_fin inE.
  Qed.

  Lemma set_of_set0 :  [:set: finset.set0] = set0.
  Proof.
    by rewrite predeqE => x;split;[rewrite -inP in_set_of_fin inE |].
  Qed.

End FinsetToClassical.

Notation "[ ':set:' A ]" := (set_of_fin A) (format "[ ':set:'  A ]").
Notation "[ ':fin:' A ]" := (fin_of_set A) (format "[ ':fin:'  A ]").

Section Finite. 
  (** * for a finType we have ~ (iic_inj R) *)
  Variable (T : finType).
  Implicit Types (R U O D: relation T).

  Definition Sink R v := forall w, ~ R (v,w).
  Definition vRloop R v := forall w, R (v, w) -> R(w,v).
  
  Lemma Sink_to_Rloop R v: Sink R v -> vRloop R v.
  Proof. by move => + w H1 => /(_ w) H2. Qed.
  
  Lemma fin_not_iic_inj R: ~ (iic_inj R). 
  Proof. 
    move => [f [_ finj]].
    have inj_restrict : injective (fun i : 'I_(#|T|).+1 => f i)
      by move=> x y /finj Exy;apply/val_inj. 
    move: (leq_card _  inj_restrict) => H1.
    by rewrite card_ord ltnn in H1. 
  Qed.

  Lemma fin_not_iic R: (sporder R) -> ~ (iic R).
  Proof.
    move => /[dup] Hsp /sporder_antisym Ha.
    by move: (@fin_not_iic_inj R) => H1 /(sporder_iic_injective R Hsp)H2. 
  Qed.
  
  Lemma fin_rloop R: (NotEmpty T) -> (sporder R) -> exists v, (vRloop R v).
  Proof.
    move => Hne /[dup] /fin_not_iic Hniic /sporder_asym/AsymEq Has.
    by rewrite -Has in Hniic;move: (@notiic_rloop _ R Hne Hniic). 
  Qed.
  
  Lemma fin_sink R: (NotEmpty T) -> (sporder R) -> exists v, (Sink R v).
  Proof.
    move => Hne /[dup] /sporder_asym Has Hsp.
    move: (fin_rloop Hne Hsp) => [v H1].
    by exists v;move => w /[dup] Rvw /[dup] /Has nRwv /H1 Rwv. 
  Qed.
  
  Lemma fin_rloop1 R U: (NotEmpty T) -> (sporder R)
                      -> exists v, (v)_:#(R) `<=` U#_(v).
  Proof.
    move => Hne Hsp;move: (@fin_sink _ Hne Hsp) => [v Rl].
    exists v;move: Rl => /[swap] w /(_ w) Rl.
    by rewrite /Aset 2!Fset_s => ?.
  Qed.
  
  Lemma fin_rloop2 O R D:
    (NotEmpty T) -> (sporder O) -> R `<=` O -> exists v, (v)_:#(R) `<=` D#_(v).
  Proof.
    move => Hne Hsp Hinc;move: (@fin_rloop1 O D Hne Hsp) => [v H1].
    exists v.
    have H2: (v)_:#R `<=`  (v)_:#O 
      by rewrite /Aset;apply: Fset_inc;apply: inverseS.
    by apply: (@subset_trans T _ _ _ H2 H1). 
  Qed.
  
End Finite. 

Reserved Notation "A [:<=:] B" (at level 4, no associativity). 
Reserved Notation "A [:<= R :] S" (at level 4, no associativity). 

(** * leSet_fin: leSet version for finite sets and a finite relation on T *)
Definition leSet_fin (T: finType) (R : relation T) : {relation {set T}} := 
  [set AB : {set T}*{set T} | ([:set: AB.1], [:set: AB.2]) \in (@leSet T R) ].
Notation "A [:<= R :] B" := ((A,B) \in (leSet_fin R)).

Section leSet_fin_props.
  (** * reflection lemma for leSet_fin and leSet *)
  Variable (T : finType).
  Implicit Type (A B: {set T}). 

  Lemma leSet_finE (R : relation T) A B: 
    (A,B) \in (leSet_fin R) <->  (([:set: A], [:set: B]) \in (@leSet T R)).
  Proof. 
    rewrite -in_set_of_fin. 
    split => [/in_finP H1 | ?].
    by rewrite finset.in_set /= in H1.
    by rewrite in_set_of_fin finset.in_set.
  Qed.
  
  Lemma leSet_finP (R : relation T) A B: 
    reflect ((A,B) \in (leSet_fin R)) (([:set: A], [:set: B]) \in (@leSet T R)).
  Proof. by apply: (iffP idP);move/leSet_finE. Qed.
  
End leSet_fin_props.

Section RelIndep_fin. 
  (** * finite Independent sets  *)
  
  Variable (T : finType).
  Implicit Types (R : relation T) (S: {set T}).
  
  Definition RelIndep_fin R S: bool :=
  [forall x in S, forall y in S, (x == y) || ~~ ((x, y) \in R)].
  
  Local Lemma RelIndep_P R S:
    reflect (forall x y, x \in S -> y \in S -> x != y -> ~~ ((x,y) \in R))
      (RelIndep_fin R S).
  Proof.
    apply: (iffP forall_inP) => [H x y xS yS xy | H x xS].
    - move/(_ x xS)/forall_inP/(_ y yS): H => /orP [ |//].
      by rewrite (negbTE xy).
    - apply/forall_inP => y yS;apply/orP.
      by case: (eqVneq x y) => [-> | xy];[left | right; apply: H].
  Qed.

  Lemma RelIndepE R S: (RelIndep R [:set: S]) <-> (RelIndep_fin R S).
  Proof.
    split => [H1| /RelIndep_P H1 x y /in_finP xS /in_finP yS Hxy].
    + apply/RelIndep_P => x y /in_finP xS /in_finP yS Hxy.
      move: H1 => /(_ x y xS yS).
      contra => /inP H1. 
      split; last exact.
      by move: Hxy => /[swap] ->;rewrite eqxx.
    + have H2: x != y by apply/negP => /eqP H3.
      move: H1 => /(_ x y xS yS H2) H1 /inP H3.
      by rewrite H3 in H1.
  Qed.
  
  Lemma RelIndepP R S: 
    reflect (RelIndep R [:set: S]) (RelIndep_fin R S).
  Proof. by apply: (iffP idP);move/RelIndepE. Qed.
  
  Lemma RelIndep_fin_subset R (S S': {set T}) :
    S' \subset S -> RelIndep_fin R S -> RelIndep_fin R S'.
  Proof.
    move=> /fintype.subsetP SS' /RelIndepP H; apply/RelIndepP. 
    by apply: (RelIndep_Ir SS' H).
  Qed.
  
  Lemma RelIndep_fin0 R: RelIndep_fin R finset.set0.
  Proof. by apply/RelIndepP;rewrite set_of_set0;apply/RelIndep_set0. Qed.
         
  Lemma RelIndep_fin1 R a : RelIndep_fin R [set a].
  Proof. apply/RelIndepP;rewrite set_of_sfin;apply/RelIndep_set1. Qed.

  Lemma RelIndep_fin_Iv R S: RelIndep_fin R S <-> RelIndep_fin R^-1 S.
  Proof. 
    by split;rewrite -RelIndepE;move => /RelIndep_Iv/RelIndepP;
                                       [| rewrite inverseK].
  Qed.

  Lemma RelIndep_fin_IE R S: RelIndep_fin R S = RelIndep_fin R^-1 S.
  Proof. 
    case H1 : (RelIndep_fin R S).
    by move: H1 => /RelIndepP/RelIndep_Iv/RelIndepP ->.
    move: H1 => /RelIndepP. 
    contra. 
    rewrite eq_sym eqbF_neg negbK -RelIndepE => /RelIndep_Iv.
    by rewrite inverseK.
  Qed.
  
End RelIndep_fin. 

#[local] Set Warnings "-projection-no-head-constant,-redundant-canonical-projection".

Section SubSetPType.
  (** * defining a new finType isomorphic to {S : {set T} | P S} *)
  Variables (T : finType)  (P : pred {set T}).
  Record setP_type := SetP { setP_val : {set T}; setP_proof : P setP_val }.

  (* subType structure *)
  HB.instance Definition _ := [isSub for setP_val].
  HB.instance Definition _ := [Finite of setP_type by <:].
  (* explicit coercion *)
  Coercion setP_val : setP_type  >-> set_of. 
  
End SubSetPType.
#[local] Set Warnings "+projection-no-head-constant,+redundant-canonical-projection".

Module fin_Maximal.
  (** * There's always a maximal element in a finite nonempty poset *)
  (** we consider here the simplest case *)
  (** and give a proof by recursion 
      we first give the proof for a sequence(seq T) 
      and then use mem_enum to have a finite sequence 
      representation of a finite set. *)
  (** Note that this proof is valid for R: relation T 
      R: {relation T} is not requested *)

  Section fin_maximal.
    
  Variables (T: finType).
  Implicit Types (m : T) (s : seq T) (R: relation T).

  Definition seq_maximal m s R : Prop :=
    forall x, x \in s -> R (m,x) -> m = x.

  Definition maximal m R: Prop := forall x,  R (m,x) -> m = x.
  
  #[local] Lemma seq_has_maximal_step (s : seq T) (h : T) R:
    porder R -> (exists m, m \in s /\ seq_maximal m s R) \/  s = [::]
    ->  exists m, m \in h :: s /\ seq_maximal m (h :: s) R.
  Proof.
    move => [Hr Ha Ht] [[m [Hm Hmax]] | ->].
    (* s is non-empty with maximal m *)
    + move: (EM (R (m,h))) => [Rmh | hle_m].
      ++ (* R (m,h)  *)
        exists h; split;first by rewrite in_cons eqxx.
        move=> x; rewrite in_cons => /orP [/eqP -> // | Hxs] Hlt.
        have Rmx: R (m,x) by apply: (Ht m h x Rmh Hlt).
        have meqx: m = x by apply: (Hmax x Hxs Rmx).
        move: Rmh;rewrite meqx => Rxh.
        rewrite /antisymmetric in Ha.
        by move: (Ha h x Hlt Rxh).
      ++ (* ~ (R (m,h)) *)      
        exists m; split;first by rewrite in_cons;rewrite Hm orbT. 
        move => x; rewrite in_cons => /orP [/eqP -> ? //| H1 H2].
        by move: (Hmax x H1 H2).
    + (exists h);split;first by rewrite mem_seq1.
      by move => x; rewrite mem_seq1 => /eqP ->.
  Qed.
  
  #[local] Lemma seq_has_maximal R: 
    porder R -> forall s, ~ (s = [::]) -> (exists m, m \in s /\ seq_maximal m s R).
  Proof.
    move => ?;elim => [// | a s Hr _ ].
    apply: seq_has_maximal_step;first by [].
    by move: (EM (s = [::])) => [-> | /Hr ?];[right | left].
  Qed.    
  
  Lemma has_maximal R: porder R -> (exists x, x\in T) -> (exists m, maximal m R).
  Proof.
    move => Hp [x -];rewrite -mem_enum => Hx.
    have H2: ~ (enum T = [::]) by move: Hx => /[swap] ->.
    move: Hp => /seq_has_maximal/(_ (enum T) H2) [m [Hm HM]]. 
    exists m;move: HM => /[swap] x' /(_ x') HM H5.
    by apply: HM;[rewrite  mem_enum |].
  Qed.
  
  End fin_maximal.

End fin_Maximal.

Export fin_Maximal.

Section SubSetPType_order.
  (** * When O is a sporder then [:<=: O] restricted to M-independent sets is a porder *)
  
  Context (T : finType).
  Implicit Types (O R M: relation T) (S: {set T}).
  
  Definition setRM_fin R M S := (asbool ([:set: S]:#R `<=` M#([:set: S]))).
  
  Definition prekernel_fin O R M: pred {set T} := 
    fun S => (RelIndep_fin O S) && ((setRM_fin R M S) && (([:set: S]) != set0)).
  
  (** * setIndep doit s'appeller  prekernelfinType ? *)
  Definition setIndep O R M := setP_type (prekernel_fin O R M). 

  Lemma prekernel_fin_Iv O R M S: 
    prekernel_fin O R M S = prekernel_fin O^-1 R M S.
  Proof.
    by rewrite /prekernel_fin RelIndep_fin_IE.
  Qed.
  
  Lemma prekernelE O R M S: 
    prekernel_fin O R M S <->
    RelIndep O [:set: S] /\ setRM R M [:set: S] /\ [:set: S] != set0.
  Proof.
    split.
    by move => /andP [/RelIndepE H1 /andP [/asboolP H2 H3]].
    move => [H1 [H2 H3]].
    apply/andP;rewrite -RelIndepE H3 andbT.
    split;first exact.
    by  apply/asboolP.
  Qed.
  
  Lemma prekernel_notempty O R M 
    (A1: NotEmpty T) (At: sporder O^-1) (Au: R `<=` O^-1):
    exists v, prekernel_fin O R M [set v].
  Proof.
    move: (At) (@fin_not_iic_inj T O^-1) => /[dup] Hsp [H1 /[dup] Ht /Tclos_iff H2] H3.
    have H4: ~(iic O^-1)
      by move => /(@sporder_iic_injective _ _ At ) ?.
    move: (@fin_rloop2 T O^-1 R M A1 At Au) => [v H6].
    exists v.
    apply/andP.
    split;first by apply: RelIndep_fin1.
    apply/andP.
    split;first by apply/asboolP;rewrite /setRM_fin set_of_sfin.
    rewrite set_of_sfin.
    apply/asboolP => H.
    have H7: [set v]%classic v by exact.
    by rewrite H in H7.
  Qed.
  
  Lemma leSet2_porder O R M :
    sporder O -> 
    @porder (setIndep O R M) 
      [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic.
  Proof.
    move => H_sp.
    split => [A /= | A B /= Ha Hb | A B C /= Ha Hb].
    + (* reflexive *)  apply: le_refl.
    + (* antisymmetric *) 
      move: (valP A) => /andP[/RelIndepE Pa _].
      move: (valP B) => /andP[/RelIndepE Pb _].
      move: (le_antisym_if_sp H_sp Pa Pb Ha Hb) => /set_of_fin_inj/eqP H5.
      by apply/eqP;rewrite -val_eqE.
    + (* transitive *)
      move: H_sp => [_ H1];move: (le_trans_if_tr H1) => H2. 
      by move: H2 => /(_ [:set:\val A] [:set:\val B] [:set:\val C] Ha Hb) H2.
  Qed.
  
  Lemma exists_setIndep O R M 
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1):
      (exists x : setIndep O R M, x \in {: (setIndep O R M)}).
  Proof.
    move: Asp => /sporder_inv Asp.
    move: (@prekernel_notempty O R M A1 Asp Au) => [v Pv].
    by exists (SetP Pv).
  Qed.
  
  Lemma Maximal_fin O R M 
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1):
    exists (m: (setIndep O R M)),
      @maximal (setIndep O R M) m [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic.
  Proof.
    move: (Asp) => /sporder_inv Asp'. 
    move: (leSet2_porder R M Asp) => po.
    pose proof (@exists_setIndep O R M A1 Asp Au) as Hne.
    by move: (@has_maximal (setIndep O R M) 
            [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic
         po Hne).
  Qed.
  
  Lemma Maximal O R M
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1):
    exists S, prekernel_fin O R M S /\ (forall U, prekernel_fin O R M U ->
                                    [:set: S] [<= O] [:set: U] -> S = U).
  Proof.
    move: (@Maximal_fin O R M A1 Asp Au)  => [S H3].
    exists S;move: (valP S) => Pr;split; first exact.
    move => U H4; move: H3 => /(_ (SetP H4)) H3.
    by move => /H3/eqP ?;apply/eqP. 
  Qed.

End SubSetPType_order.

  
Definition Cyclic {T: Type} (R: relation T):= exists sq, exists s, allL R sq s s.

Section Acyclicity.
  (** The case of acyclicity **)
  
  Lemma CyclicE (T: Type) (R: relation T): 
    Cyclic R <-> exists s, R.+ (s,s).
  Proof.
    split => [ [sq [s +]] | [ s +]].
    by move: (@allL_to_Tclos T R sq s s) => H1 /H1 H2;exists s.
    by rewrite (TCP R) /= => -[sp H1];exists sp;exists s.
  Qed.
  
  Context (T : eqType).
  Implicit Types (O R M: relation T) (S: set T).

  
  Lemma step T' (sq: seq T') s (S : set T'): 
    ~(nth s sq 0) \in S -> (exists k, (nth s sq k) \in S )
    -> exists j,  ~(nth s sq j) \in S /\ (nth s sq j.+1) \in S.
  Proof.
    move => H0 [k Hk];elim: k Hk => [// | n Hr Hl].
    by case H1: (nth s sq n \in S);[move: H1 => /Hr H1 |exists n;rewrite H1 Hl].
  Qed.
  (* 
  Variables (T': eqType) (x1 s v z a b c d: T').
  
  Compute (head z[:: a;b ;c])::(rcons (behead (rot 1 (x1::[:: a;b ;c])))
                                (head z[:: a;b ;c])).

  Compute (head z [::])::(rcons (behead (rot 1 (x1::[:: a;b ;c])))
                                (head z[:: a;b ;c])).
  
  Definition sq := [:: a].

  Compute (nth v (rcons sq s) 0, nth v (rcons sq s) 1). 
  Compute (head v sq, nth v (rcons (behead (rcons sq s)) (head v sq)) 0).

  Definition sq' := [:: a;b].

  Compute (nth v (rcons sq' s) 0, nth v (rcons sq' s) 1). 
  Compute (head v sq', nth v (rcons (behead (rcons sq' s)) (head v sq')) 0).
  *) 

  (* apply rot1 on (s::sq) *)
  Definition circrot {T': eqType} (ssq: T'*seq T') := locked
    (head (ssq.1) (ssq.2), (behead (rot 1 (ssq.1::ssq.2)))).

  (* 
  Variables (T': eqType) (a b c d: T').
  Definition ssq: T'*seq T' := (a, [:: b;c;d]).

  Compute (ssq.1, (circrot ssq)). 
  Compute (nth ssq.1 (circrot ssq).2 (size ssq.2).-1).
  Compute (nth ssq.1 ssq.2 (size ssq.2)).
  *)

  Lemma circrotE {T': eqType} (ssq: T'*seq T'):
    circrot ssq = (head (ssq.1) (ssq.2), (behead (rot 1 (ssq.1::ssq.2)))).
  Proof. by rewrite /circrot -lock. Qed.
  
  Lemma nth_circrot (T': eqType) (ssq: T'*seq T') (v: T'):
    forall j, j.+1 < size ssq.2 -> (nth v (circrot ssq).2 j) = (nth v ssq.2 j.+1).
  Proof.
    by move => j Hj;rewrite circrotE /= rot1_cons nth_behead nth_rcons Hj. 
  Qed.

  Lemma nth_circrot_l (T': eqType) (ssq: T'*seq T') (v: T'):
    0 < (size ssq.2) -> (nth v (circrot ssq).2 (size ssq.2).-1) = ssq.1.
  Proof.
    move => Hsp.
    have H0: (size ssq.2) = (size ssq.2).-1.+1 by lia.
    by rewrite circrotE /= rot1_cons nth_behead nth_rcons -H0 ltnn eq_refl. 
  Qed.
    
  (** * plus rapide un seul lemme *)
  Lemma nth_circrot' (T': eqType) (ssq: T'*seq T') :
    forall j, j.+1 <= size ssq.2 -> (nth ssq.1 (circrot ssq).2 j) = (nth ssq.1 ssq.2 j.+1).
  Proof.
    move => j Hj.
    rewrite circrotE /= rot1_cons nth_behead nth_rcons. 
    case H1: (j.+1 < size ssq.2);first exact.
    have H0: (size ssq.2) = (size ssq.2).-1.+1 by lia.
    have ->: (j.+1 = size ssq.2) by lia.
    by rewrite eq_refl nth_default. 
  Qed.
  
  Lemma nth_circrot_0 (T': eqType) (ssq: T'*seq T') :
    (circrot ssq).1 = (nth ssq.1 ssq.2 0).
  Proof.  by rewrite circrotE /=. Qed.

  Lemma size_circrot (T': eqType) (ssq: T'*seq T'):
    size (circrot ssq).2 = size ssq.2.
  Proof. by rewrite circrotE /= size_behead size_rot /=. Qed.
    
  Lemma nth_rcons_circrot (T': eqType) (ssq: T'*seq T') n:
    0 < n -> n <= (size ssq.2)
    -> (nth ssq.1 ((circrot ssq).1 :: (rcons (circrot ssq).2 (circrot ssq).1)) n) 
      = nth ssq.1 ssq.2 n.
  Proof. 
    move => Hsp Hn.
    have H0: n < (size ssq.2).+1 by lia.
    rewrite -rcons_cons nth_rcons nth_circrot_0 /= size_circrot H0.
    have H2: n = n.-1.+1 by lia.
    rewrite H2 /=.
    move: (@nth_circrot' T' ssq n.-1).
    by rewrite -H2 Hn => ->.
  Qed.
  
  Lemma nth_rcons_circrot0 (T': eqType) (ssq: T'*seq T') :
    (nth ssq.1 ((circrot ssq).1 :: (rcons (circrot ssq).2) (circrot ssq).1) 0) 
      = nth ssq.1 ssq.2 0.
  Proof. by rewrite /= nth_circrot_0. Qed.
    
  Lemma allL_rot_s1 (T': eqType) (sq: seq T') (s v: T'): 
    0 < size sq -> 
    (nth v (rcons sq s) 0, nth v (rcons sq s) 1)
    = (head v sq, nth v (rcons (behead (rcons sq s)) (head v sq)) 0).
  Proof.
    move => H1;rewrite nth_rcons H1 /= nth_rcons. 
    case H2: (size sq == 1);first  by move: H2 => /eqP/seq_1 [x' ->] /=.
    have H3: 1 < size sq by lia.
    by move: (H3) => /seq_cc [sq' [x' [y' ->]]] /=.
  Qed.
  
  Lemma allL_rot (T': eqType) (R: relation T') (sq: seq T') (s v: T'): 
    0 < size (sq) -> allL R sq s s -> 
    allL R (behead (rot 1 (s::sq))) (head s sq) (head s sq).
  Proof.
    move => H1 H2.
    rewrite (@allL_nth' T' R _ _ _ s) rot1_cons size_behead size_rcons /=.
    move => n Hn.
    have H0': 0 <= size sq by lia.
    (* we keep assumption for n= 0 and n.+1 *)
    move: H2;rewrite (@allL_nth' T' R _ _ _ s)  => /[dup] /(_ 0 H0') H0 /(_ n.+1) H3.
    move: H0;rewrite /= nth_rcons H1 => H0.
    
    case H4: (n == 0). 
    by move: H4 H3 (H1) => /eqP -> /= H3 /H3 H1';rewrite -allL_rot_s1. 
    case H5: (n < size sq);last first.
    + have -> : n = size sq by lia.
      rewrite nth_rcons size_behead size_rcons ltnn eq_refl /=.
      rewrite -rcons_cons nth_rcons /= size_behead size_rcons /=.         
      rewrite ltnSn /= -headI nth_rcons ltnn eq_refl /=.
      exact. 
    + move: (H5) => /H3 /=.
      rewrite  2!nth_rcons H5 /=.
      case H6: (n.+1 < size sq).
      ++ rewrite -rcons_cons 2!nth_rcons /= size_behead size_rcons /=.
         have ->: n < (size sq).+1 by lia.
         by rewrite H5 -headI nth_rcons H5 nth_behead nth_rcons H6.
         have H7 : n.+1 == size sq by lia.
         rewrite H7 /= nth_rcons !size_behead size_rcons /= H5.
         rewrite -rcons_cons nth_behead 2!nth_rcons /= size_behead size_rcons /=.
         rewrite H6 H7.
         have ->:n < (size sq).+1 by lia.
         by rewrite -headI nth_rcons H5.
  Qed.
    
  
  (** * without loss of generality
  Lemma DiffE' (Sq: seq (set T)) S: 
    0 < size Sq 
    -> @allL (set T) Diff Sq S S 
    -> exists a0, a0 \in (nth S (S::Sq) 0) /\ ~( a0 \in (nth S (S::Sq) 1)).
  Proof.

  *) 

  Lemma choice (T': Type) (R: relation T') (S1 S2: set T'):
    forall (x: S1), exists (y: S2), R (val x,val y).
  Admitted.
  
  Lemma Sq_choice (T': Type) (R: relation T') (Sq: seq (set T')) (S: set T'): 
    @allL (set T') (leSet R) Sq S S
    -> forall j, j <= (size Sq) -> 
           (exists (f : T' -> T' ),
               (forall x, x \in (nth S (S::(rcons Sq S)) j) -> R (x, f x))).
  Proof.
  Admitted.
  

End Acyclicity.

Section ChampetierExt_Theorem.

  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T) (X: {set T}).
  
  Context (A2 : Assumption2 R) (A6 : Assumption6 B (M R B) O) 
    (A7 : Assumption7 R B (M R B)) (A8 : Assumption8 R B (M R B)).
  Context (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1).
  Context (Apk : forall X , RelIndep O [:set: X] <->  RelIndep (M R B) [:set: X]).
  
  Lemma prekernelP S: 
    (prekernel_fin O R (M R B) S) <-> preKernel R (M R B) [:set: S].
  Proof. by rewrite (@prekernelE T O R (M R B) S) Apk. Qed.
  
  Lemma maximal_mabsorbant S:
    (prekernel_fin O R (M R B) S) /\ (forall U, prekernel_fin O R (M R B) U ->
                                  [:set: S] [<= O] [:set: U] -> S = U)
    -> Mabsorbant R B [:set: S].
  Proof.
    contra; move => H1 /prekernelP Hpk.
    have H3: Non_Mabsorbant R B [:set: S]
      by move: H1 => [y H1] H3;exists y;rewrite inP;
                    split;[ |rewrite notin_setE in H3;rewrite inP].
    
    move: (@extend T R B O [:set: S] A2 A6 A7 A8 Hpk H3) 
        => [S' [Hpre [H7 [x' [H8 H9]]]]].
    exists [:fin: S'].
    by rewrite prekernelP set_finInvol.
    split;first by  rewrite set_finInvol.
    apply/negP => /eqP Heq.
    by rewrite Heq set_finInvol in H9.
  Qed.
  
  Lemma Kernel_ChampetierExt: 
    exists (S : {set T}), RelIndep (M R B) [:set: S] /\ Mabsorbant R B [:set: S].
  Proof.
    (* There exist a maximal set *)
    move: (@Maximal T O R (M R B) A1 Asp Au) => [S Hm].
    move: Hm => /[dup] /maximal_mabsorbant Ma [/prekernelP [Hpk _] _].
    by (exists S).
  Qed.

End ChampetierExt_Theorem.

Section simpleGraph. 

  Context (T : Type).
  Implicit Types (G D O Re: relation T).

  Definition simpleGraph G := symmetric G /\ irreflexive G.
  Definition Direction G D := D `|` D^-1 = G. 
  Definition Orientation G O := Direction G O /\ asymmetric O.

  Lemma RelIndep_sym Re S: (RelIndep Re S) <-> (RelIndep (Re `|` Re^-1) S).
  Proof.
    split => [+ x y Hx Hy Hne|+ x y Hx Hy Hne].
    have Hne': ~ (y = x). by move => H1;rewrite H1 in Hne.
    by move => /[dup] /(_ y x Hy Hx Hne') H1 /(_ x y Hx Hy Hne) H2 [H3 | H3].
    by move => /(_ x y Hx Hy Hne);contra => ?;left.
  Qed.
  
  Lemma direction_relIndep G D S: 
    Direction G D -> (RelIndep D S <-> RelIndep G S).
  Proof. by move => Hd;rewrite RelIndep_sym Hd. Qed.

  Lemma orientation_relIndep G D S: 
    Orientation G D -> (RelIndep D S <-> RelIndep G S).
  Proof. by move => [Hd _];rewrite RelIndep_sym Hd. Qed.
  
End simpleGraph.

Section Champ.

  Context (T : finType) (G D O: relation T).
  
  Context (Asg: simpleGraph G).
  Context (Ao: Orientation G O).
  Context (Ad: Direction G D).

  Definition R := D `&` O^-1.
  Definition B := D `&` O.

  Context 
    (A1: NotEmpty T) 
    (Asp: sporder O)
    (A6 : Assumption6 B (M R B) O) 
    (A7 : Assumption7 R B (M R B))
    (A8 : Assumption8 R B (M R B)).
  
  Lemma RB: (M R B) = D.
  Proof.
    have H1:  R `<=` D. by rewrite /R;apply: subIsetl.
    have H2:  B `<=` D. by rewrite /R;apply: subIsetl.
    rewrite predeqE => -[x y].
    split => [[/H2 H0 | /H1 H0] // | H3].
    case H4: ((x,y) \in O).
    + move: H4 => /inP H4.
      ++ case H5: ((y,x) \in O).
         move: H5 => /inP H5.
         by right;split.
         by left;split.
    + case H5: ((y,x) \in O).
      move: H5 => /inP H5.
      by right;split.
      (** (x, y) \in O) = false /\ (y, x) \in O) = false *)
      (** is not possible *)
      have H6: D `|` D^-1 = G by [].
      have H7: O `|` O^-1 = G by move: (Ao) => [Do _].
      have H8:  D `|` D^-1 = O `|` O^-1. by rewrite H6 H7. 
      have [/inP //| H9]: (O `|` O^-1) (x,y) by rewrite -H8; left.
      by rewrite H4.
      have: (y,x) \in O by rewrite inP.  
      by rewrite H5.
  Qed.
  
  Lemma AspIv: sporder O^-1.
  Proof. by apply: sporder_inv. Qed.
  
  Lemma Au:  R `<=` O^-1. 
  Proof. by rewrite /R;apply: subIsetr. Qed.

  Lemma Onoticc: ~ (iic  O^-1). 
  Proof. by apply: (@fin_not_iic _ O^-1 AspIv). Qed.
  
  Lemma Rnotiic: ~ (iic R).
  Proof. by move: Onoticc => ? /(@iic_sub T R O^-1 (Au)) ?. Qed.

  Lemma Apk:  forall X , RelIndep O [:set: X] <->  RelIndep (M R B) [:set: X].
  Proof. move => X. rewrite RB. 
         rewrite (@direction_relIndep T G D [:set: X] Ad).
         by rewrite (@orientation_relIndep T G O [:set: X] Ao).
  Qed.
  
  Lemma Rsym : asymmetric R.
  Proof.
    move => x y /Au H1 /Au H2.
    by move: H1 Ao => + [_ /(_ x y) Ha] => /Ha H3.
  Qed.
  
  Lemma haveA2 : ~ (iic (Asym R)).
    move: Rsym => /AsymEq ->;apply: Rnotiic.
  Qed.

  Lemma haveA6 : forall x y : T, B (x, y) /\ ~ (M R B) (y, x) -> O (x, y).
  Proof. by move => x y [[_ H1] _]. Qed.

  Lemma Kernel_Champetier: 
    exists (S : {set T}), RelIndep (M R B) [:set: S] /\ Mabsorbant R B [:set: S].
  Proof.
    by pose proof (@Kernel_ChampetierExt T O R B (haveA2) (haveA6)
                     A7 A8 A1 Asp (Au) (Apk)).
  Qed.
  
End Champ.

Section test.

Variable T : Type.
Variable s : seq T.   (* s = [:: x1; x2; ...; xk] *)
Variable x1: T.
Hypothesis Hs : ~ (s = [::]).

Definition f (n : nat) : T := nth x1 s (n %% size s).

Lemma f_periodic n : f (n + (size s)) = f n.
Proof. by rewrite /f (modnDr n (size s)). Qed.
  
End test.

