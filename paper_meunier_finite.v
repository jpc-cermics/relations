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

Definition Inc {T: Type} (SS: (set T)*(set T)) := SS.1 `<=` SS.2.
Definition strictInc {T: Type} (SS: (set T)*(set T)) :=
  SS.1 `<=` SS.2 /\ ~ ( SS.1 = SS.2).
Notation Inc' := <=%O.

Module utilities.
  Section utilities.
    Context {T:choiceType} (f: nat -> T) (S: set T) (R: relation T).
    
    Lemma f2allL: 
      (forall n, R (f(n), f(n.+1)))
      -> forall n m, allL R (mkseq (fun i => f (n + i+1)) m) (f n) (f (n+m+1)).
    Proof.
      move => H0 n m.
      elim: m n H0 => [n /=| n' Hr n H0].
      by rewrite addn0 addn1 /mkseq/= allL0 inE. 
      rewrite mkseqS allL_rc.
      have ->: (n + (n'.+1) + 1) = (n + n' + 1).+1 by lia. 
      by apply/andP;split;[rewrite inE|apply: Hr].
    Qed.
    
    Lemma f2in: (forall n, f(n) \in S)
                -> forall n m,  ((f n)::(mkseq (fun i => f (n + i+1)) m)) [\in] S.
    Proof.
      move => H0 n m.
      elim: m n H0 => [n /= ?| n' Hr n H0];first by rewrite andbT.
      rewrite mkseqS -rcons_cons allset_rcons.  
      split. by apply: Hr. by rewrite -inE.
    Qed.
    
    Lemma f2allL': 
      (forall n m, allL R (mkseq (fun i => f (n + i+1)) m) (f n) (f (n+m+1)))
      -> (forall n, R (f(n), f(n.+1))).
    Proof.
      by move => + n => /(_ n 0);rewrite addn0 allL0 inE addn1.
    Qed.

  End utilities.
End utilities.
Export utilities.

Module injectivity.
  Section injectivity.
  
  Lemma not_injective_prop (T: Type) (h: nat -> T):
    ~ (injective h) ->exists n p, h n = h (n + p.+1).
  Proof. 
    move => Hinj.
    have [n [n' [Hd Hh]]]: exists n n', n <> n' /\ h n = h n'.
    {
      apply: contrapT => Hc.
      apply: Hinj => k k' Ehkk'.
      apply: contrapT => Nkk'.
      by apply: Hc;exists k, k'.
    }
    have Hkk' k k': k < k' -> exists p, k'= k + p.+1.
    {
      elim: k' => [//| k' Hr H5].
      case H6: (k == k').
      by move: H6 => /eqP ->;(exists 0);rewrite addn1.
      by (have /Hr [p ->]: k < k' by lia);exists p.+1;lia. 
    }
    case H6: (n < n').
    by move: H6 => /Hkk' [p H6];exists n, p;rewrite H6 in Hh.
    have H7: (n' < n) by lia.
    by move: H7 => /Hkk' [p H7];exists n',p;rewrite -H7 Hh. 
  Qed.

  Context {T:finType}.

  Lemma fin_codomain_prop (h: nat -> T): exists n p, h n = h (n + p.+1).
  Proof.
    apply: not_injective_prop.
    (** * proving now that h is not injective *)
    move => hinj.
    have inj_restrict : injective (fun i : 'I_(#|T|).+1 => h i)
      by move=> x y /hinj Exy;apply/val_inj. 
    move: (leq_card _  inj_restrict) => H1.
    by rewrite card_ord ltnn in H1. 
  Qed.
  
  End injectivity.
End injectivity.
Export injectivity(fin_codomain_prop,not_injective_prop).

Module setT_injectivity.
  Section setT_injectivity.
    (** * (h : nat -> set T) not injective when T is finType *)
    Context {T:finType}.
    Local Definition encode1 (S : set T) : {ffun T -> bool} :=
      [ffun x => `[< S x >] ].
  
    Local Lemma encode1_inj : injective encode1.
    Proof.
      move=> S S' eqSS'.
      move: (@ffunP T (fun _ => bool) (encode1 S) (encode1 S')) => HffunP.
      have {}HffunP := HffunP.2 eqSS'.
      rewrite predeqE => x.
      have := HffunP x.
      rewrite /encode1 !ffunE /= => He. 
      split => [Ha| Ha].
      by move: Ha => /asboolP;rewrite He => /asboolP.
      by move: Ha => /asboolP;rewrite -He => /asboolP.
    Qed.
    
    Local Lemma not_injective1_h (h : nat -> set T) : ~ injective h.
    Proof.
      move=> h_inj.
      pose N := #|{ffun T -> bool}|.
      pose g : 'I_N.+1 -> {ffun T -> bool} := fun i => encode1 (h i).
      have g_inj : injective g.
      by move=> i j /encode1_inj /h_inj eqij; exact/val_inj.
      have := leq_card g g_inj.
      by rewrite card_ord ltnn.
    Qed.
    
    Lemma set_fin_codomain_prop (h: nat -> set T): exists n p, h n = h (n + p.+1).
    Proof.
      apply: not_injective_prop.
      apply: not_injective1_h.
    Qed.
    
    (* The same proof for (h : nat -> set (set T))

    Definition encode (A : set (set T)) : {ffun {ffun T -> bool} -> bool} :=
      [ffun f : {ffun T -> bool} => `[< A [set x | f x]%classic >] ].
  
    Lemma encode_inj : injective encode.
    Proof.
      move=> A A' eqAA'.
      move: (@ffunP {ffun T -> bool} (fun _ => bool) (encode A) (encode A')) => HffunP.
      have {}HffunP := HffunP.2 eqAA'.
      rewrite predeqE => S.
      pose f_S: {ffun T -> bool}  := [ffun x => `[< S x >] ].
      have := HffunP f_S.
      rewrite /encode !ffunE.
      have eqB : [set x | f_S x]%classic = S.
      {
        rewrite predeqE /= => x. rewrite /f_S ffunE.
        split. by move => /asboolP. by move => ?;apply/asboolP.
      }
      rewrite eqB => eqbool.
      split => [Ha| Ha].
      by move: Ha => /asboolP;rewrite eqbool => /asboolP.
      by move: Ha => /asboolP;rewrite -eqbool => /asboolP.
    Qed.
  
    Lemma not_injective_h (h : nat -> set (set T)) : ~ injective h.
    Proof.
      move=> h_inj.
      pose N := #|{ffun {ffun T -> bool} -> bool}|.
      pose g : 'I_N.+1 -> {ffun {ffun T -> bool} -> bool} := fun i => encode (h i).
      have g_inj : injective g.
      by move=> i j /encode_inj /h_inj eqij; exact/val_inj.
      pose proof leq_card.
      have := leq_card g g_inj.
      by rewrite card_ord ltnn.
    Qed.
  
    *)

End setT_injectivity.
End setT_injectivity.

Export setT_injectivity(set_fin_codomain_prop).

Module partial_iic_lemma.
  Section partial_iic_lemma.
    (** a partial iic lemma *)
    Context {T:choiceType} (R: relation T) (B: set T).
    Context (A0: forall b, b \in B -> exists a, R (b,a)).
    Context (A1: exists a, a \in (@setT T)).
    
    Definition Re := 
      [set p | (p.1 \in B) /\ R p \/ (~(p.1 \in B) /\ p.2 = p.1)]%classic.
        
    Lemma choose_l1: iic Re.
    Proof.
      apply: DC;first exact: A1.
      (* now we prove that total_rel Re *)
      move: A0 => + s => /(_ s) H0.
      case H2: (s \in B);last first.
      by (exists s);rewrite /Re /= H2;right.
      by move: (A0 H2) => [a H3];exists a;rewrite /Re /=;left.
    Qed.
    
    Lemma choose: (iic R) \/ (exists s, ~ (s \in B)).
    Proof.
      have [j Hj]: exists (j: nat -> T),
          (forall n, (j n) \in B) -> (forall n, (R ((j n), (j n.+1)))).
      {
        move: choose_l1 => [j Hj];exists j;move => H2 n.
        by move: (Hj n);rewrite /Re /= H2 => -[[_ H3]| [? _]].
      }
      move: (lem (forall n : nat, j n \in B)) => [/Hj H2 | H2].
      by left;(exists j).
      by move: H2 => /existsNP [p H2];right;exists (j p).
    Qed.
    
  End partial_iic_lemma.
End partial_iic_lemma.

Export partial_iic_lemma (choose).

Module partial_iic_lemma_sub.
  Section partial_iic_lemma_sub.
    (** extending partial_iic_lemma with subtyping *)
    Context {T:choiceType} (R: relation T) (A B: set T).
    Context (A0: forall a, a \in (A `&` B) -> exists b, b \in A /\ (R (a,b))).
    Context (A1: exists a, a \in A).
    
    Lemma choose_sub: (exists h, (iic_fun  R h) /\ (forall n, (h n) \in A))
                      \/ (exists s, (s \in A) /\ ~ (s \in B)).
    Proof.
      (* we use subtyping to enable the use of tpartial_iic_lemma *)
      (* T': choiceType := A *)
      pose B': set A := [set b': A | (val b') \in B]%classic.
      pose R':= [set p : A*A | R (val p.1,val p.2)]%classic.
      
      have H1: (iic R') \/ (exists s, ~ (s \in B')).
      {
        apply: choose. 
        move => a;rewrite inE /B' /= => HainB.
        have /A0 [b [Hb H1]]: (sval a) \in  A `&` B
          by rewrite inE;split;[rewrite -inE;apply/valP| rewrite /B' -inE].
        by (exists (exist _ b Hb)).
        move: (A1) => [a Ha].
        by (exists (exist _ a Ha));rewrite inE /=.
      }
      have H2: (exists s, ~ (s \in B')) ->  (exists s, s \in A /\ ~ s \in B).
      {
        move => [s Hs].
        rewrite inE /B' /= in Hs.
        have Ha: (sval s) \in A by rewrite inE;apply: set_valP.
        by exists (sval s).
      }
      have H3: (iic R') -> (exists h, (iic_fun  R h) /\ (forall n, (h n) \in A)).
      {
        move => [j Hj];exists (fun n => (sval (j n))).
        split. 
        by move => n;rewrite /R'/= in Hj;apply: Hj.
        by move => n;rewrite inE;apply: set_valP.
      }
      move: H1 => [H1 | H1].
      by left;apply: H3.
      by right;apply: H2.
    Qed.
    
  End partial_iic_lemma_sub.
End  partial_iic_lemma_sub.
Export partial_iic_lemma_sub(choose_sub).

Module leSet_choice.
  (** * an increasing selection lemma choose_inc_seq *)
  Section leSet_choice_sec.

    Context {T:choiceType} (R: relation T) (f : nat -> set T).
    Context (A0: exists s, s\in (f 0)) (A1: forall n, (f n) [<= R] (f n.+1)).
    
    Definition R'' (p1: nat*T) := 
      [set p | ((p.2 \in (f p.1) /\ (p1.2 \in (f p1.1) /\ (p1.2 = p.2 \/ R (p1.2,p.2)))) 
               \/ ~(p1.2 \in (f p1.1))) /\ p.1 = p1.1.+1 ]%classic.

    #[local] Lemma P1 (p1: nat*T): exists p, p \in R'' p1.
    Proof. 
      move: A1 =>/(_ p1.1) Hp1;case H1: (p1.2 \in (f p1.1)).
      by move: (H1) => /Hp1 [s2 /= [? ?]];(exists (p1.1.+1,s2));
                      rewrite inE;split;[left|].
      by move: A0 H1 => [v0 ?] /negP ?;exists (p1.1.+1,v0);rewrite inE;split;[right|].
    Qed.

    #[local] Lemma P2: exists (j: nat*T -> nat*T),
      forall p, p.2 \in (f p.1) -> ((j p).2 \in (f (j p).1) /\ (p.2 = (j p).2 \/ R (p.2,(j p).2)))
                             /\ (j p).1 = p.1.+1.
    Proof.
      exists (fun t => xchoose (P1 t));move => p1.
      have H0: xchoose (P1 p1) \in R'' p1 by apply: xchooseP.
      by move: H0 => /inP /= [[[? [_ ?]] _ // |? ? //] ?].
    Qed.

    #[local] Lemma P3: exists (k: nat -> (T -> T)),
      forall n, forall s, s \in (f n) -> ((k n s) \in (f n.+1) /\ (s = (k n s) \/ R (s,(k n s)))).
    Proof.
      move: P2 => [j H1];exists (fun k => (fun s => (j (k,s)).2)).
      move:H1 => + n s => /(_ (n,s))/= H1 => /H1 /= [+ H2].
      by rewrite H2.
    Qed.
    
    #[local]Fixpoint kiter (k: nat-> (T -> T)) n :=
      if n is n'.+1 then (k n') \o kiter k n' else id.

    (* this is the main lemma *)
    Lemma choose_inc_seq s: s \in (f 0) -> exists (h: nat -> T), 
          (h 0) = s
          /\ (forall n, (h n) \in (f n)) 
          /\ (forall n, (h n)=(h n.+1) \/ R (h n, h n.+1)).
    Proof.
      move: P3 => [k H1];exists (fun n => (kiter k n s)).
      have IterP2: forall n, (kiter k n s) \in (f n).
      { elim;first by move: H1 => /(_ 0 s H) [? _].
        by move => n' Hr;move: H1 => /(_ n' _ Hr) => -[? _].
      }
      have IterP3: forall n, (kiter k n s) = (kiter k n.+1 s)
                        \/ R ((kiter k n s),(kiter k n.+1 s)).
      { elim. 
        by move: (IterP2 0) => /H1 [_ ?].
        by move => n Hr;move: (IterP2 n.+1) => /H1 [_ ?].
      }      
      by split;[ | split;[apply: IterP2| apply: IterP3]].
    Qed.
    
  End leSet_choice_sec.
  
End leSet_choice.

Export leSet_choice(choose_inc_seq).

Module f_periodic. 
  (** * XXXX here using (S: set T) (Sq: seq (set T)) is not necessary  T and set T is enough *)
  (** * some properties of the periodic function f: nth S (S::Sq) (n %% size (S::Sq)) *)
  Section f_periodic.
    Context {T: Type} (S: set T) (Sq: seq (set T)).
    Context (U R: relation T).
    Implicit Types (setS: set (set T)) (setR: relation (set T)).
    
    Definition fb (n: nat) := nth S (S::Sq) n.
    Definition f (n : nat) := fb (n %% size (S::Sq)).

    (** * f properties *)
    Lemma f_periodic n: f (n + (size (S::Sq))) = f n.
    Proof. by rewrite /f (modnDr n (size (S::Sq))). Qed.

    Lemma f_kperiodic k n: f (n + k*(size (S::Sq))) = f n.
    Proof.
      elim: k n => [n |k Hk n];first by rewrite mul0n addn0.
      by rewrite mulSnr addnA f_periodic Hk.
    Qed.

    Lemma f_small n: f n = f (n %% size (S :: Sq)).
    Proof.
      by rewrite {1}(divn_eq n (size (S :: Sq))) addnC f_kperiodic.
    Qed.

    Lemma f_addn1 n: f (n %% size (S :: Sq)).+1 = f (n.+1).
    Proof.
      by rewrite -addn1 f_small (modnDml n 1 (size (S :: Sq))) -f_small addn1.
    Qed.

    Lemma f_S: (f (size (S::Sq))) = S.
    Proof. by rewrite -[size (S :: Sq)]add0n f_periodic. Qed.
    
    (** * fb properties *)
    Lemma fb_allset setS: (S::Sq) [\in] setS <-> (forall n : nat, (fb n) \in setS).
    Proof. by apply: allset_nth. Qed.

    Lemma fb_f_s n: n < size (S::Sq) -> (fb n) = (f n). 
    Proof. by move => /modn_small Hsiz;rewrite -{1}Hsiz. Qed.
    
    Lemma fb_S n: n = size (S::Sq) -> (fb n) = (f n).
    Proof. by move => ->; rewrite /fb nth_default -f_S. Qed.
    
    Lemma fb_f n: n <= size (S::Sq) -> (fb n) = (f n). 
    Proof. by rewrite leq_eqVlt => /orP [/eqP/fb_S// |/fb_f_s]. Qed.
    
    Lemma fb_S' n: size (S::Sq) <= n -> (fb n) = S.
    Proof. by move => H; rewrite /fb nth_default. Qed.
    
    (** * links with [\in] and allL *)
    (**  from property of setS on S::Sq to forall n property of f*)
    Lemma f_setS setS: (S::Sq) [\in] setS -> forall n, (f n) \in setS.
    Proof. 
      move => ?. 
      have: forall n, (fb n) \in setS by rewrite -allset_nth. 
      by move => + n => /(_ (n %% size (S :: Sq))) ?.
    Qed.
    
    (**  The converse. too strong could be changed aas in f_setR' *)
    Lemma f_setS' setS: (forall n, (f n) \in setS) -> (S::Sq) [\in] setS.
    Proof. 
      move => Hf;rewrite (@allset_nth (set T) setS S Sq) => n.
      move: Hf => /[dup] /(_ 0) Hf0 /(_ n) Hf.
      case H1: (n < size (S::Sq)). 
      by  move: H1 => /fb_f_s; rewrite /fb => ->.
      have /fb_S': size (S::Sq) <= n by lia.
      by rewrite /fb => ->.
    Qed.

    (**  from property of setR on S::(rcons Sq S) to forall n property of f*)
    Lemma f_setR setR: allL setR Sq S S -> forall n, setR ((f n), (f n.+1)).
    Proof.
      move: (allL_nth' setR Sq S S S) => H1. 
      move => /H1 + n => /(_ (n %% size (S::Sq))) H2.
      have H3: n %% size (S :: Sq) < size (S::Sq)
        by rewrite  ltn_pmod.
      rewrite -rcons_cons nth_rcons H3 nth_rcons in H2.
      have: n %% size (S :: Sq) <= size (Sq) by [].
      move => /H2 H4;clear H1 H2.
      case H5: ((n %% size (S :: Sq)).+1 == size (S :: Sq)).
      + move: H5 => /eqP H5.
        rewrite H5 ltnn eq_refl in H4.
        have H6: setR ((f n), S) by [].
        have -> : f(n.+1) = S by rewrite -f_addn1 H5 f_S.
        exact.
      + have H6: (n %% size (S :: Sq)).+1 < size (S :: Sq) by lia.
        rewrite H6 in H4. 
        have H8: setR ((f n), (nth S (S :: Sq) (n %% size (S :: Sq)).+1)) by [].
        have H10: (n %% size (S :: Sq) + 1) %% size (S :: Sq) = (n %% size (S :: Sq) + 1)
          by apply: modn_small;lia.
        rewrite -addn1 -H10 in H8. 
        have H11: setR ((f n), (f (n %% size (S :: Sq) + 1))) by [].
        by rewrite addn1 f_addn1 in H11.
    Qed.

    (** a strong converse *)
    Lemma f_setR' setR: (forall n, n <= size (S::Sq) -> setR ((f n), (f n.+1)))
                        -> allL setR Sq S S.
    Proof.
      move => H1;rewrite (allL_nth' setR _ S S S) => n Hs'.
      have Hs: n < size (S::Sq) by rewrite /=;lia.
      rewrite -rcons_cons 2!nth_rcons Hs.
      case Hs2: ( n.+1 < size (S :: Sq)).
      + move: (fb_f_s Hs);rewrite /fb => ->.
        move: (fb_f_s Hs2);rewrite /fb => ->.
        by apply: H1;lia.
      + have: n.+1 == size (S :: Sq) by lia.
        move => /[dup] /eqP H5 ->.
        have H3: n <= size (S :: Sq) by lia.
        move: H1 => /(_ n H3);rewrite H5 f_S.
        by rewrite -(fb_f_s Hs).
    Qed.
    
    (** could be proved from f_setR' by contra, but maybe not shorter *)
    Lemma f_exists setR: 
      (exists j, j <= (size Sq) /\ setR ((nth S (S::(rcons Sq S)) j), (nth S (S::(rcons Sq S)) j.+1)))
      -> exists j, j <= (size Sq) /\ setR ((f j),(f j.+1)).
    Proof.
      move => [j [Hs]];rewrite -rcons_cons 2!nth_rcons.
      have ->: j < size (S::Sq) by rewrite /=;lia.
      case H2: (j.+1 < size (S::Sq)).
      + move => HH.
        exists j;split;first by [].
        rewrite -(@fb_f_s j). 
        by rewrite -(@fb_f_s j.+1);[|rewrite H2].
        by rewrite /=;lia.
      + have H1': j.+1 <= size (S::Sq) by rewrite /=;lia.
        have H2': j.+1 = (size (S::Sq)) by lia.
        rewrite -H2' eq_refl => H3.
        exists j;split;first by [].
        by rewrite H2' f_S -(fb_f_s H1').
    Qed.
    
  End f_periodic.
End f_periodic.

Export f_periodic.

Module f_periodic_for_leSet.
  (** * properties of increasing  sequences of sets *)
  (** * for the ('Δ.^c `&` (leSet R)) relation *)
  
  Section seq_leSet.
    Context {T:choiceType} (M U R: relation T) (S: set T) (Sq: seq (set T)).
    (** strict increasing sequence of sets for (leSet R) *)
    Context (A0: @allL (set T) ('Δ.^c `&` (leSet R)) Sq S S).
    (** which are also (U,R)-prekernels *)
    Context (A3: (S::Sq) [\in] (preKernel R U M)).
    Implicit Types (sq: seq T) (s: T).
    
    Definition g := f S Sq.

    Lemma A1: @allL (set T) (leSet R) Sq S S.
    Proof. by move: A0 => /allL_I [_ ?]. Qed.

    Lemma A2: @allL (set T) 'Δ.^c Sq S S.
    Proof. by move: A0 => /allL_I [? _]. Qed.
    
    Lemma g_inc n: ('Δ.^c `&` (leSet R)) ((g n),(g n.+1)).
    Proof. by apply: f_setR. Qed.
    
    Lemma g_prekernel n: (g n) \in (preKernel R U M).
    Proof. by apply: f_setS. Qed.
    
    (** * existence of j and aj such that aj \in (f j) and ~ (aj \in (f j.+1)) *)
    
    Local Lemma allL_Tr (Rset: relation (set T)): 
      0 < size Sq -> @allL (set T) Rset Sq S S -> transitive Rset 
      -> forall S', (S' \in Sq) -> (Rset (S, S')) /\ (Rset (S',S)).
    Proof.
      move => H1 H2 /Tclos_iff H3 S' H4. 
      move: (@allL_to_Tclos_left _ Rset Sq S S S' H4 H2). 
      move: (@allL_to_Tclos_right _ Rset Sq S S S' H4 H2). 
      by rewrite -H3.
    Qed.

    Definition setRa : relation (set T):= (fun p =>  exists aj, aj \in p.1 /\ ~( aj \in p.2)). 
    
    Local Lemma DiffE: 
      exists j, j <= (size Sq) 
           /\ setRa ((nth S (S::(rcons Sq S)) j), (nth S (S::(rcons Sq S)) j.+1)).
    Proof.
      (* implied by A2 *)
      have H1: 0 < size Sq.
      { move: A2;contra;rewrite leqn0 => /eqP/size0nil H1.
        by move: A2;rewrite H1 allL0 inE DeltaCP notin_setE DeltaCP.
      }
      (* for lemma allL_Tr *)
      have Inc_Tr : transitive (@Inc T)
        by move => A B C;apply: subset_trans.
      (* main proof *)
      move: A2;rewrite (@allL_nth' (set T) 'Δ.^c Sq S S S).
      contra => H2.
      have H4: allL Inc Sq S S
        by rewrite (@allL_nth' (set T));move => j Hs b /inP/(H2 j Hs b)/inP.
      have H6: forall S', S' \in Sq -> S = S'.
      move => S' Hs;move: (@allL_Tr Inc H1 H4 Inc_Tr S' Hs).
      by rewrite eqEsubset.
      by exists 0;[lia | rewrite /= // nth_rcons H1 DeltaP;apply: H6;apply: mem_nth ].
    Qed.

    Lemma DiffE': 
      exists j, j <= (size Sq) /\ setRa ((g j), (g j.+1)).
    Proof.
      move: (@f_exists _ S Sq setRa) => H1.
      by move: DiffE  => /H1 H2. 
    Qed.
    
    (** * using a j offset on f *)
    Lemma exists_g: exists g: nat -> set T, 
        (forall n k, g (n + k*(size (S::Sq))) = g n)
        /\ (exists a, a \in (g 0) /\ ~ (a \in (g 1)))
        /\ (forall n, (g n) [<= R] (g n.+1))
        /\ (forall n, preKernel R U M (g n)).
    Proof.
      move: DiffE' => [j [_ [a [H1 H2]]]].
      exists (fun n => (g (j + n))). 
      rewrite addn0 addn1.
      move: (@f_setS _ S Sq (preKernel R U M)) A3 => Hpk /Hpk Hpk'.
      move: (@f_setR _ S Sq (leSet R)) A1 => Hinc /Hinc Hinc'.
      split;first by move => n k;rewrite addnA /g f_kperiodic.
      split;first by (exists a).
      split;move => n;last by rewrite -inE.
      by rewrite -addn1 addnA;move: Hinc' => /(_ (j + n));rewrite -addn1.
    Qed.

  End seq_leSet.
End f_periodic_for_leSet.

Export f_periodic_for_leSet(exists_g).

Module build_h.
  (** for any g satisfying G1-G4 assumptions choose a selection h *)
  Section build_h.
    Context {T:choiceType} (M U R: relation T) (g: nat -> set T).
    Context (S: set T) (Sq: seq (set T)).

    Context (G1: forall n k, g (n + k*(size (S::Sq))) = g n).
    Context (G2: exists a, a \in (g 0) /\ ~ (a \in (g 1))).
    Context (G3: forall n, (g n) [<= R] (g n.+1)).
    Context (G4: forall n, preKernel R U M (g n)).
    
    Implicit Types (sq: seq T) (s: T).

    Lemma seq_not (h: nat -> T) (A : set T): 
      ~ (h 0) \in A -> (exists k, (h k) \in A) -> exists j, ~ (h j) \in A /\ (h j.+1) \in A.
    Proof.
      move => H0 [k Hk];elim: k Hk => [// | n Hr Hl].
      by case H1: ((h n) \in A);[move: H1 => /Hr H1 |exists n;rewrite H1 Hl].
    Qed.

    Definition Ig (g: nat -> set T) := [set x | forall n, x \in (g n)]%classic.

    Lemma IgP: (Ig g) =  [set x | forall n, n < size (S::Sq) -> x \in (g n)]%classic.
    Proof.
      rewrite predeqE => x;split => [H1 n _ //| H1 n].
      have ->: forall n, (g n) = g (n %% (size (S::Sq)))
          by move => n';rewrite [in LHS](divn_eq n' (size (S::Sq))) addnC G1.
      apply: H1;apply: ltn_mod.
    Qed.
    
    (** we use choose_inc_seq to choose h and prove the last extra property *)
    (** as (g n) are RelIndep sets *)
    Lemma exists_h: exists h : nat -> T,
        (forall n, (h n) \in (g n))
        /\ (forall n, (h n)=(h n.+1) \/ R (h n, h n.+1))
        /\ ~(exists n, (h n) \in (Ig g)).
    Proof.
      move: (G2) => [a [Hg0 H2]].
      have H4: exists s, s \in (g 0) by (exists a).
      move: (@choose_inc_seq T R g H4 G3 a Hg0) => [h [H6 [H7 H8]]].
      exists h;split;[exact|split;[exact |]].
      move => Hinter. 
      (* lastt step : ~(exists n, (h n) \in (Ig g)) *)
      have P5: ~ ( h 0 \in (Ig g)) by move => /inP /(_ 1);rewrite H6 => ?.
      move: (seq_not P5 Hinter) => [j [P6 P7]].
      (* we build a contradiction as (g j) is a prekernel *)
      have P8:  h j.+1 \in (g j) by move: P7 => /inP/(_ j).
      have P9:  h j \in (g j) by apply: H7.
      have P10: ~ ( h j = h j.+1) by move => He;rewrite He in P6.
      move: G4 => /(_ j) [Hindep _].
      move: Hindep => /(_ (h j) (h j.+1) P9 P8 P10) HnotR.
      by move: H8 => /(_ j) [? | ?].
    Qed.

  End build_h.
End build_h.

Export build_h(exists_h,Ig,IgP).

Module h_extra_props.
  
  Section h_extra_props.
    (** properties for any h satisfying G1 and H1-H3 *)  
    Context {T:choiceType} (U R: relation T) (g: nat -> set T) (h: nat-> T).
    Context (S: set T) (Sq: seq (set T)).

    Context (G1: forall n k, g (n + k*(size (S::Sq))) = g n).
    Context (H1: forall n, (h n) \in (g n)).
    (** XXXX reformulate with ('Δ `|` R) *)
    Context (H2: forall n, (h n)=(h n.+1) \/ R (h n, h n.+1)).
    Context (H3: ~(exists n, (h n) \in (Ig g))).

    Lemma h_Tclos:
      forall m n, allL ('Δ `|` R) (mkseq (fun i => h (n + i+1)) m) (h n) (h (n+m+1)).
    Proof.
      have: forall n,  ('Δ `|` R) (h n, h n.+1)
          by move: H2 => + n => /(_ n) [H1' | H1'];[left;rewrite DeltaP|right].
      by move => /@f2allL.
    Qed.
    
    (** * true but too strong *)
    Lemma h_Tclos1: forall m n, (('Δ `|` R).+ ((h n), (h (n+m+1)))).
    Proof.
      move => m n.
      have Hall: (forall m n, allL ('Δ `|` R) (mkseq (fun i => h (n + i+1)) m) (h n) (h (n+m+1))).
      by apply: h_Tclos;split.
      by apply: allL_to_Tclos.
    Qed.
    
    (** * the property we need *)
    Lemma hP1: forall n m, (forall j, j <= m.+1 -> (h (n+j)= (h n))) \/ R.+ (h n, h (n+m+1)).
    Proof.
      move => n m;elim: m n => [n|n' Hr n]. 
      + move: H2 => /(_ n) [H2' | H2'];last first.
        by right;rewrite addn0 addn1;apply/TclosSu.
        left;move => j Hj;case Hc2: (j == 0). 
        by move: Hc2 => /eqP ->;rewrite addn0.
        by (have ->: (j = 1) by lia); rewrite addn1 H2'.
      + move: Hr => /(_ n) [Hr | Hr].
        ++ have H4: h (n + n'.+1) = h n by apply: Hr;lia. 
           move: H2 => /(_ (n+ n'.+1)) [H1' | /TclosSu H1'];last first.
           by right;rewrite -H4;rewrite addn1.
           left;move => j;case Hc2: (j <= n'.+1).
           by move => _;apply: Hr.
           move => H3'.
           have ->: j = n'.+2 by lia.
           rewrite H4 in H1'.
           by rewrite H1' addnS.
        ++ rewrite -addnA addn1 in Hr.
           move: H2 => /(_ (n+ n'.+1)) [H1' | H1'];right;rewrite addn1.
           by rewrite H1' in Hr.
           by have /Tclos_composel:  (R.+ `;` R) (h n, h (n + n'.+1).+1)
                 by (exists (h (n + n'.+1))).
    Qed.

    Lemma inIg' k: 
      (forall j : nat, j <= (size (S::Sq)) -> h (k*(size (S::Sq))+j) = h (k*(size (S::Sq))))
      -> (h (k*(size (S::Sq)))) \in (Ig g).
    Proof.
      move => H4.
      rewrite (IgP G1) inE => j Hs.
      have <-: g (j + k * size (S :: Sq)) = g j by apply:G1.
      have H5: j <= (size (S::Sq)) by lia.
      by move: H4 => /(_ j H5) <-;rewrite 1!addnC.
    Qed.

    Lemma hmapk k: R.+ (h (k*(size (S::Sq))), h (k.+1*(size (S::Sq)))).
    Proof.
      move: hP1 => /(_ (k*(size (S::Sq))) (size Sq)) [/inIg' H5|];last first. 
      by have ->: k * size (S :: Sq) + size Sq + 1 = k.+1 * size (S :: Sq)
        by rewrite /=;lia.
      by have H6: (exists n : nat, h n \in Ig g) by (exists (k * size (S :: Sq))).
    Qed.

    (** * The main lemma of this module *)    
    Lemma hmap' k p: R.+ (h (k*(size (S::Sq))), h ((k+ p.+1)*(size (S::Sq)))).
    Proof.
      elim: p k => [k |p Hr k];first by rewrite [k + 1]addn1;apply: (hmapk k).
      have: R.+ (h ((k + p.+1) * size (S :: Sq)), h ((k + p.+1).+1 * size (S :: Sq)))
        by apply: (hmapk (k+p.+1)) =>H1.
      have ->: (k + p.+1).+1 = k +p.+2 by lia.
      move => H4.
      by move: (TclosT (Hr k) H4).
    Qed.

  End h_extra_props.
End h_extra_props.
Export h_extra_props.

Module BH.
  (** * Now we assume finType *)
  Section BH.
    
    Context {T:finType} (M U R: relation T) (S: set T) (Sq: seq (set T)).
    (** strict increasing sequence of sets for (leSet R) *)
    Context (A0: @allL (set T) ('Δ.^c `&` (leSet R)) Sq S S).
    (** which are also (U,R)-prekernels *)
    Context (A3: (S::Sq) [\in] (preKernel R U M)).
    Implicit Types (sq: seq T) (s: T).
    
    Lemma Rcyclic: exists s, R.+ (s,s).
    Proof.
      move: (exists_g A0 A3) => [g [G1 [G2 [G3 G4]]]].
      move: (exists_h G2 G3 G4) => [h [H1 [H2 H3]]].
      move: (hmap' G1 H1 H2 H3) => Hhmap.
      move: (fin_codomain_prop (fun k => h(k*(size(S::Sq))))) => [n [p H4]].
      by exists (h (n * size (S :: Sq)));rewrite {2}H4;apply: Hhmap.
    Qed.
    
  End BH.
End BH.

Export BH (Rcyclic).

Module test3.
Section test3.
  (** main result here *)
  Context {T: finType} (O R B: relation T).

  Definition M := B `|` R.

  Context (A2: Assumption2 R) (A6: Assumption6 B M O)
    (A7: Assumption7 R B M) (A8: Assumption8 R B M). 
  Context (A1: NotEmpty T) (Au: R `<=` O^-1).
  Context (Apk : forall X , RelIndep O X <-> RelIndep M X).
  Context (A_Onotcyclic: ~ (exists s, O.+ (s,s))).
  
  Lemma preKernelP S: 
    preKernel O R M S <-> preKernel M R M S.
  Proof. by rewrite /preKernel /= Apk. Qed.
  
  Lemma extend_pk X: preKernel M R M X -> (Non_Mabsorbant R B X) ->
        exists X', preKernel M R M X' /\  X [<= O] X' /\ ~ (X = X').
  Proof.
    by apply: extend. Qed.
  
  Definition Rst := ('Δ).^c `&` (leSet O). 
  
  Lemma A0 S: S \in (preKernel M R M) `&` (Non_Mabsorbant R B) 
              -> exists S', S' \in (preKernel M R M) /\ Rst (S, S').
  Proof.
    rewrite inE => -[Hpk Hna];move: (extend_pk Hpk Hna) 
            => [S' [/mem_set Hpk' [Hle Hd]]].
    exists S';split;[ | ].
    by []. by rewrite /Rst /= DeltaP.
  Qed.

  Lemma A1': exists S,  S \in (preKernel M R M).
  Proof.
    (** XXXXX  montrer qu'il existe un puit *)
  Admitted.

  Lemma iic_to_cyclic (h : nat -> (set T)):  
    (iic_fun Rst h) ->  exists n p : nat, h n = h (n + p.+1).
  Proof. by move => Hiic;apply: set_fin_codomain_prop. Qed.
  
  Lemma iic_to_allL  (h : nat -> (set T)):  
    (iic_fun Rst h) -> 
    exists n p, h n = h (n+p+1)
           /\ allL Rst (mkseq (fun i => h (n + i+1)) p) (h n) (h n).
  Proof. 
    move => /[dup] /iic_to_cyclic [n [m Heq]] /f2allL /(_ n m) HallL.
    rewrite -addn1 addnA in Heq;rewrite -Heq in HallL. 
    by exists n, m.
  Qed.

  Lemma iic_and_prekernels (h : nat -> (set T)):
    (iic_fun Rst h) -> (forall n, (h n) \in  (preKernel O R M))
    -> exists n p,
        allL Rst (mkseq (fun i => h (n + i+1)) p) (h n) (h n)
        /\ ((h n)::(mkseq (fun i => h (n + i+1)) p)) [\in] (preKernel O R M).
  Proof.
    move => /iic_to_allL [n [p [_ Hiic]]] Hpk.
    exists n, p. split; first exact.
    by apply: f2in.
  Qed.
  
  Lemma iic_and_prekernels_to_cyclic (h : nat -> (set T)):
    (iic_fun Rst h) -> (forall n, (h n) \in  (preKernel O R M))
    -> exists s, O.+ (s,s).
  Proof.
    move => Hiic Hpk;move: (iic_and_prekernels Hiic Hpk) => [n [p [Ha Hpk']]].
    by apply: (@Rcyclic T M R O (h n) (mkseq (fun i : nat => h (n + i + 1)) p));last first.
  Qed.
  
  Lemma choose: (exists h, (iic_fun Rst h) /\ (forall n, (h n) \in  (preKernel M R M)))
                \/ (exists S, (S \in (preKernel M R M)) /\ ~ ( S \in ((Non_Mabsorbant R B): set (set T)))).
  Proof.
    move: (@choose_sub _ Rst (preKernel M R M) (Non_Mabsorbant R B) A0 A1') => [Hiic | [S Hker]].
    by left.
    by right;exists S.
  Qed.

  Lemma last: (exists S, (S \in (preKernel M R M)) /\ ~ ( S \in ((Non_Mabsorbant R B): set (set T)))).
    move: choose => [[h [Hiic Hk]] | H1];last by [].
    have HpkO: (forall n, (h n) \in  (preKernel O R M))
      by move => n; rewrite inE preKernelP -inE.
    by move: (iic_and_prekernels_to_cyclic Hiic HpkO) => HOcyclic.
  Qed.

End test3.
End test3.

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

  Lemma set_to_finK : cancel fin_of_set set_of_fin.
  Proof.
    move=> A;rewrite predeqE /fin_of_set /set_of_fin /= => x.
    by split => [|?];rewrite inE;[move => /asboolP|apply/asboolP].
  Qed.
  
  Lemma fin_to_setK : cancel set_of_fin fin_of_set.
  Proof.
    move=> A;apply/setP => x; case H1: (x \in A).
    + by move: H1 => /in_set_of_fin/in_fin_of_set ->.
    + move: H1 => /negP/in_set_of_fin/in_fin_of_set H1.
      by case H2: (x \in [:fin:[:set:A]]).
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
    by rewrite inE;split;by rewrite -inE.
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
    split;first by rewrite -inE in_set_of_fin inE => /eqP ->.
    by move => ->;rewrite -inE in_set_of_fin inE.
  Qed.

  Lemma set_of_set0 :  [:set: finset.set0] = set0.
  Proof.
    by rewrite predeqE => x;split;[rewrite -inE in_set_of_fin inE |].
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
      move: H1 => /(_ x y xS yS H2) H1 H3.
      by rewrite -inE in H3;rewrite H3 in H1.
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

End Acyclicity.

Section ChampetierExt_Theorem.

  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T) (X: {set T}).
  
  Context (A2 : Assumption2 R) (A6 : Assumption6 B (M R B) O) 
    (A7 : Assumption7 R B (M R B)) (A8 : Assumption8 R B (M R B)).
  Context (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1).
  Context (Apk : forall X , RelIndep O [:set: X] <->  RelIndep (M R B) [:set: X]).
  
  Lemma prekernelP S: 
    (prekernel_fin O R (M R B) S) <-> preKernel (M R B) R (M R B) [:set: S].
  Proof. by rewrite (@prekernelE T O R (M R B) S) Apk. Qed.
  
  Lemma maximal_mabsorbant S:
    (prekernel_fin O R (M R B) S) /\ (forall U, prekernel_fin O R (M R B) U ->
                                  [:set: S] [<= O] [:set: U] -> S = U)
    -> Mabsorbant R B [:set: S].
  Proof.
    contra; move => H1 /prekernelP Hpk.
    have H3: Non_Mabsorbant R B [:set: S]
      by move: H1 => [y H1] H3;exists y;rewrite inE;
                    split;[ |rewrite notin_setE in H3;rewrite inE].
    move: (@extend T R B O [:set: S] A2 A6 A7 A8 Hpk H3)
        => [S' [Hpre [H7 Hne]]].
    rewrite /prekernel_fin.
    exists [:fin: S'].
    by rewrite prekernelP set_to_finK.
    split;first by  rewrite set_to_finK.
    apply/negP => /eqP Heq.
    by rewrite Heq set_to_finK in Hne.
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

Section Blidia_Engel_Ext_Theorem.
  (** * Similar to Champetier but  (Asp: sporder O) *)
  (** * is replaced by Acyclicity *)

  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T) (X: {set T}).
  
  Context (A2 : Assumption2 R) (A6 : Assumption6 B (M R B) O) 
    (A7 : Assumption7 R B (M R B)) (A8 : Assumption8 R B (M R B)).
  Context (A1: NotEmpty T) (Au: R `<=` O^-1).
  Context (Apk : forall X , RelIndep O [:set: X] <->  RelIndep (M R B) [:set: X]).
  Context (Anc : ~ ( exists s, R.+ (s,s))).

  Lemma prekernelP' S: 
    (prekernel_fin O R (M R B) S) <-> preKernel (M R B) R (M R B) [:set: S].
  Proof. by rewrite (@prekernelE T O R (M R B) S) Apk. Qed.
  
End Blidia_Engel_Ext_Theorem.

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
      have [ //| H9]: (O `|` O^-1) (x,y) by rewrite -H8; left.
      by rewrite -inE H4.
      have: (y,x) \in O by rewrite inE.  
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

