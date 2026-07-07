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
From RL Require Import  seq1 seq2 rel paper_meunier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope. (* we can use %classic *)
Local Open Scope set_scope. (* we can use %SET *)

Definition fin_relation (T: finType) := {set (T * T)}.
Notation "{ 'relation' T }" := (fin_relation T) (format "{ 'relation'  T }"): type_scope.

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

  (* begin snippet Rloop:: no-out *)    
  Definition Sink (R: relation T) v := forall w, ~ R (v,w).
  (* end snippet Rloop *)
  
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
    move => [Hi /[dup] Ht /Tclos_iff H2] Hiic. 
    pose proof (@sporder_antisym _ R Ht Hi) as Has.
    pose proof (@fin_not_iic_inj R) as H4.
    have H5: Asym R = R by apply/(@AsymE T R).
    by move: (@iic_asym_injective T R);rewrite -H2 H5 => /(_ Hiic) ?.
  Qed.

  Lemma fin_rloop R: (NotEmpty T) -> (sporder R) -> (Rloop R).
  Proof.
    move => Hne /[dup] Hsp [Hi Ht].
    pose proof (@sporder_antisym _ R Ht Hi) as Has.
    have H1: Asym R = R by apply/(@AsymE T R).
    move: (@fin_not_iic R Hsp);rewrite -{1}H1 => H2.
    by apply: notiic_rloop.  
  Qed.

  Lemma fin_sink R: (NotEmpty T) -> (sporder R) -> exists v, (Sink R v).
  Proof.
    move => Hne Hsp;move: (fin_rloop Hne Hsp) => [v H1].
    exists v. move => w /[dup] H2 /H1 H3. 
    move: Hsp => [Hi Ht].
    pose proof (@sporder_asym _ R Ht Hi) as Has.
    rewrite /asymmetric in Has.
    by move: H2 => /Has H2.
  Qed.
  
  Lemma fin_rloop1 R U: (NotEmpty T) -> (sporder R)
                      -> exists v, (v)_:#(R) `<=` U#_(v).
  Proof.
    move => Hne Hsp;move: (@fin_sink _ Hne Hsp) => [v Rl].
    exists v;move: Rl => /[swap] w /(_ w) Rl.
    by rewrite /Aset 2!Fset_s => ?.
  Qed.
  
  (** * the one we need for champetier *)
  (** * O: orientation, D: direction, R = D `&` O, B = D  `&` O^-1 *)
  (** * D is equal to R `|` B which is also M *)
  
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

Section Maximal.
  (** * There's always a maximal element in a finite nonempty poset *)
  (** we consider here the simplest case *)
  (** and give a proof by recursion 
      we first give the proof for a sequence(seq T) 
      and then use mem_enum to have a finite sequence 
      representation of a finite set. *)
  (** Note that this proof is valid for R: relation T 
      R: {relation T} is not requested *)

  Variables (T: finType).
  
  Definition seq_maximal (m : T) (s : seq T) (R: relation T): Prop :=
    forall x, x \in s -> R (m,x) -> m = x.

  Definition maximal (m : T) R: Prop :=
    forall x,  R (m,x) -> m = x.
  
  Local Lemma seq_has_maximal_step (s : seq T) (h : T) R:
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
  
  Local Lemma seq_has_maximal R: 
    porder R -> forall s, ~ (s = [::]) -> (exists m, m \in s /\ seq_maximal m s R).
  Proof.
    move => ?;elim => [// | a s Hr _ ].
    apply: seq_has_maximal_step;first by [].
    by move: (EM (s = [::])) => [-> | /Hr ?];[right | left].
  Qed.    
  
  Lemma has_maximal R: 
    porder R -> (exists x, x\in T) -> (exists m, maximal m R).
  Proof.
    move => Hp [x -];rewrite -mem_enum => Hx.
    have H2: ~ (enum T = [::]) by move: Hx => /[swap] ->.
    move: Hp => /seq_has_maximal/(_ (enum T) H2) [m [Hm HM]]. 
    exists m;move: HM => /[swap] x' /(_ x') HM H5.
    by apply: HM;[rewrite  mem_enum |].
  Qed.

End Maximal.

Section SubSetPType_order.
  (** * When O is a sporder then [:<=: O] restricted to M-independent sets is a porder *)
  
  Context (T : finType).
  Implicit Types (O R M: relation T) (S: {set T}).
  
  Definition setRM R M (S:set T) := S:#R `<=` M#S.
  Definition setRM_fin R M S := (asbool ([:set: S]:#R `<=` M#([:set: S]))).

  Definition prekernelP O R M: pred {set T} := 
    fun S => (RelIndep_fin O S) && ((setRM_fin R M S) && (([:set: S]) != set0)).
  
  (** * setIndep doit s'appeller  prekernelfinType ? *)
  Definition setIndep O R M := setP_type (prekernelP O R M). 
  
  Lemma prekernel O R M S: 
    prekernelP O R M S ->
    RelIndep O [:set: S] /\ setRM R M [:set: S] /\ [:set: S] != set0.
  Proof.
    by rewrite /prekernelP => /andP [/RelIndepE H1 /andP [/asboolP H2 H3]].
  Qed.
  
  Lemma prekernel_notempty O R M 
    (A1: NotEmpty T) (At: sporder O) (Au: R `<=` O):
    exists v, prekernelP O R M [set v].
  Proof.
    move: (At) (@fin_not_iic_inj T O) => [H1 /[dup] Ht /Tclos_iff H2] H3.
    pose proof (@sporder_antisym _ O Ht H1) as Has.
    have H4: Asym O = O
      by apply/(@AsymE T O).
    move: (@iic_asym_injective T O).
    rewrite -H2 H4 => H5.
    have A2: ~ iic O by move => /H5/H3.
    move: (@fin_rloop2 T O R M A1 At Au) => [v H6].
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
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O):
      (exists x : setIndep O R M, x \in {: (setIndep O R M)}).
  Proof.
    move: (@prekernel_notempty O R M A1 Asp Au) => [v Pv].
    by exists (SetP Pv).
  Qed.
  
  Lemma Maximal_fin O R M 
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O):
    exists (m: (setIndep O R M)),
      @maximal (setIndep O R M) m [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic.
  Proof.
    move: (Asp) => /(leSet2_porder R M) po.
    pose proof (@exists_setIndep O R M A1 Asp Au) as Hne.
    by move: (@has_maximal (setIndep O R M)
                [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic
              po Hne).
  Qed.
  
  Lemma Maximal O R M
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O):
    exists S, prekernelP O R M S /\ (forall U, prekernelP O R M U ->
                                    [:set: S] [<= O] [:set: U] -> S = U).
  Proof.
    move: (@Maximal_fin O R M A1 Asp Au)  => [S H3].
    exists S;move: (valP S) => Pr;split; first exact.
    move => U H4; move: H3 => /(_ (SetP H4)) H3.
    by move => /H3/eqP ?;apply/eqP. 
  Qed.
  
End SubSetPType_order.

