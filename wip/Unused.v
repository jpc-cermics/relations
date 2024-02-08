Section pairp.
  (** * Utilities when pairing sequences *) 
  (** * (Lift (pair st so)) = pairp (Lift st) (Lift so) *)
  (* 
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
  

  Lemma pairp_sz: forall (st: seq(T*T)) (so: seq (O*O)),
      size(st) = size (so) -> size (pairp st so) = size st.
  Proof.
    elim => [so //= | tt st Hr so H1].
    have H2: size(so) > 0 by rewrite -H1 //.
    pose proof seq_c H2 as [so' [oo H3]].
    rewrite H3 /pairp -/pairp /size -2!/size Hr.
    by [].
    by rewrite H3 /= in H1; apply succn_inj.
  Qed.

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
  *)

End pairp.

  Lemma Epe_L1: forall (spt: seq (T*T)) (x y:T),
      size(spt) > 0 -> spt [Suc\in] (@Chrel T) -> Epe spt = (x, y) 
      -> exists st, size(st) > 1 /\ spt = Lift st /\ Pe st =(x,y).
  Proof.
    move => spt x y H1 H2 H3.
    have H4: spt \in (@I T) by apply inP.
    pose proof Lift_surj H4 as [st [H5 H6]].
    have H7:(UnLift (Lift st) ptv.1) = st by apply UnLift_left;rewrite inP in H5.
    by exists st; rewrite -Lift_sz2 H6; rewrite /Epe -H6 H7 in H3.
  Qed.
  
  Lemma Epe_L2: forall (st: seq T) (x y:T),
      size st > 1 -> Pe st =(x,y) -> exists q, st = x::(rcons q y).
  Proof.
    move => st x y H1 H2.
    pose proof seq_crc H1 as [q [x' [y' H3]]].
    move: H2;rewrite /Pe H3 //= => [[H2 //= H4]].
    have H5: forall q' x'', last x'' (rcons q' y') = y'
        by elim;[| move => z q' Hr x'';rewrite rcons_cons /=; rewrite Hr].
    by exists q;rewrite H2 -H4 H5.
  Qed.

  Lemma Epe_L2': forall (st: seq T) (x y:T),
      size st > 1 -> Pe st =(x,y) -> Epe1 (Lift st) = (x,y).
  Proof.
    move => st' x y H1 H2.
    pose proof Epe_L2 H1 H2 as [st H3].
    rewrite H3 /Epe1.
    pose proof Lift_head st ptv x y as H9.
    pose proof Lift_last st ptv x y as H10.
    by rewrite H9 H10 /=.
  Qed.
  
  Lemma Epe_L3: forall (spt: seq (T*T)) (x y:T),
      size(spt) > 0 -> spt [Suc\in] (@Chrel T) -> Epe spt = (x, y) 
      -> exists (st: seq T), spt = Lift (x::(rcons st y)).
  Proof.
    move => spt x y H1 H2 H3.
    pose proof Epe_L1 H1 H2 H3 as [st' [H4 [H5 H6]]].
    pose proof Epe_L2 H4 H6 as [st H7].
    by exists st; rewrite -H7 -H5.
  Qed.
  
  Lemma Epe_L4: forall (spt: seq (T*T)) (pt: T*T) (x y:T),
      size(spt) > 0 -> spt [Suc\in] (@Chrel T) -> Epe spt = (x, y) 
      -> Epe1 spt = (x,y).
  Proof.
    move => spt pt x y H1 H2 H3.
    pose proof Epe_L1 H1 H2 H3 as [st' [H5 [H6 H7]]].
    pose proof Epe_L2 H5 H7 as [st H8].
    rewrite H6 H8.
    rewrite /Epe1. 
    pose proof Lift_head st ptv x y as H9.
    pose proof Lift_last st ptv x y as H10.
    by rewrite H9 H10 /=.
  Qed.

  (** * XXXX unused but kept for intermediate nodes *)

  Definition decomp (st: seq T) := 
    (head t st, last t st, behead (behead (belast t st))).
  Definition comp (tr: T*T*(seq T)) := tr.1.1::(rcons tr.2 tr.1.2).

  Lemma Pe_eq: forall (st: seq T), Pe st = (decomp st).1.
  Proof. move => st //. Qed.

  Definition Edecomp (spt: seq (T*T)) := (decomp (UnLift spt t)).
  Definition Ecomp (tr: T*T*(seq T)) := Lift (comp tr).

  Lemma Epe_eq: forall (spt: seq (T*T)), Epe spt = (Edecomp spt).1.
  Proof. move => spt //. Qed.
  
  Definition D1 (x y :T) := [set st:seq T | (decomp st).1 = (x,y)].
  Definition I1 (x y :T) := [set spt:seq (T*T) | (Edecomp spt).1 = (x,y)].

  Lemma D1_eq: forall (x y:T), D1 x y = [set st:seq T | Pe st = (x,y)]. 
  Proof.
    by move => x y;rewrite /D1 /mkset predeqE => st;rewrite Pe_eq.
  Qed.

  Lemma I1_eq: forall (x y:T), I1 x y = [set spt:seq (T*T) | Epe spt = (x,y)].
  Proof.
    move => x y; rewrite /I1 /mkset predeqE => spt.
    by rewrite /Edecomp /Epe /Pe /decomp /=.
  Qed.
  
  Lemma Lxx: forall (st:seq T), size(st)> 1 -> comp (decomp st) = st.
  Proof. 
    move => p.
    pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //.
    move => _.
    by rewrite /decomp /comp /= belast_rcons last_rcons /=.
  Qed.

  Lemma Lyy: forall (tr: T*T*(seq T)),  decomp (comp tr) = tr.
  Proof. 
    move => [[x p] y].
    by rewrite /comp /decomp /=  belast_rcons last_rcons /=.
  Qed.




Section Pair_of_seq.
  (** * pair of sequences using Record *)
  Variables (T S: Type).
  
  Record Pairs (n m:nat) 
    := pair_s { pfst: (seq T);
               psnd: (seq S);
               cond1: size(pfst) >= n;cond2: size(pfst)=size(psnd) + m}.

  Definition Pairs0 : (Pairs 0 0).
  Proof.
    by refine {| pfst:= [::]; psnd:= [::]; cond1:= _;cond2:= _|}.
  Defined.
  
  (* define a cons operator for Pairs: second way with refine *)
  Definition spair_cons (n m:nat) (ts: T*S) (sp : Pairs n m) : (Pairs n m).
  Proof.
    refine {| pfst:= (ts.1::(pfst sp)); psnd:= (ts.2::(psnd sp)); cond1:= _;cond2:= _|}.
    by apply leqW; apply (cond1 sp).
    by rewrite /= (cond2 sp) -addn1 -addnA [m+1]addnC addnA addn1. 
  Defined.
  
  Definition Pair (ps: (Pairs 0 0)) (s:S) := pair_ (pfst ps) (psnd ps).
  
  Definition Unpair (s: seq (T*S)) : (Pairs 0 0).
  Proof.
    refine {| pfst:= (unpair s).1;psnd := (unpair s).2;cond1:= _ ;cond2:= _|}.
    by [].
    by rewrite addn0 unpair_sz.
  Defined. 
  
  Lemma unpair_right': forall(s: S) (sts: seq (T*S)),
      Pair (Unpair sts) s = sts.
  Proof.
    move => s;elim => [/= | [t1 s1] sts Hrt]. 
    by rewrite /Pair /=.
    by rewrite /Pair /= -[in RHS]Hrt.
  Qed.

End Pair_of_seq.

Section LiftO. 
  (** * LiftO with Record *)
  Variables (T S: Type).
  
  Lemma size_l: forall (ps : (@Pairs T S 2 1)), size((Lift (pfst ps)))= size(psnd ps) + 0.
  Proof.
    move => ps. 
    pose proof (cond2 ps) as H1.
    pose proof (cond1 ps) as H2.
    pose proof (Lift_sz H2) as H3. 
    by rewrite H3 H1 addn1 addn0 subn1.
  Qed.
  
  Lemma size_gt1: forall (ps : (@Pairs T S 2 1)), size((Lift (pfst ps))) > 0.
  Proof.
    move => ps. 
    pose proof (cond2 ps) as H1.
    pose proof (cond1 ps) as H2.
    pose proof (Lift_sz H2) as H3. 
    rewrite H3 H1 addn1 subn1 /=.
    pose proof ltn_predK H2 as H4.
    rewrite -H4 addn1 in H1. apply succn_inj in H1.
    by rewrite -H1 ltn_predRL.
  Qed.
  
  Definition LiftT (s: (@Pairs T S 2 1)): (@Pairs (T*T) S 1 0) := 
    {| pfst:= (Lift (pfst s));psnd:=(psnd s);cond1:= size_gt1 s ; cond2:= size_l s |}.

End LiftO.
