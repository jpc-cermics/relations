Require dpdgraph.dpdgraph.

(* Set Warnings "-parsing -coercions". *)
(* From mathcomp Require Import all_ssreflect order. *)
(* From mathcomp Require Import mathcomp_extra boolp. *)
(* From mathcomp Require Import classical_sets. *)
(* Set Warnings "parsing coercions". *)

From RL Require paper_csbr paper_relations seq1 paper_tcs_facts.

Set DependGraph File "graph.dpd".
Print FileDependGraph paper_csbr. 

Set DependGraph File "graph2.dpd".
Print FileDependGraph paper_relations.

Set DependGraph File "graph3.dpd".
Print FileDependGraph seq1.

Set DependGraph File "graph4.dpd".
Print FileDependGraph paper_tcs_facts.





