# Binary relations and extended oriented graphs

This repository contains Coq code used as companion material for the following papers:

- [Conditional Separation as a Binary Relation. A Coq Assisted Proof](https://hal.science/hal-03315809v2)
- [Topological Conditional Separation](https://hal.science/hal-03315811)
- [A formal proof of the Sands-Sauer-Woodrow theorem](https://hal.science/xxxxxx)

## Meta

- Author(s):
  - Jean-Philippe Chancelier
- License: see `LICENCE`
- Compatible Coq versions: 8.20.1
- Build system: `dune`
- Additional dependencies:
  - `coq-aac-tactics`
  - `coq-mathcomp-ssreflect`
  - `coq-mathcomp-classical`
- Related publication(s): see above

## What's inside?

Binary relations: 

- `rel.v`: binary relations as sets 

Graphs and paths:

- `seq1.v`: edges, extended oriented paths, and active extended oriented paths
- `seq2.v`: additional results on paths using eqtype and uniq 

Paper companion files:

- `paper_relations.v`: lemmas for binary relations used in the two first papers
- `paper_csbr.v`: companion code for *Conditional Separation as a Binary Relation*
- `paper_csbr_paths.v`: path-related lemmas used in the CSBR development
- `paper_tcs_facts.v`, `paper_tcs.v`: companion code for *Topological Conditional Separation*
- `paper_monochromatic.v`, `paper_monochromatic_f.v`: companion developments for monochromatic-related results
- `rel_dpdgraph.v`: utility to produce graphs for TeX files
  
Unused files:
- `ssrel.v`: transitive closure (MathComp/SSReflect version of `Coq/theories/Relations`)
- `topology.v`: topology notions associated to orders.
- `mypreorder.v`: preorders and related utilities

Documentation and misc:

- `doc/`: material used to produce snippets of code

## How to get it

Clone from GitHub:

- https://github.com/jpc-cermics/relations

## Compilation

From the repository root:

```sh
make
```

The `Makefile` simply calls:

```sh
dune build
```

