# Binary relations, extended oriented graphs, kernels

This repository contains a Rocq general library for classical relations 
and Rocq code used as companion material for a set of papers.

## Meta

- Author(s):
  - XXX 
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
- `paper_kernels.v`, `paper_kernels_common.v`, companion developments for kernel-related results
- `rel_dpdgraph.v`: utility to produce graphs for TeX files
  
Unused files:
- `ssrel.v`: transitive closure (MathComp/SSReflect version of `Coq/theories/Relations`)
- `topology.v`: topology notions associated to orders.
- `mypreorder.v`: preorders and related utilities

Documentation and misc:

- `doc/`: material used to produce snippets of code

## Installed packages with opam 
# Name                        # Installed   # Synopsis
coq                           9.1.1         Compatibility metapackage for Coq after the Rocq renaming
coq-core                      9.1.1         Compatibility binaries for Coq after the Rocq renaming
coq-dpdgraph                  1.0+9.1       Compute dependencies between Coq objects (definitions, theorems) and produce graphs
coq-elpi                      3.5.0         Compatibility metapackage for Elpi extension language after the Rocq renaming
coq-mathcomp-algebra          2.5.0         Compatibility package for rocq-mathcomp-algebra
coq-mathcomp-algebra-tactics  1.2.7         Ring, field, lra, nra, and psatz tactics for Mathematical Components
coq-mathcomp-ssreflect        2.5.0         Compatibility package for rocq-mathcomp-ssreflect
coq-mathcomp-zify             1.7.0+2.4+9.0 Compatibility package for rocq-mathcomp-zify
coq-stdlib                    9.0.0         Compatibility metapackage for Coq Stdlib library after the Rocq renaming
rocq-elpi                     3.5.0         Elpi extension language for Coq
rocq-hierarchy-builder        1.10.3        High level commands to declare and evolve a hierarchy based on packed classes
rocq-mathcomp-algebra         2.5.0         Mathematical Components Library on Algebra
rocq-mathcomp-analysis        1.16.0        An analysis library for mathematical components
rocq-mathcomp-analysis-stdlib 1.16.0        A library to link real numbers from mathematical components and Stdlib
rocq-mathcomp-bigenough       1.0.4         A small library to do epsilon - N reasoning
rocq-mathcomp-boot            2.5.0         Small Scale Reflection
rocq-mathcomp-classical       1.16.0        A library for classical logic for mathematical components
rocq-mathcomp-field           2.5.0         Mathematical Components Library on Fields
rocq-mathcomp-fingroup        2.5.0         Mathematical Components Library on finite groups
rocq-mathcomp-finmap          2.2.4         Finite sets, finite maps, finitely supported functions
rocq-mathcomp-order           2.5.0         Mathematical Components Library on order theory
rocq-mathcomp-reals           1.16.0        A library for real numbers for mathematical components
rocq-mathcomp-reals-stdlib    1.16.0        A library to link real numbers from mathematical components and Stdlib
rocq-mathcomp-solvable        2.5.0         Mathematical Components Library on finite groups (II)
rocq-mathcomp-ssreflect       2.5.0         Compatibility package for rocq-mathcomp-boot and rocq-mathcomp-order
rocq-mathcomp-zify            1.7.0+2.4+9.0 Micromega tactics for Mathematical Components
rocq-micromega-plugin         1.1.1         Micromega plugin for Rocq
rocq-runtime                  9.1.1         The Rocq Prover -- Core Binaries and Tools
rocq-stdlib                   9.0.0         The Rocq Proof Assistant -- Standard Library
vsrocq-language-server        2.4.3+1       VSRocq language server

## Compilation

From the repository root:

```sh
make
```

The `Makefile` simply calls:

```sh
dune build
```

