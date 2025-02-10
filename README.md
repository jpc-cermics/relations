# binary relations and extended oriented graphs

Coq code used to serve as companion code for the followind papers
- [Conditional Separation as a Binary Relation. A Coq Assisted Proof](https://hal.science/hal-03315809v2)
- [Topological Conditional Separation](https://hal.science/hal-03315811)

## Meta

- Author(s):
  - Jean-Philippe Chancelier
- License: see LICENCE file
- Compatible Coq versions: 8.20.1
- Additional dependencies:
  - dune
  - coq-aac-tactics
  - coq-mathcomp-ssreflect
  - coq-mathcomp-classical
- Related publication(s): see above

## What's inside?

- aacset.v:  relations in aac-tactics
- paper_relations.v: lemmata for binary relations used in the two papers
- paper_csbr.v: companion code for Conditional Separation as a Binary Relation
- paper_tcs_facts.v paper_tcs.v paper_tcs_rel.v : companion code for Topological Conditional Separation
- seq1.v: edge, extended oriented paths and active extended oriented paths
- rel.v: binary relations
- ssrel.v: transitive closure (mathcomp/ssreflect version of existing lib/coq/theories/Relations)
- doc/ : repository used to produce snippets of code 
## How to get it

You can:
- either clone it from GitHub at: https://github.com/jpc-cermics/relations

### Compilation

 make

 The makefile will just call dune build
 
 
    

