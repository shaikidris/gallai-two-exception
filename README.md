# Gallai's conjecture with two exceptional even vertices

Let `EV(G)` be the subgraph induced by the even-degree vertices of a finite
simple graph. This development proves that every connected such graph has
an edge partition into at most `ceil(|V(G)|/2)` nonempty simple paths when
at most two vertices of `EV(G)` have degree greater than three.

There is no bound on the ordinary degrees or on the two exceptional E-degrees.
The result also permits one positive even vertex in the designated pair to
be prescribed as an endpoint of at least two paths at the ceiling budget.
At odd order both designated vertices can be exposed twice in the same
decomposition. At arbitrary order the simultaneous conclusion uses
`floor(|V(G)|/2)+1` paths. Simultaneous ceiling exposure at even order and
the unrestricted Gallai conjecture are not asserted.

The corresponding paper is Idris Ali Shaik,
[Gallai's conjecture with two exceptional even vertices](https://doi.org/10.5281/zenodo.23134427),
Zenodo preprint, version 1.0.0 (2026). Theorem 1.1, Corollary 1.2,
Proposition 3.1 and Corollary 3.2 correspond to the four declarations below.
The manuscript is licensed under CC BY 4.0; the formalization is licensed
under Apache-2.0.

## Selected statements

| Declaration in `Gallai.Submission` | Conclusion |
|---|---|
| `prescribed_endpoint` | Ceiling budget with one prescribed vertex exposed twice |
| `ceiling_bound` | Ceiling budget with at most two E-degree exceptions |
| `simultaneous_floor_add_one` | Both designated vertices exposed twice within floor plus one |
| `odd_order_simultaneous` | Both designated vertices exposed twice within the odd-order ceiling |

`Challenge.lean` states these claims using Mathlib graphs and walks, and
literal definitions of nonempty simple paths, edge partitions, endpoint
counts and E-degrees. `Solution.lean` supplies the corresponding proofs.
`comparator.json` selects the four declarations for comparison. Isolated
vertices contribute no path; every edge is covered exactly once.

## Proof development

The proof establishes the prescribed-endpoint theorem by finite-graph
induction. A bare prescribed vertex reduces to a windmill at the other
exception, ordinary triangles and isolated even vertices. Contact-restoration
schedules preserve the endpoint reserve. Cut-vertex gluing and retained-edge
restoration give the general theorem. The zero-, one- and two-exception
cases then yield the path-number conclusion. The simultaneous statements
use edge addition/deletion and the bridge/nonbridge alternatives.

The supporting published results are formalized in the proof cone:

- Botler–Sambinelli, [Towards Gallai's path decomposition conjecture](https://arxiv.org/abs/1911.04546).
- Fan–Hou–Zhou, [Gallai's Conjecture on Path Decompositions](https://doi.org/10.1007/s40305-022-00435-3).
- Fan, [Path decompositions and Gallai's conjecture](https://doi.org/10.1016/j.jctb.2004.09.008).

The selected roots permit only `propext`, `Classical.choice` and `Quot.sound`.
The Challenge's deliberate statement holes are excluded from proof counts.
No finite graph census is a premise of the four selected results.

## Environment and provenance

Lean: `leanprover/lean4:v4.35.0-rc3`.
Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e`.
The manifest fixes the transitive dependencies. See `SOURCE_PROVENANCE.md`
for source identities and `VISIBILITY_PORT.json` with
`VISIBILITY_REPAIRS.md` for the module-system conversion.

Software licence: Apache-2.0. Idris Ali Shaik is responsible for this
formalization. OpenAI Codex and Claude assisted the mathematical development,
Lean implementation and review. Registry verification and automated editorial
review do not constitute a literature-priority finding or human peer review.
