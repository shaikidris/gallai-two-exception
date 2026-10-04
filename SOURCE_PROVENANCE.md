# C2 proof-source provenance

This substantive proof package contains the selected import closure of
`Gallai.TwoException.Main` and `Gallai.TwoException.SimultaneousEndpoint`
from the C2 research formalization. It proves a ceiling path-decomposition
bound with at most two E-degree exceptions, one prescribed endpoint at the
ceiling, simultaneous endpoints within floor(n/2)+1, and simultaneous
ceiling exposure at odd order.

## Manuscript correspondence

The four selected results are presented in Idris Ali Shaik,
[Gallai's conjecture with two exceptional even vertices](https://doi.org/10.5281/zenodo.23134427),
Zenodo preprint, version 1.0.0 (2026): Theorem 1.1, Corollary 1.2,
Proposition 3.1 and Corollary 3.2. The readable preprint and the
implementation-reference manuscript state the same four results.

| Artifact | SHA-256 | Role |
| --- | --- | --- |
| Implementation-reference manuscript | `786e393dfaad34807effe7d4eabb3adbb81e63ed6f13869cca61c4df294a7590` | Manuscript used for the paper-to-Lean correspondence |
| Readable manuscript source | `607346bf1b9d08bac9b2ecfb40c42d576416dbfeb7893a9a3856d844b952d20d` | Exposition source for the preprint |
| Published PDF | `6f7be07b1009ad7a5100b2627a62ac13beba8bdb270034ac171f3172169dca57` | Immutable version 1.0.0 deposited at the cited DOI |

The preprint cites `ddabb48efe1ca579d52a17a41eda9a84ddbbd575` as the
formalization snapshot. This is the proof snapshot associated with the
preprint, rather than the identity of a later Palomar intake snapshot.

## Formalization source

The inherited Gallai inputs originated in the Apache-2.0 bowtie development
at `2f19c6ff50ec0a7cb0d979f33870378299d78fea`. That commit is a historical
extraction source, not the authoritative snapshot for this successor. The
authoritative submission snapshot will be the clean immutable commit handed
to Palomar after the release checks pass. No such submission is claimed here.

Mathlib is pinned to `c55e6e786f49471c72fbddbec5415808896aec1e` with Lean
`leanprover/lean4:v4.35.0-rc3`. This SHA is a software dependency pin, not a
revision of the new mathematical proof. The earlier registered release and
its Comparator are not modified by this package.

| Role | Repository | Commit |
| --- | --- | --- |
| Authoritative substantive successor source | `shaikidris/gallai-two-exception` | The immutable commit selected for replay |
| Proof snapshot cited by the preprint | `shaikidris/gallai-two-exception` | `ddabb48efe1ca579d52a17a41eda9a84ddbbd575` |
| Historical inherited input source | `shaikidris/gallai-bowtie-removal` | `2f19c6ff50ec0a7cb0d979f33870378299d78fea` |
| Mathlib software dependency | `leanprover-community/mathlib4` | `c55e6e786f49471c72fbddbec5415808896aec1e` |

`VISIBILITY_PORT.json` records the source and converted SHA-256 for every
copied module. The mechanical conversion adds a module header, makes imports
public, and exposes the existing declaration section. Its hash record does
not certify elaboration, unchanged kernel terms or independent checking;
those are established by the separate builds and replay reports.

For local diagnostics, `.lake/packages` links to the matching research
dependency cache. It is not part of the distributed snapshot or clean replay.
All release-local Lean outputs are kept in this package's own build directory.
