# C2 proof-source provenance

This substantive proof package contains the selected import closure of
`Gallai.TwoException.Main` and `Gallai.TwoException.SimultaneousEndpoint`
from the C2 research formalization. It proves a ceiling path-decomposition
bound with at most two E-degree exceptions, one prescribed endpoint at the
ceiling, simultaneous endpoints within floor(n/2)+1, and simultaneous
ceiling exposure at odd order.

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
