# Visibility-port addendum

`VISIBILITY_PORT.json` records the initial mechanical conversion from the
research source. The following release-only declarations additionally require
public visibility because exposed public definitions or declaration types use
them. Their bodies and types are unchanged. The research source is untouched.

| Owner module | Helpers made public |
|---|---|
| Gallai.Operations.DecompositionSplit | splitFamily, splitFamily_covers |
| Gallai.Operations.AddEdge | addFamily, addFamily_mem_edges |
| Gallai.Operations.EraseCarrier | eraseFamily, eraseFamily_covers, eraseManyFamily, eraseManyFamily_covers |
| Gallai.Operations.DecompositionTrim | other_avoids_first, trimFamily, trimFamily_edges |
| Gallai.Operations.Rotate | rotation_left_edges, rotation_right_edges |
| Gallai.Transport.RunSlots | terminal_hyp, through_hyp |
| Gallai.Operations.InsertEdge | edgePath, insertEdgeFamily, insertEdgeFamily_covers |

The six-owner focused build passed. The complete selected-root rebuild after
the InsertEdge repair passed (1,781 jobs). The mechanical port
script intentionally rejects these files as no longer byte-identical to its
initial transformation; do not rerun it to overwrite the repairs.

Release formatting also removes trailing spaces and redundant blank lines at
end of file. The initial conversion hashes precede these whitespace-only
changes; the immutable release commit identifies the distributed source.
