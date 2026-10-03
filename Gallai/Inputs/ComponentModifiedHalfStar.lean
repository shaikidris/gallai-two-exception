/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedSupply

@[expose] public section

/-! # Inward restoration of the enlarged star

The initial odd hub supplies the extra endpoint which later compensates the
exceptional two-spoke triangle's one-unit counting deficit.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- A selected leaf of the enlarged star is an original hub neighbour. -/
theorem componentModifiedLeaves_adj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (ha : G.Adj u e.1) (v : V)
    (hv : v ∈ insert e.1 (componentDeletionLeaves d)) : G.Adj u v := by
  rcases Finset.mem_insert.mp hv with h | h
  · exact h ▸ ha
  · exact componentDeletionLeaves_adj d v h

/-- The enlarged selected star does not include its centre as a leaf. -/
theorem componentModifiedLeaves_not_hub
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (ha : G.Adj u e.1) :
    u ∉ insert e.1 (componentDeletionLeaves d) := by
  intro h
  exact (componentModifiedLeaves_adj d e ha u h).ne rfl

/-- Restore a prescribed half of the enlarged star after its opposite matching.
The exact vector, extra endpoint and strict reserve use one common output. -/
theorem Decomposition.restore_modified_half_star
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (hs : Odd #(componentDeletionLeaves d))
    (D : Decomposition (G \ componentModifiedDeletion d e))
    (b : V) (hb : b ∈ insert e.1 (componentDeletionLeaves d)) :
    ∃ B : Finset V, B ⊆ insert e.1 (componentDeletionLeaves d) ∧ b ∈ B ∧
      #(insert e.1 (componentDeletionLeaves d)) ≤ 2 * #B ∧
      ∃ Q : Decomposition (starPuncture G u (insert e.1 (componentDeletionLeaves d)) ⊔
          B.sup (SimpleGraph.edge u)),
        Q.size = D.size ∧
        (∀ v, Q.endpointCount v + (if v ∈ B then 1 else 0) +
            (∑ f ∈ (componentDeletionPairs d).erase e, if f.2 = v then 1 else 0) =
          D.endpointCount v +
            (∑ f ∈ (componentDeletionPairs d).erase e, if f.1 = v then 1 else 0) +
            if u = v then #B else 0) ∧
        Q.endpointCount u = D.endpointCount u + #B ∧
        #B + 1 ≤ Q.endpointCount u ∧
        #((insert e.1 (componentDeletionLeaves d)) \ B) < Q.endpointCount u ∧
        (4 ≤ #(insert e.1 (componentDeletionLeaves d)) → 3 ≤ Q.endpointCount u) := by
  classical
  obtain ⟨E, hE, hvect⟩ := D.restore_modified_pairs_to_star d hu e he ha hs
  obtain ⟨heu, hpos⟩ := D.modified_matching_supply d hu e he ha E hvect
  have huS := componentModifiedLeaves_not_hub d e ha
  have hmissing := starPuncture_missing G u (insert e.1 (componentDeletionLeaves d)) huS
  obtain ⟨B, hB, hbB, hhalf, Q, hQ, hq⟩ := E.prescribed_half_star_addibility u
    (insert e.1 (componentDeletionLeaves d)) huS hmissing
    (fun v hv => hpos v (hv.elim (fun h => h.1)
      (componentModifiedLeaves_adj d e ha v))) b hb
  have huB : u ∉ B := fun h => huS (hB h)
  have hqu : Q.endpointCount u = D.endpointCount u + #B := by
    have h : Q.endpointCount u = E.endpointCount u + #B := by
      simpa [huB] using hq u
    rwa [heu] at h
  have hdu := D.endpointCount_pos_of_odd_degree u
    (componentModifiedDeletion_odd_hub d hu e he ha hs)
  refine ⟨B, hB, hbB, hhalf, Q, hQ.trans hE, ?_, hqu, ?_, ?_, ?_⟩
  · intro v
    have h₁ := hvect v
    have h₂ := hq v
    omega
  · omega
  · have hc := Finset.card_sdiff_add_card_eq_card hB
    omega
  · intro hsize
    omega

end Gallai
