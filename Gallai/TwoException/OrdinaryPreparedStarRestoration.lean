/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPendingBound
public import Gallai.TwoException.OrdinaryAssembledHalfStarGain
public import Gallai.TwoException.PacketGainStarRestoration

@[expose] public section

/-! # Reassembling the prepared ordinary star within its path budget -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance preparedStarEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance preparedStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- Ordinary packet gain together with existing centre endpoints forces
full restoration. The actual pending bound and gain are derived, not assumed. -/
theorem bare_ordinary_prepared_star_restore
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (S : Finset (evenVertices G))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hSh : ∀ t ∈ S, (t : V) ≠ h)
    (hadj : ∀ t ∈ insert (x : V) ((F.biUnion P).image Subtype.val), G.Adj u t)
    (hcover : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (havoid : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∉ P C ∧ e.2 ∉ P C)
    (hlabels : ∀ C ∈ F, ∀ e ∈ mates C, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P C)
    (hspecial : ∀ C ∈ F, C ∈ special →
      #(ordinaryComponentPacket G S C) = 2 ∧ P C = ordinaryComponentPacket G S C)
    (D : Decomposition (starPuncture G u (insert (x : V) ((F.biUnion P).image Subtype.val))))
    (hstrict : #special < #F + D.endpointCount u)
    (hrec : ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
      2 ≤ D.endpointCount e.1)
    (hpositive : ∀ t, (starPuncture G u (insert (x : V)
      ((F.biUnion P).image Subtype.val))).Adj u t ∨
      t ∈ insert (x : V) ((F.biUnion P).image Subtype.val) → 0 < D.endpointCount t)
    (hDu : 0 < D.endpointCount u ∨
      Odd (insert (x : V) ((F.biUnion P).image Subtype.val)).card) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ t, t ≠ u → t ∉ insert (x : V) ((F.biUnion P).image Subtype.val) →
        E.endpointCount t = D.endpointCount t := by
  classical
  let L := (F.biUnion P).image Subtype.val
  let B := insert (x : V) L
  have hxL : (x : V) ∉ L := by
    intro ht
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
    have he' : a = x := Subtype.ext he
    obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
    exact hx C hC (he' ▸ (Finset.mem_filter.mp (hP C hC ha)).2)
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hleaves : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact x.property
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ht
      exact a.property
  have hPB : ∀ C ∈ F, (P C).image Subtype.val ⊆ B := by
    intro C hC t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a,Finset.mem_biUnion.mpr ⟨C,hC,ha⟩,rfl⟩)
  have hmissing : ∀ t ∈ B, ¬ (starPuncture G u B).Adj u t := by
    intro t ht ha
    exact ha.2 ((star_sup_adj_center u B huB t).mpr ht)
  obtain ⟨E,hsize,hend⟩ := restore_star_of_packet_gain D u x L hxL huB hmissing hpositive hDu
    (by
      intro A hAB hxA Q _ t ht
      have htL : t ∈ L := by
        rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp ht).1 with he | hl
        · exact False.elim ((Finset.mem_sdiff.mp ht).2 (he ▸ hxA))
        · exact hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp htL
      obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
      have hap := Finset.mem_filter.mp (hP C hC ha)
      exact bare_ordinary_half_star_pending_le_two h x a H C (hx C hC) hap.2
        (hSh a hap.1) u B A hAB hadj hleaves ht Q)
    (by
      intro A hAB _ Q hvec htight
      have hg := bare_ordinary_assembled_half_star_gain h x H u B A hAB hadj hleaves
        S F special P mates hF hx hP hPB hcover havoid hlabels hspecial D hrec Q hvec htight
      change #(L \ A) + 1 ≤ #(L ∩ A) + D.endpointCount u
      change #(L \ A) + #F ≤ #(L ∩ A) + #special at hg
      omega)
  have hgraph : starPuncture G u B ⊔ B.sup (SimpleGraph.edge u) = G := by
    rw [ordinary_half_star_graph u B B (by rfl) hadj, Finset.sdiff_self]
    simp [starPuncture]
  have hout : ∃ E : Decomposition (starPuncture G u B ⊔ B.sup (SimpleGraph.edge u)),
      E.size = D.size ∧ ∀ t, t ≠ u → t ∉ B → E.endpointCount t = D.endpointCount t :=
    ⟨E,hsize,hend⟩
  rwa [hgraph] at hout

end Gallai.TwoException
