/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyMixedSeparation
public import Gallai.TwoException.OrdinaryFiniteMateAssembly
public import Gallai.TwoException.WindmillContactSets

@[expose] public section

/-! # Mixed ordinary mates avoid the entire early deletion star -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mixedMateGuardComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- Local regular-mate data supply disjointness, genuine even edges, and
avoidance of the centre, both selected families, the hub and the spare private.
Special packet spokes stay in the avoidance union although their mates are
not deleted. -/
theorem early_mixed_mate_guards
    (u : V) (hu : Odd (G.degree u)) (x q : evenVertices G) (hxq : G.Adj x q)
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ Z ∈ F, ∀ t ∈ Q Z, t ∈ Z.supp)
    (hx : ∀ Z ∈ F, x ∉ Z.supp)
    (hlen : ∀ Z ∈ F, Z ∉ special → (mates Z).length ≤ 1)
    (hmates : ∀ Z ∈ F, Z ∉ special → ∀ e ∈ mates Z,
      G.Adj e.1 e.2 ∧ e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp ∧
      e.1 ∉ Q Z ∧ e.2 ∉ Q Z) :
    let O := ((F \ special).toList.flatMap mates).map
      (fun e => ((e.1 : V),(e.2 : V)))
    O.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
    ∀ e ∈ O, (G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) ∧
      (e.1 ≠ u ∧ e.2 ≠ u ∧
        e.1 ∉ windmillPrivateSet x A ∪ (F.biUnion Q).image Subtype.val ∧
        e.2 ∉ windmillPrivateSet x A ∪ (F.biUnion Q).image Subtype.val ∧
        e.1 ≠ (x : V) ∧ e.2 ≠ (x : V) ∧ e.1 ≠ (q : V) ∧ e.2 ≠ (q : V)) := by
  classical
  dsimp only
  have hassembly := ordinary_finite_mate_assembly G (F \ special) Q mates
    (fun Z hZ => hsupp Z (Finset.mem_sdiff.mp hZ).1)
    (fun Z hZ => hlen Z (Finset.mem_sdiff.mp hZ).1 (Finset.mem_sdiff.mp hZ).2)
    (fun Z hZ => hmates Z (Finset.mem_sdiff.mp hZ).1 (Finset.mem_sdiff.mp hZ).2)
    x (fun Z hZ => hx Z (Finset.mem_sdiff.mp hZ).1)
  refine ⟨hassembly.1,?_⟩
  intro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  obtain ⟨Z,hZ,haZ⟩ := List.mem_flatMap.mp ha
  obtain ⟨hZF,hZS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hZ)
  obtain ⟨hedge,hl,hr,hlQ,hrQ⟩ := hmates Z hZF hZS a haZ
  have hsep := early_ordinary_component_spoke_separation x q hxq Z (hx Z hZF)
  have havK : ∀ t : evenVertices G, t ∈ Z.supp →
      (t : V) ∉ windmillPrivateSet x A := by
    intro t ht hk
    obtain ⟨b,hb,he⟩ := (mem_windmillPrivateSet x A _).mp hk
    have htB : t = b.val := Subtype.ext he.symm
    have hbZ : b.val ∈ Z.supp := htB ▸ ht
    exact hx Z hZF (Z.mem_supp_of_adj_mem_supp hbZ b.property.symm)
  have havL := ordinary_component_vertex_avoids_spoke_union G F Q hsupp Z
  have hlB : (a.1 : V) ∉ windmillPrivateSet x A ∪ (F.biUnion Q).image Subtype.val := by
    simpa only [Finset.mem_union,not_or] using And.intro (havK a.1 hl) (havL a.1 hl hlQ)
  have hrB : (a.2 : V) ∉ windmillPrivateSet x A ∪ (F.biUnion Q).image Subtype.val := by
    simpa only [Finset.mem_union,not_or] using And.intro (havK a.2 hr) (havL a.2 hr hrQ)
  have hlu : (a.1 : V) ≠ u := by
    intro ht
    exact (Nat.not_even_iff_odd.mpr hu) (ht ▸ a.1.property)
  have hru : (a.2 : V) ≠ u := by
    intro ht
    exact (Nat.not_even_iff_odd.mpr hu) (ht ▸ a.2.property)
  exact ⟨⟨hedge,a.1.property,a.2.property⟩,hlu,hru,hlB,hrB,
    (hsep a.1 hl).1,(hsep a.2 hr).1,(hsep a.1 hl).2,(hsep a.2 hr).2⟩

end Gallai.TwoException
