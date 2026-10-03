/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3HubBudget
public import Gallai.TwoException.EarlyT3E3Restoration

@[expose] public section

/-! # Native hub-inclusive T3/E3 contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Star deletion and a fixed edge deletion commute as graphs. -/
theorem t3_star_delete_comm (u : V) (B : Finset V) (b c : V) :
    (starPuncture G u B).deleteEdges {s(b,c)} =
      starPuncture (G.deleteEdges {s(b,c)}) u B := by
  ext v w
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sdiff_adj]
  tauto

/-- Original labels in the hub-inclusive E3 row construct the auxiliary
decomposition and restore the graph within its ceiling budget. -/
theorem bare_native_t3_E3_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c})
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hu : u ∉ S) (haS : (a : V) ∉ S) (hua : G.Adj u a)
    (huOdd : Odd (G.degree u)) (hodd : Odd #S)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbS : (b : V) ∉ S) (hcS : (c : V) ∉ S)
    (hadj : ∀ t ∈ S, G.Adj u t) (heven : ∀ t ∈ S, Even (G.degree t))
    (hxS : (x : V) ∈ S)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ insert (a : V) S ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (hS : ∀ t ∈ S, t = (x : V) ∨ t ∈ privates)
    (hprivateNonempty : privates.Nonempty) (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ S)
    (hhu : h ≠ u) (hha : h ≠ (a : V)) (hhb : h ≠ (b : V))
    (hhc : h ≠ (c : V)) (hhS : h ∉ S) : False := by
  classical
  have hcap : ∀ t ∈ S, t ≠ (x : V) → eDegree G t ≤ 2 := by
    intro t ht htx
    rcases hS t ht with ht | ht
    · exact False.elim (htx ht)
    · exact (hprivates t ht).2.le
  have hseparate : ∀ t ∈ S, ¬ G.Adj a t := by
    intro t ht hat
    rcases triangle_component_even_neighbors Z b a c
      (by rw [hsupp]; ext w; simp; tauto) t hat (heven t ht) with hb | hc
    · exact hbS (hb ▸ ht)
    · exact hcS (hc ▸ ht)
  have hout := bare_t3_hub_auxiliary_endpoint h u x H (insert (a : V) S)
    privates Z a b c hsupp hbc (Finset.mem_insert_of_mem hxS) (by simp)
    (by simp [hab.ne.symm,hbS]) (by simp [hca.ne,hcS]) hbu hcu
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact ht ▸ hua
      · exact hadj t ht)
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact ht ▸ a.property
      · exact heven t ht)
    hcontacts
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inr (Or.inr ht)
      · rcases hS t ht with ht | ht
        · exact Or.inl ht
        · exact Or.inr (Or.inl ht))
    hprivateNonempty hprivateCentre hprivates
    (fun t ht hadj => Finset.mem_insert_of_mem (hprivateContacts t ht hadj))
    hhu (by simp [hha,hhS]) hhb hhc
  rw [t3_star_delete_comm] at hout
  obtain ⟨D,hs,hh⟩ := hout
  obtain ⟨E,he,hhE⟩ := restore_t3_E3 Z a b c hsupp hab hbc hca u h x S
    hu haS hua huOdd hodd hbu hcu hbS hcS hadj heven hxS hcap hseparate
    hcontacts hhu hha hhb hhc hhS D hh
  apply H.counterexample.2
  exact ⟨E,by rw [he]; exact hs,hhE⟩

end Gallai.TwoException
