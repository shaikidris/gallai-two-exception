/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.TriangleHubDeletion

@[expose] public section

/-! # Data-preserving choices of actual component deletions

The constructors retain the triangle labels for subsequent restoration.
Choosing a graph with only abstract degree properties would lose that data.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The three actual local choices in Claim 5, retaining all reconstruction data. -/
inductive ComponentDeletionChoice (u : V) (C : (evenSubgraph G).ConnectedComponent)
  | untouched (hn : ¬ ∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v)
  | isolate (a : evenVertices G) (hC : C.supp = {a}) (ha : G.Adj u a)
  | triangle (a b c : evenVertices G)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hC : ∀ v, v ∈ C.supp ↔ v = a ∨ v = b ∨ v = c)
      (habE : G.Adj a b) (hacE : G.Adj a c) (hbcE : G.Adj b c)
      (hua : G.Adj u a) (horder : G.Adj u c → G.Adj u b)

variable {G}

/-- Claim 4's literal component classification constructs the choice data. -/
theorem componentDeletionChoice_nonempty (u : V)
    (C : (evenSubgraph G).ConnectedComponent)
    (hc : (C.supp.ncard = 1 ∨ C.supp.ncard = 3) ∧ C.toSimpleGraph = ⊤) :
    Nonempty (ComponentDeletionChoice G u C) := by
  classical
  by_cases ht : ∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v
  · rcases hc.1 with hsingle | htriangle
    · obtain ⟨a, ha, hua⟩ := ht
      obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp hsingle
      have hab : a = b := by simpa [hb] using ha
      subst b
      exact ⟨.isolate a hb hua⟩
    · obtain ⟨a, b, c, hab, hac, hbc, hC, habE, hacE, hbcE, hua, ho⟩ :=
        even_triangle_hub_labels u C htriangle hc.2 ht
      exact ⟨.triangle a b c hab hac hbc hC habE hacE hbcE hua ho⟩
  · exact ⟨.untouched ht⟩

namespace ComponentDeletionChoice

variable {u : V} {C : (evenSubgraph G).ConnectedComponent}

/-- The actual selected edge set, preserving the source's partial/full distinction. -/
def graph : ComponentDeletionChoice G u C → SimpleGraph V
  | .untouched _ => ⊥
  | .isolate a _ _ => SimpleGraph.edge u a
  | .triangle a b c _ _ _ _ _ _ _ _ _ => triangleHubDeletion G u a b c

omit [DecidableEq V] in
/-- Every selected edge belongs to the original graph. -/
theorem graph_le (d : ComponentDeletionChoice G u C) : d.graph ≤ G := by
  cases d with
  | untouched => exact bot_le
  | isolate a hC ha => exact (SimpleGraph.edge_le_iff G).mpr (Or.inr ha)
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    exact triangleHubDeletion_le u a b c hua ho hbcE

omit [DecidableEq V] in
/-- An odd hub is distinct from every even vertex used in a local choice. -/
theorem hub_ne_even (hu : Odd (G.degree u)) (a : evenVertices G) : u ≠ a := by
  intro h
  exact (Nat.not_even_iff_odd.mpr hu) (h.symm ▸ a.property)

/-- Local decision instance for the selected graph. -/
noncomputable local instance choiceGraphAdj (d : ComponentDeletionChoice G u C) :
    DecidableRel d.graph.Adj := fun _ _ => Classical.propDecidable _

/-- The selected graph has degree at most one away from the odd hub. -/
theorem degree_le_one (d : ComponentDeletionChoice G u C) (hu : Odd (G.degree u))
    (v : V) (hvu : v ≠ u) : d.graph.degree v ≤ 1 := by
  classical
  cases d with
  | untouched =>
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro p hp q _
    exact False.elim ((SimpleGraph.mem_neighborFinset _ _ _).mp hp)
  | isolate a hC ha =>
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hp := (SimpleGraph.mem_neighborFinset _ _ _).mp hp
    have hq := (SimpleGraph.mem_neighborFinset _ _ _).mp hq
    change (SimpleGraph.edge u a).Adj v p at hp
    change (SimpleGraph.edge u a).Adj v q at hq
    simp only [SimpleGraph.edge_adj] at hp hq
    aesop
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    have hd := triangleHubDeletion_degree (G := G) u a b c
      (hub_ne_even hu a) (hub_ne_even hu b) (hub_ne_even hu c)
      (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
      (fun h => hbc (Subtype.ext h)) v
    simp only [hvu, if_false] at hd
    change (triangleHubDeletion G u a b c).degree v ≤ 1
    rw [hd]
    split_ifs <;> omega

/-- Every non-hub endpoint of a selected edge belongs to its actual component. -/
theorem supported (d : ComponentDeletionChoice G u C) (hu : Odd (G.degree u))
    (v w : V) (h : d.graph.Adj v w) : v = u ∨ v ∈ evenComponentVertices C := by
  classical
  by_cases hvu : v = u
  · exact Or.inl hvu
  right
  cases d with
  | untouched => exact False.elim h
  | isolate a hC ha =>
    change (SimpleGraph.edge u a).Adj v w at h
    have hv : v = a := by
      rcases (SimpleGraph.edge_adj ..).mp h with ⟨⟨he, _⟩ | ⟨he, _⟩, _⟩
      · exact (hvu he).elim
      · exact he
    subst v
    exact ⟨a, by simp [hC], rfl⟩
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    have hd := triangleHubDeletion_degree (G := G) u a b c
      (hub_ne_even hu a) (hub_ne_even hu b) (hub_ne_even hu c)
      (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
      (fun h => hbc (Subtype.ext h)) v
    have hp := h.degree_pos_left
    change 0 < (triangleHubDeletion G u a b c).degree v at hp
    have hv : v = a ∨ v = b ∨ v = c := by
      by_contra hn
      simp [hvu, hn] at hd
      omega
    rcases hv with rfl | rfl | rfl
    · exact ⟨a, (hC a).mpr (Or.inl rfl), rfl⟩
    · exact ⟨b, (hC b).mpr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨c, (hC c).mpr (Or.inr (Or.inr rfl)), rfl⟩

/-- Every hub neighbour in a touched component is incident with a deleted edge,
even if its hub spoke is retained in the two-neighbour triangle case. -/
theorem covers_neighbor (d : ComponentDeletionChoice G u C) (hu : Odd (G.degree u))
    (v : V) (hv : v ∈ evenComponentVertices C) (huv : G.Adj u v) :
    0 < d.graph.degree v := by
  classical
  obtain ⟨t, ht, rfl⟩ := hv
  cases d with
  | untouched hn => exact (hn ⟨t, ht, huv⟩).elim
  | isolate a hC ha =>
    have hta : t = a := by simpa [hC] using ht
    subst t
    apply SimpleGraph.Adj.degree_pos_right
    change (SimpleGraph.edge u a).Adj u a
    exact (SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, ha.ne⟩
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    have hd := triangleHubDeletion_degree (G := G) u a b c
      (hub_ne_even hu a) (hub_ne_even hu b) (hub_ne_even hu c)
      (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
      (fun h => hbc (Subtype.ext h)) t
    have htu : (t : V) ≠ u := (hub_ne_even hu t).symm
    have hm : (t : V) = a ∨ (t : V) = b ∨ (t : V) = c := by
      rcases (hC t).mp ht with h | h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (Or.inl (congrArg Subtype.val h))
      · exact Or.inr (Or.inr (congrArg Subtype.val h))
    change 0 < (triangleHubDeletion G u a b c).degree t
    simp [hd, htu, hm]

end ComponentDeletionChoice
end Gallai
