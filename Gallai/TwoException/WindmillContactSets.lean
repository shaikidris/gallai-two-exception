/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactSelection

@[expose] public section

/-! # Ambient contact deletion sets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The private vertices of a windmill, embedded in the ambient graph. -/
def windmillPrivateEmbedding (x : evenVertices G) :
    {a : evenVertices G // (evenSubgraph G).Adj x a} ↪ V :=
  ⟨fun a => a.val.val, fun _ _ he => Subtype.ext (Subtype.ext he)⟩

/-- Translate an indexed private selection into the ambient deletion leaves. -/
def windmillPrivateSet (x : evenVertices G)
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}) : Finset V :=
  A.map (windmillPrivateEmbedding x)

theorem windmillPrivateSet_card (x : evenVertices G)
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}) :
    #(windmillPrivateSet x A) = #A := Finset.card_map _

theorem mem_windmillPrivateSet (x : evenVertices G)
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}) (v : V) :
    v ∈ windmillPrivateSet x A ↔ ∃ a ∈ A, a.val.val = v := by
  exact Finset.mem_map

theorem hub_not_mem_windmillPrivateSet (x : evenVertices G)
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}) :
    (x : V) ∉ windmillPrivateSet x A := by
  intro hx
  obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x A x).mp hx
  exact a.property.ne (Subtype.ext ha.symm)

/-- Every ambient private deletion leaf is even and has E-degree two.
The counterexample's windmill theorem, not a caller-supplied cap, proves it. -/
theorem bare_windmillPrivateSet_leaf_guards
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}) :
    ∀ v ∈ windmillPrivateSet x A, Even (G.degree v) ∧ eDegree G v = 2 := by
  intro v hv
  obtain ⟨a, _, rfl⟩ := (mem_windmillPrivateSet x A v).mp hv
  refine ⟨a.val.property, bare_hub_private_eDegree_eq_two h x a.val H
    a.property.reachable ?_⟩
  intro he
  exact a.property.ne (Subtype.ext he.symm)

/-- Actual contact selections provide adjacency and centre avoidance. -/
theorem windmillPrivateSet_contact_guards
    (x : evenVertices G) (u : V)
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hcontact : ∀ a ∈ A, G.Adj u a.val.val) :
    u ∉ windmillPrivateSet x A ∧ ∀ v ∈ windmillPrivateSet x A, G.Adj u v := by
  have hadj : ∀ v ∈ windmillPrivateSet x A, G.Adj u v := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_windmillPrivateSet x A v).mp hv
    exact hcontact a ha
  exact ⟨fun hu => G.irrefl (hadj u hu), hadj⟩

/-- The five ambient row sets have the required odd star size. Erased
vertices must really be selected contacts; the hub is proved absent. -/
theorem windmill_contact_row_parities
    (x : evenVertices G)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (P A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) :
    (Odd #(singleContactPetals f P A) → Odd #(windmillPrivateSet x A)) ∧
    (Even #(singleContactPetals f P A) →
      ∀ q ∈ windmillPrivateSet x A, Odd #((windmillPrivateSet x A).erase q)) ∧
    (Even #(singleContactPetals f P A) → Odd #(insert (x : V) (windmillPrivateSet x A))) ∧
    (Odd #(singleContactPetals f P A) →
      ∀ p ∈ windmillPrivateSet x A,
        Odd #(insert (x : V) ((windmillPrivateSet x A).erase p))) := by
  have hcard : #(windmillPrivateSet x A) = #(singleContactPetals f P A) +
      2 * #(doubleContactPetals f P A) := by
    rw [windmillPrivateSet_card]
    exact indexed_petal_contact_card f hfree P A hindex
  have hx := hub_not_mem_windmillPrivateSet x A
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ho
    rw [Nat.odd_iff] at ho ⊢
    omega
  · intro he q hq
    have hc := Finset.card_erase_add_one hq
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · intro he
    rw [Finset.card_insert_of_notMem hx]
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · intro ho p hp
    have hc := Finset.card_erase_add_one hp
    have hxe : (x : V) ∉ (windmillPrivateSet x A).erase p :=
      fun he => hx (Finset.mem_of_mem_erase he)
    rw [Finset.card_insert_of_notMem hxe]
    rw [Nat.odd_iff] at ho ⊢
    omega

/-- Native adjacency, parity and private-cap inputs for the contact star. -/
theorem bare_windmill_ambient_contact_guards
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V)) (u : V) :
    let A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a} :=
      Finset.univ.filter (fun a => G.Adj u a.val.val)
    (x : V) ∉ windmillPrivateSet x A ∧ u ∉ windmillPrivateSet x A ∧
      ∀ v ∈ windmillPrivateSet x A,
        G.Adj u v ∧ Even (G.degree v) ∧ eDegree G v = 2 := by
  classical
  dsimp only
  let A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a} :=
    Finset.univ.filter (fun a => G.Adj u a.val.val)
  obtain ⟨hu, hadj⟩ := windmillPrivateSet_contact_guards x u A
    (fun a ha => (Finset.mem_filter.mp ha).2)
  refine ⟨hub_not_mem_windmillPrivateSet x A, hu, ?_⟩
  intro v hv
  exact ⟨hadj v hv, bare_windmillPrivateSet_leaf_guards h x H A v hv⟩

/-- The mate interface supplies the complete even-neighbour list at a
private vertex, as required by the spoke and mate restoration lemmas. -/
theorem bare_windmill_private_even_neighbors
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a}) :
    ∀ t, G.Adj p.val.val t → Even (G.degree t) →
      t = (x : V) ∨ t = (f p).val.val := by
  have hpx : p.val.val ≠ (x : V) := by
    intro he
    exact p.property.ne (Subtype.ext he.symm)
  have hpDeg := bare_hub_private_eDegree_eq_two h x p.val H p.property.reachable hpx
  have hxp : (x : V) ∈ evenNeighbors G p.val.val :=
    (mem_evenNeighbors (G := G) _ _).mpr ⟨p.property.symm, x.property⟩
  have hpf : (f p).val.val ∈ evenNeighbors G p.val.val :=
    (mem_evenNeighbors (G := G) _ _).mpr ⟨(hedge p (f p)).mpr rfl, (f p).val.property⟩
  have hxf : (x : V) ≠ (f p).val.val := by
    intro he
    exact (f p).property.ne (Subtype.ext he)
  exact even_neighbors_pair_of_degree_two p.val.val (x : V) (f p).val.val
    hpDeg hxp hpf hxf

/-- The unique petal index gives disjoint ambient two-vertex packets,
including after restricting to the double-contact representatives. -/
theorem indexed_windmill_ambient_pairs_disjoint
    (x : evenVertices G)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P F : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) (hFP : F ⊆ P) :
    (F : Set {a : evenVertices G // (evenSubgraph G).Adj x a}).PairwiseDisjoint
      (fun p => ({p.val.val,(f p).val.val} : Finset V)) := by
  intro r hr s hs hrs
  have hd := indexed_petal_pairs_disjoint f P hindex r s (hFP hr) (hFP hs) hrs
  have hn : ∀ a ∈ ({r,f r} : Finset _), ∀ b ∈ ({s,f s} : Finset _),
      a.val.val ≠ b.val.val := by
    intro a ha b hb he
    have hab : a = b := Subtype.ext (Subtype.ext he)
    exact Finset.disjoint_left.mp hd ha (hab ▸ hb)
  apply Finset.disjoint_left.mpr
  intro t ht ht'
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht ht'
  rcases ht with ht | ht <;> rcases ht' with ht' | ht'
  · exact hn r (by simp) s (by simp) (ht.symm.trans ht')
  · exact hn r (by simp) (f s) (by simp) (ht.symm.trans ht')
  · exact hn (f r) (by simp) s (by simp) (ht.symm.trans ht')
  · exact hn (f r) (by simp) (f s) (by simp) (ht.symm.trans ht')

end Gallai.TwoException
