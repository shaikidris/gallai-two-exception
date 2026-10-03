/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparedHalfStarGain
public import Gallai.TwoException.OrdinaryContactShapes

@[expose] public section

/-! # Regular packet labels retained after actual mate restoration -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A singleton prepared packet with a restored mate supplies exactly the
regular triangle shape and recipient reserve consumed by half-star gain. -/
theorem ordinary_restored_singleton_packet_shape
    (C : (evenSubgraph G).ConnectedComponent)
    (P : Finset (evenVertices G)) (mates : List (evenVertices G × evenVertices G))
    (hsupp : ∀ t ∈ P, t ∈ C.supp) (hnon : mates ≠ [])
    (havoid : ∀ e ∈ mates, e.1 ∉ P ∧ e.2 ∉ P)
    (hlabels : ∀ e ∈ mates, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P)
    (J : SimpleGraph V) [DecidableRel J.Adj] (D : Decomposition J)
    (hrec : ∀ e ∈ mates, 2 ≤ D.endpointCount e.1) :
    ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
      P.image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b := by
  classical
  cases mates with
  | nil => exact False.elim (hnon rfl)
  | cons e rest =>
    obtain ⟨a,hs,ha⟩ := hlabels e (by simp)
    have hP : P = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨ha,?_⟩
      intro t ht
      have htC := hsupp t ht
      rw [hs] at htC
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at htC
      rcases htC with hta | htb | htc
      · exact hta
      · exact False.elim ((havoid e (by simp)).1 (htb ▸ ht))
      · exact False.elim ((havoid e (by simp)).2 (htc ▸ ht))
    refine ⟨a,e.1,e.2,hs,?_,hrec e (by simp)⟩
    simp [hP]

/-- Full ordinary-component coverage with no mate leaves exactly an
isolate packet or a whole triangle packet. -/
theorem bare_ordinary_mate_empty_packet_shape
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (P : Finset (evenVertices G))
    (hsupp : ∀ t ∈ P, t ∈ C.supp) (hcover : ∀ t ∈ C.supp, t ∈ P) :
    (∃ a : evenVertices G, P.image Subtype.val = {(a : V)} ∧
      ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
    (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      P.image Subtype.val = {(a : V),(b : V),(c : V)}) := by
  classical
  obtain ⟨hs,_⟩ | ⟨b,c,hs,hwb,hbc,hcw,_⟩ :=
    bare_ordinary_contact_shapes h x w H S C hx hwC hwS
  · have hP : P = {w} := by
      ext t
      have he : t ∈ P ↔ t ∈ C.supp := ⟨hsupp t,hcover t⟩
      simpa [hs] using he
    left
    refine ⟨w,by simp [hP],?_⟩
    intro t hwt ht
    let v : evenVertices G := ⟨t,ht⟩
    have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hwC hwt
    have hvw : v = w := by simpa [hs] using hvC
    exact G.irrefl (by simpa only [← congrArg Subtype.val hvw] using hwt)
  · have hP : P = {w,b,c} := by
      ext t
      have he : t ∈ P ↔ t ∈ C.supp := ⟨hsupp t,hcover t⟩
      simpa [hs] using he
    right
    exact ⟨w,b,c,hs,hwb,hbc,hcw,by simp [hP]⟩

/-- Native support, coverage and restored recipients recover every regular
packet shape required by the half-star gain theorem. -/
theorem bare_ordinary_restored_regular_shape
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (P : Finset (evenVertices G)) (mates : List (evenVertices G × evenVertices G))
    (hsupp : ∀ t ∈ P, t ∈ C.supp)
    (hcover : ∀ t ∈ C.supp, t ∈ P ∨ ∃ e ∈ mates, t = e.1 ∨ t = e.2)
    (havoid : ∀ e ∈ mates, e.1 ∉ P ∧ e.2 ∉ P)
    (hlabels : ∀ e ∈ mates, ∃ a : evenVertices G, C.supp = {a,e.1,e.2} ∧ a ∈ P)
    (J : SimpleGraph V) [DecidableRel J.Adj] (D : Decomposition J)
    (hrec : ∀ e ∈ mates, 2 ≤ D.endpointCount e.1) :
    (∃ a : evenVertices G, P.image Subtype.val = {(a : V)} ∧
      ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
    (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
      P.image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
    (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      P.image Subtype.val = {(a : V),(b : V),(c : V)}) := by
  by_cases hempty : mates = []
  · have hc : ∀ t ∈ C.supp, t ∈ P := by
      intro t ht
      rcases hcover t ht with hp | ⟨e,he,_⟩
      · exact hp
      · simp [hempty] at he
    rcases bare_ordinary_mate_empty_packet_shape h x w H S C hx hwC hwS P hsupp hc with
      hi | ht
    · exact Or.inl hi
    · exact Or.inr (Or.inr ht)
  · exact Or.inr (Or.inl (ordinary_restored_singleton_packet_shape C P mates
      hsupp hempty havoid hlabels J D hrec))

end Gallai.TwoException
