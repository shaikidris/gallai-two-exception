/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparationExistence

@[expose] public section

/-! # Simultaneous regular preparations on actual ordinary components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance preparationFamilyComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Bare minimality supplies one coherent regular preparation family on
any selected set of actual touched ordinary components. Its per-component
data retain the exact T3 count and triangle labels needed by consumers. -/
theorem bare_ordinary_regular_preparation_family
    (h : V) (z : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hz : ∀ C ∈ F, z ∉ C.supp) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ M : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
    ∀ C ∈ F,
      (P C).Nonempty ∧ P C ⊆ ordinaryComponentPacket G S C ∧
      (∀ t, t ∈ C.supp → t ∈ P C ∨ ∃ e ∈ M C, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ M C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P C ∧ e.2 ∉ P C) ∧
      (M C).length ≤ 1 ∧ (#(P C) = 1 ∨ #(P C) = 3) ∧
      #(P C) = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0) ∧
      (∀ e ∈ M C, ∃ a : evenVertices G,
        C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a) := by
  classical
  have hlocal : ∀ C : {C // C ∈ F},
      ∃ P : Finset (evenVertices G), ∃ M : List (evenVertices G × evenVertices G),
      P.Nonempty ∧ P ⊆ ordinaryComponentPacket G S C.val ∧
      (∀ t, t ∈ C.val.supp → t ∈ P ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ C.val.supp ∧ e.2 ∈ C.val.supp ∧
        e.1 ∉ P ∧ e.2 ∉ P) ∧
      M.length ≤ 1 ∧ (#P = 1 ∨ #P = 3) ∧
      #P = 1 + 2 * (if #(ordinaryComponentPacket G S C.val) = 3 then 1 else 0) ∧
      (∀ e ∈ M, ∃ a : evenVertices G,
        C.val.supp = {a,e.1,e.2} ∧ a ∈ P ∧ G.Adj a e.1 ∧ G.Adj e.2 a) := by
    intro C
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hF C.property)
    have hwC : w ∈ C.val.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C.val w).mpr he
    exact bare_ordinary_regular_preparation_exists h z w H S C.val
      (hz C.val C.property) hwC hw
  choose P M hdata using hlocal
  let P' := fun C => if hc : C ∈ F then P ⟨C,hc⟩ else ∅
  let M' := fun C => if hc : C ∈ F then M ⟨C,hc⟩ else []
  refine ⟨P',M',?_⟩
  intro C hC
  simpa only [P',M',dif_pos hC] using hdata ⟨C,hC⟩

end Gallai.TwoException
