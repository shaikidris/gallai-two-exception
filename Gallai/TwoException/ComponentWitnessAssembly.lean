/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ComponentBudget
public import Gallai.Inputs.OneException
public import Gallai.TwoException.ContactPunctureWitness

@[expose] public section

/-! # Protected endpoint assembly from local component witnesses -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual low-E-degree witnesses in all unprotected components combine
with the published endpoint theorem on the protected component. No component
decomposition or path-budget premise is assumed. -/
theorem assemble_one_ceiling_of_component_floors
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (hhpos : 0 < G.degree h) (hhEven : Even (G.degree h))
    (hcap : ∀ t, Even (G.degree t) → eDegree G t ≤ 3)
    (hf : ∀ C : G.ConnectedComponent, C ≠ G.connectedComponentMk h →
      HasPathBudget (G.induce C.supp) (Fintype.card C.supp / 2)) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  let C := G.connectedComponentMk h
  have hclosed : ∀ v ∈ C.supp, G.neighborSet v ⊆ C.supp := by
    intro v hv w hvw
    exact C.mem_supp_of_adj_mem_supp hv hvw
  have hdeg : ∀ v : C.supp, (G.induce C.supp).degree v = G.degree v := by
    intro v
    exact SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v.val v.property)
  have hc : ∀ v : C.supp, Even ((G.induce C.supp).degree v) →
      v ≠ ⟨h,rfl⟩ → eDegree (G.induce C.supp) v ≤ 3 := by
    intro v hv _
    rw [hdeg] at hv
    rw [eDegree_induce_of_closed G C.supp hclosed]
    exact hcap v hv
  obtain ⟨D,hd,he⟩ := one_exception_endpoint (G.induce C.supp) ⟨h,rfl⟩
    C.connected_toSimpleGraph (by rw [hdeg]; exact hhpos)
    (by rw [hdeg]; exact hhEven) hc
  exact assemble_one_ceiling G h D hd he hf

/-- Low-E-degree witnesses supply the unprotected component floors. -/
theorem assemble_one_ceiling_of_component_witnesses
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (hhpos : 0 < G.degree h) (hhEven : Even (G.degree h))
    (hcap : ∀ t, Even (G.degree t) → eDegree G t ≤ 3)
    (hw : ∀ C : G.ConnectedComponent, C ≠ G.connectedComponentMk h →
      ∃ p ∈ C.supp, eDegree G p ≤ 1) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  apply assemble_one_ceiling_of_component_floors G h hhpos hhEven hcap
  intro K hK
  obtain ⟨p,hp,hle⟩ := hw K hK
  exact contact_component_floor_of_eDegree_le_one hcap K p hp hle

end Gallai.TwoException
