/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryFiniteMateAssembly
public import Gallai.TwoException.OrdinarySequentialRestoration

@[expose] public section

/-! # Sequential restoration of the actual assembled mate family -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance assembledComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance assembledStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance assembledMateAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Actual component packet data supply all list guards for restoring
regular mates. A centre reserve or nonadjacency of all recipients suffices;
no path is added and all mate recipients obtain two endpoints. -/
theorem restore_assembled_ordinary_mates
    (u : V) (hu : Odd (G.degree u)) (x : evenVertices G) (hxu : G.Adj u x)
    (S : Finset (evenVertices G)) (hcontacts : ∀ t ∈ S, G.Adj u t)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hlen : ∀ C ∈ F, (mates C).length ≤ 1)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C,
      G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (hlabels : ∀ C ∈ F, ∀ e ∈ mates C, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P C)
    (hx : ∀ C ∈ F, x ∉ C.supp) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      (0 < D.endpointCount u ∨ ∀ e ∈ M, ¬ G.Adj e.1 u) →
      ∃ E : Decomposition (starPuncture G u B),
        E.size = D.size ∧ E.endpointCount u = D.endpointCount u ∧
        (∀ e ∈ M, 2 ≤ E.endpointCount e.1) ∧
        ∀ t, (∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) →
          E.endpointCount t = D.endpointCount t := by
  classical
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp :=
    fun C hC t ht => (Finset.mem_filter.mp (hP C hC ht)).2
  obtain ⟨hdis,hguard⟩ := ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx
  have hadj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · simpa only [ht] using hxu
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,hvC⟩ := Finset.mem_biUnion.mp hv
      exact hcontacts v (Finset.mem_filter.mp (hP C hC hvC)).1
  have heven : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · rw [ht]
      exact x.property
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ht
      exact v.property
  have havoidCentre := ordinary_even_mates_avoid_odd_centre G M u hu
    (fun e he => ⟨(hguard e he).2.1,(hguard e he).2.2.1⟩)
  have havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    obtain ⟨hl,hr⟩ := havoidCentre e he
    exact ⟨hl,hr,(hguard e he).2.2.2.1,(hguard e he).2.2.2.2⟩
  have hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hguard e he).1,(hguard e he).2.1,(hguard e he).2.2.1⟩
  have hpacket := ordinary_finite_mate_labels G F P mates hlabels (x : V)
  dsimp only
  intro D hDu
  exact restore_ordinary_mate_family u B hadj heven M hdis havoid hedges hpacket D
    hDu

end Gallai.TwoException
