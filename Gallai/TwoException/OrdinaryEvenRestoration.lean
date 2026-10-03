/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAssembledRestoration
public import Gallai.TwoException.OrdinaryStarMateProfile

@[expose] public section

/-! # Sequential restoration of the actual assembled mate family -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance evenRestorationComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance evenRestorationStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance evenRestorationMateAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Even total spoke deletion supplies the centre reserve automatically.
The actual mate family restores with no additional positivity premise. -/
theorem restore_assembled_ordinary_mates_even
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
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (heven : Even (1 + ((F.biUnion P).image Subtype.val).card)) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
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
  obtain ⟨_,hguard⟩ := ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx
  have hxnot : (x : V) ∉ (F.biUnion P).image Subtype.val := by
    intro hm
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hm
    have htx : t = x := Subtype.ext he
    obtain ⟨C,hC,htC⟩ := Finset.mem_biUnion.mp ht
    exact hx C hC (htx ▸ hsupp C hC t htC)
  have hB : Even B.card := by
    simpa only [B,Finset.card_insert_of_notMem hxnot,Nat.add_comm] using heven
  have hadj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · simpa only [ht] using hxu
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,hvC⟩ := Finset.mem_biUnion.mp hv
      exact hcontacts v (Finset.mem_filter.mp (hP C hC hvC)).1
  have hav := ordinary_even_mates_avoid_odd_centre G M u hu
    (fun e he => ⟨(hguard e he).2.1,(hguard e he).2.2.1⟩)
  dsimp only
  intro D
  have hpos := ordinary_star_mates_centre_reserve u B M hadj hu hB hav D
  exact restore_assembled_ordinary_mates u hu x hxu S hcontacts F P mates
    hP hlen hmates hlabels hx D (Or.inl hpos)

end Gallai.TwoException
