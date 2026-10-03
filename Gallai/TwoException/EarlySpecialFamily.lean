/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOrdinaryFamily
public import Gallai.TwoException.OrdinarySpecialSelection
public import Gallai.TwoException.OrdinarySpecialExistence

@[expose] public section

/-! # Native parity-selected special family for early restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance earlySpecialComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Select at most one actual two-contact triangle when parity requires
it. The retained third vertex avoids the restoration centre; its component
and genuine triangle edges are carried with the selected packet. -/
theorem bare_early_special_family
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (k : ℕ) :
    let eligible := F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
      special ⊆ eligible ∧ #special ≤ 1 ∧
      (Even k → special = ∅) ∧
      ((eligible \ special).Nonempty → Even (k + #special)) ∧
      #special ≤ (if Even (k + #special) then 1 else 0) ∧
      ∀ C ∈ special, ∃ a b c : evenVertices G,
        C.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        ordinaryComponentPacket G S C = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
  classical
  dsimp only
  obtain ⟨special,hsub,hlen,hempty,hpar,hreserve⟩ :=
    select_special_ordinary_packet
      (F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)) k
  refine ⟨special,hsub,hlen,hempty,hpar,hreserve,?_⟩
  intro C hC
  obtain ⟨hCF,hsize⟩ := Finset.mem_filter.mp (hsub hC)
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hF hCF)
  have hwC : w ∈ C.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mpr he
  obtain ⟨b,c,hs,hwb,hbc,hcw,hpacket,hc,hcu⟩ :=
    bare_ordinary_special_preparation_classified h u x w H S C
      (hx C hCF) hwC hw hsize hclass
  exact ⟨w,b,c,hs,hwb,hbc,hcw,hpacket,hc,hcu⟩

end Gallai.TwoException
