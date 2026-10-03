/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryLocalPreparation

@[expose] public section

/-! # Regular preparations constructed from bare minimality -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every touched ordinary component admits a regular deletion packet.
Its labels and coverage are constructed from the actual bare kernel.
There is at most one mate, and its endpoints avoid the packet's spokes. -/
theorem bare_ordinary_regular_preparation_exists
    (h : V) (z w : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S) :
    ∃ P : Finset (evenVertices G), ∃ M : List (evenVertices G × evenVertices G),
      P.Nonempty ∧ P ⊆ ordinaryComponentPacket G S C ∧
      (∀ t, t ∈ C.supp → t ∈ P ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P ∧ e.2 ∉ P) ∧
      M.length ≤ 1 ∧ (#P = 1 ∨ #P = 3) ∧
      #P = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0) ∧
      (∀ e ∈ M, ∃ a : evenVertices G,
        C.supp = {a,e.1,e.2} ∧ a ∈ P ∧ G.Adj a e.1 ∧ G.Adj e.2 a) := by
  classical
  obtain ⟨hs,hpacket⟩ | ⟨b,c,hs,hwb,hbc,hcw,_⟩ :=
    bare_ordinary_contact_shapes h z w H S C hz hwC hwS
  · refine ⟨{w}, [], by simp, ?_, ?_, by simp, by simp,
      Or.inl (by simp), by simp [hpacket], by simp⟩
    · rw [hpacket]
    · intro t ht
      exact Or.inl (by simpa [hs] using ht)
  · obtain ⟨P,M,hsub,hcover,hmates,hshape⟩ :=
      ordinary_triangle_regular_preparation S C w b c hs hwb hbc hcw hwS
    have hwbN : w ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hwb)
    have hwcN : w ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hcw.symm)
    have hbcN : b ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc)
    have hcount := ordinary_triangle_contact_count S C w b c hs hwb hbc hcw hwS
    refine ⟨P,M,?_,hsub,hcover,hmates,?_,?_,?_,?_⟩
    · rcases hshape with ⟨hP,_,_,_⟩ | ⟨hP,_,_⟩ <;> simp [hP]
    · rcases hshape with ⟨_,hM,_,_⟩ | ⟨_,hM,_⟩ <;> simp [hM]
    · rcases hshape with ⟨hP,_,_,_⟩ | ⟨hP,_,_⟩
      · right
        simp [hP, hwbN, hwcN, hbcN]
      · left
        simp [hP]
    · rcases hshape with ⟨hP,_,hb,hc⟩ | ⟨hP,_,hmissing⟩
      · simp [hP, hcount, hb, hc, hwbN, hwcN, hbcN]
      · have hn : #(ordinaryComponentPacket G S C) ≠ 3 := by
          rcases hmissing with hb | hc
          · by_cases hc : c ∈ S <;> simp [hb, hc] at hcount <;> omega
          · by_cases hb : b ∈ S <;> simp [hb, hc] at hcount <;> omega
        simp [hP, hn]
    · intro e he
      rcases hshape with ⟨_,hM,_,_⟩ | ⟨hP,hM,_⟩
      · simp [hM] at he
      · have heq : e = (b,c) := by simpa [hM] using he
        subst e
        exact ⟨w,hs,by simp [hP],hwb,hcw⟩

end Gallai.TwoException
