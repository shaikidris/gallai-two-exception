/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryEvenRestoration

@[expose] public section

/-! # Full-neighbourhood positivity after oriented ordinary restoration -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance retainedPositivityAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- Retained contacts cannot be donors. Every even retained contact is
therefore a restored recipient or the protected vertex; odd retained
neighbours and deleted even leaves have parity-forced endpoints. -/
theorem ordinary_restored_full_neighbourhood_positive
    (u h : V) (B S : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hclass : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ B ∨ t = h ∨ t ∈ S)
    (hcover : ∀ t ∈ S, t ∈ B ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2)
    (hdonor : ∀ e ∈ M, e.2 ∉ S)
    (D : Decomposition (starPuncture G u B))
    (hh : 0 < D.endpointCount h)
    (hrec : ∀ e ∈ M, 0 < D.endpointCount e.1) :
    ∀ t, (starPuncture G u B).Adj u t ∨ t ∈ B → 0 < D.endpointCount t := by
  classical
  intro t ht
  by_cases htB : t ∈ B
  · apply D.endpointCount_pos_of_odd_degree
    have hd := starPuncture_degree_leaf (G := G) u B t htB (hadj t htB)
    have he := hleaves t htB
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · have hat : G.Adj u t := (ht.resolve_right htB).1
    by_cases he : Even (G.degree t)
    · rcases hclass t hat he with hb | rfl | hs
      · exact False.elim (htB hb)
      · exact hh
      · rcases hcover t hs with hb | ⟨e,hem,heq⟩
        · exact False.elim (htB hb)
        · rcases heq with rfl | rfl
          · exact hrec e hem
          · exact False.elim (hdonor e hem hs)
    · apply D.endpointCount_pos_of_odd_degree
      have htu : t ≠ u := fun heq => G.irrefl (heq ▸ hat)
      have hd := starPuncture_degree_other (G := G) u B t htu htB
      have ho : Odd (G.degree t) := Nat.not_even_iff_odd.mp he
      simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
      rwa [hd]

noncomputable local instance retainedPositivityComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Actual packet coverage and oriented donors discharge the complete
Fan positivity premise for the assembled ordinary star. -/
theorem ordinary_assembled_restored_full_neighbourhood_positive
    (u h : V) (x : evenVertices G) (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hcover : ∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hdonor : ∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (hadj : ∀ t ∈ insert (x : V) ((F.biUnion P).image Subtype.val), G.Adj u t)
    (D : Decomposition (starPuncture G u
      (insert (x : V) ((F.biUnion P).image Subtype.val))))
    (hh : 0 < D.endpointCount h)
    (hrec : ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
      0 < D.endpointCount e.1) :
    ∀ t, (starPuncture G u (insert (x : V) ((F.biUnion P).image Subtype.val))).Adj u t ∨
      t ∈ insert (x : V) ((F.biUnion P).image Subtype.val) → 0 < D.endpointCount t := by
  classical
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  apply ordinary_restored_full_neighbourhood_positive u h B (S.image Subtype.val) M hadj
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact x.property
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ht
      exact a.property
  · intro t hat ht
    rcases hclass t hat ht with hx | hh | hs
    · left; simp [B,hx]
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨⟨t,ht⟩,hs,rfl⟩))
  · intro t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    let C := (evenSubgraph G).connectedComponentMk a
    have hC : C ∈ F := htouched a ha
    have hap : a ∈ ordinaryComponentPacket G S C :=
      Finset.mem_filter.mpr ⟨ha, (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mpr rfl⟩
    rcases hcover C hC a hap with hp | ⟨e,he,heq⟩
    · left
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hC,hp⟩,rfl⟩
    · right
      refine ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
      · exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
      · exact heq.imp (congrArg Subtype.val) (congrArg Subtype.val)
  · intro e he ht
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp ht
    have heq' : a = f.2 := Subtype.ext heq
    exact hdonor C (Finset.mem_toList.mp hC) f hfC (heq' ▸ ha)
  · exact hh
  · exact hrec

end Gallai.TwoException
