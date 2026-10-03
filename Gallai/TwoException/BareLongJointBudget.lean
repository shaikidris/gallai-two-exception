/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongOrdinaryWitness
public import Gallai.TwoException.ComponentWitnessAssembly

@[expose] public section

/-! # Endpoint-rich joint auxiliary budget from local deletion witnesses -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longBudgetAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Local witness labels on the actual two-star deletion support suffice
for the joint ceiling budget. No connectedness of the auxiliary, component
floor, or auxiliary decomposition is an input. A retained hub-private edge
handles components whose boundary witness is the exceptional hub itself. -/
theorem bare_long_joint_endpoint_budget
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B S : Finset V) (O N : List (V × V))
    (hprofile : ∀ t,
      Even ((ordinaryMatePuncture
        (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
          u (insert v S)) N).degree t) → Even (G.degree t) ∨ t = v)
    (hhdegree : (ordinaryMatePuncture
      (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
        u (insert v S)) N).degree h = G.degree h)
    (hxOdd : Odd ((ordinaryMatePuncture
      (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
        u (insert v S)) N).degree x))
    (hcenter : ∀ t,
      (ordinaryMatePuncture
        (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
          u (insert v S)) N).Adj v t →
      Even ((ordinaryMatePuncture
        (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
          u (insert v S)) N).degree t) → t = h)
    (hwitness : let J := ordinaryMatePuncture (starPuncture
          (ordinaryMatePuncture (starPuncture G v B) O) u (insert v S)) N
      eDegree J u ≤ 1 ∧
      (∀ t ∈ B, eDegree J t ≤ 1) ∧
      (∀ t ∈ S, t = (x : V) ∨ eDegree J t ≤ 1) ∧
      (∀ e ∈ O, eDegree J e.1 ≤ 1 ∧ eDegree J e.2 ≤ 1) ∧
      (∀ e ∈ N, ∀ t, t = e.1 ∨ t = e.2 → t = (x : V) ∨ eDegree J t ≤ 1) ∧
      (∃ p, J.Adj x p ∧ eDegree J p ≤ 1)) :
    ∃ D : Decomposition (ordinaryMatePuncture
      (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
        u (insert v S)) N),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let J := ordinaryMatePuncture (starPuncture Q u (insert v S)) N
  have hsub : J ≤ G := by
    intro a b hab
    have hs : (starPuncture Q u (insert v S)).Adj a b :=
      (ordinaryMatePuncture_le N) hab
    exact ((ordinaryMatePuncture_le O) hs.1).1
  obtain ⟨hcap,hvCap,_⟩ := bare_long_joint_cap_of_profile h v x H J
    hsub hprofile hxOdd hcenter
  obtain ⟨huCap,hB,hS,hO,hN,⟨p,hxp,hp⟩⟩ := hwitness
  obtain ⟨hconn,_,hhpos,hhEven,_,_,_⟩ := H.counterexample.1
  apply assemble_one_ceiling_of_component_witnesses J h
    (by rw [hhdegree]; exact hhpos) (by rw [hhdegree]; exact hhEven) hcap
  intro K _
  have hhub : (x : V) ∈ K.supp → ∃ t ∈ K.supp, eDegree J t ≤ 1 := by
    intro hxK
    exact ⟨p,K.mem_supp_of_adj_mem_supp hxK hxp,hp⟩
  obtain ⟨t,ht,hbd⟩ := long_joint_component_meets_boundary hconn u v B S O N K
  rcases hbd with htu | htv | htB | htS | ⟨e,he,hte⟩
  · exact ⟨t,ht,by simpa only [htu] using huCap⟩
  · exact ⟨t,ht,by simpa only [htv] using hvCap⟩
  · exact ⟨t,ht,hB t htB⟩
  · rcases hS t htS with htx | hc
    · exact hhub (htx ▸ ht)
    · exact ⟨t,ht,hc⟩
  · rcases List.mem_append.mp he with heO | heN
    · rcases hte with hte | hte
      · exact ⟨t,ht,hte ▸ (hO e heO).1⟩
      · exact ⟨t,ht,hte ▸ (hO e heO).2⟩
    · rcases hN e heN t hte with htx | hc
      · exact hhub (htx ▸ ht)
      · exact ⟨t,ht,hc⟩

end Gallai.TwoException
