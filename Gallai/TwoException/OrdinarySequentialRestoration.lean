/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryHeadRestoration

@[expose] public section

/-! # Complete restoration of a disjoint ordinary mate family -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance sequentialAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance sequentialStarAdj (G : SimpleGraph V) (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- Restore all regular ordinary triangle mates before the contact star.
A positive centre suffices; alternatively every recipient can avoid the
centre. The latter covers T1 mates even with zero centre endpoints.
Every recipient has at least two endpoints and no path is added. -/
theorem restore_ordinary_mate_family
    (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t)) (M : List (V × V)) :
    M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) →
    (∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B) →
    (∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) →
    (∀ e ∈ M, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V), (c : V)) ∧
      C.supp = {a, b, c} ∧ (a : V) ∈ B) →
    ∀ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      (0 < D.endpointCount u ∨ ∀ e ∈ M, ¬ G.Adj e.1 u) →
      ∃ E : Decomposition (starPuncture G u B),
        E.size = D.size ∧ E.endpointCount u = D.endpointCount u ∧
        (∀ e ∈ M, 2 ≤ E.endpointCount e.1) ∧
        ∀ t, (∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) →
          E.endpointCount t = D.endpointCount t := by
  classical
  induction M with
  | nil =>
    intro _ _ _ _ D _
    exact ⟨D, rfl, rfl, by simp, fun _ _ => rfl⟩
  | cons e M ih =>
    intro hdis havoid hedges hpacket D hu
    obtain ⟨C, a, b, c, heq, hsupp, haB⟩ := hpacket e (List.mem_cons_self ..)
    subst e
    have hmem : ((b : V), (c : V)) ∈ ((b : V), (c : V)) :: M := List.mem_cons_self ..
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdis
    have hcentre : ¬ (ordinaryMatePuncture (starPuncture G u B)
        (((b : V), (c : V)) :: M)).Adj b u ∨ 0 < D.endpointCount u := by
      rcases hu with hu | hn
      · exact Or.inr hu
      · left
        intro ha
        exact hn _ hmem ((ordinaryMatePuncture_le _ ha).1)
    obtain ⟨E1, hs1, hb1, hu1, hkeep1⟩ := restore_ordinary_family_head
      u B M C a b c hsupp haB hadj hleaves hdis havoid hedges D hcentre
    have huE1 : 0 < E1.endpointCount u ∨ ∀ e ∈ M, ¬ G.Adj e.1 u := by
      rcases hu with hu | hn
      · left; rwa [hu1]
      · right; exact fun e he => hn e (List.mem_cons_of_mem _ he)
    obtain ⟨E2, hs2, hu2, hrec2, hkeep2⟩ := ih htail
      (fun f hf => havoid f (List.mem_cons_of_mem _ hf))
      (fun f hf => hedges f (List.mem_cons_of_mem _ hf))
      (fun f hf => hpacket f (List.mem_cons_of_mem _ hf)) E1 huE1
    refine ⟨E2, hs2.trans hs1, hu2.trans hu1, ?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · have hbAvoid : ∀ f ∈ M, (b : V) ≠ f.1 ∧ (b : V) ≠ f.2 :=
          fun f hf => ⟨(hhead f hf).1, (hhead f hf).2.1⟩
        rw [hkeep2 b hbAvoid]
        exact hb1
      · exact hrec2 f hf
    · intro t ht
      obtain ⟨htb, htc⟩ := ht _ hmem
      have htTail : ∀ f ∈ M, t ≠ f.1 ∧ t ≠ f.2 :=
        fun f hf => ht f (List.mem_cons_of_mem _ hf)
      exact (hkeep2 t htTail).trans (hkeep1 t htb htc)

/-- Restore an ordinary prefix while leaving all later private mates and
the unpaid hub spoke deleted. Only the prefix needs triangle labels. -/
theorem restore_ordinary_mate_prefix
    (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t)) (M tail : List (V × V)) :
    (M ++ tail).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) →
    (∀ e ∈ M ++ tail, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B) →
    (∀ e ∈ M ++ tail, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) →
    (∀ e ∈ M, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B) →
    ∀ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) (M ++ tail)),
      0 < D.endpointCount u →
      ∃ E : Decomposition (ordinaryMatePuncture (starPuncture G u B) tail),
        E.size = D.size ∧ E.endpointCount u = D.endpointCount u ∧
        (∀ e ∈ M, 2 ≤ E.endpointCount e.1) ∧
        ∀ t, (∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) →
          E.endpointCount t = D.endpointCount t := by
  classical
  induction M with
  | nil =>
    intro _ _ _ _ D _
    exact ⟨D,rfl,rfl,by simp,fun _ _ => rfl⟩
  | cons e M ih =>
    intro hdis havoid hedges hpacket D hu
    obtain ⟨C,a,b,c,heq,hsupp,haB⟩ := hpacket e (List.mem_cons_self ..)
    subst e
    have hmem : ((b : V),(c : V)) ∈ ((b : V),(c : V)) :: (M ++ tail) :=
      List.mem_cons_self ..
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hdis
    obtain ⟨E1,hs1,hb1,hu1,hkeep1⟩ := restore_ordinary_family_head
      u B (M ++ tail) C a b c hsupp haB hadj hleaves hdis havoid hedges D (Or.inr hu)
    obtain ⟨E2,hs2,hu2,hrec2,hkeep2⟩ := ih htail
      (fun f hf => havoid f (List.mem_cons_of_mem _ hf))
      (fun f hf => hedges f (List.mem_cons_of_mem _ hf))
      (fun f hf => hpacket f (List.mem_cons_of_mem _ hf)) E1 (by rwa [hu1])
    refine ⟨E2,hs2.trans hs1,hu2.trans hu1,?_,?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · have hbAvoid : ∀ f ∈ M, (b : V) ≠ f.1 ∧ (b : V) ≠ f.2 := by
          intro f hf
          have hs := hhead f (List.mem_append_left tail hf)
          exact ⟨hs.1,hs.2.1⟩
        rw [hkeep2 b hbAvoid]
        exact hb1
      · exact hrec2 f hf
    · intro t ht
      obtain ⟨htb,htc⟩ := ht _ (List.mem_cons_self ..)
      have htTail : ∀ f ∈ M, t ≠ f.1 ∧ t ≠ f.2 :=
        fun f hf => ht f (List.mem_cons_of_mem _ hf)
      exact (hkeep2 t htTail).trans (hkeep1 t htb htc)

end Gallai.TwoException
