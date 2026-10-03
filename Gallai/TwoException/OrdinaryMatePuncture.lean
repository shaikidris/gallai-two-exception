/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparationProfile

@[expose] public section

/-! # Simultaneous disjoint ordinary mate deletions -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Delete the ordinary triangle mates in a specified preparation order. -/
def ordinaryMatePuncture (G : SimpleGraph V) : List (V × V) → SimpleGraph V
  | [] => G
  | e :: M => (ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}

noncomputable local instance mateFamilyAdj (G : SimpleGraph V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture G M).Adj := fun _ _ => Classical.propDecidable _

/-- A fixed edge deletion commutes with the entire mate preparation.
This identifies spoke-first and mate-first auxiliary graphs exactly. -/
theorem ordinaryMatePuncture_deleteEdges_comm
    (M : List (V × V)) (E : Set (Sym2 V)) :
    ordinaryMatePuncture (G.deleteEdges E) M = (ordinaryMatePuncture G M).deleteEdges E := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    simp only [ordinaryMatePuncture,ih,SimpleGraph.deleteEdges_deleteEdges]
    rw [Set.union_comm]

/-- Splitting the deletion list exposes the graph on which its prefix
is restored while the suffix remains absent. -/
theorem ordinaryMatePuncture_append (M N : List (V × V)) :
    ordinaryMatePuncture G (M ++ N) =
      ordinaryMatePuncture (ordinaryMatePuncture G N) M := by
  induction M with
  | nil => rfl
  | cons e M ih => simp only [List.cons_append,ordinaryMatePuncture,ih]

/-- Moving one spoke deletion behind an ordinary prefix changes only the
preparation order, not the punctured graph. -/
theorem ordinaryMatePuncture_ordered_spoke
    (x q : V) (O N : List (V × V)) :
    ordinaryMatePuncture (G.deleteEdges {s(x,q)}) (O ++ N) =
      ordinaryMatePuncture G (O ++ (x,q) :: N) := by
  rw [ordinaryMatePuncture_append]
  have hc := ordinaryMatePuncture_deleteEdges_comm (G := G) N
    ({s(x,q)} : Set (Sym2 V))
  rw [hc]
  exact (ordinaryMatePuncture_append (G := G) O ((x,q) :: N)).symm

/-- Deletions in other components do not change a retained adjacency. -/
theorem ordinaryMatePuncture_adj_of_avoids
    (M : List (V × V)) (v w : V)
    (hv : ∀ e ∈ M, v ≠ e.1 ∧ v ≠ e.2) :
    (ordinaryMatePuncture G M).Adj v w ↔ G.Adj v w := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    have he := hv e (List.mem_cons_self ..)
    have ht : ∀ f ∈ M, v ≠ f.1 ∧ v ≠ f.2 :=
      fun f hf => hv f (List.mem_cons_of_mem e hf)
    simp only [ordinaryMatePuncture, SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    rw [ih ht]
    simp [he.1, he.2]

/-- A restored spoke commutes with mate deletions that avoid its leaf. -/
theorem ordinaryMatePuncture_sup_edge
    (M : List (V × V)) (p u : V)
    (hp : ∀ e ∈ M, p ≠ e.1 ∧ p ≠ e.2) :
    ordinaryMatePuncture (G ⊔ SimpleGraph.edge p u) M =
      ordinaryMatePuncture G M ⊔ SimpleGraph.edge p u := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    have he := hp e (List.mem_cons_self ..)
    have ht : ∀ f ∈ M, p ≠ f.1 ∧ p ≠ f.2 :=
      fun f hf => hp f (List.mem_cons_of_mem e hf)
    have hedge : (SimpleGraph.edge p u).deleteEdges {s(e.1,e.2)} =
        SimpleGraph.edge p u := by
      ext v w
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h,?_⟩
        rw [SimpleGraph.edge_adj] at h
        rcases h.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · simp [Set.mem_singleton_iff]
          rintro (heq | heq)
          · exact False.elim (he.1 (congrArg Prod.fst heq))
          · exact False.elim (he.2 (congrArg Prod.fst heq))
        · simp [Set.mem_singleton_iff]
          rintro (heq | heq)
          · exact False.elim (he.2 (congrArg Prod.snd heq))
          · exact False.elim (he.1 (congrArg Prod.snd heq))
    simp only [ordinaryMatePuncture,ih ht,SimpleGraph.deleteEdges_sup,hedge]

/-- After the first private spoke is restored, the remaining graph is the
same mate puncture on the star with that leaf erased. -/
theorem ordinaryMatePuncture_restore_star_leaf
    (u p : V) (B : Finset V) (M : List (V × V))
    (hu : u ∉ B) (hpB : p ∈ B) (hup : G.Adj u p)
    (hp : ∀ e ∈ M, p ≠ e.1 ∧ p ≠ e.2) :
    ordinaryMatePuncture (starPuncture G u B) M ⊔ SimpleGraph.edge p u =
      ordinaryMatePuncture (starPuncture G u (B.erase p)) M := by
  classical
  letI : DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
  rw [← ordinaryMatePuncture_sup_edge M p u hp,
    starPuncture_restore_leaf G u p B hu hpB hup]

/-- A vertex outside every deleted mate keeps its exact degree, not only
its parity. This is used for untouched private vertices and the centre. -/
theorem ordinaryMatePuncture_degree_of_avoids
    (M : List (V × V)) (v : V)
    (hv : ∀ e ∈ M, v ≠ e.1 ∧ v ≠ e.2) :
    (ordinaryMatePuncture G M).degree v = G.degree v := by
  induction M with
  | nil =>
    simp only [← SimpleGraph.ncard_neighborSet]
    rfl
  | cons e M ih =>
    have he := hv e (List.mem_cons_self ..)
    have ht : ∀ f ∈ M, v ≠ f.1 ∧ v ≠ f.2 :=
      fun f hf => hv f (List.mem_cons_of_mem e hf)
    have hd := degree_delete_edge_of_ne (ordinaryMatePuncture G M) e.1 e.2 v he.1 he.2
    have hi := ih ht
    simp only [← SimpleGraph.ncard_neighborSet] at hd hi ⊢
    change (((ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}).neighborSet v).ncard =
      (G.neighborSet v).ncard
    exact hd.trans hi

/-- Disjoint even mates can all be deleted without introducing any new
even vertex. Their parity guards are supplied in the graph before the
whole mate family, rather than separately at each intermediate graph. -/
theorem ordinaryMatePuncture_even_preserved
    (M : List (V × V))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ t, Even ((ordinaryMatePuncture G M).degree t) → Even (G.degree t) := by
  induction M with
  | nil =>
    intro t ht
    simp only [← SimpleGraph.ncard_neighborSet] at ht ⊢
    exact ht
  | cons e M ih =>
    rcases List.pairwise_cons.mp hdis with ⟨hhead, htail⟩
    obtain ⟨he, hp, hq⟩ := hedges e (List.mem_cons_self ..)
    have hpAvoid : ∀ f ∈ M, e.1 ≠ f.1 ∧ e.1 ≠ f.2 :=
      fun f hf => ⟨(hhead f hf).1, (hhead f hf).2.1⟩
    have hqAvoid : ∀ f ∈ M, e.2 ≠ f.1 ∧ e.2 ≠ f.2 :=
      fun f hf => (hhead f hf).2.2
    have hpd := ordinaryMatePuncture_degree_of_avoids (G := G) M e.1 hpAvoid
    have hqd := ordinaryMatePuncture_degree_of_avoids (G := G) M e.2 hqAvoid
    have hpEven : Even ((ordinaryMatePuncture G M).degree e.1) := hpd ▸ hp
    have hqEven : Even ((ordinaryMatePuncture G M).degree e.2) := hqd ▸ hq
    have heCurrent := (ordinaryMatePuncture_adj_of_avoids (G := G) M e.1 e.2 hpAvoid).mpr he
    have hkeep := even_edge_deletion_even_preserved
      (G := ordinaryMatePuncture G M) e.1 e.2 heCurrent hpEven hqEven
    intro t ht
    apply ih htail (fun f hf => hedges f (List.mem_cons_of_mem e hf)) t
    simp only [← SimpleGraph.ncard_neighborSet] at hkeep ht ⊢
    change Even ((((ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}).neighborSet t).ncard) at ht
    exact hkeep t ht

/-- The simultaneous puncture is a subgraph of its input graph. -/
theorem ordinaryMatePuncture_le (M : List (V × V)) :
    ordinaryMatePuncture G M ≤ G := by
  induction M with
  | nil => exact le_rfl
  | cons e M ih => exact fun _ _ ha => ih ha.1

/-- Every listed mate is absent, independently of deletion order. -/
theorem ordinaryMatePuncture_missing (M : List (V × V)) :
    ∀ e ∈ M, ¬ (ordinaryMatePuncture G M).Adj e.1 e.2 := by
  induction M with
  | nil => simp
  | cons f M ih =>
    intro e he ha
    rcases List.mem_cons.mp he with rfl | he
    · apply ha.2
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Set.mem_singleton _, ha.1.ne⟩
    · exact ih e he ha.1

end Gallai.TwoException
