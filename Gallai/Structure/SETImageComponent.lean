/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SETRetainedPair

@[expose] public section

/-! # A preserved SET triangle exhausts an original even component -/

namespace Gallai

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]
variable {G : SimpleGraph W} [DecidableRel G.Adj]

/-- An original even neighbour of a preserved SET even vertex remains in
the image of the SET triangle. Labels are derived from the SET structure. -/
theorem IsSET.even_image_closed (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃a b⦄, H.Adj a b → G.Adj (f a) (f b))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hkeep : ∀ a, Even (H.degree a) → Even (G.degree (f a)))
    (a : V) (ha : Even (H.degree a)) (w : W) (hw : Even (G.degree w))
    (haw : G.Adj (f a) w) : ∃ b, Even (H.degree b) ∧ f b = w := by
  obtain ⟨b, c, hbc, hba, hca, hb, hc, _⟩ := h.even_pair_away a ha
  have hclose := even_triangle_close_path ht (hkeep b hb) (hkeep a ha) (hkeep c hc)
    (hle (h.even_clique b a hb ha hba)) (hle (h.even_clique a c ha hc hca.symm))
    (fun he => hbc (f.injective he))
  rcases hclose.2 w hw haw with he | he
  · exact ⟨b, hb, he.symm⟩
  · exact ⟨c, hc, he.symm⟩

/-- An embedded SET graph cannot gain an original even vertex outside its
own even triangle if that triangle preserves parity. -/
theorem IsSET.even_image_reflects (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃a b⦄, H.Adj a b → G.Adj (f a) (f b))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hkeep : ∀ a, Even (H.degree a) → Even (G.degree (f a)))
    (u : V) (hu : Even (G.degree (f u))) : Even (H.degree u) := by
  obtain ⟨a, hua, ha, _⟩ := h.even_neighbor_ne u u
  obtain ⟨b, hb, he⟩ := h.even_image_closed f hle ht hkeep a ha (f u) hu (hle hua.symm)
  have hbu := f.injective he
  rwa [hbu] at hb

/-- Every vertex reachable in the original even graph from the preserved
SET triangle has a preimage in that triangle. -/
theorem IsSET.even_image_reachable (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃a b⦄, H.Adj a b → G.Adj (f a) (f b))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hkeep : ∀ a, Even (H.degree a) → Even (G.degree (f a)))
    (a : V) (ha : Even (H.degree a)) (q : evenVertices G)
    (hr : (evenSubgraph G).Reachable ⟨f a, hkeep a ha⟩ q) :
    ∃ b, Even (H.degree b) ∧ f b = (q : W) := by
  let R := fun q : evenVertices G => ∃ b, Even (H.degree b) ∧ f b = (q : W)
  have hstep (p q : evenVertices G) (hpq : (evenSubgraph G).Adj p q) (hp : R p) : R q := by
    obtain ⟨b, hb, he⟩ := hp
    exact h.even_image_closed f hle ht hkeep b hb q q.property (by rw [he]; exact hpq)
  have hwalk : ∀ {p q : evenVertices G}, (evenSubgraph G).Walk p q → R p → R q := by
    intro p q walk
    induction walk with
    | nil => exact id
    | @cons p q r hpq walk ih => exact fun hp => ih (hstep p q hpq hp)
  obtain ⟨walk⟩ := hr
  exact hwalk walk ⟨a, ha, rfl⟩

end Gallai
