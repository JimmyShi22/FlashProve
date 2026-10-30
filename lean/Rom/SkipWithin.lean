-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SkipWithin.lean: two facts on the relation `StRel` of Rom/SkipRel.lean.

  `Wd.same n`, `StRel.refl`  A state all of whose tokens exist is related to itself, for the
                             correspondence in which every token corresponds to itself and none is
                             dead.
  `StRel.within`             What the lemma on deferred programming (`Spec.defer`, Rom/Defer.lean)
                             requires of a state (`DSt.Within`) carries over from the first state to
                             the second.
-/
import Rom.SkipRel

namespace Rom

variable {S : OSpec}

/-- every one of the first n tokens corresponds to itself; none is dead -/
def Wd.same (n : ℕ) : Wd := ⟨n, n, fun a b => a = b ∧ a < n, fun _ => False, fun _ _ => False⟩

theorem forall₂_same {n : ℕ} : ∀ {l : List Tok}, (∀ u ∈ l, u < n) → List.Forall₂ (Wd.same n).rel l l
  | [], _ => .nil
  | a :: _, h =>
    .cons (Or.inl ⟨rfl, h a List.mem_cons_self⟩)
      (forall₂_same fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem evsRel_same {n : ℕ} :
    ∀ {l : List (Ev S)},
      (∀ e ∈ l, e.charged < n ∧ e.tail < n ∧ ∀ u ∈ e.others, u < n) → EvsRel (Wd.same n) l l
  | [], _ => .nil
  | e :: l, h => by
    obtain ⟨h1, h2, h3⟩ := h e List.mem_cons_self
    exact EvsRel.both (e₁ := e) (c := e.charged) (us := e.others) (t := e.tail) (Or.inl ⟨rfl, h1⟩)
      (forall₂_same h3) (Or.inl ⟨rfl, h2⟩)
      (evsRel_same fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- A state all of whose tokens exist is related to itself. -/
theorem StRel.refl (d : DSt S) (hs : ∀ t ∈ d.shown, t < d.vals.length)
    (he : ∀ e ∈ d.evs,
      e.charged < d.vals.length ∧ e.tail < d.vals.length ∧ ∀ u ∈ e.others, u < d.vals.length) :
    StRel (Wd.same d.vals.length) d d where
  tok :=
    { n₁ := Nat.le_refl _
      n₂ := Nat.le_refl _
      lt := by rintro a b (⟨rfl, h⟩ | h); exacts [⟨h, h⟩, h.elim]
      injL := by rintro a b b' (⟨rfl, _⟩ | h) (⟨rfl, _⟩ | h'); exacts [rfl, h'.elim, h.elim, h.elim]
      injR := by rintro a a' b (⟨rfl, _⟩ | h) (⟨rfl, _⟩ | h'); exacts [rfl, h'.elim, h.elim, h.elim]
      ddlt := fun _ h => h.elim
      ddρ := fun _ _ h => h.elim
      val := by rintro a b (⟨rfl, _⟩ | h); exacts [rfl, h.elim]
      shown := by rintro a b ⟨rfl, _⟩; exact Iff.rfl
      slshown := fun _ _ h => h.elim
      slρ := fun _ _ h => h.elim
      ddshown := fun _ h => h.elim
      shlt₁ := hs
      shlt₂ := hs }
  table := rfl
  evs := evsRel_same he
  nPlain := rfl
  viol := id

/-- Under `StRel w d₁ d₂`, the experiment that leaves work out keeps the rules and the counts
(`DSt.Within`, at the same e, M, ℓ, os) if the experiment that does the work keeps them.
(`DSt.Within`, Rom/Defer.lean: what a run may do at most: e o plain and M o marked evaluations of o;
marked ones only at oracles of os, each charged to a token of at least ℓ o bits; no violation of the
rules.) -/
theorem StRel.within {w : Wd} {d₁ d₂ : DSt S} (h : StRel w d₁ d₂) {e M ℓ : S.ι → ℕ}
    {os : Finset S.ι} (h₁ : d₁.Within e M ℓ os) : d₂.Within e M ℓ os := by
  obtain ⟨hv, hp, hm, hc⟩ := h₁
  refine ⟨h.viol hv, fun o => h.nPlain ▸ hp o,
    fun o => (h.evs.count_le o).trans (hm o), fun v hv2 => ?_⟩
  obtain ⟨e₁, he₁, hch, -, -, heq⟩ := h.evs.exists_left v hv2
  have ho : v.o = e₁.o := by rw [heq]; rfl
  have hval : d₂.val v.charged = d₁.val e₁.charged := (h.tok.val _ _ hch).symm
  rw [ho, hval]
  exact hc e₁ he₁

end Rom
