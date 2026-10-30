-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyLensLaws.lean: THE KEY FILE's ROW 1.16: WHAT THE KEY FILE's LENS (Key.batchLens, Johnson/Desc/Key/One.lean) SATISFIES, AS EQUATIONS. Carried by hand from Johnson/RunOne/KeyLensLaws.lean, which is not in this library (over the working names;
there the lens has a hook, here none) to the library names over the one base.
  lens_enter | lens_get | lens_set · lens_get_set · lens_get_set_same (THE LENS LAW THAT HOLDS) · not_strict (the strict law «get? (set t p) = some p» is false here).
Definitions are another file's. Nothing on soundness.
-/
import Johnson.Desc.Key.One

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params

variable {β : Type}

theorem lens_enter (s t : ChainState β) : (batchLens (β := β)).enter s = some t ↔ s.atEnd = false ∧ t = { s with atEnd := true } := by
  unfold batchLens
  cases h : s.atEnd <;> simp [h, eq_comm]

theorem lens_get (t : ChainState β) (p : K13.Part) : (batchLens (β := β)).get? t = some p ↔ t.atEnd = true ∧
    p = { owed := t.debt, heard := none, indexMasks := t.idx, pile := t.pile, msg := t.msgW, ids := t.ids, lin := t.lin, d := t.d } := by
  unfold batchLens
  cases h : t.atEnd <;> simp [h, eq_comm]

theorem lens_set (t : ChainState β) (p : K13.Part) : (batchLens (β := β)).set t p = { t with owed := p.owed, msgW := p.msg, ids := p.ids, lin := p.lin, d := p.d } := rfl

theorem lens_get_set (t : ChainState β) (p : K13.Part) (h : t.atEnd = true) : (batchLens (β := β)).get? ((batchLens (β := β)).set t p) =
    some { p with owed := p.owed.filter (· != 0), heard := none, indexMasks := t.idx, pile := t.pile } := by
  rw [lens_set]
  exact (lens_get _ _).2 ⟨h, rfl⟩

/-- **The lens law that holds.** -/
theorem lens_get_set_same (t : ChainState β) (p p' : K13.Part) (hg : (batchLens (β := β)).get? t = some p) (h1 : p'.heard = p.heard) (h2 : p'.indexMasks = p.indexMasks)
    (h3 : p'.pile = p.pile) (h4 : p'.owed = none) : (batchLens (β := β)).get? ((batchLens (β := β)).set t p') = some p' := by
  obtain ⟨ha, rfl⟩ := (lens_get t p).1 hg
  rw [lens_get_set t p' ha]
  obtain ⟨o, hd, im, pl, ms, is, ln, d⟩ := p'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem not_strict (t : ChainState β) (p : K13.Part) (h : p.heard ≠ none) : (batchLens (β := β)).get? ((batchLens (β := β)).set t p) ≠ some p := by
  intro e
  obtain ⟨_, e'⟩ := (lens_get _ _).1 e
  exact h (by rw [e'])

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.lens_get_set_same
