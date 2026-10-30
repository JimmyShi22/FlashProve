-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project that is not in this repository: as copied, the same
-- bytes behind this line.
/-
Johnson/Desc/K1/Law/LinkKeptAtLater.lean: what a segment's later moment leaves of the open link's
context (`LinkCtx`), beside what Johnson/Desc/K1/Law/FrameAtLater.lean says of its frame: the link's
number, its table of arrays, the rows' part of its check, and the frame's shape.

Main names: `commitOwn_linkKept` (the kind's block); `commitAtS_linkKept` (the block at the first
chain's state `S`).

What is not claimed. Nothing on the ledger. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.FrameAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **The kind's block.** -/
theorem commitOwn_linkKept (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.held.L.link = s.held.L.link ∧ s'.held.L.arrayOf = s.held.L.arrayOf ∧
      s'.held.L.check.rows = s.held.L.check.rows := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', _, _, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        rw [← e, ← e3, a3]
        exact ⟨rfl, rfl, rfl⟩
      · cases h3
  · cases h

/-- **The block at the first chain's state.** -/
theorem commitAtS_linkKept (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧ L'.link = L.link ∧
      L'.arrayOf = L.arrayOf ∧ L'.check.rows = L.check.rows ∧
      L'.check.frame.shape = L.check.frame.shape := by
  obtain ⟨L₀, L₁, b0, b1, ef, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨e1, e2, e3⟩ := commitOwn_linkKept P link moment arrays _ y r₁ r₂ gs hy
    have hL' := link_put s y.held.w L y.held.L y.held.F hL
    obtain rfl : L₀ = L := Option.some.inj (b0.symm.trans hL)
    obtain rfl : L₁ = y.held.L := Option.some.inj (b1.symm.trans hL')
    exact ⟨L₀, y.held.L, hL, hL', e1, e2, e3, by rw [ef]⟩
  · cases h

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.commitAtS_linkKept
