-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LinkAtLater.lean: WHAT A LATER MOMENT's SENDING OF KIND K1 DOES TO THE OPEN
LINK's RECORD, WHOLE, at the first chain's record: behind a yes of `commitAtS` it is the link's
record in front with the walk's state of the calls replaced (Johnson/Desc/K1/Law/FrameAtLater.lean
says by what) and its count of moments one higher; EVERY OTHER FIELD IS AS IT WAS. Statements with
their proofs.
  `commitOwn_linkRec`: the kind's block. `commitAtS_linkRec`: **the block at the record.**
  `commitAtS_moments`: read off it: the count of moments, the link's number, the arrays' map.
What is not claimed. Who lays the count of moments and the frame's link at the link's opening: that
is the opening step's. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.FrameAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **The kind's block**: the link's record behind, whole. -/
theorem commitOwn_linkRec (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    s'.held.L = { s.held.L with check := s'.held.L.check, moments := s.held.L.moments + 1 } := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        rw [← e, ← e3]
      · cases h3
  · cases h

/-- **THE BLOCK AT THE RECORD.** -/
theorem commitAtS_linkRec (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧
      L' = { L with check := L'.check, moments := L.moments + 1 } := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    exact ⟨L, y.held.L, hL, link_put s _ L _ _ hL,
      commitOwn_linkRec P link moment arrays _ y rs gs hy⟩
  · cases h

/-- The count of moments, the link's number and the arrays' map. -/
theorem commitAtS_moments (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧ L'.moments = L.moments + 1 ∧
      L'.link = L.link ∧ L'.arrayOf = L.arrayOf := by
  obtain ⟨L, L', a, b, e⟩ := commitAtS_linkRec P link moment arrays s s' rs gs h
  exact ⟨L, L', a, b, by rw [e], by rw [e], by rw [e]⟩

end VerifiableInference.Desc.K1
