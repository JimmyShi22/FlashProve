-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LaterAtRecord.lean: WHAT A SEGMENT's LATER MOMENT DOES TO THE FIRST CHAIN's
RECORD, beside the statement and the book (Johnson/Desc/K1/Law/BookAtRecord.lean). Statements with
their proofs. It names no table of joints.
Main names:
  `commitOwn_link`: the block's decision leaves the open link's number.
  `commitAtS_rec`: **where the block says yes**: a link is open; the record behind is the one in
    front with the statement's part laid back (no count of rows waits), the link's record and the
    sub-proof's engine put: and the link's record put has the number of the one in front.
  `commitAtS_here`: so the chain stands in a segment of the same sort, the same link open.
The sub-proof's engine's next free slot: Johnson/Desc/K1/KeepsNext.lean and
Johnson/Desc/K1/Law/NextKept.lean.

What is not claimed. What the link's record and the engine hold behind, beyond the number. Nothing
on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.BookAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- The block's decision leaves the open link's number. -/
theorem commitOwn_link (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    s'.held.L.link = s.held.L.link := by
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

/-- **Where the block says yes.** -/
theorem commitAtS_rec (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ (L L' : LinkCtx) (F' : Fork) (w : DState Unit), s.link? = some L ∧ L'.link = L.link ∧
      s' = ((laid s w).putLink L').putFork F' := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    exact ⟨L, y.held.L, y.held.F, y.held.w, hL, commitOwn_link P link moment arrays _ y rs gs hy,
      rfl⟩
  · cases h

/-- The same link is open behind, in a segment of the same sort; no count of rows waits. -/
theorem commitAtS_here (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    (∃ L L', s.link? = some L ∧ s'.link? = some L' ∧ L'.link = L.link) ∧ s'.rowsOwed = none ∧
      ((∃ a a', s.here = .lay a ∧ s'.here = .lay a') ∨
        (∃ a a', s.here = .att a ∧ s'.here = .att a') ∨
        ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ a.opened = true ∧ a'.opened = true) := by
  obtain ⟨L, L', F', w, hL, hl, rfl⟩ := commitAtS_rec P link moment arrays s s' rs gs h
  cases hs : s.here with
  | lay a =>
    refine ⟨⟨L, L', hL, ?_, hl⟩, ?_, Or.inl ⟨a, { a with L := L', F := F' }, rfl, ?_⟩⟩ <;>
      simp [S.putFork, S.putLink, S.link?, laid, hs]
  | att a =>
    refine ⟨⟨L, L', hL, ?_, hl⟩, ?_,
      Or.inr (Or.inl ⟨a, { a with L := L', F := F' }, rfl, ?_⟩)⟩ <;>
      simp [S.putFork, S.putLink, S.link?, laid, hs]
  | head a =>
    have ho : a.opened = true := by
      by_contra hn
      simp [S.link?, hs, hn] at hL
    refine ⟨⟨L, L', hL, ?_, hl⟩, ?_,
      Or.inr (Or.inr ⟨a, { a with L := L', F := F' }, rfl, ?_, ho, ho⟩)⟩ <;>
      simp [S.putFork, S.putLink, S.link?, laid, hs, ho]
  | between => simp [S.link?, hs] at hL
  | fin a => simp [S.link?, hs] at hL
  | mem a => simp [S.link?, hs] at hL

end VerifiableInference.Desc.K1
