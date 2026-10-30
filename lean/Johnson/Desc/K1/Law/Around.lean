-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Around.lean: the kind's two other decisions hold the sending's decision inside:
a yes of a segment's later moment, and of the first segment's opening, is a yes of the sending's
decision with a joining behind it (and, at the opening, a new group in front).

Main names: laterOwn_ok, commitOwn_ok, firstOwn_ok.

What is not claimed. What the joining and the new group do to the statement is not unfolded here.
The tests of the walk and of the frame around the sending are dropped from the conclusions. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Step
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP)

variable {Cl : Type}

/-- **A yes of a later moment**: the sending's decision has said yes at the record in front, and the
new messages have joined the segment's group. -/
theorem laterOwn_ok (P : Par) (owed : Option Nat) (c c' : ChainCheck) (w w' : DState Unit)
    (rs : List Fmt.RoundView) (h : laterOwn P owed c w rs = .ok (c', w')) :
    ∃ ids d₁ f', decideSend P owed w rs = .ok (ids, d₁) ∧
      joinOwnP groundG P.gp d₁ { c.frame with moment := c.frame.moment + 1 }
        (c.frame.atMoment c.frame.moment) ids = some (f', w') ∧
      c' = { c with frame := f', sent := ids, moments := c.moments + 1 } := by
  unfold laterOwn at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i x hx
          split at h
          · cases h
          · rename_i y hy
            have e := Except.ok.inj h
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            refine ⟨x.1, x.2, y.1, hx, ?_, e1.symm⟩
            rw [hy, ← e2]

/-- **A yes of the block of a later moment.** -/
theorem commitOwn_ok (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    ∃ ids d₁ f', decideSend P s.owed s.held.w rs = .ok (ids, d₁) ∧
      joinOwnP groundG P.gp d₁
        { s.held.L.check.frame with moment := s.held.L.check.frame.moment + 1 }
        (s.held.L.check.frame.atMoment s.held.L.check.frame.moment) ids =
          some (f', s'.held.w) := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨ids, d₁, f', a1, a2, _⟩ := laterOwn_ok P s.owed _ _ _ _ rs h2
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      refine ⟨ids, d₁, f', a1, ?_⟩
      rw [a2, ← e]
  · cases h

/-- **A yes of the first segment's opening**: a new group, the sending's decision at the record with
it, and the joining. -/
theorem firstOwn_ok (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (rs : List Fmt.RoundView) (h : firstOwn P owed c d rs = .ok (c', d')) :
    ∃ g d₁ ids d₂, Ground.newGroupP d c.frame.shape.code c.frame.shape.maskCode = some (g, d₁) ∧
      decideSend P owed d₁ rs = .ok (ids, d₂) ∧
      ∃ f₁ own mine f₂, joinOwnP groundG P.gp d₂ f₁ own mine = some (f₂, d') := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (bind_ok _ _ _).1 h
  have e : d₃ = d' := by
    have := Except.ok.inj h
    exact (Prod.mk.inj this).2
  subst e
  exact ⟨g, d₁, ids, d₂, (named_ok _ _ _).1 h1, h2, _, _, _, f₂, (named_ok _ _ _).1 h3⟩

end VerifiableInference.Desc.K1
