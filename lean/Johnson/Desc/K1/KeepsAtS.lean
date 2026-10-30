-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/KeepsAtS.lean: the first segment's opening, and kind K1's three blocks at the first
chain's record, keep EVERY relation R on statements that the ground's plain functions keep
(Johnson/Desc/GroundKeeps.lean: GroundKeeps R), read at the record's own field. Theorems.

  firstOwn_keeps       the first segment's opening.
  putLink_st · putFork_st   the record's own puts leave the statement as it is.
  sendAtS_keeps · commitAtS_keeps · firstAtS_keeps   the three blocks.
What is not claimed: as in Johnson/Desc/K1/Keeps.lean.

-/
import Johnson.Desc.K1.First
import Johnson.Desc.K1.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.Rel
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.Keeps (Decides)

variable {L Cl : Type} {R : Statement → Statement → Prop}

/-- The first segment's opening. -/
theorem firstOwn_keeps (H : GroundKeeps R) (P : Par) (owed : Option Nat) (c : ChainCheck)
    (d : DState Unit)
    (rs : List Fmt.RoundView) (y : ChainCheck × DState Unit) (h : firstOwn P owed c d rs = .ok y) :
    R d.st y.2.st := by
  unfold firstOwn at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact H.trans (H.trans (H.newGroup d d₁ _ _ g ((named_ok _ _ _).1 h1))
    (decideSend_keeps H _ _ _ _ _ h2)) (joinOwnP_keeps H _ _ _ _ _ _ ((named_ok _ _ _).1 h3))
/-- Laying the link's record leaves the statement as it is. -/
theorem putLink_st (s : S) (X : LinkCtx) : (s.putLink X).st = s.st := by
  unfold S.putLink
  split <;> first | rfl | (split <;> rfl)

/-- Laying the ledger leaves the statement as it is. -/
theorem putFork_st (s : S) (X : Fork) : (s.putFork X).st = s.st := by
  unfold S.putFork
  split <;> first | rfl | (split <;> rfl)

/-- W's sending, at the first chain's record. -/
theorem sendAtS_keeps (H : GroundKeeps R) (P : Par) : Decides (By R fun s : S => s.st) (sendAtS
    (Cl := Cl) P) := by
  intro s rs gs s' h
  simp only [sendAtS] at h
  split at h
  · split at h
    · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      exact sendOwn_keeps (Cl := Cl) H P _ _ _ _ h1
    · cases h
  · cases h

/-- A segment's later moment, at the first chain's record. -/
theorem commitAtS_keeps (H : GroundKeeps R) (P : Par) (link moment : Nat) (arrays : Option
    (List Nat)) :
    Decides (By R fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  simp only [commitAtS] at h
  split at h
  · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
    subst h2
    show R s.st (((laid s y.held.w).putLink y.held.L).putFork y.held.F).st
    rw [putFork_st, putLink_st]
    exact commitOwn_keeps (Cl := Cl) H P link moment arrays _ _ _ _ h1
  · cases h

/-- The first segment's opening, at the first chain's record. -/
theorem firstAtS_keeps (H : GroundKeeps R) (q : Params.First) (gp : GPar) :
    Decides (By R fun s : S => s.st) (firstSegmentOpening (Cl := Cl) q gp) := by
  intro s rs _ s' h
  simp only [firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact firstOwn_keeps H _ _ _ _ _ _ h1
end VerifiableInference.Desc.K1.Rel
