-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/KeepsAtSCore.lean: Johnson/Desc/K1/KeepsAtS.lean once more, for a relation that
reads the statement, the book of trees and the count of roots (Johnson/Desc/CoreKeeps.lean): the
first segment's opening, and kind K1's three blocks at the first chain's record, keep EVERY
relation that meets CoreRecv at the block's own first tree, read at the record's own three fields
(coreS). Theorems: that file's six, statement and
proof, with the three in the statement's place.

  coreS                the three, off the first chain's record.
  firstOwn_keeps · putLink_core · putFork_core · sendAtS_keeps · commitAtS_keeps · firstAtS_keeps.
What is not claimed: as in Johnson/Desc/K1/KeepsCore.lean.

-/
import Johnson.Desc.K1.First
import Johnson.Desc.K1.KeepsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.RelCore
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (Core coreOf CoreStill CoreRecv ByC)
open VerifiableInference.Desc.Keeps (Decides)

variable {L Cl : Type} {R : Core → Core → Prop}

/-- The three, off the first chain's record. -/
def coreS (s : S) : Core := ⟨s.st, s.book, s.roots⟩

/-- The first segment's opening. -/
theorem firstOwn_keeps (P : Par) (H : CoreRecv P.gp.firstTree R) (owed : Option Nat)
    (c : ChainCheck)
    (d : DState Unit)
    (rs : List Fmt.RoundView) (y : ChainCheck × DState Unit) (h : firstOwn P owed c d rs = .ok y) :
    R (coreOf d) (coreOf y.2) := by
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
    (decideSend_keeps P H _ _ _ _ h2))
    (joinOwnP_keeps H.toCoreStill _ _ _ _ _ _ ((named_ok _ _ _).1 h3))
/-- Laying the link's record leaves the three as they are. -/
theorem putLink_core (s : S) (X : LinkCtx) : coreS (s.putLink X) = coreS s := by
  unfold S.putLink
  split <;> first | rfl | (split <;> rfl)

/-- Laying the ledger leaves the three as they are. -/
theorem putFork_core (s : S) (X : Fork) : coreS (s.putFork X) = coreS s := by
  unfold S.putFork
  split <;> first | rfl | (split <;> rfl)

/-- W's sending, at the first chain's record. -/
theorem sendAtS_keeps (P : Par) (H : CoreRecv P.gp.firstTree R) : Decides (ByC R coreS) (sendAtS
    (Cl := Cl) P) := by
  intro s rs gs s' h
  simp only [sendAtS] at h
  split at h
  · split at h
    · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      exact sendOwn_keeps (Cl := Cl) P H _ _ _ _ h1
    · cases h
  · cases h

/-- A segment's later moment, at the first chain's record. -/
theorem commitAtS_keeps (P : Par) (H : CoreRecv P.gp.firstTree R) (link moment : Nat)
    (arrays : Option
    (List Nat)) :
    Decides (ByC R coreS) (commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  simp only [commitAtS] at h
  split at h
  · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
    subst h2
    show R (coreS s) (coreS (((laid s y.held.w).putLink y.held.L).putFork y.held.F))
    rw [putFork_core, putLink_core]
    exact commitOwn_keeps (Cl := Cl) P H link moment arrays _ _ _ _ h1
  · cases h

/-- The first segment's opening, at the first chain's record. -/
theorem firstAtS_keeps (q : Params.First) (gp : GPar) (H : CoreRecv gp.firstTree R) :
    Decides (ByC R coreS) (firstSegmentOpening (Cl := Cl) q gp) := by
  intro s rs _ s' h
  simp only [firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  cases h
  refine firstOwn_keeps _ ?_ _ _ _ _ _ h1
  exact H
end VerifiableInference.Desc.K1.RelCore
