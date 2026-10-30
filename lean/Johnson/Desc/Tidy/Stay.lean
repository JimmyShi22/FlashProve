-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Tidy/Stay.lean: "if the statement in front is tidy, so is the statement behind"
(`Tidy`, Johnson/Desc/Means/Walk.lean: in order; the open rows' kinds; no sample row on a message
that is not sampled; sampled members) as a relation on statements, and which of the plain ground's
functions keep it, each under the condition that row 23's laws ask. Statements with their proofs.
Main names:
  `TidyStay A B`: Tidy A → Tidy B. `tidyStay_of_quiet`, `tidyStay_of_walk`.
  `groundQuiet_tidy`: it is a `GroundQuiet` (Johnson/Desc/GroundQuiet.lean): the eight functions
    that ask nothing of their caller keep it.
  `admitOn_tidy`: the admitting keeps it where the rows handed in are on the message.
  `ElsewhereOn R`, `elsewhereOn_tidy`: the copying from another statement keeps it where that
    statement is in order.
  `tidyStay_begun`: the beginning of a proximity test keeps it.
  `not_tidyStay`: a try: from the empty statement to one with an open row marked as a sample row it
    does not hold.

What is not claimed. That a block goes by these functions alone: each kind's law says that. Nothing
on soundness.

-/
import Johnson.Desc.K1.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Slice Desc.Plain
open OnBytes.Means (Tidy Quiet Walk InOrder)

/-- If the statement in front is tidy, so is the statement behind. -/
def TidyStay (A B : Statement) : Prop := Tidy A → Tidy B

theorem tidyStay_of_quiet {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {A B : Statement}
    (q : Quiet ρ A B) : TidyStay A B := q.tidy

theorem tidyStay_of_walk {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {A B : Statement}
    (w : Walk ρ A B) : TidyStay A B := w.tidy

/-- **The eight functions that ask nothing of their caller keep it.** -/
theorem groundQuiet_tidy : GroundQuiet TidyStay where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun _ _ _ _ _ h => (Means.quiet_newGroupP OnBytes.Model.Reading.gl h).tidy
  recv := fun _ _ _ _ _ h => (Means.quiet_recvP OnBytes.Model.Reading.gl h).tidy
  join := fun _ _ _ _ _ h => (Means.quiet_joinP OnBytes.Model.Reading.gl h).tidy
  addRow := fun _ _ _ _ h => (Means.quiet_addRowP OnBytes.Model.Reading.gl h).tidy
  takeMask := fun _ _ _ _ h => (Means.quiet_takeMaskP OnBytes.Model.Reading.gl h).tidy
  closeLedger := fun _ _ _ h => (Means.quiet_closeLedgerP OnBytes.Model.Reading.gl h).tidy
  spendAsMask := fun _ _ _ h => (Means.quiet_spendAsMaskP OnBytes.Model.Reading.gl h).tidy
  adopt := fun _ _ _ _ _ h => (Means.quiet_adoptP OnBytes.Model.Reading.gl h).tidy

/-- The admitting keeps it where the rows handed in are on the message. -/
theorem admitOn_tidy : K1.AdmitOn TidyStay :=
  fun _ _ _ _ h hr => (Means.quiet_admitP OnBytes.Model.Reading.gl h hr).tidy

/-- The copying from another statement keeps R where that statement is in order. -/
def ElsewhereOn (R : Statement → Statement → Prop) : Prop :=
  ∀ {L : Type} (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat),
    elsewhereP d mine other theirs = some d' → InOrder other → R d.st d'.st

theorem elsewhereOn_tidy : ElsewhereOn TidyStay :=
  fun _ _ _ _ _ h hO => (Means.quiet_elsewhereP OnBytes.Model.Reading.gl h hO).tidy

/-- The beginning of a proximity test keeps it. -/
theorem tidyStay_begun (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    TidyStay S (Slice.begun S g G) := fun h => h.begun g G hG

/-- **A try.** -/
theorem not_tidyStay (codes : Codes) (r : OnBytes.Row) (hr : r.kind = .sample) :
    ¬ TidyStay { codes := codes, oracles := #[], groups := #[] }
      { codes := codes, oracles := #[], groups := #[{ code := 0, rows := #[r] }] } := by
  intro h
  exact (h (Tidy.start codes)).kinds 0 { code := 0, rows := #[r] } rfl r (by simp) hr

end VerifiableInference.Desc.Ground
