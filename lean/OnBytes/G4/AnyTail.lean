-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/AnyTail.lean: a caller of the lookup verifier with something behind the lookup.

The laws on a run of the lookup (OnBytes/G4/AnyCaller.lean and the files above it) speak of contexts
whose entries and rounds are listed, and of rounds that are plain: elements sent, elements drawn. In
a chain of the program other rounds stand behind a lookup's: rounds that draw positions, answers to
samples, a seal. These are no plain rounds. `Caller.withTail C tailEntries tailRounds` is the caller
C with each context's entries followed by tailEntries and its rounds by tailRounds, both arbitrary.
`Caller.Laws.withTail`: if C meets the laws, so does it. So every law on a run holds with an
arbitrary tail behind the plain rounds: the run does not look at the tail.

Main definitions: Caller.withTail.
Main theorems: Caller.Laws.withTail.
Not claimed: as in OnBytes/G4/AnyCaller.lean.


-/
import OnBytes.G4.AnyRun

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-- The caller with arbitrary entries and rounds behind those that are listed. -/
def Caller.withTail (C : Caller) (tailEntries : List Fmt.Entry) (tailRounds : List Fmt.RoundView) : Caller :=
  { C with ctx := fun es cur rs last σ rows => C.ctx (es ++ tailEntries) cur (rs ++ tailRounds) last σ rows }

theorem openedLeft_append (r : FlatRound) (rs tail : List Fmt.RoundView) :
    openedLeft r rs ++ tail = openedLeft r (rs ++ tail) := by
  unfold openedLeft
  cases r.sent.isEmpty <;> rfl

/-- A caller that meets the laws meets them with a tail. -/
theorem Caller.Laws.withTail {C : Caller} (L : C.Laws) (tailEntries : List Fmt.Entry)
    (tailRounds : List Fmt.RoundView) : (C.withTail tailEntries tailRounds).Laws where
  recv := by
    intro es rs last σ rows r
    show (Blk.recvEs r.sent.length) (C.ctx (es ++ tailEntries) none (r.rv :: (rs ++ tailRounds)) last σ rows) =
      .ok (r.sent, C.ctx (es ++ tailEntries) (openedCur r) (openedLeft r rs ++ tailRounds) last σ rows)
    rw [openedLeft_append]
    exact L.recv _ _ _ _ _ r
  close := by
    intro e es rs last σ rows r name kind nz h1 h2 h3 h4 h5 h6
    show (Blk.close name kind nz) (C.ctx (e :: (es ++ tailEntries)) (openedCur r)
        (openedLeft r rs ++ tailRounds) last σ rows) =
      .ok (r.rv.drawn, C.ctx (es ++ tailEntries) none (rs ++ tailRounds) (some e) σ rows)
    rw [openedLeft_append]
    exact L.close e _ _ _ _ _ r name kind nz h1 h2 h3 h4 h5 h6
  note := fun es cur rs last σ rows what x => L.note _ cur _ last σ rows what x
  take := fun es rs last σ rows n h => L.take _ _ last σ rows n h
  takeKey := fun es rs last σ rows n h => L.takeKey _ _ last σ rows n h
  takeLength := L.takeLength
  takeKeyLength := L.takeKeyLength
  leftTake := L.leftTake
  keyLeftTake := L.keyLeftTake
  leftTakeKey := L.leftTakeKey
  keyLeftTakeKey := L.keyLeftTakeKey
  takeOK := L.takeOK
  leave := fun es rs last σ rows row h => L.leave _ _ last σ rows row h
  fineTarget := L.fineTarget
  fineUnit := L.fineUnit
  finePlanes := L.finePlanes
  sampled := fun es rs last σ rows l h => L.sampled _ _ last σ rows l h

end OnBytes.G4

#print axioms OnBytes.G4.Caller.Laws.withTail
