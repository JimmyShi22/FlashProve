-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/StatementCalls.lean: WHAT A RELATION ON THE STATEMENT OWES SO THAT EVERY
SUB-PROTOCOL OF THE FIRST CHAIN KEEPS IT, as one Lean structure; and the first chain's last
proximity test, general in such a relation.

  StKeeps R        three fields: the ground's routines keep R (GroundKeeps,
                   Johnson/Desc/GroundKeeps.lean); the beginning of a proximity test keeps it
                   (Slice.begun); the one write of a pending row keeps it (pendingRowO,
                   Johnson/Desc/First/Pend/Row.lean).
  call_keeps, calls_keeps   each call of the ground, and a run of calls
                   (Johnson/Desc/K12/Law/CallsDef.lean), keep R.
  atFinish_keeps   so does kind K12's sub-protocol at the first chain's end (k12_calls,
                   Johnson/Desc/K12/Law/Calls.lean).
  stKeeps_fit      THE INSTANCE: FitStays: every ledger in order in front, every ledger in order
                   behind (ledgersKept, fit_begun, pendingRowO_ledgers).
  atFinish_ledgersFit   the sub-protocol at that instance.

WHICH RELATIONS FIT. GroundKeeps asks that the admitting of a message keeps R at ANY rows. A
relation that is kept only where the rows are those of the message's own sample ("tidy in front,
tidy behind") has no such field: it is no instance.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.LedgersBegun
import Johnson.Desc.K13.Law.LedgersB
import Johnson.Desc.K13.Law.LedgersAtRow
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.Keeps (Decides)
open H2K.Out (Call Calls DS dT k12_calls)

/-- **What a relation on the statement owes.** -/
structure StKeeps (R : Statement → Statement → Prop) : Prop where
  ground : GroundKeeps R
  begun : ∀ (T : Statement) (g : Nat) (G : Group), R T (begun T g G)
  row : ∀ (lay : WsLay) (im : ℕ) (o : WsForkOut) (n : ℕ) (lin : LinShape) (T : Statement)
    (r : TensorRow) (os' : Array OnBytes.Oracle),
    pendingRowO lay im o n lin T.oracles = .ok (r, os') → R T { T with oracles := os' }

variable {R : Statement → Statement → Prop} {ft : ℕ}

/-- **Each call of the ground** keeps R. -/
theorem call_keeps (K : StKeeps R) (d d' : DS) (h : Call ft d d') : R d.st d'.st := by
  cases h with
  | newGroup h => exact K.ground.newGroup _ _ _ _ _ h
  | recv h => exact K.ground.recv _ _ _ _ _ h
  | admit _ _ _ _ h => exact K.ground.admit _ _ _ _ h
  | join h => exact K.ground.join _ _ _ _ _ h
  | addRow h => exact K.ground.addRow _ _ _ _ h
  | closeLedger h => exact K.ground.closeLedger _ _ _ h
  | spend h => exact K.ground.spendAsMask _ _ _ h
  | begin h =>
    obtain ⟨G, -, -, e⟩ := Means.beginRunP_inv h
    rw [e]
    exact K.begun _ _ _
  | count t => exact K.ground.refl _
  | cols l => exact K.ground.refl _

/-- So does a run of calls. -/
theorem calls_keeps (K : StKeeps R) {d d' : DS} (h : Calls ft d d') : R d.st d'.st :=
  Calls.keeps (R := fun a b => R a.st b.st) (fun _ => K.ground.refl _)
    (fun _ _ _ p q => K.ground.trans p q) (call_keeps K) h

/-- **The first chain's last proximity test** keeps R. -/
theorem atFinish_keeps (K : StKeeps R) (p : K12.P12) :
    Decides (By R fun s : S => s.st) (K12.atFinish p) := by
  intro s rs gs s' h
  obtain ⟨o, t', -, -, -, hk, rfl⟩ := K12.Seat.atFinish_ok p s _ rs gs h
  exact calls_keeps K (k12_calls p _ t' rs gs hk [] [])

/-- **THE INSTANCE**: every ledger in order in front, every ledger in order behind. -/
theorem stKeeps_fit : StKeeps FitStays where
  ground := ledgersKept
  begun := fun T g G h => fit_begun T g G h
  row := fun _ _ _ _ _ _ _ _ h hf => (pendingRowO_ledgers h hf).1

theorem atFinish_ledgersFit (p : K12.P12) :
    Decides (By FitStays fun s : S => s.st) (K12.atFinish p) := atFinish_keeps stKeeps_fit p

end VerifiableInference.Desc.K13.Law
