-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLookups.lean: the values of the key file's prover's two lookups: what a lookup's sums are
taken of, the sums, and where each lookup stands.

A lookup sums over keys and bits. Here they are the library's own words for them, hiddenKey
(E2E/KeyLookupSeat.lean): a key is keyVec of the matrix; a bit is what bitVec reads off the main table
of the multiplicities' message. That table is planesVal of the same matrix, and planesVal is by its
definition (E2E/KeyPlanesRead.lean) planesData, which multiplicitiesSending lays, read at main row i % 2 ^ rb and
place i / 2 ^ rb: so what the lookups sum over is what was sent. These are the letters of
TruthAt (E2E/KeyLookupTruth.lean). The sums are fastJobs at each lookup's own face, as seatKeyFast
has them: the one filling that reads several parts of keys.

  matOf, mainOf, readOf   the matrix in machine words; the multiplicities' main table; the two
  WitK, keyWit  the two lookups' records, one input for both
  onHalf, keyJobs0, keyJobs1   each lookup's sums, at its own face and its own half of WitK
  keyReads, lookOf   how points are read; each lookup's place, face and rounds in front

Limits. This file holds these sums to nothing: that is done at any number of parts of keys by the
lookups' K3/Parts and K3/FastLaw (lawful_key_fast), which this file does not import.
A toy program plays them at up to twelve parts, masks at 0: that is no run of this text.
E2E/KeyLookupSeat.lean holds definitions, facts by unfolding and tests by Lean's evaluator; nothing
is played there. Out of range a key is counted nowhere: a play then fails, as it should. Nothing on
any property.
-/
import E2E.KeyFirstSends
import E2E.KeyLookupSeat
import Johnson.Desc.ProofFile.Honest.K3.JobsFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyValues
open OnBytes OnBytes.Params
open ProofFile.Honest (Weights)
open ProofFile.Honest.K3 (Ask LookJobs Reads At ptsOf pointsAt fastJobs)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.Key (planesVal)
open AtPublicFiles.KeyLookup (witKey readsKey atKey)
open AtPublicFiles.KeyFile (In1)

variable {W₀ Rc : Type}

/-- The matrix in machine words. -/
def matOf (f : W₀ → Weights) : In1 W₀ Rc → Nat → Nat → F :=
  fun t y c => OnBytes.Slice.ofF (matrixEntryOf f t y c)

/-- The multiplicities' main table: what multiplicitiesSending lays, as the library numbers its entries. -/
def mainOf (f : W₀ → Weights) (Xs : Source) : In1 W₀ Rc → Nat → E := fun t =>
  planesVal (matrixEntryOf f t) (Wf.matrixOf (oneOf Xs).lin).kCol (oneOf Xs).ranges.lookups
    ((oneOf Xs).codes.base.getD (oneOf Xs).ranges.message.shape.code default).ell
    (ceilLog2 (oneOf Xs).ranges.message.shape.mainRows)

/-- The two, as the library's seat reads them. -/
def readOf (f : W₀ → Weights) (Xs : Source) : In1 W₀ Rc → (Nat → Nat → F) × (Nat → E) :=
  fun t => (matOf f t, mainOf f Xs t)

/-- What both lookups read: one input, a half for each. -/
abbrev WitK : Type := Ask × Ask

/-- The record of lookup i. -/
def witAt (f : W₀ → Weights) (Xs : Source) (i : Nat) : In1 W₀ Rc → Ask :=
  witKey (oneOf Xs).ranges (oneOf Xs).codes i (Wf.matrixOf (oneOf Xs).lin)
    ((oneOf Xs).ranges.lookups.getD i default) (readOf f Xs)

/-- **The two lookups' records, of a half's input.** -/
def keyWit (f : W₀ → Weights) (Xs : Source) : In1 W₀ Rc → WitK :=
  fun t => (witAt f Xs 0 t, witAt f Xs 1 t)

/-- **How points are read.** -/
abbrev keyReads : Reads := readsKey

/-- Sums at one record, seated at a half of both. -/
def onHalf (pr : WitK → Ask) (J : LookJobs Ask) : LookJobs WitK :=
  ⟨fun s =>
    { round := fun w => (J.job s).round (pr w)
      inY := fun w => (J.job s).inY (pr w)
      ends := fun w => (J.job s).ends (pr w) }⟩

/-- Lookup i's sums, as seatKeyFast has them: at its face, with its public record's rows. -/
def jobsAt (Xs : Source) (i : Nat) : LookJobs Ask :=
  (fastJobs (faceAt Xs i) fun theta u => Lkp.rowAt (lookAt Xs i) theta u).asked

/-- **The first lookup's sums.** -/
def keyJobs0 (Xs : Source) : LookJobs WitK := onHalf Prod.fst (jobsAt Xs 0)

/-- **The second lookup's sums.** -/
def keyJobs1 (Xs : Source) : LookJobs WitK := onHalf Prod.snd (jobsAt Xs 1)

/-- Lookup i at its place. -/
def lookOf (Xs : Source) (N : H2U.PlaceNums) (i : Nat) : At :=
  atKey i (lookAt Xs i) (baseAt Xs N i)

end AtPublicFiles.KeyValues
