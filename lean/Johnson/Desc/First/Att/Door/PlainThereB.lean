-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/PlainThereB.lean: the public item «K5.plain» as a test with code, for a walk over stored records: at the record an attention segment's ledger is open, what
kind K5 heard is held, no "start" of a heard sumcheck names an entry, and the array of the reads (number iU3) is in the ledger, just nW columns wide. Definitions with code. No Mathlib.
iU3 and nW are letters: the segment's plan's (parCOf A).iU3 and (parCOf A).nW.
What it means, and who makes, keeps and spends it: PlainThereTie.lean, in the folder Law/ here.
Limits: a test. Nothing is proved here. Nothing on soundness.

-/
import Johnson.Desc.First.State
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (Heard)

def noEntsB (f : Aff) : Bool := f.ents.toList.isEmpty

def heardPlainB (h : Heard) : Bool :=
  (h.scores.toList.all fun o => noEntsB o.2.start) && noEntsB h.division.start && noEntsB h.below.start &&
  noEntsB h.on.start && noEntsB h.atIndex.start && noEntsB h.key.start && noEntsB h.cells.start

def wideB (U : Fork) (iU3 nW : Nat) : Bool :=
  match U.trees[iU3]? with
  | some T => T.K == nW
  | none => false

/-- **The item «K5.plain».** -/
def plainThereB (iU3 nW : Nat) (s : S) : Bool :=
  match s.fork?, s.heard5? with
  | some U, some h => heardPlainB h && wideB U iU3 nW
  | _, _ => false

end H2K5.Door
