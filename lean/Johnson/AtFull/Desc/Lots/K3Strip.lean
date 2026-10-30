-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3Strip.lean: THE LOT OF THE KIND "LOOKUP": BEHIND THE TEST ON THE CALLS
NOTHING OF A SKELETON READS A CALL's TABLE. Definitions with code; theorems. General in the lookup's
parameters. Why. At each of the 25 lookups on a segment's calls three calls bear a table of 65,536
rows: no written value can hold them. The test on a call (`callOk`,
Johnson/Desc/First/Look/ShapeOwn.lean) reads a table whole; what stands behind it reads the calls'
numbers alone.
  `stripP p`: the parameters with every call's table taken out (`strip`, `stripS`, `shapeOwn_strip`,
    `pubOk_strip`: Johnson/AtFull/ProofRows/K3HeadRow.lean: another file's: called).
  `shape_strip`, `entries_strip`, `rounds_strip`, `planOk_strip`, `fitsVia_strip`: under "every call
    passes callOk". (`entriesV_strip`: the one field of a face that reads the tables, the factor of
    a leaf, is read by no entry.)
  `skOwn_strip`: so the skeleton is the stripped parameters'.
Limits. "Every call passes callOk" is a premise. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Skel
import Johnson.AtFull.ProofRows.K3HeadRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Look (P shapeOwn pubOk callOk)
open Johnson.AtFull.ProofRows.K3 (strip stripS shapeOwn_strip pubOk_strip)

/-- The parameters with every call's table taken out. -/
def stripP (p : P) : P := { p with calls := p.calls.map strip }

variable {p : P} (hOk : p.calls.all callOk = true)
include hOk

theorem shape_strip : (stripP p).shape = p.shape.map stripS := by
  unfold P.shape stripP
  show ((shapeOwn (p.calls.map strip) p.lid).bind fun h0 =>
    if pubOk h0 p.pub then some { h0 with pub := p.pub } else none) = _
  rw [shapeOwn_strip hOk]
  cases shapeOwn p.calls p.lid with
  | none => rfl
  | some s =>
    show (if pubOk (stripS s) p.pub then some { stripS s with pub := p.pub } else none) =
      (if pubOk s p.pub then some { s with pub := p.pub } else none).map stripS
    rw [pubOk_strip]
    cases pubOk s p.pub <;> rfl

theorem entries_strip : (stripP p).entries = p.entries := by
  unfold P.entries
  rw [shape_strip hOk]
  cases p.shape <;> rfl

theorem rounds_strip : (stripP p).rounds = p.rounds := by
  unfold P.rounds
  rw [entries_strip hOk]

theorem planOk_strip (laid : Array Nat) :
    K3.planOk (S := First.S) (Cl := Claim) (stripP p) laid [] =
      K3.planOk (S := First.S) (Cl := Claim) p laid [] := by
  unfold K3.planOk P.planOk
  rw [shape_strip hOk, entries_strip hOk]
  cases p.shape <;> rfl

omit hOk in
/-- The rounds that the hearing goes by read of a face its numbers alone: not the factor of a leaf,
which reads the tables. -/
theorem entriesV_strip (h : Forest.Shape) :
    K3.entriesV (K3.faceOf (stripS h)) = K3.entriesV (K3.faceOf h) := by
  unfold K3.entriesV K3.leafVars
  rfl

theorem fitsVia_strip : K3.Law.fitsVia (stripP p) = K3.Law.fitsVia p := by
  unfold K3.Law.fitsVia
  rw [shape_strip hOk, entries_strip hOk]
  cases p.shape with
  | none => rfl
  | some h =>
    show (K3.entriesFit (K3.faceOf (stripS h)) (p.entries.getD []) && _) =
      (K3.entriesFit (K3.faceOf h) (p.entries.getD []) && _)
    unfold K3.entriesFit
    rw [entriesV_strip]

/-- **The skeleton is the stripped parameters'.** -/
theorem skOwn_strip (piece : Nat) (sent : List (Nat × Nat)) (laid : Array Nat) (key : Bool) :
    skOwn p piece sent
        (K3.planOk (S := First.S) (Cl := Claim) p laid [] && K3.Law.fitsVia p && key) =
      skOwn (stripP p) piece sent
        (K3.planOk (S := First.S) (Cl := Claim) (stripP p) laid [] &&
          K3.Law.fitsVia (stripP p) && key) := by
  unfold skOwn
  rw [rounds_strip hOk, planOk_strip hOk, fitsVia_strip hOk]
  rfl

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.shape_strip
#print axioms Johnson.AtFull.Lots.K3.entries_strip
#print axioms Johnson.AtFull.Lots.K3.rounds_strip
#print axioms Johnson.AtFull.Lots.K3.planOk_strip
#print axioms Johnson.AtFull.Lots.K3.entriesV_strip
#print axioms Johnson.AtFull.Lots.K3.fitsVia_strip
#print axioms Johnson.AtFull.Lots.K3.skOwn_strip
