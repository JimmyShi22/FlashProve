-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ModelLines.lean: a test that a parameter file's other model lines are the reference
parameter file's.

A definition, and four laws. The library's integer program is written for one parameter file, the
reference's. `sizesAt` (Johnson/Flat/Instance.lean) reads ten lines of a file, the sizes, and five
of its acceptance policy; `scalesOfFiles` (Johnson/Flat/ScalesOf.lean) reads the scale file, eight
numbers more (eps1, eps2, MF, KF, epsF, C, theta, cap; three of them stand on two lines each) and L.
The programs' model hangs on more lines. Inst/Model/Scales.lean says of the library's settings that
they cover a file's only if they are used with the reference parameter file's sizes, digit forms,
tables and rotary pattern. This file describes that test, and reads the table of scales behind it:
at a file that passes it, with the reference's sizes, these further lines are the reference's. The
test's own definitions (`otherLinesOf`, `firstOtherLine`, `otherLinesHeld` and three helpers) stand
in Johnson/Flat/SettingsRead.lean; what is said of them here holds of them there.

Main names:
  `otherLinesOf S` (defined in Johnson/Flat/SettingsRead.lean, as are the next two): the further
    lines of a scanned parameter file, each with the line's own name in the file and with the
    reference's value (theta0 stands for the two lines theta0_lo and theta0_hi; the row prof holds
    the line's number modulo 16, as the scan does: the file says 20; a digit form that the scan lays
    out for several classes bears its line's name at each; four rows "… (how many)" compare lengths
    of lists and are no lines): the profile; ll, by which four layers make a group; cs and theta0 of
    the rotary table; the seven digit forms, as the scan lays them out for the thirteen classes; ut;
    the fourteen declared widths of weights; S, rx and kFD of the softmax table; toksrc; sh, sT and
    F of the acceptance policy; the five optional lines eg, smax, rcl, gcl, xl, as 0 or 1; the 32
    words of the four public tables' digests.
  `firstOtherLine S`: the name of the first of them that is not the reference's, if there is one.
  `otherLinesHeld S`: true if there is none.
  `scalesAtRef policy KL`: `scalesOfFiles policy KL`, refused under "model-line-not-the-reference's:
    " and that name where the test fails.
  `scalesAtRef_eq`, `scalesAtRef_held`, `scalesAtRef_lawful`: what it returns is what
  `scalesOfFiles` returns; the test held; the table is lawful. `scalesAtRef_of`: the way back.
Where each reference value comes from. From the head of Inst/Model/ProgTests.lean: profile 4; a
group of four layers, so ll = 2; digit form 2 for queries and keys, 1 for the other classes; S = 12,
rx = 8, kFD = 16; sh = 8, sT = 4, F = 24; no eg, no smax, both clamps, five limbs. From the
reference parameter file (prover/examples/target_full_f2/policy.txt), typed by hand in
Johnson/Flat/SettingsRead.lean: cs = 12, theta0 = 500,000, ut = 1, toksrc = 1, the widths (13; 21
for the embedding) and the 32 words of the digests.
Limits: a comparison of numbers with typed numbers. THAT THE LIBRARY's FIXED TABLES (`tbRef`,
Inst/Model/TablesRef.lean) ARE THE TABLES WITH THESE FOUR DIGESTS IS NOT SHOWN HERE OR IN ANY FILE
NAMED HERE; THE REST OF THE LIBRARY HAS NOT BEEN READ FOR IT. That the list is whole, that is, that
the programs' model hangs on no further line, is a reading of what each line means (the fields of
`Model.Hdr` and `Model.PolScan`, OnBytes/Model/Config.lean; the lines' order and the four tables:
docs/format/FORMAT.md, 13.4, steps 1 and 4) and of the head of Inst/Model/ProgTests.lean, and no
law. The table of exponentials that the model's last stage looks up has no digest among the file's
lines: it is made by a recurrence. Left out on purpose, as lines that lay out the proof or that no
equation reads: la, nmin, D, tau; the matrices' sizes lmaf, NAf, lmad, NAd, lmar, lmb, lmq, lmx,
lmS, NAs, lmh, lmo, lmbA, lmhf, NHf, lmhd, lmhr, lmbH; the lines call, callA, callH with iota_0 to
iota_7, iotaA_0, iotaH_0 to iotaH_5; lidb, nminH; lB; kFM; seed; s. Whether the integer program's
result hangs on lB, the side of a tile of a head's score matrix, has not been read. The file's first
32 lines, from version to table, are no model lines and are outside this test. AT A FILE WITHOUT
EXPERTS (NE 0) THE NAME IN THE REFUSAL CAN POINT AT A LINE THAT IS THE REFERENCE's: the scan lays
the form 0 for the five expert classes, and the first row that differs bears the name hgD. One row
is idle: the scan itself refuses a file whose toksrc is not 1 (`polScan`,
OnBytes/Model/Config.lean). The sizes are not compared here. No claim of Johnson/Flat/ asks this
test; the function `settingsAtRef` (Johnson/Flat/SettingsRead.lean) makes it, and the theorem
`sound_progFull` (Johnson/Top/Own/OwnMember.lean [not in this library]) asks it, as its premise t3
(`scalesAtRef Z.pol Z.KL = .ok s`). It is evaluated at the reference's two files, and at copies with
one line turned, in Johnson/Flat/TestModelLines.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ScalesOf

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- The table of scales off the two files' bytes, refused where a further model line of the
parameter file is not the reference's. -/
def scalesAtRef (policy KL : ByteArray) : Except String Cm.Scales := do
  let S ← polScan policy
  match firstOtherLine S with
  | some name => throw ("model-line-not-the-reference's: " ++ name)
  | none => scalesOfFiles policy KL

/-- What is returned is what `scalesOfFiles` returns. -/
theorem scalesAtRef_eq {policy KL : ByteArray} {s : Cm.Scales}
    (h : scalesAtRef policy KL = .ok s) : scalesOfFiles policy KL = .ok s := by
  unfold scalesAtRef at h
  cases hS : polScan policy with
  | error e => rw [hS] at h; cases h
  | ok S =>
    rw [hS] at h
    have h' : (match firstOtherLine S with
      | some name => throw ("model-line-not-the-reference's: " ++ name)
      | none => scalesOfFiles policy KL) = .ok s := h
    cases h1 : firstOtherLine S with
    | some name => rw [h1] at h'; cases h'
    | none => rw [h1] at h'; exact h'

/-- Where a table is returned, the scan has returned and the test held. -/
theorem scalesAtRef_held {policy KL : ByteArray} {s : Cm.Scales}
    (h : scalesAtRef policy KL = .ok s) :
    ∃ S, polScan policy = .ok S ∧ otherLinesHeld S = true := by
  unfold scalesAtRef at h
  cases hS : polScan policy with
  | error e => rw [hS] at h; cases h
  | ok S =>
    rw [hS] at h
    have h' : (match firstOtherLine S with
      | some name => throw ("model-line-not-the-reference's: " ++ name)
      | none => scalesOfFiles policy KL) = .ok s := h
    refine ⟨S, rfl, ?_⟩
    unfold otherLinesHeld
    cases h1 : firstOtherLine S with
    | some name => rw [h1] at h'; cases h'
    | none => rfl

/-- The way back: where the scan returns, the test holds and `scalesOfFiles` returns a table,
`scalesAtRef` returns it. -/
theorem scalesAtRef_of {policy KL : ByteArray} {S : PolScan} {s : Cm.Scales}
    (hS : polScan policy = .ok S) (hh : otherLinesHeld S = true)
    (h : scalesOfFiles policy KL = .ok s) : scalesAtRef policy KL = .ok s := by
  unfold scalesAtRef
  rw [hS]
  show (match firstOtherLine S with
    | some name => throw ("model-line-not-the-reference's: " ++ name)
    | none => scalesOfFiles policy KL) = .ok s
  unfold otherLinesHeld at hh
  cases h1 : firstOtherLine S with
  | some name => rw [h1] at hh; cases hh
  | none => exact h

/-- The table that is returned is lawful. -/
theorem scalesAtRef_lawful {policy KL : ByteArray} {s : Cm.Scales}
    (h : scalesAtRef policy KL = .ok s) : s.Lawful :=
  scalesOfFiles_lawful (scalesAtRef_eq h)

end OnBytes.Flat
