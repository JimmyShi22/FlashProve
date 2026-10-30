-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ScalesOf.lean: the table of scales of the integer model, off the scale file and the
parameter file.

Definitions, and two laws. The claims of Johnson/Flat/Claims.lean and ClaimsAny.lean take a table of
scales s : `Cm.Scales` (Cm/Rel2.lean) as a letter. The library has the implementation's public
numbers as a type, `Inst.Model.KLFile`, the settings that they encode, `Inst.Model.ofKL`
(Inst/Model/ProgTests.lean), and the scales of settings, `Cm.Scales.of` (Cm/Rel2Guards.lean).
`klFileOf` (Johnson/Flat/SettingsRead.lean) reads a `KLFile` off the two files' bytes; this file
makes the settings and the table of scales of it.

The scale file (docs/format/FORMAT.md, 13.4, step 2): for each of the L layers a record of 13 words
of 32 bits: kq, kk, kv, ko, kg, ku, kd, M1, K1, M2, K2, sh, rp; after all layers three words kr,
kgR, kuR for each layer with an odd number. The lines eps1, eps2, MF, KF, epsF, C, theta, cap are
the parameter file's.

Main names:
  `klFileOf h KL` (defined in Johnson/Flat/SettingsRead.lean): the public numbers; nothing unless
    the parameter file has at most 48 layers and the scale file has exactly 13 L + 3 (L / 2) words.
    The library's type has 48 layers: BEHIND THE FILE's LAST LAYER STAND THE REFERENCE's SHIFTS,
    EXPONENTS AND FLAGS, with the file's own eps1 and eps2 as in every layer; a program of L layers
    does not read them.
  `settingsOfFiles policy KL`: the settings. Refused where `sizesAt` refuses the parameter file (so
    at every acceptance policy but exact match), where `klFileOf` gives nothing, where the rotary
    flags are not the reference pattern (`ofKL`), and WHERE THE SETTINGS ARE NOT LAWFUL
    (`Inst.Model.Lawful`, Inst/Model/Scales.lean, which is decidable).
  `scalesOfFiles policy KL`: their scales.
  `settingsOfFiles_lawful`, `scalesOfFiles_lawful`: what is returned is lawful.
Limits: nothing on a protocol. That the verifier program reads the scale file so is by the page and
by the library's own comments, not by a law on the program's reader. A dense layer, which has no
numbers kr, kgR, kuR, gets the reference's (`KLFile.words`). At fewer than 48 layers the table is
not the file's alone, as said; THE SMALL EXAMPLE's SETTINGS (its scale file's words with its
parameter file's lines) ARE READ AND ARE NOT LAWFUL by the library's intervals, so `scalesOfFiles`
refuses them (by an evaluation at copies of its two files). THE TABLE IS A PARAMETER FILE's MODEL's
ONLY IF THAT FILE's OTHER MODEL LINES ARE THE LIBRARY's: the five fixed tables of the integer model
are no part of a table of scales, and the lines cs, theta0, the digit forms, S, rx and the four
tables' digests are read by nothing here (Inst/Model/Scales.lean says of its settings that they
cover a file's only with the reference parameter file's sizes, digit forms, tables and rotary
pattern): at a file with the reference's sizes and, say, another theta0 a lawful table is returned,
and the claims are about a model that those programs do not run. L = 48 is not asked, though the
claims at the reference sizes take the table. "scales-not-read" is one name for two refusals: the
length, and the rotary pattern.

-/
import Johnson.Flat.Instance
import Johnson.Flat.SettingsRead
import Cm.Rel2Guards

set_option autoImplicit false

/- No default table of scales here: each table is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open Inst.Model

/-- The settings of the integer model, off the parameter file's and the scale file's bytes. -/
def settingsOfFiles (policy KL : ByteArray) : Except String ScalesAndPolicy := do
  let _ ← sizesAt policy
  let P ← Model.polScan policy
  match (klFileOf P.h KL).bind ofKL with
  | none => throw "scales-not-read"
  | some pp => if Lawful pp then pure pp else throw "scales-not-lawful"

/-- The table of scales, off the two files' bytes. -/
def scalesOfFiles (policy KL : ByteArray) : Except String Cm.Scales :=
  (settingsOfFiles policy KL).map Cm.Scales.of

/-- The settings that are returned are lawful. -/
theorem settingsOfFiles_lawful {policy KL : ByteArray} {pp : ScalesAndPolicy}
    (h : settingsOfFiles policy KL = .ok pp) : Lawful pp := by
  unfold settingsOfFiles at h
  cases h1 : sizesAt policy with
  | error e => rw [h1] at h; cases h
  | ok P0 =>
    rw [h1] at h
    cases h2 : Model.polScan policy with
    | error e => rw [h2] at h; cases h
    | ok P =>
      rw [h2] at h
      cases h3 : (klFileOf P.h KL).bind ofKL with
      | none =>
        simp [h3, bind, Except.bind] at h
      | some q =>
        by_cases hl : Lawful q
        · have h' : (pure q : Except String ScalesAndPolicy) = .ok pp := by
            simpa [h3, hl, bind, Except.bind] using h
          cases h'
          exact hl
        · simp [h3, hl, bind, Except.bind] at h

/-- **The table of scales that is returned is lawful.** -/
theorem scalesOfFiles_lawful {policy KL : ByteArray} {s : Cm.Scales}
    (h : scalesOfFiles policy KL = .ok s) : s.Lawful := by
  unfold scalesOfFiles at h
  cases h1 : settingsOfFiles policy KL with
  | error e => rw [h1] at h; cases h
  | ok pp =>
    rw [h1] at h
    cases h
    exact Cm.lawful_of (settingsOfFiles_lawful h1)

end OnBytes.Flat
