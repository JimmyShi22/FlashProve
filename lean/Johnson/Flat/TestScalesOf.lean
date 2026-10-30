-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TestScalesOf.lean: the table of scales off the copies of two configurations' files.

The copies are those that stand in the tests of the verifier's Lean text: the parameter files of
Johnson/Flat/TestInstance.lean; the scale files `Tie.Pv.Plan.scalesF`
(OnBytes/Tie/Pv/Plan/PlanKits.lean) and `Params.SmallFiles.scales`
(OnBytes/Params/SmallFiles.lean).

What is tested: at the full size a table is returned, so it is lawful, and it is compared, layer by
layer, with the library's reference scales `Cm.sRef`; what `scalesOfFiles` answers at the small
size; refusals: a scale file that is one word short; a shift outside its range; a rotary flag
against the pattern; a parameter file with a tolerance.

What is not tested: that the copies are the files. Each test is checked when the file compiles, by
Lean's evaluator. The file is no part of the program.

-/
import Johnson.Flat.ScalesOf
import Johnson.Flat.TestInstance

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat.TestScalesOf

open Inst.Model OnBytes.Flat.TestInstance

/-- The full-size scale file's copy. -/
def fullKL : ByteArray := Tie.Pv.Plan.wordsFile Tie.Pv.Plan.scalesF

/-- The small example's scale file's copy. -/
def smallKL : ByteArray := Params.SmallFiles.scales

/-- The name under which `scalesOfFiles` refuses; the empty string if it does not. -/
def whyNot (policy KL : ByteArray) : String :=
  match scalesOfFiles policy KL with
  | .ok _ => ""
  | .error name => name

/-- The words of all 48 layers and the final normalisation. -/
def wordsTold (s : Cm.Scales) : List Words × NormPar := ((List.finRange 48).map s.w, s.nf)

/-- The scale file with the 32-bit word number i put to v (v below 256). -/
def withWord (KL : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  (((KL.set! (4 * i) v).set! (4 * i + 1) 0).set! (4 * i + 2) 0).set! (4 * i + 3) 0

-- the lengths: 13 * 48 + 3 * 24 and 13 * 8 + 3 * 4 words
#guard fullKL.size == 4 * 696 && smallKL.size == 4 * 116
-- the full size: a table is returned
#guard whyNot fullPolicy fullKL == ""
-- it is the library's reference table, in all 48 layers and the final normalisation
#guard (scalesOfFiles fullPolicy fullKL).toOption.map wordsTold == some (wordsTold Cm.sRef)
-- what stands behind a file's last layer is the reference's words, where the parameter file's eps1
-- and eps2 are the reference's too: at a file of no layer, all 48
#guard (klFileOf { L := 0, eps := #[53687, 53687] } ByteArray.empty).map
    (fun f => (List.finRange 48).all fun L => f.words L == wRef) == some true
-- THE SMALL EXAMPLE's SETTINGS (the scale file's words with the parameter file's lines) ARE READ,
-- AND ARE NOT LAWFUL by the library's intervals
#guard ((Model.polScan smallPolicy).toOption.bind fun P => (klFileOf P.h smallKL).bind ofKL).isSome
#guard whyNot smallPolicy smallKL == "scales-not-lawful"
-- refusals at the full size: one word short; kq of layer 0 put to 4; the rotary flag of layer 0 put
-- to 0; a parameter file with a tolerance
#guard whyNot fullPolicy (fullKL.extract 0 (fullKL.size - 4)) == "scales-not-read"
#guard whyNot fullPolicy (withWord fullKL 0 4) == "scales-not-lawful"
#guard whyNot fullPolicy (withWord fullKL 12 0) == "scales-not-read"
#guard whyNot (turned fullPolicy "cap 0" "cap 1") fullKL == "policy-not-exact-match"

end OnBytes.Flat.TestScalesOf
