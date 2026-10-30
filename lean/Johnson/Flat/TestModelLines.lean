-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TestModelLines.lean: tests of Johnson/Flat/ModelLines.lean, which run when this file is
compiled.

At the library's copy of the full-size example's parameter file (`TestInstance.fullPolicy`,
Johnson/Flat/TestInstance.lean) every further model line is the reference's, and `scalesAtRef`
returns a table with the words that `scalesOfFiles` returns. At copies with one line turned the test
names that line, and `scalesAtRef` refuses under its name. At the small example's parameter file the
first line that differs is theta0.
Where each expected value comes from: the names are the lines' own in the file, as `otherLinesOf`
has them; the turned lines are typed here.
Limits: the copies are the library's; nothing here reads a folder of examples. SIXTEEN ROWS OF THE
EIGHTY HAVE A TURNED COPY: ll, cs, theta0, hv, hgD, ut, wb_v, wb_emb, S, rx, kFD, sh, sT, F, trope7,
texp0. The other rows have none: so these guards do not hold the order of most of the typed names;
that order is read off `hdrOf` (OnBytes/Model/Config.lean).

-/
import Johnson.Flat.ModelLines
import Johnson.Flat.TestScalesOf

set_option autoImplicit false

namespace OnBytes.Flat.TestModelLines

open OnBytes.Model OnBytes.Flat.TestInstance OnBytes.Flat.TestScalesOf

/-- The first further line that is not the reference's; "scan" if the scan refuses the file. -/
def first (policy : ByteArray) : Option String :=
  match polScan policy with
  | .ok S => firstOtherLine S
  | .error _ => some "scan"

/-- The name under which `scalesAtRef` refuses; the empty string if it does not. -/
def whyRef (policy KL : ByteArray) : String :=
  match scalesAtRef policy KL with
  | .ok _ => ""
  | .error name => name

-- the full-size copy passes; how many rows there are
#guard first fullPolicy == none
#guard (polScan fullPolicy).toOption.map (fun S => (otherLinesOf S).length) == some 80
#guard (polScan fullPolicy).toOption.map otherLinesHeld == some true
#guard tableLineNames.length == 32 && tableLineNames.take 2 == ["tsilu0", "tsilu1"] &&
  tableLineNames.getLast? == some "texp7"
#guard whyRef fullPolicy fullKL == ""
#guard (scalesAtRef fullPolicy fullKL).toOption.map wordsTold ==
  (scalesOfFiles fullPolicy fullKL).toOption.map wordsTold

-- one line turned: the test names it. Each turned file is one that the scan admits: else "scan"
-- would stand here
#guard first (turned fullPolicy "ll 2" "ll 1") == some "ll"
#guard first (turned fullPolicy "cs 12" "cs 11") == some "cs"
#guard first (turned fullPolicy "theta0_lo 500000" "theta0_lo 10000") == some "theta0"
#guard first (turned fullPolicy "hv 1" "hv 2") == some "hv"
#guard first (turned fullPolicy "hgD 1" "hgD 2") == some "hgD"
#guard first (turned fullPolicy "ut 1" "ut 0") == some "ut"
#guard first (turned fullPolicy "wb_v 13" "wb_v 12") == some "wb_v"
#guard first (turned fullPolicy "wb_emb 21" "wb_emb 20") == some "wb_emb"
#guard first (turned fullPolicy "S 12" "S 11") == some "S"
#guard first (turned fullPolicy "rx 8" "rx 7") == some "rx"
#guard first (turned fullPolicy "kFD 16" "kFD 15") == some "kFD"
#guard first (turned fullPolicy "sh 8" "sh 7") == some "sh"
#guard first (turned fullPolicy "sT 4" "sT 3") == some "sT"
#guard first (turned fullPolicy "F 24" "F 23") == some "F"
#guard first (turned fullPolicy "trope7 4050797957" "trope7 4050797956") == some "trope7"
#guard first (turned fullPolicy "texp0 3648852807" "texp0 3648852806") == some "texp0"
#guard whyRef (turned fullPolicy "theta0_lo 500000" "theta0_lo 10000") fullKL ==
  "model-line-not-the-reference's: theta0"

-- the small example's file
#guard first smallPolicy == some "theta0"

end OnBytes.Flat.TestModelLines
