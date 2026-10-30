-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SizesAnyRun.lean: the test sizesAnyRefB (Johnson/Top/SizesAnyDef.lean) by evaluation, at
the copies of two parameter files that stand in Johnson/Flat/TestInstance.lean.

Everything here is a run. A line "#guard" is evaluated when this file is compiled, by Lean's
interpreter, and the compilation fails if the value is not true. It is no theorem.

What is run. The test says true at the full-size parameter file's copy. IT STILL SAYS TRUE at that
copy with the line "cap 0" put to "cap 1" (another acceptance policy), where sizesRefB says false.
With "lt 10" put to "lt 9" (half the window) and with "V 202048" put to "V 202047" sizesAny returns,
with that one size turned, and the test says false; at the small example's parameter file sizesAny
returns its own ten sizes and the test says false. THE SCAN STILL READS THE POLICY's LINES: with
"cap 0" put to "cap 4294967296" (2^32) or to "kap 0" (another name), or with "sh 8" put to "sh 08"
(another spelling), sizesAny refuses the file.
Limits: runs alone. Not tested: that the copies are the files; a file with the lines of a policy
that anybody uses.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TestInstance
import Johnson.Top.SizesAny

set_option autoImplicit false

namespace VerifiableInference.OnPublicFiles.Flat.SizesAnyRun

open OnBytes.Flat.TestInstance

#guard sizesAnyRefB fullPolicy
#guard sizesAnyRefB (turned fullPolicy "cap 0" "cap 1")
#guard !sizesRefB (turned fullPolicy "cap 0" "cap 1")
-- a size is turned: sizesAny returns, with that size alone turned, and the test says false
#guard (sizesAny (turned fullPolicy "lt 10" "lt 9")).toOption.map ten ==
  some ((ten Inst.Model.ppref).set 0 512)
#guard !sizesAnyRefB (turned fullPolicy "lt 10" "lt 9")
#guard (sizesAny (turned fullPolicy "V 202048" "V 202047")).toOption.map ten ==
  some ((ten Inst.Model.ppref).set 1 202047)
#guard !sizesAnyRefB (turned fullPolicy "V 202048" "V 202047")
#guard (sizesAny smallPolicy).toOption.map ten == some [64, 512, 8, 512, 4, 2, 128, 1024, 512, 4]
#guard !sizesAnyRefB smallPolicy
-- the scan refuses a file where a line of the policy is too large, misnamed or misspelt
#guard (sizesAny (turned fullPolicy "cap 0" "cap 4294967296")).toOption.isNone
#guard (sizesAny (turned fullPolicy "cap 0" "kap 0")).toOption.isNone
#guard (sizesAny (turned fullPolicy "sh 8" "sh 08")).toOption.isNone
#guard !sizesAnyRefB (turned fullPolicy "cap 0" "cap 4294967296")

end VerifiableInference.OnPublicFiles.Flat.SizesAnyRun
