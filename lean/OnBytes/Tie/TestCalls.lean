-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestCalls.lean: two of the program's test calls, evaluated.

The calls of OnBytes/Shell/Toys.lean derive a chain's parameter bytes from the public files. The
tests, made when the file compiles, show that on the C++ programs' public files they derive the very
bytes on which OnBytes/Tie/TestProgram.lean [not in this library; so here read: not tested in this library] evaluates the hypotheses of the theorems, and that the
calls say "accepted" on the honest files. So `shell_product`, `shell_links` and `shell_entry`
(OnBytes/Tie/Program.lean) apply to these three calls. The tests show what is so at these files and
parameters, and nothing beyond them.
-/
import OnBytes.Tie.Program
import Fmt.M1ProgPTFiles
import Fmt.M2ProgLTFiles
import Fmt.M1Theirs
import Fmt.M2Theirs

set_option autoImplicit false

namespace OnBytes.Tie

-- At the two test protocols' tiny parameters the calls accept with `bits` 0, and not with 128.
#guard (Plan.productRun Fmt.M1.Theirs.pubTiny 0).toOption.any (·.params == Fmt.M1.ProgPT.params)
#guard Shell.product 0 Fmt.M1.Theirs.pubTiny Fmt.M1.ProgPT.proof == .accepted
#guard Shell.product 128 Fmt.M1.Theirs.pubTiny Fmt.M1.ProgPT.proof != .accepted
#guard (Plan.linksRun Fmt.M2.Theirs.pubTiny 0).toOption.any (·.params == Fmt.M2.ProgLT.params)
#guard Shell.links 0 Fmt.M2.Theirs.pubTiny Fmt.M2.ProgLT.proof == .accepted
#guard Shell.links 128 Fmt.M2.Theirs.pubTiny Fmt.M2.ProgLT.proof != .accepted

end OnBytes.Tie
