-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestCallsFull.lean: two of the program's test calls at the full parameters, evaluated.

The tests, made when the file compiles, show that from the C++ programs' full public files, with
`bits` 128, the calls `product` and `links` derive the parameter bytes of `product_full` and
`links_full` (OnBytes/Tie/ToysClosed.lean), and that they say "accepted" on the honest files that
the directory Fmt/ holds as data. The tests show what is so at these files and parameters, and
nothing beyond them.
-/
import OnBytes.Tie.ToysClosed
import Fmt.M1ProgPFFiles
import Fmt.M2ProgLFFiles
import Fmt.M1Theirs
import Fmt.M2Theirs

set_option autoImplicit false

namespace OnBytes.Tie

-- The product test.
#guard (Plan.productRun Fmt.M1.Theirs.pubFull 128).toOption.any
  (·.params == Fmt.M1.Theirs.specFull.params)
#guard Shell.product 128 Fmt.M1.Theirs.pubFull Fmt.M1.ProgPF.proof == .accepted
-- The chain of links.
#guard (Plan.linksRun Fmt.M2.Theirs.pubFull 128).toOption.any
  (·.params == Fmt.M2.Theirs.specFull.params)
#guard Shell.links 128 Fmt.M2.Theirs.pubFull Fmt.M2.ProgLF.proof == .accepted

end OnBytes.Tie
