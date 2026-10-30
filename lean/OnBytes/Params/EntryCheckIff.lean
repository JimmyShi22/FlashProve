-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryCheckIff.lean: this file declares nothing; it imports
OnBytes/Params/EntryRounds.lean.










Not claimed. Nothing on soundness, on probabilities, or on what a yes of `Entry.check` shows. That
its decision says yes on any view is not shown. That any bytes are read as parameters is not shown.
The first table is an argument of `Entry.check` and of `Entry.read` (both of the Lean port built
from OnBytes/, not the C++ verifier's). Neither tests that it has passed a key file's check
(OnBytes/Entry/File.lean).
-/
import OnBytes.Params.EntryRounds

set_option autoImplicit false

namespace OnBytes.Params

end OnBytes.Params
