-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Views.lean: one type, the three views of a proof file (one view for each of
its three chains). It has a file of its own so that LotCore.lean, which needs the type, imports no
tool that alters a view.

-/
import Fmt.View

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

/-- The views of the first, the shared and the second chain. -/
abbrev Views : Type := Fmt.View × Fmt.View × Fmt.View

end ProofFile
