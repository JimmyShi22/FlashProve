-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/ParCodes.lean: the numbers of positions in a list (`tOff`, `tOn`) and the bound on a batch
(`maxBatch`), at the reference parameters of the paper (a print of the technical report,
lean/CREDITS.md).

What is not said: nothing on a protocol; that these numbers are the paper's is a comparison by
reading.
Terms: lean/GLOSSARY.md.
-/
import Code.Circle

set_option autoImplicit false

namespace Cb.Par
open Code Code.Circle

/-! ## Numbers of positions in a list, and the bound on a batch -/

/-- positions of one list: in the encoded index offline and in a further encoded index by its link
(`tOff`); in the encoded index by a session and in the first encoded index by a link (`tOn`) -/
def tOff : ℕ := 686
def tOn : ℕ := 53
/-- the bound on a batch -/
def maxBatch : ℕ := 64

end Cb.Par
