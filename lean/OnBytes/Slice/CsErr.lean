-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsErr.lean: the error count of a code switch's second round, written out.

OnBytes/Slice/CsData.lean sets the library's code switch at the sizes of two stages (`csSw`). The
library's count of the bad verifier messages of the second round (`Cb.LdSwW.err2`) is written with
the numbers of positions and of seeds. This file writes it in the stage's own numbers.

Main theorem.
 `cs_err2`  at the radius e and the bound L on the lists: with n = 2^a positions, t draws and a
           field of q elements the count is (n - e - 1)^t q + n^t (L (1 + 3 t)).
           The verifier message is t positions and one element, so there are n^t q messages.
           1 + 3 t is one less than the number of rows that are batched under the element's
           powers: three for each draw, one for the claim that is carried, one for the sample.

Not claimed. Nothing on the size of the count.
-/
import OnBytes.Slice.CsData

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-- The count of the second round of a code switch, in the stage's own numbers. -/
theorem cs_err2 {s s' : Sg} (hf : CsFit s s') (e L : ℕ) :
    (csSw hf).W.err2 e L =
      (2 ^ s.C.a - e - 1) ^ s.t * Fintype.card GE + (2 ^ s.C.a) ^ s.t * (L * (1 + 3 * s.t)) := by
  have hP : Fintype.card s.Ps = 2 ^ s.C.a := Fintype.card_fin _
  have hZ : 2 + 3 * s.t - 1 = 1 + 3 * s.t := by omega
  show (Fintype.card s.Ps - e - 1) ^ s.t * Fintype.card GE +
    Fintype.card s.Ps ^ s.t * (L * (2 + 3 * s.t - 1)) = _
  rewrite [hP, hZ]
  rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.cs_err2
