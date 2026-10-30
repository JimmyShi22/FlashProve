-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38A/MatrixOkAhead.lean: an array of a lawful layout is laid lawfully at the bits
that its message's shape gives, before that message is sent.

  `matrixOk_ahead`: from `reqLayoutOk cs shape lay = true`, the array A by the layout, the segment's
    shape and A's message M: `laidMatrixOk A (rowBitsOf M.shape .main) (placeBitsOf cs M.shape
    .main) = true` (Johnson/Desc/First/Batch/Ahead.lean). By `matrixOk_of_layoutOk`
    (Johnson/Desc/First/Att/K05LayoutOk.lean). After the pattern of `matrixOk_at`
    (Johnson/P1K8R/MatAtFold.lean), which speaks of a message that stands in the statement of oracle
    messages already.

Limits. General: no public file, no written value, no head of conditions is read. Nothing on
soundness.
-/
import Johnson.Desc.First.Att.K05LayoutOk
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)

/-- **Laid lawfully at the shape's own bits.** -/
theorem matrixOk_ahead {cs : Codes} {shape : Params.ReqShape} {lay : Params.ReqLayout}
    (hlo : reqLayoutOk cs shape lay = true) {born : ℕ} {name : String} {A : Params.ReqArray}
    (hA : reqArray lay born name = some A) {sh : Params.ReqLink}
    (hs : shape.link[born]? = some sh) {M : Params.ReqMessage}
    (hM : sh.messages[A.message]? = some M) :
    laidMatrixOk A (rowBitsOf M.shape .main) (placeBitsOf cs M.shape .main) = true := by
  obtain ⟨Lk, msg, c, h1, h2, h3, h4, h5, -⟩ :=
    VerifiableInference.Desc.First.Att.P.matrixOk_of_layoutOk _ _ _ hlo born name A hA
  obtain rfl : Lk = sh := Option.some.inj (h1.symm.trans hs)
  obtain rfl : msg = M := Option.some.inj (h2.symm.trans hM)
  have eR : rowBitsOf msg.shape .main = ceilLog2 msg.shape.mainRows := rfl
  have eP : placeBitsOf cs msg.shape .main = c.logEll := by
    show (if (msg.shape.mainRows == 0) = true then 0
      else (cs.base.getD msg.shape.code default).logEll) = _
    rw [if_neg (by simpa using h4), Array.getD_eq_getD_getElem?, h3]
    rfl
  rw [eR, eP]
  exact h5

end Q38

#print axioms Q38.matrixOk_ahead
