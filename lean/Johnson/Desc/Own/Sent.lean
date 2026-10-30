-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Sent.lean: one small test on the shape of an oracle message that is sent, in the
description's own text, for every block that takes in announced messages.

  sentShapeFits codes s
      THE SHAPE OF A MESSAGE THAT IS SENT. It has a row (main or mask); if it has main rows, its
      main code's number is one of the list of main codes; if it has mask rows, its mask code's
      number is one of the list of mask codes; the degree of its main rows' field is 1 or 3, AND
      THAT IS ASKED ALSO OF A MESSAGE WITHOUT MAIN ROWS.
What is taken from the hand-written program's files: the records Codes and OracleShape with their
fields. No function of these files is called: a walk by constants beneath it finds none.
That it says just what the program's Blk.shapeOk says, at all arguments, is proved beside, in
Johnson/Desc/Own/SentAgree.lean, which no block imports.
LIMIT: whether this test asks enough is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- The shape of a message that is sent. -/
def sentShapeFits (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Bool :=
  decide (0 < s.mainRows + s.maskRows) &&
    (s.mainRows == 0 || decide (s.code < codes.base.size)) &&
    (s.maskRows == 0 || decide (s.maskCode < codes.mask.size)) &&
    (s.mainDeg == 1 || s.mainDeg == 3)

end VerifiableInference.Desc.Own
