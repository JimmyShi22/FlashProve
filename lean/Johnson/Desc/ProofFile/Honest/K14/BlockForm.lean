-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BlockForm.lean: kind K14: THE FORM OF THE VECTOR OF A BLOCK OF
ROWS. One definition; no theorem.

IT IS A SECOND TEXT: it says again, as a proposition on a vector's pairs and its list of written-out
variables, what the library's maker of a stretch's blocks lays there (stretchBlocks,
OnBytes/Iop/Lin.lean; one block: blockOf, Johnson/Road/Rows/StretchLaws.lean). THE LAW THAT TIES IT
TO THAT MAKER: stretch_form (Honest/K14/CutBlocks.lean): each vector that stretchBlocks returns has
this form.

  BlockForm kRow d q w   the low d variables of w are written out (the library's word: dense) and
                  have the pair (1, 1); above them stand the library's choicePairs for the number q,
                  kRow - d of them, each with one half 0. Where d ≤ kRow, w has kRow variables in
                  all; where q < 2 ^ (kRow - d), these pairs pick the block number q among the
                  blocks of 2 ^ d rows (choicePairs takes the low kRow - d bits of q alone)

What it does not ask. Nothing of the vector's scalar, of its written-out values, or of where these
begin.
-/
import OnBytes.Iop.Tensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes

/-- The form of the vector of a block of 2 ^ d rows: the low d variables are written out and have
the pair (1, 1); above them stand the pairs that pick the number q. -/
def BlockForm (kRow d q : Nat) (w : Tensor) : Prop :=
  w.pairs = List.replicate d (oneE, oneE) ++ choicePairs (kRow - d) q ∧
    w.denseVars = List.range' 0 d

end ProofFile.Honest.K14
