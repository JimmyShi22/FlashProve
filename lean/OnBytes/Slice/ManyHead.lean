-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyHead.lean: this file declares nothing; it imports OnBytes/Slice/BlkHead.lean and
OnBytes/Slice/ManyView.lean.


The program's link, run on the view of a written transcript whose rounds after the batching are a
chain of any number of stages, from the start to the joint before the first fold, is
`headRuns_manyR` (OnBytes/Slice/ManyHeadRec.lean).







Not claimed. All that the head of OnBytes/Slice/ManyHeadRec.lean does not claim. Nothing on the
rounds after the batching. Nothing on the dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkHead
import OnBytes.Slice.ManyView

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (LinkShape IoppStage)

end OnBytes.Slice
