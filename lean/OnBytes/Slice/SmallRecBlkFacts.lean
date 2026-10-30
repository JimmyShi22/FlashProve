-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecBlkFacts.lean: the public facts of OnBytes/Slice/SmallRecBlkSizes.lean and
SmallRecBlkPub.lean at the sizes `srS` and the chain `srC` of OnBytes/Slice/SmallRecLink.lean, one
theorem for each hypothesis of the statement "the program's yes gives the yes in the field".

The two files state their facts with the tables' four radii as parameters. The instance of
`link_chain_joh` is at `srS` and `srC`, which fix them. This file says the facts again there, so
that a call needs no unfolding.

Main theorems: `sr_h0`, `sr_pub`, `sr_trees`, `sr_len`, `sr_groupFacts`, `sr_linkSizesR`,
`sr_linkFitR`, `sr_batDrawsS`, `sr_pads`, `sr_recordShape`.
Not claimed. What the heads of the two files do not claim. Nothing on a key, a record or its rows.
That the link's steps keep what the joint before the first fold asks. Nothing on soundness.

-/
import OnBytes.Slice.SmallRecBlkPub
import OnBytes.Slice.SmallRecLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (smallRecordRead)

/-- The stage of the link's group has no mask variable. -/
theorem sr_h0 : (srS.sg 97).h = 0 := rfl

/-- `Chain.Pub` of the chain and the program's stages. -/
theorem sr_pub : srC.Pub smallRecordRead.codes srSt1 srRest := sr_chain_pub _ _ _ _

/-- Which rounds of the chain send a tree. -/
theorem sr_trees : srC.Trees := sr_chain_trees _ _ _ _

/-- The trees' keys lie below 2 ^ 16. -/
theorem sr_len : 1 + srC.len ≤ 2 ^ 16 := sr_chain_few _ _ _ _

/-- The link's group: what the reading of its columns asks. -/
theorem sr_groupFacts :
    PQ.colW (srRd 1).tree = Fmt.M2.widthOf srS.P.mems 1 ∧
    srS.P.mems = [srS.P.mem, srS.P.mem] ∧
    srS.P.mem.overE = true ∧ srS.P.mem.masks = 0 ∧
    (Fmt.M2.starts [srS.P.mem, srS.P.mem]).1 =
      [some 0, some (2 ^ ceilLog2 smallRecordRead.link.rows)] ∧
    srS.P.mem.rows ≤ 2 ^ ceilLog2 smallRecordRead.link.rows ∧
    2 ^ ceilLog2 smallRecordRead.link.rows + srS.P.mem.rows ≤
      2 ^ Fmt.M2.kOf [srS.P.mem, srS.P.mem] ∧
    (rowShape smallRecordRead.link).mainRows = srS.P.mem.rows ∧
    (rowShape smallRecordRead.link).mainDeg = 3 ∧ (rowShape smallRecordRead.link).maskRows = 0 ∧
    (maskShape smallRecordRead.link).mainRows = 0 ∧
    0 < (maskShape smallRecordRead.link).maskRows := sr_groupFacts_par

/-- The sizes of the program's link, as a record. -/
theorem sr_linkSizesR : LinkSizes srS smallRecordRead.link (Entry.start smallRecordRead).st.codes :=
  sr_linkSizes _ _ _ _

/-- What is asked of the sizes and shapes, as a record. -/
theorem sr_linkFitR :
    LinkFit srS smallRecordRead.link (smallRecordRead.link.side false 1)
      (smallRecordRead.link.side true 1) :=
  sr_linkFit _ _ _ _

/-- What the link's five rounds and the batching's round send and draw. -/
theorem sr_batDrawsS : BatDraws srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5) :=
  sr_batDraws _ _ _ _

/-- A row's message has room for the pad of its one answer. -/
theorem sr_pads : 3 * 1 ≤ srS.P.T.l := sr_recordNumbers.2.2

/-- The shape's numbers of a record: the coordinates of a seed's point, and one answer a row. -/
theorem sr_recordShape : smallRecordRead.link.table.cubeBits = 19 ∧
    smallRecordRead.link.table.answers = 1 :=
  ⟨sr_recordNumbers.2.1, sr_recordNumbers.1⟩

end OnBytes.Slice
