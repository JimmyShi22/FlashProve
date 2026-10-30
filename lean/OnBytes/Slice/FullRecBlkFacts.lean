-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecBlkFacts.lean: the public facts of OnBytes/Slice/FullRecBlkSizes.lean and
FullRecBlkPub.lean at the sizes `frS` and the chain `frC` of OnBytes/Slice/FullRecLink.lean, one
theorem for each hypothesis of the statement "the program's yes gives the yes in the field".

The two files state their facts with the tables' four radii as parameters. The instance of
`link_chain_joh` is at `frS` and `frC`, which fix them. This file says the facts again there, so
that a call needs no unfolding.

Main theorems: `fr_h0`, `fr_pub`, `fr_trees`, `fr_len`, `fr_groupFacts`, `fr_linkSizesR`,
`fr_linkFitR`, `fr_batDrawsS`, `fr_pads`, `fr_recordShape`.
Not claimed. What the heads of the two files do not claim. Nothing on a key, a record or its rows.
That the link's steps keep what the joint before the first fold asks. Nothing on soundness.

-/
import OnBytes.Slice.FullRecBlkPub
import OnBytes.Slice.FullRecLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (recordRead)

/-- The stage of the link's group has no mask variable. -/
theorem fr_h0 : (frS.sg 97).h = 0 := rfl

/-- `Chain.Pub` of the chain and the program's stages. -/
theorem fr_pub : frC.Pub recordRead.codes frSt1 frRest := fr_chain_pub _ _ _ _

/-- Which rounds of the chain send a tree. -/
theorem fr_trees : frC.Trees := fr_chain_trees _ _ _ _

/-- The trees' keys lie below 2 ^ 16. -/
theorem fr_len : 1 + frC.len ≤ 2 ^ 16 := fr_chain_few _ _ _ _

/-- The link's group: what the reading of its columns asks. -/
theorem fr_groupFacts :
    PQ.colW (frRd 1).tree = Fmt.M2.widthOf frS.P.mems 1 ∧
    frS.P.mems = [frS.P.mem, frS.P.mem] ∧
    frS.P.mem.overE = true ∧ frS.P.mem.masks = 0 ∧
    (Fmt.M2.starts [frS.P.mem, frS.P.mem]).1 =
      [some 0, some (2 ^ ceilLog2 recordRead.link.rows)] ∧
    frS.P.mem.rows ≤ 2 ^ ceilLog2 recordRead.link.rows ∧
    2 ^ ceilLog2 recordRead.link.rows + frS.P.mem.rows ≤ 2 ^ Fmt.M2.kOf [frS.P.mem, frS.P.mem] ∧
    (rowShape recordRead.link).mainRows = frS.P.mem.rows ∧
    (rowShape recordRead.link).mainDeg = 3 ∧ (rowShape recordRead.link).maskRows = 0 ∧
    (maskShape recordRead.link).mainRows = 0 ∧
    0 < (maskShape recordRead.link).maskRows := fr_groupFacts_par

/-- The sizes of the program's link, as a record. -/
theorem fr_linkSizesR : LinkSizes frS recordRead.link (Entry.start recordRead).st.codes :=
  fr_linkSizes _ _ _ _

/-- What is asked of the sizes and shapes, as a record. -/
theorem fr_linkFitR :
    LinkFit frS recordRead.link (recordRead.link.side false 1) (recordRead.link.side true 1) :=
  fr_linkFit _ _ _ _

/-- What the link's five rounds and the batching's round send and draw. -/
theorem fr_batDrawsS : BatDraws frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5) :=
  fr_batDraws _ _ _ _

/-- A row's message has room for the pad of its one answer. -/
theorem fr_pads : 3 * 1 ≤ frS.P.T.l := fr_recordNumbers.2.2

/-- The shape's numbers of a record: the coordinates of a seed's point, and one answer a row. -/
theorem fr_recordShape : recordRead.link.table.cubeBits = 29 ∧ recordRead.link.table.answers = 1 :=
  ⟨fr_recordNumbers.2.1, fr_recordNumbers.1⟩

end OnBytes.Slice
