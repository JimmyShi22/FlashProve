-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/GroupsFull.lean: the 99 group lines of the full-size layout file as a
typed list, and what the sizing of a proof's first chain reads of the links that are made of them.

A group line of a layout file (Plan.LayoutGroup, OnBytes/Plan/ReqFrame.lean) names one oracle
message of a link: link, moment and group, counted from 0, the class as a byte, the rows and the
life. Params.proofSized reads of a request's links seven numbers: the five of Params.reqLoad, the
most messages of a link, and the row variables of the last group. Here these are evaluated by Lean's
kernel at the links that LinksOfLayout.lean makes of the typed lines.
Main names:
  `groupsFull`: the typed lines. `linksFull`: the links of 25 declared links, one answer and these
    lines, as proofSized fills them.
  `load_full`, `messages_full`, `lastK_full`: the seven numbers.
Limits: the typed lines were printed by Lean's evaluator from Plan.layoutRead at the text layoutF
(OnBytes/Tie/Pv/Plan/PlanLayoutFull.lean) and laid in by a program. THAT THEY ARE WHAT layoutRead
RETURNS THERE IS PROVED NOWHERE (LastAtScope.lean in this folder says what was tried). Nothing on
soundness. Nothing on hiding.
-/
import Johnson.Desc.K12.Law.Sizes.LinksOfLayout
import OnBytes.Params.DeriveReq

set_option autoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Plan OnBytes.Params

/-- The group lines of the full-size layout file. -/
def groupsFull : List LayoutGroup :=
  [⟨0, 0, 0, 78, 106, 0⟩, ⟨0, 0, 1, 66, 9, 1⟩, ⟨0, 0, 2, 66, 3, 2⟩, ⟨0, 1, 0, 87, 1, 0⟩, ⟨0, 2, 0,
    78, 31, 0⟩, ⟨1, 0, 0, 78, 42, 0⟩, ⟨1, 1, 0, 87, 1, 0⟩, ⟨1, 2, 0, 78, 14, 0⟩, ⟨2, 0, 0, 78, 104,
    0⟩, ⟨2, 0, 1, 66, 9, 1⟩, ⟨2, 0, 2, 66, 3, 2⟩, ⟨2, 1, 0, 87, 1, 0⟩, ⟨2, 2, 0, 78, 31, 0⟩, ⟨3, 0,
    0, 78, 42, 0⟩, ⟨3, 1, 0, 87, 1, 0⟩, ⟨3, 2, 0, 78, 14, 0⟩, ⟨4, 0, 0, 78, 104, 0⟩, ⟨4, 0, 1, 66,
    9, 1⟩, ⟨4, 0, 2, 66, 3, 2⟩, ⟨4, 1, 0, 87, 1, 0⟩, ⟨4, 2, 0, 78, 31, 0⟩, ⟨5, 0, 0, 78, 42, 0⟩, ⟨5,
    1, 0, 87, 1, 0⟩, ⟨5, 2, 0, 78, 14, 0⟩, ⟨6, 0, 0, 78, 104, 0⟩, ⟨6, 0, 1, 66, 9, 1⟩, ⟨6, 0, 2, 66,
    3, 2⟩, ⟨6, 1, 0, 87, 1, 0⟩, ⟨6, 2, 0, 78, 31, 0⟩, ⟨7, 0, 0, 78, 42, 0⟩, ⟨7, 1, 0, 87, 1, 0⟩, ⟨7,
    2, 0, 78, 14, 0⟩, ⟨8, 0, 0, 78, 104, 0⟩, ⟨8, 0, 1, 66, 9, 1⟩, ⟨8, 0, 2, 66, 3, 2⟩, ⟨8, 1, 0, 87,
    1, 0⟩, ⟨8, 2, 0, 78, 31, 0⟩, ⟨9, 0, 0, 78, 42, 0⟩, ⟨9, 1, 0, 87, 1, 0⟩, ⟨9, 2, 0, 78, 14, 0⟩,
    ⟨10, 0, 0, 78, 104, 0⟩, ⟨10, 0, 1, 66, 9, 1⟩, ⟨10, 0, 2, 66, 3, 2⟩, ⟨10, 1, 0, 87, 1, 0⟩, ⟨10,
    2, 0, 78, 31, 0⟩, ⟨11, 0, 0, 78, 42, 0⟩, ⟨11, 1, 0, 87, 1, 0⟩, ⟨11, 2, 0, 78, 14, 0⟩, ⟨12, 0, 0,
    78, 104, 0⟩, ⟨12, 0, 1, 66, 9, 1⟩, ⟨12, 0, 2, 66, 3, 2⟩, ⟨12, 1, 0, 87, 1, 0⟩, ⟨12, 2, 0, 78,
    31, 0⟩, ⟨13, 0, 0, 78, 42, 0⟩, ⟨13, 1, 0, 87, 1, 0⟩, ⟨13, 2, 0, 78, 14, 0⟩, ⟨14, 0, 0, 78, 104,
    0⟩, ⟨14, 0, 1, 66, 9, 1⟩, ⟨14, 0, 2, 66, 3, 2⟩, ⟨14, 1, 0, 87, 1, 0⟩, ⟨14, 2, 0, 78, 31, 0⟩,
    ⟨15, 0, 0, 78, 42, 0⟩, ⟨15, 1, 0, 87, 1, 0⟩, ⟨15, 2, 0, 78, 14, 0⟩, ⟨16, 0, 0, 78, 104, 0⟩, ⟨16,
    0, 1, 66, 9, 1⟩, ⟨16, 0, 2, 66, 3, 2⟩, ⟨16, 1, 0, 87, 1, 0⟩, ⟨16, 2, 0, 78, 31, 0⟩, ⟨17, 0, 0,
    78, 42, 0⟩, ⟨17, 1, 0, 87, 1, 0⟩, ⟨17, 2, 0, 78, 14, 0⟩, ⟨18, 0, 0, 78, 104, 0⟩, ⟨18, 0, 1, 66,
    9, 1⟩, ⟨18, 0, 2, 66, 3, 2⟩, ⟨18, 1, 0, 87, 1, 0⟩, ⟨18, 2, 0, 78, 31, 0⟩, ⟨19, 0, 0, 78, 42, 0⟩,
    ⟨19, 1, 0, 87, 1, 0⟩, ⟨19, 2, 0, 78, 14, 0⟩, ⟨20, 0, 0, 78, 104, 0⟩, ⟨20, 0, 1, 66, 9, 1⟩, ⟨20,
    0, 2, 66, 3, 2⟩, ⟨20, 1, 0, 87, 1, 0⟩, ⟨20, 2, 0, 78, 31, 0⟩, ⟨21, 0, 0, 78, 42, 0⟩, ⟨21, 1, 0,
    87, 1, 0⟩, ⟨21, 2, 0, 78, 14, 0⟩, ⟨22, 0, 0, 78, 104, 0⟩, ⟨22, 0, 1, 66, 9, 1⟩, ⟨22, 0, 2, 66,
    3, 2⟩, ⟨22, 1, 0, 87, 1, 0⟩, ⟨22, 2, 0, 78, 31, 0⟩, ⟨23, 0, 0, 78, 42, 0⟩, ⟨23, 1, 0, 87, 1, 0⟩,
    ⟨23, 2, 0, 78, 14, 0⟩, ⟨24, 0, 0, 78, 103, 0⟩, ⟨24, 1, 0, 87, 1, 0⟩, ⟨24, 2, 0, 78, 24, 0⟩]

/-- The links of these lines, with the reply's scalar and the codes' numbers filled in. -/
def linksFull : List ReqLink :=
  fillLinks (Model.Verify.withReply (linksOfGroups 25 1 groupsFull))

set_option maxRecDepth 1000000 in
/-- The load of the chain of links. -/
theorem load_full : reqLoad (shapeOfLinks linksFull 1) 22 13 (List.replicate 25 1) =
    ⟨8, 16, 30, 10, 15⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The most messages of a link, doubled, and two. -/
theorem messages_full :
    linksFull.foldl (fun m x => max m (2 * x.messages.length + 2)) 8 = 12 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The row variables of the last group. -/
theorem lastK_full :
    ((reqGroups (shapeOfLinks linksFull 1)).toList.getLast?.map (·.k)).getD 1 = 1 := by
  decide +kernel

end H2K.Sizes

#print axioms H2K.Sizes.load_full
#print axioms H2K.Sizes.messages_full
#print axioms H2K.Sizes.lastK_full
