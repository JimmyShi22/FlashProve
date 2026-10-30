-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SitsDoor.lean: THROUGH THE DOOR OF THE TABLE OF JOINTS
(Johnson/Desc/First/Borders.lean: `Pub.more`, `More`): one public item by name, and who makes it.
Two definitions. It imports that file alone.
  `wSitsItem`: the item "K13.wSits": "W sits as the plan says". What it says is a filling's
    (`Meaning.pub` at it): MEANT: `wSitsB cs P s && wSeatB N.w s` at the record s
    (Johnson/Desc/K13/Law/SitsAt.lean, SeatMade.lean): cs the codes of the place of W's sending, P
    kind K13's numbers, N.w the table's tenant for W.
  `wSitsMore`: the door's filling: MADE by the block of kind K1 behind the links (W's commitment:
    the table's own row there is found by the same two tests); asked by nobody here; dropped by
    nobody; not open at the start.
The makers' lemmas and "kept at the chain's last block": Johnson/Desc/K13/Law/SitsMade.lean,
SeatMade.lean. The
table's test on a filling at two lists of segments: Johnson/Desc/K13/Law/AtTableW.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (Pub More)

/-- **Through the table's door**: "W sits as the plan says". -/
def wSitsItem : Pub := .more none "K13.wSits"

/-- The door's filling: the item is made by the block of kind K1 behind the links; nobody drops it
on this chain. -/
def wSitsMore : More where
  rows := fun _ p =>
    if p.link.isNone && p.kind == .K1 then { makes := [(none, "K13.wSits")] } else {}

end VerifiableInference.Desc.K13.Law
