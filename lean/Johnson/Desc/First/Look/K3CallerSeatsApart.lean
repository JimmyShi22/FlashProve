--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3CallerSeatsApart.lean: UNDER THE PROGRAMS' OWN TEST ON A LAYOUT
(reqLayoutOk, OnBytes/Iop/ReqRows.lean) THE SEATS OF THE CALLER OF A LINK's LOOKUP ON THE CALLS ARE
APART: two cells with one seat are one element of one array. One theorem, on public data alone.

Why. SymsSit's clause "apart" (Johnson/Desc/First/Att/K05MsgOnto.lean) asks that two symbol
addresses with one seat hold one value. Here: two cells (tree, row, column) with one seat have one
row, one column, and trees at which the link's list of arrays names one array.

Main name: seatCalls_apart.

It adds no strength: glue. seatCalls_parts and msgIn_inj
(Johnson/Desc/First/Look/K3CallerMsgIn.lean): what a seat says of its cell; one number of a message
in the caller's list names one message of one link. laidPlace_apart
(Johnson/Desc/First/Look/K3CallerLaidApart.lean): in one message of one link no entry of the table
holds two elements.

Limits. It ends in "the list names one array at both trees", not in "one tree": a list of arrays
that names an array twice, or a record whose list of trees hands one tree to two matrices, is not
shut here. That the test has said yes at a description's own letters: pub_layoutOk
(Johnson/IMR/LayoutOkPub.lean), not called here. The mask row's seats are not spoken of. Nothing on
soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3CallerLaidApart
import Johnson.Desc.First.Look.K3CallerMsgIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes
open OnBytes.Road.Rows (Addr)

/-- **Two cells with one seat are one element of one array.** -/
theorem seatCalls_apart {D : Sent} (ok : reqLayoutOk D.codes D.shape D.layout = true)
    {k t t' r c r' c' : ℕ} {s : Seat} (h : seatCalls D k (.cell t r c) = some s)
    (h' : seatCalls D k (.cell t' r' c') = some s) :
    (D.arrayOf.getD k #[])[t]? = (D.arrayOf.getD k #[])[t']? ∧ r = r' ∧ c = c' := by
  obtain ⟨bn, a, rp, h1, h2, h3, h4, -, h5, h6⟩ := seatCalls_parts h
  obtain ⟨bn', a', rp', g1, g2, g3, g4, -, g5, g6⟩ := seatCalls_parts h'
  obtain ⟨eb, em⟩ := msgIn_inj h4 g4
  have er : rp = rp' := Prod.ext (h5.symm.trans g5) (h6.symm.trans g6)
  rw [← eb] at g2
  rw [← er] at g3
  obtain ⟨en, e3, e4⟩ := laidPlace_apart ok h2 g2 em h3 g3
  refine ⟨?_, e3, e4⟩
  rw [h1, g1]
  exact congrArg some (Prod.ext eb en)

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.seatCalls_apart
