-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorCodes.lean: THE FORM's HALF AT THE LINK, AT THE FULL SIZE: A SMALL SEAM: the
codes in the statement behind the batching are the plan's: so a fact on the plan that stands at
frP.codes (Johnson/Desc/K15/TypedP.lean) serves where the loop's laws ask it at the record's own
codes.

Main names (namespace Johnson.Prover.Link.Full).
  codes_full   THE STATEMENT.

By calls: ran_of_front (Johnson/Prover/Link/DoorPay.lean); plan_full (AtD.lean); begun_codes
(OnBytes/Slice/BlkLinkHead.lean); LinkRanR.codes (OnBytes/Slice/BlkLinkHeadRec.lean).

Limits. Premises: the two keys' items; the six front blocks' yes. Nothing on values. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 (St frP frontBlock blocksOrV first t12Of)

/-- **The codes in front of the stages are the plan's.** -/
theorem codes_full (x : TableKey × TableKey) (hi0 : x.1.item = 0) (hi1 : x.2.item = 1) (d' : St)
    (G' : Group) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
    (h : foldBlocks 0 (frontBlock frP :: blocksOrV frP) (first frP.codes x) rs cols =
      .ok (d', rest, cols'))
    (row : GroupRow) : (batT (t12Of d') G' row).st.codes = frP.codes := by
  obtain ⟨X, D, hR, -, -⟩ := ran_of_front frP x plan_full.2.1 plan_full.2.2.2 rfl _
    plan_full.1 [] d' rs rest cols cols' hi0 hi1 plan_full.2.2.1 h
  show (begun d'.st _ G').codes = _
  rw [begun_codes]
  exact hR.codes

end Johnson.Prover.Link.Full

#print axioms Johnson.Prover.Link.Full.codes_full
