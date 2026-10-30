-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/AtHead.lean: `SeatedFree` UNDER THE LIBRARY's ONE HEAD. A statement and its proof ON
THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

All that K9 has at the seat (`SeatedFree`, Honest/K9/AtSeatAll.lean) stands under three premises: the public files are
in the goals' scope, they are read, and the description's maker's value is opened (`IM.Open`,
Johnson/IMR/SeatOpen.lean). The frame's first thread is laid under another head: `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean), with its list of blocks := cF.blocksInOrder. THE BRIDGE LIES IN THE SEALED LIBRARY: `AtMgA` extends
`AtMg` (Johnson/P5J/AtMg.lean), whose fields `scope` and `reads` are the first two premises, and whose field `laid`
holds an opening at the head's own letters (`LaidAt.opened`, Johnson/P5J/LaidOpens.lean).
  **`seated_at_head`**   under `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`: at each l < 25 there are Lk, p, w with
      `SeatedFree cF Zp l k Lk p w`, k := 9 at the head's segment and 7 elsewhere
So K9's seat, the premise Sd : `SeatedFree` of its laws at a thread whose blocks are cF.blocksInOrder, is paid by that head.
On a member: the head is met under four premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z)
alone (the library's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); no member of what stands beside it
here is shown. Called by Honest/K9/SeatTied.lean and XkAtHead.lean.
WHAT IS NOT CLAIMED. The head. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtSeatAll
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (Chain)

/-- **`SeatedFree` under the library's one head.** -/
theorem seated_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    ∃ Lk p w, SeatedFree cF Zp l (if l = 24 then 9 else 7) Lk p w := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact free_at_seat_all h.scope h.reads O l hl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seated_at_head
