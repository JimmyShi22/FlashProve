-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/RowFourteenThree.lean: THE FOURTEENTH ENTRY TEST's YES FROM THREE PREMISES:
`rowsMadeB_of_written` (Johnson/AtFull/Top/RowFourteen.lean) without its premise on the sendings:
`sendsWhole_all` (Johnson/AtFull/Sends/SendsWhole.lean) has the seven lists of
sendings, the fifth being the written `proofSends0`, at every planner's value whose four fields that
do not hang on the digest are the written ones. One call. A law file; no running text imports it.

Statement.
  `rowsMadeB_of_three`: these four fields of Z's planner's value are the written ones · the arms'
    test `armsB` accepts at Z's public data · the closed test `rowsWB` accepts ⊢ rowsMadeB Z = true.
    General in Z.

How. `sendsWhole_all` speaks of `Johnson.G.sendsFrom` (Johnson/G/SendsFrom.lean),
`rowsMadeB_of_written` of `VerifiableInference.Number.sendsFrom`
(Johnson/Desc/Ok/NumberPrices/AtDigest.lean): two constants with one text, tied by
`sendsFrom_same` (by rfl; Johnson/Desc/First/Link/Law/RowsRunLaws.lean): Lean sees it here by
unfolding.

Limits. Those of RowFourteen.lean: every premise is a premise. With `rowsWB = true` paid:
Johnson/AtFull/Top/RowFourteenTwo.lean. The place of the premise on the sendings is taken by other
files' closed facts, by Lean's kernel, with their negative tests (Johnson/AtFull/Sends/,
Johnson/IMR/KeySend*.lean). No use of
protocolDataWellFormed, of the pin, of the return of verify-on-bytes's planner or of the scope. The full size
alone. Nothing on soundness.
-/
import Johnson.AtFull.Top.RowFourteen
import Johnson.AtFull.Sends.SendsWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open Johnson.G.MadeFree (freeOf)
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Desc.LinkJoin

/-- **The fourteenth entry test accepts, from three premises.** -/
theorem rowsMadeB_of_three {Z : ProofFile.Pub} (e1 : freeOf Z.made.p.chains.made = writtenMade)
    (ha : armsB Z.made.p.X = true) (K : rowsWB = true) : rowsMadeB Z = true := by
  obtain ⟨En, h⟩ := Johnson.AtFull.Sends.sendsWhole_all
  exact rowsMadeB_of_written e1 (h _ e1) ha K

end AtFull.Top

#print axioms AtFull.Top.rowsMadeB_of_three
