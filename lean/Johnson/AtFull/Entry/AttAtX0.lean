-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/AttAtX0.lean: the seven tests on public data at the attention segments say yes
at the value that the public part's maker returns at the three full-size public files as
Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`). One statement, under the join's one premise.
  **`att_zFull`** (hsz : the layout file of `VerifierAndGoals.storedPublicFiles` has 224,975 bytes) (hX : `publicOfO
    OnBytes.secondHashFunction` returns X₀ at the three files): `∀ k < 7, K5Asks.rowW k X₀ = true`.
How. The join's conclusion (`publicOfO_zFull_of_rest`, Johnson/AtFull/Public/Join.lean) names the
value's parts by letters with their makers' equations; a maker is a function, so X₀ is that value;
`rowW_eq` (AttLaw.lean) brings each row to the scan and the twelve plans; `at_witnesses`
(Johnson/AtFull/Public/AtWitnesses.lean) carries the seven closed facts (AttRow0.lean to
AttRow6.lean) to these letters.
Why. It is one of the premises under which the proof file's maker is shown to return at these files
(the entry tests' rows on attention).
Limits. UNDER hsz, WHICH IS NOT PAID HERE (it is shown in the side library:
AtFullSide/Layout/Size.lean). At `VerifierAndGoals.storedPublicFiles` alone: three terms written in Ladder/Stored.lean; no
Lean code ties them to the top-level folder examples/. At the second hash function. A yes of seven
tests on public data: no proof is read, and nothing is accepted. Nothing on soundness, on a binding
of the commitment (the opening form, `BindsWith`), on correctness of extraction, on completeness or
on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.AttRow0
import Johnson.AtFull.Entry.AttRow1
import Johnson.AtFull.Entry.AttRow2
import Johnson.AtFull.Entry.AttRow3
import Johnson.AtFull.Entry.AttRow4
import Johnson.AtFull.Entry.AttRow5
import Johnson.AtFull.Entry.AttRow6
import Johnson.AtFull.Public.AtX0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (Makers at_witnesses opens_yFull)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Att.P

/-- **The seven tests at the attention segments say yes at the public part's value at
`VerifierAndGoals.storedPublicFiles`.** -/
theorem att_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : ∀ k < 7, K5Asks.rowW k X₀ = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -, -,
    hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have e : X₀ = _ := Except.ok.inj (hX.symm.trans hX')
  have h4 : X₀.p4 = true := by
    rw [e]
    show layers.y.h.p4 = true
    rw [ey]
    exact _root_.AtFull.Public.yFull_p4
  have hN : X₀.NGr = 12 := by
    rw [e]
    show layers.y.NGr = 12
    rw [ey]
    exact _root_.AtFull.Public.yFull_NGr
  intro k hk
  rw [rowW_eq h4 hN, e]
  have h0 := at_witnesses opens_yFull M att_0
  have h1 := at_witnesses opens_yFull M att_1
  have h2 := at_witnesses opens_yFull M att_2
  have h3 := at_witnesses opens_yFull M att_3
  have h4' := at_witnesses opens_yFull M att_4
  have h5 := at_witnesses opens_yFull M att_5
  have h6 := at_witnesses opens_yFull M att_6
  match k, hk with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4'
  | 5, _ => exact h5
  | 6, _ => exact h6

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.att_zFull
