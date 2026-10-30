-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsAskedOfHead.lean: the proofs of the four statements of
Johnson/P1K8R/RowsAskedOfHeadStatement.lean, to the letter. Lemmas; none of the library's goals.

How. `lay_left_at_most`: `K9Asks.rows_join` (Johnson/Desc/First/Link/Law/K9RowsParts.lean, another
group of authors', as it lies) at the plan's own data: the number of matrices is the list's length
(`OnBytes.Road.planG_sizes`, Johnson/Road/FormsKeysPlan.lean, at `Fo.Pub.public_G`,
OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean); the shapes' rows of symbols
(`OnBytes.Road.K4.Plan.public_G_mS`, Johnson/Road/K4/Plan/ShapeRowsG.lean); the reads (`reads_lay`,
Johnson/P1K8R/ReadsLay.lean); the plan's rows (`Fo.Pub.public_G_rows`). `rowsFit_lay_of_head`: the
built segment and its data by `IM.ground_tails`, `built_tl`, `ProofFile.Law.blankBy_W`; the plan's rows
are the written number (`planRows_by_plan`, Johnson/P1K8R/PlanRowsAtHead.lean), and so are the
declared round's (`k9Rows_at_head`, Johnson/P1K8R/K9RowsByLink.lean). `rowsFit_att_paid`:
`rowsFit_att_of_head` (Johnson/P1K8R/RowsFitAtt.lean), its one premise paid by `planRows_by_plan`.
`rowsAsked_of_head`: a number below 25 is 24, or 2 g, or 2 g + 1 with g below 12; at 24:
`rowsFit_head_of_head` (Johnson/P1K8R/RowsFitHead.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.RowsAskedOfHeadStatement
import Johnson.P1K8R.RowsFitHead
import Johnson.P1K8R.RowsFitAtt
import Johnson.P1K8R.PlanRowsAtHead
import Johnson.P1K8R.ReadsLay
import Johnson.Road.K4.Plan.ShapeRowsG
import Johnson.Road.FormsKeysPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9Asks (rowsFitB rowsFitB_iff built_tl claimsAt firstB readsB layPairs
  RowsAsked)

/-- **The test's left side at a stored layers' plan is at most the plan's rows.** -/
theorem lay_left_at_most : LayLeftAtMost := by
  intro Pb pp lay X g hp hS hR hpub hg
  obtain ⟨ps, e, hr⟩ := reads_lay Pb pp lay X g hp hS hR hpub hg
  exact ⟨ps, e, VerifiableInference.Desc.K9Asks.rows_join hp.tl ps
    (OnBytes.Road.planG_sizes (Fo.Pub.public_G hpub g hp hg)).2
    (OnBytes.Road.K4.Plan.public_G_mS hpub g hp hg) hr (Fo.Pub.public_G_rows hpub g hp hg)⟩

/-- **The test's yes at every 2 g, under the head.** -/
theorem rowsFit_lay_of_head : RowsFitLayOfHead := by
  intro Z D r Zp Np cF h g hg
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hp, -, l, -, hG, -, el, etl, -⟩ := (IM.ground_tails h.scope h.reads O.pub O.blank).1 g hg
  rw [ProofFile.Law.blankBy_W O.blank] at hG
  obtain ⟨X, eX, e⟩ := built_tl O.blank el
  obtain ⟨p, ep, er⟩ := k9Rows_at_head OnBytes.secondHashFunction Z D r Zp Np cF h (2 * g) (by omega)
  obtain ⟨ps, e2, q⟩ := lay_left_at_most Z _ _ Zp.p.X g hp h.scope h.reads h.pubOne hG
  have c1 : claimsAt Zp.p.X (2 * g) = some hp.nLin := by
    unfold claimsAt
    rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hG]
    rfl
  have c2 : VerifiableInference.Desc.K9Asks.pairsAt Zp.p.X (2 * g) = some ps := by
    unfold VerifiableInference.Desc.K9Asks.pairsAt
    rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]
    exact e2
  refine ⟨X, eX, (rowsFitB_iff Zp (2 * g) X).2 ⟨_, ps, p, c1, c2, ep, ?_⟩⟩
  rw [← e, etl, er, ← (planRows_by_plan OnBytes.secondHashFunction Z D r Zp Np cF h).1 g hg hp hG]
  exact q

/-- **The test's yes at every 2 g + 1, under the head, with no premise more.** -/
theorem rowsFit_att_paid : RowsFitAttPaid := by
  intro Z D r Zp Np cF h
  exact rowsFit_att_of_head Z D r Zp Np cF h fun g hg a ha =>
    Nat.le_of_eq (((planRows_by_plan OnBytes.secondHashFunction Z D r Zp Np cF h).2.1 g hg a ha).trans
      (rowsAtLink_odd g))

/-- **Under the head the rows fit at all 25 segments.** -/
theorem rowsAsked_of_head : RowsAskedOfHead := by
  intro Z D r Zp Np cF h l hl
  obtain rfl | ⟨g, hg, rfl | rfl⟩ : l = 24 ∨ ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) := by
    by_cases h24 : l = 24
    · exact Or.inl h24
    · exact Or.inr ⟨l / 2, by omega, by omega⟩
  · exact rowsFit_head_of_head Z D r Zp Np cF h
  · exact rowsFit_lay_of_head Z D r Zp Np cF h g hg
  · exact rowsFit_att_paid Z D r Zp Np cF h g hg

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.lay_left_at_most
#print axioms P1K8.rowsFit_lay_of_head
#print axioms P1K8.rowsFit_att_paid
#print axioms P1K8.rowsAsked_of_head
