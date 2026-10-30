-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsFitHead.lean: the proofs of the three statements of
Johnson/P1K8R/RowsFitHeadStatement.lean, to the letter. Lemmas; none of the library's goals.

How. `built_head_tl`: three calls: `IM.ground_tails` (Johnson/IMR/K8Seat.lean: the blank ground's
built segment at 24 has the head's plan's data), `built_tl`
(Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean: the public part's segment has the blank ground's
data), `ProofFile.Law.blankBy_W` (Johnson/Desc/ProofFile/Law/MakerPublic.lean). `rowsFit_head_in_scope`:
`rowsFitB_iff` (K9RowsAskLaw.lean) from right to left: the claims and the tables by the test's text
at 24; the reads by `reads_head_eq` (Law/K9ReadsHeadPaid.lean); so the left side is the plan's
number of rows (`head_left_is_rows`, `Fo.Pub.public_H_rows`), which is 24,653,737
(`head_rows_in_scope`, Johnson/P1K8R/HeadRowsInScope.lean): "at most" holds with equality.
`rowsFit_head_of_head`: the head opens (`h.laid.opened`, as `P5J.AtMg.kind24` goes,
Johnson/P5T/Kind24AtMg.lean); K9's numbers by `k9Rows_at_head` (Johnson/P1K8R/K9RowsByLink.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.RowsFitHeadStatement
import Johnson.P1K8R.K9RowsByLink
import Johnson.P1K8R.HeadRowsInScope
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9Asks (rowsFitB rowsFitB_iff built_tl reads_head_eq claimsAt pairsAt
  firstB readsB)

/-- **The built segment at 24 has the head's plan's data.** -/
theorem built_head_tl : BuiltHeadTl := by
  intro Pb pp ly Z G₀ hS hR hZ hG
  obtain ⟨-, l, el, etl, -⟩ := IM.ground_tails hS hR hZ hG
  obtain ⟨X, eX, e⟩ := built_tl hG el
  exact ⟨X, eX, by rw [← e, etl, ProofFile.Law.blankBy_W hG]⟩

/-- **The test's yes at 24, in scope.** -/
theorem rowsFit_head_in_scope : RowsFitHeadInScope := by
  intro Pb pp ly Z G₀ hS hR hZ hG hpub hp
  obtain ⟨p, ep, er⟩ := hp
  obtain ⟨X, eX, etl⟩ := built_head_tl Pb pp ly Z G₀ hS hR hZ hG
  obtain ⟨ps, e2, e3⟩ := reads_head_eq hS hR hpub
  have c1 : claimsAt Z.p.X 24 = some Z.p.X.H.nLin := rfl
  have c2 : pairsAt Z.p.X 24 = some ps := e2
  have e : Z.p.X.H.nLin + (firstB X.tl + readsB X.tl.NM X.tl.mats ps * X.tl.stepF) = p.rows := by
    rw [etl, e3, head_left_is_rows _ _ _ _ hpub, ← Fo.Pub.public_H_rows hpub,
      head_rows_in_scope Pb pp (some ly) Z.p.X hS hR hpub, er]
  exact ⟨X, eX, (rowsFitB_iff Z 24 X).2 ⟨_, ps, p, c1, c2, ep, Nat.le_of_eq e⟩⟩

/-- **The test's yes at 24, under the head.** -/
theorem rowsFit_head_of_head : RowsFitHeadOfHead := by
  intro Z D r Zp Np cF h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact rowsFit_head_in_scope Z _ _ Zp Bs.G₀ h.scope h.reads O.pub O.blank h.pubOne
    (k9Rows_at_head OnBytes.secondHashFunction Z D r Zp Np cF h 24 (by decide))

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.built_head_tl
#print axioms P1K8.rowsFit_head_in_scope
#print axioms P1K8.rowsFit_head_of_head
