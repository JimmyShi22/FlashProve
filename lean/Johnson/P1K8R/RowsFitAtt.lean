-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsFitAtt.lean: the proofs of the three statements of
Johnson/P1K8R/RowsFitAttStatement.lean, to the letter, and one helper. Lemmas; none of the library's
goals.

How. `att_left_at_most`: `K9Asks.rows_join` (Johnson/Desc/First/Link/Law/K9RowsParts.lean, another
group of authors', as it lies) at the stored plan's own data: its four premises: the number of
matrices is the list's length (`Meaning.plan_nm`, Johnson/Goal/Meaning/HidPlanNM.lean); the shapes'
rows of symbols (`H2K5.Door.public_A_mS`, Johnson/Desc/First/Att/Door/Law/K5ShpOfPlan.lean); the
reads (`K9Asks.reads_att`, K9RowsParts.lean); the plan's rows (`Fo.Pub.public_A_rows`,
OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean). The first and the third stand at what `Attention.plan`
returns: the stored plan is that but for one field that neither reads (`planIs_public`,
Johnson/Desc/First/Att/GuardPublic.lean). `rowsFit_att_in_scope`: the built segment and its data by
`IM.ground_tails`, `built_tl`, `ProofFile.Law.blankBy_W`, as `built_head_tl` goes
(Johnson/P1K8R/RowsFitHead.lean); `rowsFitB_iff` from right to left. `rowsFit_att_of_head`: K9's
numbers by `k9Rows_at_head` (Johnson/P1K8R/K9RowsByLink.lean) and `rowsAtLink_odd`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.RowsFitAttStatement
import Johnson.P1K8R.K9RowsByLink
import Johnson.Desc.First.Link.Law.K9RowsParts
import Johnson.Desc.First.Att.Door.Law.K5ShpOfPlan
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Goal.Meaning.HidPlanNM
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9Asks (rowsFitB rowsFitB_iff built_tl claimsAt pairsAt firstB readsB
  attPairs)
open VerifiableInference.Desc.First.Att.P (planIs_public)

/-- **The test's left side at a stored attention plan is at most the plan's rows.** -/
theorem att_left_at_most : AttLeftAtMost := by
  intro pol KL lay X hpub g a ha
  obtain ⟨A0, pf, h0, e⟩ := planIs_public hpub g a ha
  have k1 := _root_.Meaning.plan_nm h0
  have k2 := VerifiableInference.Desc.K9Asks.reads_att h0
  have hN : a.seam.tl.NM = a.seam.tl.mats.size := by
    rw [e]
    exact k1
  have hr : readsB a.seam.tl.NM a.seam.tl.mats (attPairs a.S) ≤
      Attention.tableReads a.S (Attention.Counts.of a.S) := by
    rw [e]
    exact k2
  exact VerifiableInference.Desc.K9Asks.rows_join a.seam.tl (attPairs a.S) hN
    (H2K5.Door.public_A_mS hpub g a ha) hr (Fo.Pub.public_A_rows hpub g a ha)

/-- The written number at an odd segment. -/
theorem rowsAtLink_odd (g : Nat) : rowsAtLink (2 * g + 1) = 14166783 := by
  unfold rowsAtLink
  rw [if_neg (by omega), if_pos (by omega)]

/-- **The test's yes at 2 g + 1, in scope, under the named premise.** -/
theorem rowsFit_att_in_scope : RowsFitAttInScope := by
  intro Pb pp ly Z G₀ hS hR hZ hG hpub g hg hp hrow
  obtain ⟨p, ep, er⟩ := hp
  obtain ⟨-, a, -, l', -, hA, -, -, -, -, -, -, el, etl, -⟩ :=
    (IM.ground_tails hS hR hZ hG).1 g hg
  rw [ProofFile.Law.blankBy_W hG] at hA
  obtain ⟨X, eX, e⟩ := built_tl hG el
  have c1 : claimsAt Z.p.X (2 * g + 1) = some a.nLin := by
    unfold claimsAt
    rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, hA]
    rfl
  have c2 : pairsAt Z.p.X (2 * g + 1) = some (attPairs a.S) := by
    unfold VerifiableInference.Desc.K9Asks.pairsAt
    rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, hA]
    rfl
  have q := att_left_at_most _ _ _ _ hpub g a hA
  refine ⟨X, eX, (rowsFitB_iff Z (2 * g + 1) X).2 ⟨_, _, p, c1, c2, ep, ?_⟩⟩
  rw [← e, etl, er]
  exact Nat.le_trans q (hrow a hA)

/-- **The test's yes at every 2 g + 1, under the head and the named premise.** -/
theorem rowsFit_att_of_head : RowsFitAttOfHead := by
  intro Z D r Zp Np cF h hrow g hg
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨p, ep, er⟩ := k9Rows_at_head OnBytes.secondHashFunction Z D r Zp Np cF h (2 * g + 1) (by omega)
  exact rowsFit_att_in_scope Z _ _ Zp Bs.G₀ h.scope h.reads O.pub O.blank h.pubOne g hg
    ⟨p, ep, er.trans (rowsAtLink_odd g)⟩ (hrow g hg)

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.att_left_at_most
#print axioms P1K8.rowsAtLink_odd
#print axioms P1K8.rowsFit_att_in_scope
#print axioms P1K8.rowsFit_att_of_head
