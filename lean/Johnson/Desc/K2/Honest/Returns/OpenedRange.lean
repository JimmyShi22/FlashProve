-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/OpenedRange.lean: THE MESSAGES THAT A SWITCH OPENS ARE A STRETCH OF
NUMBERS WITHOUT A GAP (at the first segment: two stretches, with what rides at the start between
them), where the count of oracle messages at a later cut is the count in front of the segment and
what its three sendings add. In the goals' scope, from the returns of one fold. THE EQUATION OF
COUNTS IS A PREMISE HERE (Returns/UnopenedLinks.lean, UnopenedFirst.lean and UnopenedFinish.lean
show who pays it). A tool for the five equations a tree against the plan's list of read trees
(Returns/FiveTest.lean). Statements with their proofs: calls and sums.

  `opened_range` segments 1 to 23: o is named by the carried rows at 14 (l + 2) + 2 just when n₀ ≤ o
                    < n₀ + what the three sendings add; n₀: the count at 14 (l + 1) + 2
  `opened_range_first` segment 0, the carried rows at 16: just when o is at most the fresh mask's
                    number, or from the first sending's length on below the count
  `opened_range_last` the output head's segment, the carried rows at 353: as at the segments 1 to
                    23, from the count at 339

By, this folder's: `members_behind_laid`, `fresh_behind_laid`, `closing_behind_laid`
(Returns/SeatsWalk.lean) · `members_behind_cleared`, `fresh_behind_cleared`, `counts_head`
(Returns/HeadSegment.lean) · `counts_link` (Returns/SendCounts.lean), `counts_zero`, `mem_ids0`
(Returns/OwnFirst.lean), `mem_ids` (Returns/OwnReached.lean) · `counts_rise` (Returns/BookSame.lean)
· `first_places`, `first_sent` (Returns/FirstSending.lean). The library's: `tail_rows`
(Johnson/IMR/GroupTail.lean), `flags_zero_named` (Johnson/IMR/FlagsZeroNamed.lean),
`mask_zero_named` (Johnson/IMR/MaskZeroNamed.lean), `closeFrame_reads`
(Johnson/Desc/First/Link/Law/CloseReads.lean) · `open_recAll` (Johnson/IMR/ListsEnds.lean),
`rows_of_pub`, `laid_at` (Johnson/IMR/FrontPin.lean), `fin_link`, `front_len`
(Johnson/IMR/FinPin.lean) · `atMoment_of` (Johnson/IMR/FlagsAt.lean), `Open.first`
(Johnson/IMR/SeatOpen.lean) · `fold_cut` (Johnson/IMR/GroupRest.lean). EACH PROOF's FIRST LINES ARE
THOSE OF `mates_opened` (Returns/OwnReached.lean), `mates_opened0` (Returns/OwnFirst.lean),
`mates_opened24` (Returns/OwnFinish.lean): typed again.

Limits. THE EQUATION OF COUNTS IS PAID BY NOBODY HERE. That a fold returns is shown of no proof
here. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.UnopenedLinks
import Johnson.Desc.K2.Honest.Returns.OwnFirst
import Johnson.Desc.K2.Honest.Returns.OwnFinish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (closeFrame_reads)
open Meaning.K2 (flags_zero_named mask_zero_named tail_rows atMoment_of open_recAll rows_of_pub
  laid_at fin_link front_len fold_cut frontOf msgsAt)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Segments 1 to 23: the opened messages are a stretch without a gap.** -/
theorem opened_range (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat}
    (h24 : l + 1 < 24) {p : ProofFile.InstPub} {R R₂ RE : List Fmt.RoundView}
    {C C₂ CE : List VerifiableInference.Desc.OpenedColumn} {t₂ s : S} {d n₀ : Nat} (hd : 8 ≤ d)
    (hk : 14 * (l + 1) + 8 + d ≤ (frontOf c).length)
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1 + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 8 + d)) (ProofFile.startS Z p) R C = .ok (s, RE, CE))
    (h0 : ∀ t R' C', foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C =
      .ok (t, R', C') → t.st.oracles.size = n₀)
    (hc : s.st.oracles.size = n₀ +
      (1 + (First.K2.targetAt Z.first.shape (l + 1)).kept.size +
        (msgsAt Z.first.shape (l + 1) 0 + 1)) +
      msgsAt Z.first.shape (l + 1) 1 + msgsAt Z.first.shape (l + 1) 2) (o : Nat) :
    o ∈ (singleRowsOracles t₂.check.frame.rows).toList ↔ n₀ ≤ o ∧ o < s.st.oracles.size := by
  have h1 : 1 ≤ l + 1 := by omega
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, hmem⟩ :=
    members_behind_laid hS hR O h1 h24 f₂
  have hfresh := fresh_behind_laid hS hR O h1 h24 g₀ f₂
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 14 * (l + 1) + 3) 13
    (by rw [show 14 * (l + 1) + 3 + 13 = 14 * (l + 1 + 1) + 2 by omega]; exact f₂)
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 14 * (l + 1) + 6) 10
    (by rw [show 14 * (l + 1) + 6 + 10 = 14 * (l + 1 + 1) + 2 by omega]; exact f₂)
  obtain ⟨t6, R6, C6, g6⟩ := fold_cut (k := 14 * (l + 1) + 8) 8
    (by rw [show 14 * (l + 1) + 8 + 8 = 14 * (l + 1 + 1) + 2 by omega]; exact f₂)
  obtain ⟨c1, c4, c6⟩ := counts_link hS hR O h1 h24 g₀ g₁ g₃ g₄ g₅ g6
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega) (by omega) f₂).walk
      (by rw [(laid_at hS hR O (by omega : l + 1 + 1 < 25) f₂).2]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, hfresh, mem_ids]
  have e0 := h0 t₀ R₀ C₀ g₀
  have u13 := counts_rise O (by omega : 14 * (l + 1) + 3 ≤ 14 * (l + 1) + 5) (by omega) g₁ g₃
  have u45 := counts_rise O (by omega : 14 * (l + 1) + 6 ≤ 14 * (l + 1) + 7) (by omega) g₄ g₅
  have u6s := counts_rise O (by omega : 14 * (l + 1) + 8 ≤ 14 * (l + 1) + 8 + d) hk g6 f
  omega

/-- **Segment 0: two stretches.** -/
theorem opened_range_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (16)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hc : t₂.st.oracles.size =
      (msgsAt Z.first.shape 0 0 + 1 + Z.first.shape.atStart.length) + msgsAt Z.first.shape 0 1 +
      msgsAt Z.first.shape 0 2) (o : Nat) :
    o ∈ (singleRowsOracles t₂.check.frame.rows).toList ↔
      o < msgsAt Z.first.shape 0 0 + 1 ∨
        (msgsAt Z.first.shape 0 0 + 1 + Z.first.shape.atStart.length ≤ o ∧
          o < t₂.st.oracles.size) := by
  have h24 : 0 < 24 := by omega
  have hk : 16 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 9) 7 f₂
  obtain ⟨L, G, hL, -, -, hG, hmem, -⟩ := tail_rows hS hR O h24 fu f₂
  obtain ⟨t₃, t₅, R₃, R₅, C₃, C₅, L', G', g₃, g₅, hL', -, hG', em, -, eo, -⟩ :=
    flags_zero_named hS hR O (n := 1) (by omega) fu
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain ⟨w, Rw, Cw, Lw, Q, rs, x, fw, hLw, -, hx, hf, -⟩ := closing_behind_laid hS hR O h24 f₂
  obtain ⟨_, mk, -, -, hm, hfr⟩ := closeFrame_reads hx
  obtain ⟨Lm, hLm, -, hmask⟩ := mask_zero_named hS hR O (n := 9) (by omega) fw
  obtain rfl : Lw = Lm := Option.some.inj (hLw.symm.trans hLm)
  have hfresh : t₂.check.frame.rows.fresh = msgsAt Z.first.shape 0 0 := by
    rw [hf, hfr]
    exact Option.some.inj (hm.symm.trans hmask)
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega : 2 ≤ 16) hk f₂).walk
      (by rw [(laid_at hS hR O (by omega : 1 < 25) f₂).2]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, em, eo, hfresh, mem_ids0]
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 3) 13 f₂
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 6) 10 f₂
  obtain ⟨t6, R6, C6, g6⟩ := fold_cut (k := 8) 8 f₂
  obtain ⟨c4, c6⟩ := counts_zero hS hR O g₁ g₃ g₄ g₅ g6
  have c1 := (first_places hS hR O (Nat.le_refl 3) (by omega) g₁ g₁).1
  have e0 : msgsAt Z.first.shape 0 0 = ((K1.frame₀ Bs.G₀.first).atMoment 0).length := by
    unfold msgsAt
    rw [O.first, atMoment_of (f := K1.frame₀ Z.first) rfl rfl 0]
    rfl
  have hs : (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size =
      msgsAt Z.first.shape 0 0 + 1 + Z.first.shape.atStart.length := by
    rw [first_sent, e0, O.first]
    simp
    omega
  have u13 := counts_rise O (by omega : 3 ≤ 5) (by omega) g₁ g₃
  have u45 := counts_rise O (by omega : 6 ≤ 7) (by omega) g₄ g₅
  have u6s := counts_rise O (by omega : 8 ≤ 16) hk g6 f₂
  omega

/-- **The output head's segment.** -/
theorem opened_range_last (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    {n₀ : Nat}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (h0 : ∀ t R' C', foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      t.st.oracles.size = n₀)
    (hc : t₂.st.oracles.size = n₀ +
      (1 + (First.K2.targetAt Z.first.shape 24).kept.size + (msgsAt Z.first.shape 24 0 + 1)) +
      msgsAt Z.first.shape 24 1 + msgsAt Z.first.shape 24 2) (o : Nat) :
    o ∈ (singleRowsOracles t₂.check.frame.rows).toList ↔ n₀ ≤ o ∧ o < t₂.st.oracles.size := by
  have hk : 353 ≤ (frontOf c).length := le_of_eq (front_len hS hR O).symm
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, hmem⟩ :=
    members_behind_cleared hS hR O f₂
  have hfresh := fresh_behind_cleared hS hR O g₀ f₂
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 340) 13 f₂
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 343) 10 f₂
  obtain ⟨t6, R6, C6, g6⟩ := fold_cut (k := 345) 8 f₂
  obtain ⟨c1, c4, c6⟩ := counts_head hS hR O g₀ g₁ g₃ g₄ g₅ g6
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega) hk f₂).walk
      (by rw [fin_link hS hR O f₂]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, hfresh, mem_ids]
  have e0 := h0 t₀ R₀ C₀ g₀
  have u13 := counts_rise O (by omega : 340 ≤ 342) (by omega) g₁ g₃
  have u45 := counts_rise O (by omega : 343 ≤ 344) (by omega) g₄ g₅
  have u6s := counts_rise O (by omega : 345 ≤ 353) hk g6 f₂
  omega

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.opened_range
#print axioms VerifiableInference.Desc.K2.Honest.Returns.opened_range_first
#print axioms VerifiableInference.Desc.K2.Honest.Returns.opened_range_last
