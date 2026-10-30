-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Below.lean: AT EACH OF THE OUTPUT HEAD's OWN ROUNDS THE PRICE's COUNT IS AT MOST 2^-128 OF THE ROUND's WRITTEN
VERIFIER MESSAGES: for all sizes: in every written round that has the plan's own entry and a kind that fits. And the like for
the next token's one round, in which nothing is drawn.
It CALLS three theorems by name: fieldBelow and unitBelow (Johnson/Desc/Ok/FieldBelow.lean) and
roundBelow_zero (Johnson/Bridge/RowPriced.lean). Through these imports it stands above Cb/Bridge/CodeListRSProved.lean and the files
under ThirdParty/: files adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15). Its own
content is lists and counts: no statement on codes is used in it. FOR PROOFS ONLY: no module that runs imports this file.
WHAT IT DOES NOT SHOW. NO SOUNDNESS AND NO LEVEL OF SECURITY. ONE ROUND's SHARE; NO SUM OVER ROUNDS. IT SPEAKS OF COUNTS, NOT OF BLOCKS: that
the bad typed values of a round are no more than its count is Law/K06Rounds.lean's clause (d) for the rule's list at every round
but the point's; AT THE POINT (round 0) the count lt q^(lt - 1), of the q^lt points, is a premise of K6's files' laws (the
bridge's BadP). That a written round has the plan's entry and a kind other than seeds and sealed is the caller's. The work w
is a letter, at most 62 bits: where it is not 0, that share of the 128 bits is proof of work (at two stored sets of another build than the one that ships it is
0: Law/K06Condition.lean: workSmall, workFull).
WHAT IT IS.
  k6Priced lt lPd w   for each of the 16 + 2 lPd + 4 lt rounds, in the plan's order: the entry and its count.
  k6Priced_entries    its entries ARE the planner's closed list (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)), which by
                      Law/HeadPrices.lean k6_entries are the kind's declared rounds.
  k6Priced_counts     its counts are lt q^(lt - 1) at the point, and behind it the prices' numerators (Law/HeadPrices.lean: prices).
  K06Below | k06Below **the row**: 1 ≤ lt ≤ 2^60, w + 66 ≤ 128: every pair meets RoundBelow at 2^-128.
  k06Below_at         by the round's number j ≥ 1: every count up to prices' member number j, at the plan's entry number j.
  K07Below | k07Below the round REPLY: the count 0.

-/
import Johnson.Desc.Ok.FieldBelow
import Johnson.Desc.Kinds.Law.HeadPrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Below

open Johnson.Bridge (KindFits roundBelow_zero)
open Johnson.Desc.Ok (fieldBelow unitBelow)
open _root_.Run (PQ.RD)
open OnBytes.Slice (RoundBelow)
open OnBytes.Tie.Pv.Lay (eDraw eBat)
open Prices (prices recAt)
open scoped ENNReal

/-- The number of typed elements of the extension field. -/
def q : ℕ := Cb.Gl.p ^ 3

/-- A masked sumcheck in m variables, with b more bytes in its first message and so many end values: each entry with its
count: 1 · 2 at each variable · 2 at the further variable, whose element is never 0 · 0 where nothing is drawn. -/
def sumPriced (b m ends w : ℕ) : List (Fmt.Entry × ℕ) :=
  (eDraw "PSC epsilon" w (b + 24) 1, 1) :: (List.replicate m (eDraw "PSC round" w 48 1, 2) ++
    [({ name := "PSC Y", work := w, msg := 24 * 2, drawE := 1, drawNZ := 1 }, 2),
     ({ name := "PSC values", msg := 24 * ends }, 0)])

/-- **The head's own rounds: each entry with its count**, in the plan's order. -/
def k6Priced (lt lPd w : ℕ) : List (Fmt.Entry × ℕ) :=
  (eDraw "ZERO" w 0 lt, lt * q ^ (lt - 1)) :: (eBat w (24 * 9) 9, 8) ::
    (sumPriced 0 (lPd + lt) 2 w ++ ((eDraw "LINE" w 0 1, 1) :: (eBat w (24 * 7) 7, 6) ::
      (sumPriced 24 lt 4 w ++ (sumPriced 24 lt 2 w ++ sumPriced 24 (lt + lPd) 2 w))))

/-- Its entries are the planner's. -/
theorem k6Priced_entries (lt lPd w : ℕ) :
    (k6Priced lt lPd w).map (·.1) = OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd) := by
  simp [k6Priced, sumPriced, recAt, OnBytes.Tie.Pv.Head.headOwnList, OnBytes.Tie.Pv.Head.hPoint,
    OnBytes.Tie.Pv.Head.hBatSums, OnBytes.Tie.Pv.Head.hSquares, OnBytes.Tie.Pv.Head.hBatProducts,
    OnBytes.Tie.Pv.Head.hProducts, OnBytes.Tie.Pv.Head.hStream, OnBytes.Tie.Pv.Head.hLogits,
    OnBytes.Tie.Pv.Lay.lLayer, OnBytes.Tie.Pv.Lay.lPsc]

/-- Its counts: the point's; behind it the prices. -/
theorem k6Priced_counts (lt lPd w : ℕ) :
    (k6Priced lt lPd w).map (·.2) = lt * q ^ (lt - 1) :: (prices lt lPd).tail := by
  rw [Prices.prices_eq]
  simp [k6Priced, sumPriced]

/-- A round that draws one element and nothing else: every count up to 2^61. -/
theorem oneBelow (d : PQ.RD) (c : ℕ) (hc : c ≤ 2 ^ 61) (hlog : d.entry.logN ≤ 64)
    (hP : d.entry.poss = 0) (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 0)
    (hT : d.entry.trits = 0) (hW : d.entry.work + 66 ≤ 128) (hk : KindFits false d.kind) :
    RoundBelow c d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := fieldBelow d c 1 hc (Nat.le_refl 1) (by norm_num) hlog hP hE hZ hT hW hk
  simpa using h

/-- A sumcheck's pairs. -/
theorem sumBelow (b m ends w : ℕ) (hw : w + 66 ≤ 128) (p : Fmt.Entry × ℕ)
    (hp : p ∈ sumPriced b m ends w) (d : PQ.RD) (hd : d.entry = p.1) (hk : KindFits false d.kind) :
    RoundBelow p.2 d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  simp only [sumPriced, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | ⟨_, rfl⟩ | rfl | rfl
  · exact oneBelow d 1 (by norm_num) (by rw [hd]; simp [eDraw]) (by rw [hd]; rfl) (by rw [hd]; rfl)
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw) hk
  · exact oneBelow d 2 (by norm_num) (by rw [hd]; simp [eDraw]) (by rw [hd]; rfl) (by rw [hd]; rfl)
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw) hk
  · exact unitBelow d 2 (by norm_num) (by rw [hd]; simp) (by rw [hd]) (by rw [hd]) (by rw [hd])
      (by rw [hd]) (by rw [hd]; exact hw) hk
  · exact roundBelow_zero d _

/-- **The row**, as a closed proposition. -/
def K06Below : Prop :=
  ∀ lt lPd w : ℕ, 1 ≤ lt → lt ≤ 2 ^ 60 → w + 66 ≤ 128 → ∀ p ∈ k6Priced lt lPd w, ∀ d : PQ.RD,
    d.entry = p.1 → KindFits false d.kind → RoundBelow p.2 d ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k06Below : K06Below := by
  intro lt lPd w h1 h2 hw p hp d hd hk
  simp only [k6Priced, List.mem_cons, List.mem_append] at hp
  rcases hp with rfl | rfl | hp | rfl | rfl | hp | hp | hp
  · exact fieldBelow d lt lt (le_trans h2 (by norm_num)) h1 h2 (by rw [hd]; simp [eDraw])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw) hk
  · exact oneBelow d 8 (by norm_num) (by rw [hd]; simp [eBat]) (by rw [hd]; rfl) (by rw [hd]; rfl)
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw) hk
  · exact sumBelow _ _ _ w hw p hp d hd hk
  · exact oneBelow d 1 (by norm_num) (by rw [hd]; simp [eDraw]) (by rw [hd]; rfl) (by rw [hd]; rfl)
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw) hk
  · exact oneBelow d 6 (by norm_num) (by rw [hd]; simp [eBat]) (by rw [hd]; rfl) (by rw [hd]; rfl)
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw) hk
  · exact sumBelow _ _ _ w hw p hp d hd hk
  · exact sumBelow _ _ _ w hw p hp d hd hk
  · exact sumBelow _ _ _ w hw p hp d hd hk

/-- **By the round's number**: behind the point, every count that is at most the price of round number j meets the clause in every
written round that has the plan's entry number j. So a rule whose list at a front of j + 1 rounds is no longer than that price
(Law/K06Rounds.lean, clause (d)) is met here by its own length. -/
theorem k06Below_at {lt lPd w : ℕ} (h1 : 1 ≤ lt) (h2 : lt ≤ 2 ^ 60) (hw : w + 66 ≤ 128) (j : ℕ) (hj : 1 ≤ j) (c : ℕ)
    (hc : c ≤ (prices lt lPd).getD j 0) (d : PQ.RD)
    (hd : (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))[j]? = some d.entry)
    (hk : KindFits false d.kind) : RoundBelow c d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [← k6Priced_entries, List.getElem?_map] at hd
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 hd
  have hcnt : ((k6Priced lt lPd w).map (·.2))[j]? = some p.2 := by
    rw [List.getElem?_map, hp]
    rfl
  rw [k6Priced_counts] at hcnt
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [List.getElem?_cons_succ, List.getElem?_tail] at hcnt
  have hv : (prices lt lPd).getD (i + 1) 0 = p.2 := by
    rw [List.getD_eq_getElem?_getD, hcnt]
    rfl
  exact RoundBelow.mono (hv ▸ hc)
    (k06Below lt lPd w h1 h2 hw p (List.mem_of_getElem? hp) d hpe.symm hk)

/-- The next token's one round: nothing is drawn: the count 0, in every written round. -/
def K07Below : Prop := ∀ d : PQ.RD, RoundBelow 0 d ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k07Below : K07Below := fun d => roundBelow_zero d _

end VerifiableInference.Desc.Kinds.Head.Law.Below

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k06Below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k06Below_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k07Below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k6Priced_entries
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k6Priced_counts
