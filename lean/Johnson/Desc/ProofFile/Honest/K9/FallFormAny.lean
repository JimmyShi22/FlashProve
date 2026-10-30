-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFormAny.lean: K9's FALL ON THE FREE SLOTS, AT ALL 25 SEGMENTS, IN THE FORM OF THE
FRAME's PREMISE. The bound on falls of the smallness test (`falls_five_by_owner` and its forms,
Johnson/P1K8R/FallsAtLists.lean and FallsAtMarks.lean, which do not lie beneath this file)
asks of K9 the premise hF9: a `FallDebt` for `quietFall` wherever it is counted, at the letter qF.
HERE THAT PREMISE's TEXT IS THE END, AND IT IS EXCHANGED, NOT PAID: for hPW (the gate's condition gives, at the state in
front of each segment's batching, "good without a yes and without a length", `goodW`, Honest/K9/GateArms.lean, and
"reached by the wrapped blocks") and hq (our bound is at most qF there). `goodW` IS SHOWN AT NO STATE OF A RUN.
Statements and proofs; no definition; no goal is stated.
  `k9_fallDebt_form_at`   under the head · cut : the first chain's list is pre₁ ++ [e₁] · I : which segments: a letter ·
      hPW, hq at the l < 25 of which I holds. The end: hF9's text with "I l →" behind "l < 25 →". HOW: the proof of
      `k9_fallDebt_form_att` (Honest/K9/FallFormAtt.lean) with the segment a letter: K9's seat by `seated_at_head` · the
      fall's place by `quietPlace_is` (Honest/K9/FallDebtK9.lean) · `counted_at_own`, `batch_rounds_are`,
      `one_of_fits`, `drop_split`, `fallDebt_mono` · our `k9_fallDebt_list_blocks` (Honest/K9/FallTies.lean), which is
      general in l
  **`k9_fallDebt_form_goodW`**   the same without I: THE END IS hF9's TEXT, with fs for the list of falls and PW b for
      the gate's condition
WHERE IT WOULD BE TRUE FOR NOTHING. Where PW b holds of no state; where the fall is counted at no member. `goodW` itself
holds for nothing at a state from which draw and gatherer return at no challenge. Whoever calls it lays qF at or above
our bound, and the right side of the bound on falls grows with it; hq is not that theorem's hqF: our bound carries
`kapSl 128 ^ 3`, the fall's stated share does not. NO NUMBER IS EVALUATED; nothing says that any sum is below 1. The
letter notGood in the fall's stated share has no payer.
WHAT IS NOT CLAIMED. hPW at any gate's condition. What gives `goodW`: at the twelve attention segments three sentences
on what was heard (Honest/K9/GoodAttEight.lean; FallFormAtt.lean); at the twelve feed-forward segments one sentence
(Honest/K9/FallFormLay.lean); at the head's segment, at the state that a walk hands, the silence of the listed marks and
one sentence on that state (hK: `goodW_head_handed_of_k6`, Honest/K9/GoodHeadHanded.lean). `k9_fallDebt_form_at` is
called by Honest/K9/FallFormLay.lean, FallFormHeadWith.lean and the second theorem; that one by no line. At the full
size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 491 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallTies
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile
import Johnson.P1K8R.CountedAtOwn
import Johnson.P1K8R.LastAtAsks
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt KindFits repsAt fallSeat)
open Iop
open scoped ENNReal

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The frame's premise on K9's fall, at the segments of which I holds, exchanged** for "good without a yes and
without a length" and "reached by the wrapped blocks" at the state in front of the batching. -/
theorem k9_fallDebt_form_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (PW : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞) (I : ℕ → Prop)
    (hPW : ∀ l, l < 25 → I l → ∀ b, cF.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b →
      ∀ Lk p w, SeatedFree cF Zp l (if l = 24 then 9 else 7) Lk p w → ∀ fr s', PW b fr s' →
      goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled ∧
        ∃ z, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * l + (if l = 24 then 11 else 9)) (z, s'))
    (hq : ∀ l, l < 25 → I l → ∀ b p u, IM.k9At Zp l = some p → Desc.K9.testsWhere Zp.p.X l 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ l p u, l < 25 → I l → IM.k9At Zp l = some p → Desc.K9.testsWhere Zp.p.X l 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood l) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) 0 b
        (b' :: B ++ [e₁]) dsb [] (PW b) (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))) := by
  intro A b b' B e _ hn l p u hl hI hp hu hmem dsb hk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, hpl, hcut⟩ := ProofFile.Honest.file_head h.toAtMg
  have hall : cF.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  -- the seat
  obtain ⟨Lk, p', w, Sd⟩ := seated_at_head h l hl
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans Sd.numbers)
  have hw : w = u := Option.some.inj (Sd.tested.symm.trans hu)
  subst hw
  -- where the fall is counted, b is the batching
  have hplace : (quietFall p w.2.2.filled (w.2.1 - 1) (notGood l)).place =
      ProofFile.Honest.K8.quietPlace l (if l = 24 then 1 else 0) := quietPlace_is h.scope h.reads O hl Sd
  have hlen : A.length = 14 * l + (if l = 24 then 11 else 9) :=
    P1K8.counted_at_own h.scope h.reads O hcut (ProofFile.Honest.places_nodup hpl).1 hall hn hmem hl (Or.inr hplace)
  have hb : cF.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b := by
    rw [← hlen, hall]
    simp
  have hbat : b = Lk.batch (claimsInBy Lk.each Lk.hear Lk.order) :=
    Option.some.inj (hb.symm.trans (batching_at Sd))
  -- the data of the one round
  have hr : b.rounds = [{ entry := Desc.K9.entry p }] := P1K8.batch_rounds_are h.scope h.reads O hl hb hp
  rw [hr] at hk
  obtain ⟨d, rfl, he, h5, h6⟩ := P1K8.one_of_fits hk
  -- the list behind
  have htail : cF.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1) = b' :: B ++ [e₁] := by
    rw [← hlen]
    exact P1K8.drop_split (by rw [cut, e])
  have K := k9_fallDebt_list_blocks h.scope h.reads O hl Sd d he h5 h6 (notGood l) 0 (PW b) (ProofFile.startS Zp)
    (fun fr s' q => by
      obtain ⟨hg, z, hrr⟩ := hPW l hl hI b hb Lk p w Sd fr s' q
      exact ⟨hg, z, Johnson.Desc.First.Walk.Tied.reach_raw hrr⟩)
  rw [htail, ← hbat] at K
  exact P1K8.fallDebt_mono K (fun _ _ hh => hh) (hq l hl hI b p w hp hu)

/-- **AT ALL 25 SEGMENTS**: the end is the frame's premise's text, with fs for the list of falls and PW b for the gate's
condition. -/
theorem k9_fallDebt_form_goodW (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (PW : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hPW : ∀ l, l < 25 → ∀ b, cF.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b →
      ∀ Lk p w, SeatedFree cF Zp l (if l = 24 then 9 else 7) Lk p w → ∀ fr s', PW b fr s' →
      goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled ∧
        ∃ z, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * l + (if l = 24 then 11 else 9)) (z, s'))
    (hq : ∀ l, l < 25 → ∀ b p u, IM.k9At Zp l = some p → Desc.K9.testsWhere Zp.p.X l 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ l p u, l < 25 → IM.k9At Zp l = some p → Desc.K9.testsWhere Zp.p.X l 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood l) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) 0 b
        (b' :: B ++ [e₁]) dsb [] (PW b) (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))) :=
  fun A b b' B e hs hn l p u hl hp hu hm dsb hk =>
    k9_fallDebt_form_at h fs notGood cut PW qF (fun _ => True) (fun l hl _ => hPW l hl) (fun l hl _ => hq l hl)
      A b b' B e hs hn l p u hl trivial hp hu hm dsb hk

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_fallDebt_form_at
#print axioms ProofFile.Honest.K9.k9_fallDebt_form_goodW
