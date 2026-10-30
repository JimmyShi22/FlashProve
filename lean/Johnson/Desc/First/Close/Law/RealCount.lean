-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealCount.lean: the one premise on counts of K10's law at the real
written rounds, in the form in which a kind's count comes under the cap.

`real_fits_cap` (Law/RealRounds.lean) asks that "typed count times the sampler's number" is, round
by round, a share of at most 2⁻¹ ^ 128 of the written challenges. Here that follows from the form of
`Maps.HeldEx` (Johnson/Flat/ReadingEx.lean), said of one round:
  `HeldAt εs d e`: the typed count e is a share of at most c of the round's typed values, and c,
  with the sampler's bias BY WHAT THE ROUND DRAWS and the gain from the test of work, is at most εs.
  `HeldAll εs d k ε`: the like at each of k typed counts.
  `real_below`, `real_fits_held`: from `HeldAt` at "BAT" and at "FOLD epsilon" and `HeldAll` at the
  k "FOLD round"s, at εs := 2⁻¹ ^ 128: the cap bears the typed counts (`CarryS.Fits`). By
  `below_round_div_ex` (OnBytes/Slice/RatesEx.lean).
Limits. Numbers: that the proved block's own counts are so held at the release's numbers is the row
on K10's rounds: not shown here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Close.Law.RealRounds
import OnBytes.Slice.RatesEx

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Prob Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt

/-- One round's typed count is held. -/
def HeldAt (εs : ℝ≥0∞) (d : RDT) (e : ℕ) : Prop :=
  ∃ c : ℝ≥0∞, (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
    kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) ≤ εs

/-- Each of k typed counts is held. -/
def HeldAll (εs : ℝ≥0∞) (d : RDT) {r' : Round} : ∀ k : ℕ, Err (List.replicate k r') → Prop
  | 0, _ => True
  | k + 1, (e, ε) => HeldAt εs d e ∧ HeldAll εs d k ε

/-- Then the written count is a share of at most εs. -/
theorem HeldAt.below {εs : ℝ≥0∞} {d : RDT} {e : ℕ} (h : HeldAt εs d e)
    (hlog : d.entry.logN ≤ 64) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wT d).Chal : ℝ≥0∞) := by
  obtain ⟨c, h1, h2⟩ := h
  exact (below_round_div_ex (toRD d) hlog e c h1).trans (mul_le_mul' h2 le_rfl)

theorem HeldAll.below {εs : ℝ≥0∞} {d : RDT} {r' : Round} (hlog : d.entry.logN ≤ 64) :
    ∀ (k : ℕ) (ε : Err (List.replicate k r')), HeldAll εs d k ε →
      Err.Below (s := List.replicate k (wT d)) (timesW (bsRound .two d.entry d.kind).w k ε) εs
  | 0, _, _ => trivial
  | k + 1, (_, ε), h => ⟨h.1.below hlog, HeldAll.below hlog k ε h.2⟩

variable {c : BatFoldCaller GE} {dB dE dR : RDT} {rdZ : List E → Option c.s.Z.D}
  {rdCh : List E → Option (Yc c).Ch}

/-- The written counts of the stretch are shares of at most εs. -/
theorem real_below {εs : ℝ≥0∞} (H : RealReads c dB dE dR rdZ rdCh) (eB eE : ℕ)
    (εK : Err (List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n)))
    (hB : HeldAt εs dB eB) (hE : HeldAt εs dE eE) (hR : HeldAll εs dR (Yc c).k εK) :
    Err.Below (s := wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))
      (eB * (bsRound .two dB.entry dB.kind).w, eE * (bsRound .two dE.entry dE.kind).w,
        timesW (bsRound .two dR.entry dR.kind).w (Yc c).k εK) εs :=
  ⟨hB.below H.logB, hE.below H.logE, HeldAll.below H.logR _ εK hR⟩

/-- **Held round by round at 2⁻¹ ^ 128, the typed counts are borne by the cap.** -/
theorem real_fits_held (H : RealReads c dB dE dR rdZ rdCh) (eB eE : ℕ)
    (εK : Err (List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n)))
    (hB : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dB eB) (hE : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dE eE)
    (hR : HeldAll ((2 : ℝ≥0∞)⁻¹ ^ 128) dR (Yc c).k εK) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits (eB, eE, εK)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) :=
  real_fits_cap H eB eE εK (real_below H eB eE εK hB hE hR)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.real_below
#print axioms VerifiableInference.Desc.First.Close.real_fits_held
