-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Pad.lean: in the link prover's algorithm each answer to the link proof's own
OOD samples is additive in the message, and a change of the message can be compensated at the pad's
entry alone.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The answers here are the prover's answers to the link proof's own OOD
samples, taken on the prover's own messages, not to the instance's OOD samples. Such an answer is a
linear function of the message that it answers, and the pad's entry enters it with the seed's
factor, which is a unit. So a change dm of the message changes each answer exactly as adding one
value at the pad's entry does. The file proves this for the answers as the prover's algorithm
computes them: at the front (smAt, Johnson/Prover/Link/FrontWhole.lean) and at a switch (gAns,
Johnson/Prover/Link/SwitchMsg.lean; ansAt, Johnson/Prover/Link/BodyAll.lean).
  smAt_shift   for all sizes S, t, seeds σ, messages m, dm and members a (Defs.lean: the members),
               the answer of member a at m + dm equals its answer at m with padShift S t σ dm a
               added at the pad's entry (Sz.padJ, OnBytes/Slice/LinkAt.lean). padShift is dm's own
               answer divided by the seed's factor.
  ansAt_shift  for a switch from sizes s to s', the answer at folded message μ + dμ and tails
               tl + dtl, with free entries fr, equals the answer at μ and tl with ansShift added
               to fr at the pad's index (padIx s'). ansShift is the answer of dμ and dtl, at free
               entries 0, divided by the seed's factor. Where the two stages do not fit
               (CsFit s s' fails), ansAt is 0 on both sides.
Both hold for all sizes, seeds and messages, with no premise.

How it fits. Johnson/LinkSim/AtText/ShiftDefs.lean uses padShift and ansShift in the shift of the
prover's coins under which the prover's algorithm and the simulator's are compared. Step.lean,
FrontStep.lean, PlacesProof.lean, ShortTail.lean, MustFail.lean and TwoAnswers.lean in this folder
use names of this file too.

Other names (namespace OnBytes.LinkSim.AtText).
  smAt_val       the answer of member a at the front's message mu0 S t m is Sample.val of m a.
  smAt_add       that answer is additive in the members' messages.
  freeOf_add, gAns_add, ansAt_add   a switch's answer is additive in the folded messages, the
                 folded tails and the free entries together.
  padIx s'       the index of a switch's pad in the new mask table: its last entry.
  outAt_csPad, csPad_free   the pad's entry is at padIx, and it holds no entry of the old
                 message.
  gAns_single    with the free entries x at padIx and 0 everywhere else, and a zero message and
                 zero tails, the answer is the seed's factor times x.
The algebra is that of Johnson/LinkSim/PadAdd.lean: val_add, val_add_single, mat_std_pad and
mat_cs_pad.

Limits.
- smAt_shift speaks of the members' messages as functions. Whether the prover's algorithm (linkAll)
  puts one of its coins at the pad's entry is not said here (see PadPlace.lean).
- The seed is the same on both sides.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Front
import Johnson.LinkSim.PadAdd

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link
open Cb.Ood

/-! ## The front's sample -/

theorem smAt_val (S : Sz) (t : ℕ) (σ : (S.fam.om false).Z.D) (m : Bool → S.MJ → GE) (a : Bool) :
    smAt S t σ (mu0 S t m) a = S.memb.Z.val σ (m a) () := by
  unfold smAt
  simp only [mu0_atJ]
  rfl

theorem smAt_add (S : Sz) (t : ℕ) (σ : (S.fam.om false).Z.D) (m m' : Bool → S.MJ → GE) (a : Bool) :
    smAt S t σ (mu0 S t (m + m')) a = smAt S t σ (mu0 S t m) a + smAt S t σ (mu0 S t m') a := by
  rw [smAt_val, smAt_val, smAt_val]
  exact congrFun (val_add S.memb.Z σ (m a) (m' a)) ()

/-- The value added at the pad's entry: dm's answer divided by the seed's factor. -/
def padShift (S : Sz) (t : ℕ) (σ : (S.fam.om false).Z.D) (dm : Bool → S.MJ → GE) (a : Bool) : GE :=
  ((σ.2 : GEˣ) : GE)⁻¹ * smAt S t σ (mu0 S t dm) a

/-- The answer at m + dm equals the answer at m with padShift added at the pad's entry. -/
theorem smAt_shift (S : Sz) (t : ℕ) (σ : (S.fam.om false).Z.D) (m dm : Bool → S.MJ → GE)
    (a : Bool) :
    smAt S t σ (mu0 S t (m + dm)) a =
      smAt S t σ (mu0 S t (m + fun b => Pi.single S.padJ (padShift S t σ dm b))) a := by
  rw [smAt_add, smAt_val S t σ (m + _), smAt_val S t σ m]
  have h := val_add_single S.memb.Z σ (m a) S.padJ (padShift S t σ dm a) ()
  have hm : S.memb.Z.mat σ () S.padJ = ((σ.2 : GEˣ) : GE) := mat_std_pad S.memb σ
  rw [hm] at h
  refine Eq.trans ?_ h.symm
  unfold padShift
  rw [mul_inv_cancel_left₀ (Units.ne_zero _)]

/-! ## A switch's sample -/

section Switch
variable {s s' : Sg} (hf : CsFit s s')

theorem freeOf_add (fr fr' : ℕ → GE) : freeOf hf (fr + fr') = freeOf hf fr + freeOf hf fr' := by
  funext q
  show freeOf hf (fr + fr') q = freeOf hf fr q + freeOf hf fr' q
  unfold freeOf
  split
  · exact (add_zero _).symm
  · rfl

theorem gAns_add (μ ν : s.cMid.J → GE) (tl tl' : s.cMid.Q → GE) (fr fr' : ℕ → GE)
    (ρo : (csSw hf).Zo.D) :
    gAns hf (μ + ν) (tl + tl') (fr + fr') ρo = gAns hf μ tl fr ρo + gAns hf ν tl' fr' ρo := by
  unfold gAns
  have e : (csSw hf).msg (μ + ν, tl + tl') (freeOf hf (fr + fr')) =
      (csSw hf).msg (μ, tl) (freeOf hf fr) + (csSw hf).msg (ν, tl') (freeOf hf fr') := by
    rw [freeOf_add]
    funext n
    rcases n with (j | q) | f <;> rfl
  rw [e]
  exact congrFun (val_add (csSw hf).Zo ρo _ _) ()

/-- The index of the pad in the new mask table. -/
def padIx (s' : Sg) : ℕ := 2 ^ s'.h * s'.Z.l - 1

theorem outAt_csPad : outAt s' (csPad hf) = .inr (padIx s') :=
  congrArg Sum.inr (idxOf_cell _ _ _ _)

/-- The pad's entry is not the image of any entry of the old message. -/
theorem csPad_free : csPad hf ∉ Set.range (csPut hf) := by
  rintro ⟨n, hn⟩
  have h := (outAt_csPut hf n).symm.trans ((congrArg (outAt s') hn).trans (outAt_csPad hf))
  have hm := hf.mask
  unfold padIx at h
  rcases n with (j | j | j) | (q | q | q)
  · exact absurd h Sum.inl_ne_inr
  all_goals
    have h' := Sum.inr.inj h
    first
      | (have := j.isLt; omega)
      | (have := q.isLt; omega)

theorem gAns_single (x : GE) (ρo : (csSw hf).Zo.D) :
    gAns hf 0 0 (Pi.single (padIx s') x) ρo = ((ρo.2 : GEˣ) : GE) * x := by
  classical
  unfold gAns
  have e : (csSw hf).msg ((0 : s.cMid.J → GE), (0 : s.cMid.Q → GE))
      (freeOf hf (Pi.single (padIx s') x)) =
      Pi.single (.inr ⟨csPad hf, csPad_free hf⟩) x := by
    funext n
    rcases n with (j | q) | f
    · rw [Pi.single_apply, if_neg Sum.inl_ne_inr]
      rfl
    · rw [Pi.single_apply, if_neg Sum.inl_ne_inr]
      rfl
    · show freeOf hf (Pi.single (padIx s') x) f = _
      by_cases hq : f = ⟨csPad hf, csPad_free hf⟩
      · subst hq
        rw [Pi.single_apply, if_pos rfl]
        unfold freeOf
        simp only [outAt_csPad hf]
        rw [Pi.single_apply, if_pos rfl]
      · rw [Pi.single_apply, if_neg fun h => hq (Sum.inr.inj h)]
        obtain ⟨i, hi, -, -⟩ := free_at hf f
        unfold freeOf
        simp only [hi]
        rw [Pi.single_apply, if_neg fun h => hq (Subtype.ext (outAt_inj (by
          rw [hi, h, outAt_csPad hf])))]
  rw [e]
  have h := val_add_single (csSw hf).Zo ρo 0 (.inr ⟨csPad hf, csPad_free hf⟩) x ()
  rw [zero_add, val_zero] at h
  rw [h, mat_cs_pad hf ρo _ rfl]
  exact zero_add _

end Switch

/-! ## The answer as the prover's algorithm computes it -/

theorem ansAt_add (s s' : Sg) (μ ν : s.cMid.J → GE) (tl tl' : s.cMid.Q → GE) (fr fr' : ℕ → GE)
    (els : List E) (bits : ℕ) :
    ansAt s s' (μ + ν) (tl + tl') (fr + fr') els bits =
      ansAt s s' μ tl fr els bits + ansAt s s' ν tl' fr' els bits := by
  unfold ansAt
  split_ifs with hf
  · exact gAns_add hf μ ν tl tl' fr fr' _
  · exact (add_zero _).symm

/-- The value added at the pad's index: the answer of dμ and dtl, at free entries 0, divided by
the seed's factor. -/
def ansShift (s s' : Sg) (dμ : s.cMid.J → GE) (dtl : s.cMid.Q → GE) (els : List E)
    (bits : ℕ) : GE :=
  ((unitOf (readE (els.getD bits zeroE)) : GEˣ) : GE)⁻¹ * ansAt s s' dμ dtl 0 els bits

/-- The answer at μ + dμ and tl + dtl equals the answer at μ and tl with ansShift added to the
free entries at padIx. -/
theorem ansAt_shift (s s' : Sg) (μ dμ : s.cMid.J → GE) (tl dtl : s.cMid.Q → GE) (fr : ℕ → GE)
    (els : List E) (bits : ℕ) :
    ansAt s s' (μ + dμ) (tl + dtl) fr els bits =
      ansAt s s' μ tl (fr + Pi.single (padIx s') (ansShift s s' dμ dtl els bits)) els bits := by
  have h1 := ansAt_add s s' μ dμ tl dtl fr 0 els bits
  have h2 := ansAt_add s s' μ 0 tl 0 fr (Pi.single (padIx s') (ansShift s s' dμ dtl els bits)) els
    bits
  rw [add_zero] at h1 h2
  rw [add_zero] at h2
  rw [h1, h2]
  congr 1
  unfold ansShift
  by_cases hf : CsFit s s'
  · have e : ansAt s s' 0 0 (Pi.single (padIx s')
        (((unitOf (readE (els.getD bits zeroE)) : GEˣ) : GE)⁻¹ * ansAt s s' dμ dtl 0 els bits))
        els bits = ((unitOf (readE (els.getD bits zeroE)) : GEˣ) : GE) *
        (((unitOf (readE (els.getD bits zeroE)) : GEˣ) : GE)⁻¹ * ansAt s s' dμ dtl 0 els bits) := by
      conv_lhs => unfold ansAt
      rw [dif_pos hf]
      exact gAns_single hf _ _
    rw [e, mul_inv_cancel_left₀ (Units.ne_zero _)]
  · unfold ansAt
    rw [dif_neg hf, dif_neg hf]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.smAt_shift
#print axioms OnBytes.LinkSim.AtText.gAns_single
#print axioms OnBytes.LinkSim.AtText.ansAt_shift
