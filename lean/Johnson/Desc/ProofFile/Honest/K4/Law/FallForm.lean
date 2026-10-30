-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FallForm.lean: CONDITIONAL. `k4_fallDebt_counted`
(Law/FallAtOwn.lean) IN THE FORM IN WHICH A BOUND ON THE FIRST CHAIN's FALLS ASKS IT OF THE FIRST
FALL OF THE LAYERS' OWN ROUNDS (kind K4).

What is here. One statement with its proof: a call of `k4_fallDebt_counted`. Its end is a sentence
over every cut pre₁ = A ++ b :: b' :: B of the first chain's members but the last: at every member b
at which `k4Fall` of a group is counted, at data that fit b's declared rounds: `FallDebt`
(Honest/Law/CoverJoin.lean) at the kit `Run.ckP .two`, at the members behind b, at PW b and at qF b
of that fall. fs (the list of falls), r0, PW and qF are letters. WHY IT IS HERE: so that Lean checks
that the law has that form. The two premises of the form on b's place and on b's rounds are not
spent.

Not shown here. hq: THE BOUND (`k4ZeroBound`, Law/FallCount.lean) IS AT MOST qF b OF THE FALL, AT
EVERY b, GROUP AND PLAN: A HYPOTHESIS ON THE LETTER qF: so the sentence on measures is exchanged for
an inequality between two terms; it is not had for nothing. hS · hR · O · hnd · cut: hypotheses, as
in Law/FallAtOwn.lean, WHOSE LIMITS, AND THOSE OF Law/FallCount.lean AND Law/Falls.lean, HOLD HERE
TOO. THE FULL SIZE ALONE. NO NUMBER IS EVALUATED. No example of the hypotheses together has been
through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FallAtOwn
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open scoped ENNReal
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- CONDITIONAL: on all six hypotheses. **THE FIRST FALL's SENTENCE, AT EVERY CUT OF THE CHAIN,
WHERE THE FALL IS COUNTED.** -/
theorem k4_fallDebt_form (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hnd : (c.blocksInOrder.map (·.place)).Nodup) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : c.blocksInOrder = pre₁ ++ [e₁]) (fs : List (Fall S)) (r0 : ℕ → ℕ)
    (PW : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop) (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hq : ∀ b gk hp, k4ZeroBound ≤
      qF b (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ gk hp, gk < 12 → Bs.G₀.W.G[gk]? = some hp →
      ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩ ∈
        repsAt c.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two)
        (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩) 0 b
        (b' :: B ++ [e₁]) dsb [] (PW b)
        (qF b (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩)) := by
  intro A b b' B e _ _ gk hp hgk hh hm dsb hfit
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  exact k4_fallDebt_counted hS hR O hnd hall hgk hh (r0 gk) (2 * gk) hm dsb hfit 0
    (b' :: B ++ [e₁]) _ (hq b gk hp) (PW b)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_fallDebt_form
