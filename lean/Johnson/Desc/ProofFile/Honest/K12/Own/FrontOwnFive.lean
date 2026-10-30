-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/FrontOwnFive.lean

`FrontAsksO` FROM ONE BOOL ON THE SHAPE AND THE THREE TESTS THAT READ THE ROWS: the twin of `frontFiveB`,
`frontAsks_of_five`, `frontAsks_all` (FrontAtShape.lean in the folder above).

  `frontOwnFiveB`   the codes; doorB; no mask has come; nothing passes; plain; pub
  `frontAsksO_of_five`, `frontAsksO_all`   the laws
  `pass_of_five`    what the Bool gives of the pass, for DataThreeOwn.lean

Limits. The plain data are given by the state. `p.early` is a premise. Evaluated at no plan here. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.FrontPubOwn
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.Sh (ThinSh thinSh TestSh testSh thinOf thinOf_eq claimsB)

variable {W X : Type}

/-- **The clauses of `FrontAsksO` that read the shape, as one Bool.** -/
def frontOwnFiveB (p : P12) (K : Codes) (N : TestSh) : Bool :=
  decide (N.core.st.codes = K) &&
  Sh.doorB p (stA p) (stN p) (((laidOf p).take 1).map (·.1)) (lettersOf p (stA p) (stN p)).i
    ((lettersOf p (stA p) (stN p)).n.code, (lettersOf p (stA p) (stN p)).n.maskCode) N &&
  N.mask.isNone &&
  (match N.pass with
    | .nothing => true
    | _ => false) &&
  frontPlainB₀ p (thinOf N) && frontPubOwnB p (thinOf N)

/-- What the Bool gives of the pass. -/
theorem pass_of_five (p : P12) (K : Codes) (t : T12) (h : frontOwnFiveB p K (testSh t) = true) :
    t.pass = .nothing := by
  unfold frontOwnFiveB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, h4⟩, -⟩, -⟩ := h
  have h4' : (match ProofFile.Honest.Sh.passSh t.pass with
    | .nothing => true
    | _ => false) = true := h4
  cases hq : t.pass with
  | nothing => rfl
  | claim _ _ => rw [hq] at h4'; cases h4'
  | single _ _ => rw [hq] at h4'; cases h4'
  | switched _ _ _ => rw [hq] at h4'; cases h4'

/-- **`FrontAsksO` from the Bool on the shape and the three tests.** -/
theorem frontAsksO_of_five (J : TestJob W X) (w : W) (fr : Front X) (K : Codes)
    (he : J.p.early = true) (h : frontOwnFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (ht : stTidyB (J.rec₀ w fr).st = true) (hpl : stPlainB (J.rec₀ w fr).st = true)
    (hc : claimsB (J.rec₀ w fr) = true) : ∃ Dp : Plain, FrontAsksO J w fr K Dp := by
  have hp := pass_of_five _ _ _ h
  unfold frontOwnFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩ := h
  rw [thinOf_eq] at h5 h6
  have hm : (J.rec₀ w fr).mask = none := Option.isNone_iff_eq_none.1 h3
  obtain ⟨Dp, hD⟩ := frontPlain₀_of_B J.p _ hp he h5
  exact ⟨Dp, ⟨h1, h2, hm, ht, hpl, hc, hD,
    fun G hG => frontPubOwn_of_B J.p _ hp he h6 G hG⟩⟩

/-- **At a job whose state on entry has one shape.** -/
theorem frontAsksO_all (J : TestJob W X) (K : Codes) (N : TestSh) (he : J.p.early = true)
    (hN : ∀ w fr, testSh (J.rec₀ w fr) = N) (h : frontOwnFiveB J.p K N = true)
    (h3 : ∀ w fr, stTidyB (J.rec₀ w fr).st = true ∧ stPlainB (J.rec₀ w fr).st = true ∧
      claimsB (J.rec₀ w fr) = true) (w : W) (fr : Front X) :
    ∃ Dp : Plain, FrontAsksO J w fr K Dp :=
  frontAsksO_of_five J w fr K he (by rw [hN]; exact h) (h3 w fr).1 (h3 w fr).2.1 (h3 w fr).2.2

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.frontOwnFiveB
#print axioms ProofFile.Honest.K12.Own.pass_of_five
#print axioms ProofFile.Honest.K12.Own.frontAsksO_of_five
#print axioms ProofFile.Honest.K12.Own.frontAsksO_all
