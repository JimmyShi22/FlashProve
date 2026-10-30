-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/QuietHeadWhole.lean: the kind "lookup" (K3): the step
without a round behind the lookup on the digits of the head's link (`quietHead`,
Johnson/Desc/First/Look/K3Whole.lean), taken apart where it returns, with all six tests that it has
passed, and with what the claim that it sets is. It strengthens `quietHead_back`
(Honest/K3/Law/Thread/StateBehindHead.lean), which keeps one of the six and leaves the claim
unnamed. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `named_ok`: a named reading that returns has found its value.
  `quietHead_whole`: the head's link is open; the covered positions are made; what the head heard
    and the head's tables are set; the claim on the weights is made of these; the plan has one claim
    on the weights; and the state behind.

Hypotheses that remain.
  `h`: `quietHead` returns; in `named_ok`: the named reading returns.

Users. Honest/K3/Law/Thread/HeadDigitsBack.lean calls `quietHead_whole`;
Honest/K3/Law/Thread/HeadReturnsOf.lean imports this file.

Limits. From a return alone. On the verifier's side alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehindHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (quietHead)

local notation "FS" => VerifiableInference.Desc.First.S

theorem named_ok {α : Type} {msg : String} {o : Option α} {v : α} (h : named msg o = .ok v) :
    o = some v := by
  cases o with
  | none => exact nomatch h
  | some w =>
    have : (Except.ok w : Except String α) = .ok v := h
    rw [Except.ok.inj this]

/-- **The step without a round behind the lookup on the digits of the head's link, where it returns:
all six tests, among them the making of the claim, and the state behind.** -/
theorem quietHead_whole (X : OnBytes.Model.Verify.Public) (u t : FS) (h : quietHead X u = .ok t) :
    ∃ a cov x tt claim, u.here = .head a ∧ a.opened = true ∧
      u.covered X.T X.P.h.V = .ok cov ∧ a.x = some x ∧ a.t = some tt ∧
      VerifiableInference.Desc.First.Look.weightsClaim
        { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
          x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 } X.layers.wsLay = .ok claim ∧
      (X.H.NCL == 1) = true ∧
      t = { u with here := .head { a with claim := some claim } } := by
  unfold quietHead at h
  split at h
  · rename_i a hh
    by_cases ho : a.opened = true
    · simp only [need, ho, if_true, bind, Except.bind, pure, Except.pure] at h
      split at h
      · exact nomatch h
      · rename_i cov hcov
        split at h
        · exact nomatch h
        · rename_i x hx
          split at h
          · exact nomatch h
          · rename_i tt ht
            split at h
            · exact nomatch h
            · rename_i claim hcl
              split at h
              · exact nomatch h
              · rename_i hn
                refine ⟨a, cov, x, tt, claim, hh, ho, hcov, named_ok hx, named_ok ht, hcl, ?_, ?_⟩
                · by_cases h1 : (X.H.NCL == 1) = true
                  · exact h1
                  · simp [h1] at hn
                · rw [← Except.ok.inj h, ho]
    · simp [need, ho, bind, Except.bind] at h
  · exact nomatch h

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.named_ok
#print axioms ProofFile.Honest.K3.Law.AtThr.quietHead_whole
