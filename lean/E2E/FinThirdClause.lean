-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/FinThirdClause.lean: THE THIRD CLAUSE OF THE FILE's LAST TEST ON THE FIRST CHAIN's END ("where the request's last covered
position lies in front of its last token, the reply that is asked about is the token 0": S.finAsked,
Johnson/Desc/First/State.lean) IS A FACT ON THE INSTANCE: it follows from the description's own tests on the
instance (okBy, the first half of okStart), which run the reader of request and reply, at every state that still
holds the instance's request words. No thread, no run, no shape is read.

  call_of_okBy      where okBy says yes the reader of request and reply returns
  third_of_okBy     the clause, at a state with the instance's words
  third_of_okStart  the same from okStart at the proof file's description

Limits. Implications. THAT A STATE STILL HOLDS THE REQUEST's WORDS (hreq) AND THAT okStart ACCEPTS AT AN INSTANCE ARE
PREMISES HERE. Of finAsked's two other clauses nothing is said. Nothing on soundness, completeness or hiding.
-/
import E2E.StartAtFiles
import Johnson.IMR.RecRun
import OnBytes.K.ServedBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Start
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open P5J (F0T)

/-- Where the description's tests on the instance say yes, the reader of request and reply returns. -/
theorem call_of_okBy {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) :
    ∃ so, Head.stFromCall (Verify.words32 x.pub.request) (Verify.words32 x.y) Z.p.X.T = .ok so := by
  unfold ProofFile.okBy at h
  cases hG : ProofFile.holdBy o mk Z x with
  | error e => rw [hG] at h; cases h
  | ok G =>
    unfold ProofFile.holdBy at hG
    dsimp only at hG
    obtain ⟨_, -, hG⟩ := VerifiableInference.Desc.K3.ebind_ok hG
    obtain ⟨so, h1, -⟩ := VerifiableInference.Desc.K3.ebind_ok hG
    exact ⟨so, Meaning.K2.held_ok h1⟩

/-- **THE THIRD CLAUSE, FROM THE TESTS ON THE INSTANCE.** -/
theorem third_of_okBy {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) {s : S} (hreq : s.req = Verify.words32 x.pub.request) :
    (!decide (s.rowE < s.reqT) || x.asked == ofNat 0) = true := by
  obtain ⟨so, hc⟩ := call_of_okBy h
  obtain ⟨-, hsz, h3⟩ := OnBytes.K.stFromCall_ok hc
  have hT : s.reqT = Z.p.X.T := by
    unfold S.reqT
    rw [hreq, hsz]
    omega
  have hE : s.rowE = ((Verify.words32 x.pub.request).getD (Z.p.X.T + 1) 0).toNat := by
    unfold S.rowE
    rw [hT, hreq]
  rw [hE, hT]
  by_cases hlt : ((Verify.words32 x.pub.request).getD (Z.p.X.T + 1) 0).toNat < Z.p.X.T
  · rw [decide_eq_true hlt, Bool.true_and] at h3
    have hy : ((Verify.words32 x.y).getD 0 0).toNat = 0 := by
      simpa using h3
    unfold ProofFile.Inst.asked
    rw [hy]
    simp
  · rw [decide_eq_false hlt]
    rfl

/-- **The same from okStart at the proof file's description.** -/
theorem third_of_okStart {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain S ProofFile.Cl} {x : ProofFile.Inst}
    (h : (F0T o Zp Np cF).okStart x = true) {s : S}
    (hreq : s.req = Verify.words32 x.pub.request) :
    (!decide (s.rowE < s.reqT) || x.asked == ofNat 0) = true := by
  rw [okStart_eq, Bool.and_eq_true] at h
  exact third_of_okBy h.1 hreq

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.call_of_okBy
#print axioms AtPublicFiles.Start.third_of_okBy
#print axioms AtPublicFiles.Start.third_of_okStart
