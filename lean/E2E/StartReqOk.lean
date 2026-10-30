-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StartReqOk.lean: THE FIRST CHAIN BEGINS: WHERE THE REQUEST PASSES THE STATE's OWN TEST (`S.reqOk`).
Statements and proofs.

  `reqOk_of_bytes`    in scope, where the laying holds: the test says yes at a well-formed request's
                      bytes: by the request's type, no relation is read
  `reqOk_of_read`     the same where `ProofFile.instOf` reads the two files as an instance
  `reqOk_of_okStart`  the test says yes where the description's first test does (`ProofFile.okBy`)

Limits. At the format's second hash function for the first two. Nothing on any property.
-/
import E2E.StartInScope
import Johnson.IMR.RecRun
import Johnson.P5J.AtMg
import Johnson.Desc.ProofFile.InstOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Start
open OnBytes OnBytes.Flat OnBytes.Model OnBytes.Slice Inst.Model
open LPFD.Full (instanceAsPlainRecord XF)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl}

/-- **The bytes of a well-formed request pass**, in scope, where the laying holds. -/
theorem reqOk_of_bytes (scope : VerifierAndGoals.InScope Z = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (x : Instance ppref) (hre : x.r < x.e) :
    (Zp.s₀.withReq (Verify.words32 (requestBytesOf x))).reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  obtain ⟨hT, hV⟩ := numbers_of_laid scope Ld
  have h32T : ppref.T < 2 ^ 32 := by decide
  have h32V : ppref.V ≤ 2 ^ 32 := by decide
  obtain ⟨cov, e⟩ := coveredOf_wordsOf x h32T h32V hre
  have w1 : Verify.words32 (requestBytesOf x) = requestWordsOf x := words32_bytesOfWords _
  rw [w1, hT, hV]
  exact Meaning.K2.reqOk_of_covered e Zp.s₀

/-- **Where the two files are read as an instance, the request passes.** -/
theorem reqOk_of_read (scope : VerifierAndGoals.InScope Z = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {ξ : ProofFile.Inst} {x : Instance ppref}
    (h : ProofFile.instOf ξ = some x) :
    (Zp.s₀.withReq (Verify.words32 ξ.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  obtain ⟨e, -, hre, -⟩ := ProofFile.instOf_bytes h
  rw [← e]
  exact reqOk_of_bytes scope Ld x hre

/-- **Where the description's first test says yes, the request passes.** -/
theorem reqOk_of_okStart {o : ProofFile.SecondHashFunctionArgument} {x : ProofFile.Inst}
    (h : (F0T o Zp Np cF).okStart x = true) :
    (Zp.s₀.withReq (Verify.words32 x.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  rw [okStart_eq, Bool.and_eq_true] at h
  exact Meaning.K2.okBy_reqOk h.1

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.reqOk_of_bytes
#print axioms AtPublicFiles.Start.reqOk_of_read
#print axioms AtPublicFiles.Start.reqOk_of_okStart
