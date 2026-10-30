-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLPublicPaid.lean

It states no goal. No property of the protocol is claimed.

`closing_at_head` (K2/Law/ClosingAtHead.lean) pays the one
premise that LotLPublicClosing.lean and LotLPublicServed.lean leave, so at the first chain's closing
proximity test hok, hS and hpub stand with no premise but the head and the ground.

  `closing_at_every_place`    under the head, `ClosingAtEveryPlace`
  `closing_premises_paid`     hok, hS and the public test at every instance that passes `okStart`
  `closing_premises_paid_at_first_thread`  the three at the first thread's letters
  `closing_premises_whole`    NO PREMISE: there are letters that meet the head at storedPublicFiles, a blank ground
                              and a finish, and at them hok, hS and the public test at every
                              instance of the type hold

By what. `closing_at_head` (K2/Law/ClosingAtHead.lean), `closing_premises_at_finish`,
`closing_premises_at_zFull_whole`.

Limits.
- 25 closed facts by Lean's kernel lie beneath, in K2/Law/ClosingAtHead.lean and the files beneath it.
- storedPublicFiles is a term written in the library; no Lean code ties it to a file on a disk.
- Public tests alone: nothing on what a prover sends, nothing on a run.
- K2/Law/ClosingAtHead.lean and the files beneath it lie beneath this file.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicServed
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicThread
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open OnBytes.HonestTrace (Sz)
open P5J (AtMg AtMgA F0T TS)
open VerifierAndGoals (storedPublicFiles asDescriptionFiles)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {G : ProofFile.Ground} {pl : K2.SwitchPlace}

/-- Under the head the law `closing_at_head` is the statement that the files here leave. -/
theorem closing_at_every_place (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) :
    ClosingAtEveryPlace Z Zp Np cF :=
  fun _ _ O => K2.Law.closing_at_head h O

/-- **hok, hS and the public test at the finish, from the head and the blank ground.** -/
theorem closing_premises_paid (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : finishAt Zp G = some pl) :
    K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ ξ : ProofFile.Inst, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
        K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
          ((K2.segmentsOf Zp G).take pl.link) ξ = true :=
  closing_premises_at_finish h hG hf (closing_at_every_place h.toAtMg)

/-- **No premise: the three are met together** at the stored full-size files. -/
theorem closing_premises_whole :
    ∃ Zp Np cF x G pl, AtMgA OnBytes.secondHashFunction storedPublicFiles (VerifierAndGoals.AtTheName.dpZ storedPublicFiles)
        (FlashProve.theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x ∧
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧ finishAt Zp G = some pl ∧
      K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ z, K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
        ((K2.segmentsOf Zp G).take pl.link) (LPFD.Full.instanceAsPlainRecord z) = true :=
  closing_premises_at_zFull_whole closing_at_every_place

/-- **hok, hS and hpub at the first thread's letters**, with no premise but the head at the return
and the finish. -/
theorem closing_premises_paid_at_first_thread {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : ProofFile.Honest.FirstThread.HeadAtReturn files A)
    (hf : finishAt A.Z A.G = some pl) :
    K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ v, ReadyInput h.description A.H v →
        K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout pl
          ((K2.segmentsOf A.Z A.G).take pl.link) v.x = true :=
  closing_premises_at_first_thread h hf (closing_at_every_place h.head.toAtMg)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closing_at_every_place
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_paid
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_whole
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_paid_at_first_thread
