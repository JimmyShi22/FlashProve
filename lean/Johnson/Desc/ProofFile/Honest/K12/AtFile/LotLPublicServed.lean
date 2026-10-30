-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLPublicServed.lean

It states no goal. No property of the protocol is claimed.

hpub of `acceptedS_stands_L` at the
library's two named sets of public files: every instance of the type passes the closing's public
test, so no instance that the thread can be handed fails it there. One more theorem, with only
the law `closing_at_head` as a premise, shows that the premises of LotLPublicClosing.lean can be met together.

  `closing_public_at_zFull`, `closing_public_at_zGap`   hpub, at whatever the thread calls valid,
                                where what is valid is an instance of the type, `instanceAsPlainRecord z`
  `closing_premises_at_zFull_whole`   BUT FOR THE LAW hc: there are letters that meet the head
                                at storedPublicFiles, a blank ground and a finish, and at them hok, hS and the
                                public test at every instance of the type all hold

By what. `closing_premises_at_finish`, `closing_public_of_okStart` (LotLPublicClosing.lean),
`okStart_zFull`, `okStart_zGap` (AtFullSide/E2E/StartAtWrittenFiles.lean), `okStart_at_zFull`
(AtFullSide/K5/ItemAtFull.lean), `fitsL_head_L` (AtFullSide/K12/FitsAtHeadL.lean).

Hypotheses. hV: what the thread calls valid has an instance `instanceAsPlainRecord z`. A served request's input
has that form (`ServedInput`; not beneath this file).

Limits.
- storedPublicFiles and zGap are terms written in the library; no Lean code ties them to a file on a disk.
- hV is asked of the letter Vd here. At the first thread's own Vd, `ReadyInput`, no such premise is
  needed: LotLPublicThread.lean.
- Public tests alone: nothing on what a prover sends, nothing on a run.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicClosing
import AtFullSide.E2E.StartAtWrittenFiles
import AtFullSide.K5.ItemAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA F0T TS)
open VerifierAndGoals (storedPublicFiles zGap asDescriptionFiles)

variable {W₀ Rc Tr : Type} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {G : ProofFile.Ground} {pl : K2.SwitchPlace}

/-- **hpub at the stored full-size files.** -/
theorem closing_public_at_zFull (h : AtMgA OnBytes.secondHashFunction storedPublicFiles D₀ r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : finishAt Zp G = some pl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (hV : ∀ v, Vd v → ∃ z, v.x = LPFD.Full.instanceAsPlainRecord z) :
    ∀ v, Vd v →
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
        ((K2.segmentsOf Zp G).take pl.link) v.x = true :=
  closing_public_at_valid h hG hf Vd fun v hv => by
    obtain ⟨z, e⟩ := hV v hv
    rw [e]
    exact AtPublicFiles.Start.okStart_zFull h.laid z

/-- **hpub at the other named files.** -/
theorem closing_public_at_zGap (h : AtMgA OnBytes.secondHashFunction zGap D₀ r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : finishAt Zp G = some pl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (hV : ∀ v, Vd v → ∃ z, v.x = LPFD.Full.instanceAsPlainRecord z) :
    ∀ v, Vd v →
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
        ((K2.segmentsOf Zp G).take pl.link) v.x = true :=
  closing_public_at_valid h hG hf Vd fun v hv => by
    obtain ⟨z, e⟩ := hV v hv
    rw [e]
    exact AtPublicFiles.Start.okStart_zGap h.laid z

/-- **But for the law `closing_at_head`, no premise: the three can be met together** at the stored full-size
files. -/
theorem closing_premises_at_zFull_whole
    (hc : ∀ {D₁ r₁ Zp Np cF}, P5J.AtMg OnBytes.secondHashFunction storedPublicFiles D₁ r₁ Zp Np cF →
      ClosingAtEveryPlace storedPublicFiles Zp Np cF) :
    ∃ Zp Np cF x G pl, AtMgA OnBytes.secondHashFunction storedPublicFiles (VerifierAndGoals.AtTheName.dpZ storedPublicFiles)
        (FlashProve.theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x ∧
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧ finishAt Zp G = some pl ∧
      K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ z, K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
        ((K2.segmentsOf Zp G).take pl.link) (LPFD.Full.instanceAsPlainRecord z) = true := by
  obtain ⟨Zp, Np, cF, x, h, hz⟩ := AtFullSide.K5.Item.okStart_at_zFull
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨pl, hf, -⟩ := fitsL_head_L h.toAtMg O.blank
  obtain ⟨hok, hS, hp⟩ := closing_premises_at_finish h O.blank hf (hc h.toAtMg)
  exact ⟨Zp, Np, cF, x, Bs.G₀, pl, h, O.blank, hf, hok, hS,
    fun z => hp _ (hz z)⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closing_public_at_zFull
#print axioms ProofFile.Honest.K12.AtProof.closing_public_at_zGap
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_at_zFull_whole
