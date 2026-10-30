-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K01FactsOf.lean: TWO LEMMAS FOR THE TWO TIES OF KIND K1 (at
W's commitment and at the first segment's opening): what their premises along reached states,
W_hFacts and G_hFacts, ask beyond two facts of their own files, AT THE CLOSED CONSTANT P5J.mgAtAll,
in a form that names neither tie's data: so that it stands on a ground without the ties' files.
  factsK13_reached_of  FactsK13 D d12Full (mgAll hA.𝔇 mgBase) a at EVERY D whose codes, shape and
                       layout are the constant's: FactsK13 reads no more of D. By factsK13_reached
                       (Johnson/Desc/AtSeats/K01FactsAtAll.lean).
  liveIs_reached       liveIsC dk a.2 = true at every dk whose shape and layout are the constant's:
                       by liveShape_field and liveLayout_field
                       (Johnson/IMR/AtReach.lean).
Both at every state that is reached along the first chain's raw list and bears no mark.
USER. W_hFacts := factsK13_reached_of at the tie's dW. G_hFacts := ⟨factsK13_reached_of at dG,
liveIs_reached, the tie's own front_at_rchAt, the silence of the wider public tests at one name⟩.
What is not claimed. That hA or hP1 can be met: NO MEMBER. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K01FactsAtAll
import Johnson.Desc.First.Look.K3FillCode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (K3Data liveIsC)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.PlanWritten (madePinnedAt)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

/-- **FactsK13 at every D with the constant's codes, shape and layout.** -/
theorem factsK13_reached_of
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) {nR : ℕ}
    (D₁ : DataK13 ProofFile.InstPub
      (VerifiableInference.Desc.Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT) nR)
    (hc : D₁.codes = hA.𝔇.cs) (hs : D₁.shape = hA.𝔇.shape) (hl : D₁.layout = hA.𝔇.layout) (j : ℕ)
    (a : ProofFile.InstPub × S) (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) j a) (hu : a.2.failed = none) :
    FactsK13 D₁ d12Full (mgAll hA.𝔇 mgBase) a := by
  have F := factsK13_reached hA hP1 j a hr hu
  refine ⟨?_, F.masks, F.within, F.oneRow, F.weights, F.book, F.seats, F.shapes, F.fits, F.quiet⟩
  rw [hc, hs, hl]
  exact F.order

/-- **The copy in use has the constant's shape and layout.** -/
theorem liveIs_reached (dk : K3Data) (hs : dk.shape = hA.𝔇.shape) (hl : dk.layout = hA.𝔇.layout)
    (j : ℕ) (a : ProofFile.InstPub × S) (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) j a)
    (hu : a.2.failed = none) : liveIsC dk a.2 = true := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hpl : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc hA.laid.planOk
  have h1 := _root_.Meaning.K2.liveShape_field hA.scope hA.reads O hpl _ id (fun _ _ q => q) j a hr
    hu
  have h2 := _root_.Meaning.K2.liveLayout_field hA.scope hA.reads O hpl _ id (fun _ _ q => q) j a
    hr hu
  unfold liveIsC
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hs, hl]
  exact ⟨h1, h2⟩

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.factsK13_reached_of
#print axioms VerifiableInference.Desc.K13.Law.liveIs_reached
