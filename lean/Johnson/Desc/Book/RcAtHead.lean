-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/RcAtHead.lean: the premise hRc of the last table's field (own3_at_top |
own3_at_end), in its binder's signs, FROM THE ONE HEAD (`P5J.AtMg`, Johnson/P5J/AtMg.lean) at the
concrete second hash function. Two theorems. Joinings.

  `hRc_at_head`: `P2Law.hRc_of_five` (Johnson/P2LawR/RcAtEnd.lean) at get := the identity, Rc q :=
    `EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q` (K a letter), with the five facts called
    (`Meaning.K2.five_at_end_planOk`, Johnson/IMR/EndFivePaid.lean).
    OFF THE HEAD: the scope · an opening · the test on the list of rounds.
    THE FOUR THAT STAY, BY NAME:
      hB: `K12.Door.sendsAreB`, a test with code on the list of rounds, at every opening
      hL: the list of places and shapes can be laid at the first chain's codes: it names L
      h₃: `ownSitsB V` · h₄: `sampleTwoB cs V`, each under Oc, Rc and "no mark"
  `hRc_at_listed`: hL in the composed meaning's constant's letters: `P5J.At.laid? Zp = some L`.

Limits. The premises that stay are shown nowhere here. Where hB is met by a lemma under a test on
written values, that test stands in front again. At `OnBytes.secondHashFunction` alone. No example. Nothing on
soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.RcAtEnd
import Johnson.IMR.EndFivePaid
import Johnson.P5J.AtMg
import Johnson.P5J.LettersAt2
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open VerifiableInference.Desc.Last
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)
open ToldDesc (rcLastB sampleTwoB)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl}

/-- **hRc from the one head, the five facts called.** -/
theorem hRc_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L)
    {Str : Type} (V : OwnSeats) (cs : Codes) (K : ProofFile.InstPub × First.S → Prop)
    (Oc : ProofFile.InstPub × First.S → Str → Prop)
    (h₃ : ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → ownSitsB V q.2 = true)
    (h₄ : ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → sampleTwoB cs V q.2 = true) :
    ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → rcLastB 0 V L cs q.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P2Law.hRc_of_five (fun q => q) Oc
    (fun q => EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q)
    (fun p => Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) cF.blocksInOrder.length p)
    (fun _ hq => hq.1) V L cs
    (Meaning.K2.five_at_end_planOk h.scope O h.laid.planOk (hB Bs base _ _ O) hL) h₃ h₄

/-- **The list in the composed meaning's constant's letters.** -/
theorem hRc_at_listed (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : P5J.At.laid? Zp = some L)
    {Str : Type} (V : OwnSeats) (cs : Codes) (K : ProofFile.InstPub × First.S → Prop)
    (Oc : ProofFile.InstPub × First.S → Str → Prop)
    (h₃ : ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → ownSitsB V q.2 = true)
    (h₄ : ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → sampleTwoB cs V q.2 = true) :
    ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → rcLastB 0 V L cs q.2 = true :=
  hRc_at_head h hB hL V cs K Oc h₃ h₄

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.hRc_at_head
#print axioms VerifiableInference.Desc.Book.hRc_at_listed
