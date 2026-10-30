-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5LowAll.lean: kind K5 (an attention segment's own rounds): THREE FIELDS OF K5Rest (low · lowI · low0, K5AtMgPaid.lean) AT THE COMPOSED MEANING's CLOSED CONSTANT, FROM ONE TEST ON THE TABLE's NUMBERS: fenceFit (At.N Zp cF) At.links At.ps = true.
Typed by reading P5J/LettersAt.lean · LettersAll.lean · MgAtAll.lean · LaidOpens.lean · Desc/Sound/MgAll.lean · PieceLaid.lean ·
PieceSeated.lean.

Why. K5LowOfFence.lean's low_of_fence is general in the numbers beneath Numbers.withTold. The constant's numbers At.N Zp cF are of that form by their text, at the written list of places and at what the first chain's sub-protocols tell; the sub-protocols' own tests on the plan are in the head (laid.planOk).

Main names:
  `low_all`: the head · fenceFit at the constant's numbers · g < 12 · the piece's four facts at the border ⊢ low ∧ lowI ∧ low0 at bs := q.base, at h.𝔇.pubD.N.
  NOT HERE: the join's seatLow: it is low0 at the seats that the field sent names: to be struck.
Is it empty here? fenceFit AT THE CONSTANT's NUMBERS IS SHOWN AT NOTHING, AND NO TEST OF THE HEAD OR OF THE VERIFIER's VALUE ASKS IT: a named condition. It has not run at this term. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.Sound.PieceLaid
import Johnson.Desc.First.Att.Door.Law.K5LowOfFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open P5J (AtMgA TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)
  {C : CK} {Fr : Frame} {P W : Type} {num : Fmt.TreeSource → ℕ} {q : Piece C Fr (P × TS) ProofFile.Cl W}

/-- **K5Rest's low · lowI · low0 at the closed letters, from one test.** -/
theorem low_all (hf : fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = true) {g : ℕ} (hg : g < 12)
    (hq : PieceMore num 0 (cF.blocksInOrder.map held) (14 * (2 * g + 1) + 4) q) :
    (∀ t ∈ sampledIn h.𝔇.pubD.N (OFullK (14 * (2 * g + 1) + 4)), t.1 < q.base) ∧ h.𝔇.pubD.N.index.1 < q.base ∧
      ∀ t ∈ h.𝔇.pubD.N.sent (2 * g + 1) 0, t.1 < q.base :=
  low_of_fence ((P5T.numbersOf (P5J.At.pseats Zp)).withRows (P5J.At.shape Zp) (possAt cF.blocksInOrder P5J.At.links.length) P5J.At.links.length)
    hg hq (planOk_parts _ h.laid.planOk).1 hf


end

end H2K5.Door

#print axioms H2K5.Door.low_all
