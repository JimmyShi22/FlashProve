-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallsArePaid.lean: the falls' measure of the online prover at the room of the
completeness error: TheFallsArePaid (E2E/TheFalls.lean), at public files in scope, which the reader
reads and which pass protocolDataWellFormed.

  qM_le_markPrice    a mark's price in the sum is at most its price at the kit
  theFallsArePaid    the statement, from two premises: ShareLines, the test on the stated shares of
                     all records, and hK3, the debt of the marks of the kind K3

Limits. ShareLines and hK3 are premises here. Nothing here says that a proof is accepted: a run that
meets no fall is another statement's. Nothing here speaks of the first stops or the private stops.
-/
import E2E.TheFallsRoad
import Johnson.P1K8R.FallSmallK9Plain
import Johnson.P1K8R.WindowAtTerm

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.TheSides AtPublicFiles.TheFalls
open VerifiableInference.Desc (Chain Block KindName)
open ProofFile.Honest (Fall Odds Mark MarkDebt KindFits fallsFull marksHead qMHead)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF instanceAsPlainRecord)
open OnBytes.Maker (WholeD RDT)
open _root_.Run (ckP)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

local instance (priority := high) nonemptyPadZ_fallsArePaid : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyRunValue_fallsArePaid : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_fallsArePaid : Inhabited RunValue := ⟨fun _ => 0⟩

/-- A stated share is at most its price at the kit. -/
theorem val_le_kit (o : Odds) : o.val ≤ atKit oneElement o := by
  unfold ProofFile.Honest.Odds.val atKit
  rw [← mul_one_div]
  exact mul_le_mul_left' (ENNReal.div_le_div_right one_le_oneElement _) _

/-- A mark's price in the sum is at most its price at the kit. -/
theorem qM_le_markPrice (b : Block TS ProofFile.Cl) (mk : Mark) :
    qMHead lookupElement headElement b mk ≤ markPrice mk := by
  unfold qMHead markPrice
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · exact val_le_kit mk.share

/-- The bound of K4's fall is its price at the kit. -/
theorem k4Zero_le : ProofFile.Honest.K4.k4ZeroBound ≤ atKit oneElement ProofFile.Honest.K4.k4CoinZeroShare := by
  have h := fallsQ_coinZero
  have e : ProofFile.Honest.K4.k4ZeroBound =
      Iop.kapSl 128 ^ 3 * 1 / ((ProofFile.Honest.K4.k4CoinZeroShare.den : ℕ) : ℝ≥0∞) := by
    unfold ProofFile.Honest.K4.k4ZeroBound
    congr 2
    exact Nat.cast_one
  rw [e]
  exact h

/-- **The falls have at most the room.** -/
theorem theFallsArePaid {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (lines : ∀ returned : OnlineReturn Z, onlineMaker Z = .ok returned →
      ShareLines returned.Z returned.G)
    (hK3 : ∀ (returned : OnlineReturn Z), onlineMaker Z = .ok returned →
      ∀ (firstChain : Chain TS ProofFile.Cl), ProofFile.onlineFirstChainAt returned.Z = .ok firstChain →
      ∀ (Bs : ProofFile.PureBase), ProofFile.baseOf returned.Z
        (ProofFile.pureSeat OnBytes.secondHashFunction returned.Z) = .ok Bs →
      ∀ A b b' Bt, firstChain.blocksInOrder.dropLast = A ++ b :: b' :: Bt →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks returned.Z Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (ckP .two) mk dsb (fun _ => True) ((mk.share.num : ℝ≥0∞) * lookupElement))
    (Relation : FullSizeMatrix → XF → Prop) : TheFallsArePaid Z Relation := by
  intro returned places firstChain hM hP hC G hG e₁ e₂ e₃
  obtain ⟨Np, cF, D, r, L, hNp, hcF⟩ := return_laid live hM
  obtain rfl : places = Np := Except.ok.inj (hP.symm.trans hNp)
  obtain rfl : firstChain = cF := Except.ok.inj (hC.symm.trans hcF)
  obtain ⟨xh, h⟩ := head_at_laid Z scope live L
  have hne : firstChain.blocksInOrder ≠ [] := by
    intro hnil
    have hlen : firstChain.blocksInOrder.length = 358 := by
      rw [← List.length_map (f := (·.place)), ProofFile.Honest.places_full h]
      exact ps_length
    rw [hnil] at hlen
    cases hlen
  have cut : firstChain.blocksInOrder = firstChain.blocksInOrder.dropLast ++ [firstChain.blocksInOrder.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  obtain ⟨Bs, base, O⟩ := L.opened
  have hB : ProofFile.baseOf returned.Z (ProofFile.pureSeat OnBytes.secondHashFunction returned.Z) = .ok Bs := O.made
  have hG₀ : Bs.G₀ = returned.G := Option.some.inj
    ((IM.base_made hB).2.2.1.symm.trans (return_ground hM))
  have hs := theFalls_nothing returned.Z places firstChain returned.G
  have hF₁ : G.falls₁ = fallsFull returned.Z Bs.G₀ noneNotGood (roundsBeforeK4 firstChain) := by
    rw [e₁, hG₀]
    exact hs.1
  have hn : ∀ g ∈ (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 returned.H)).first,
      g.place.kind ≠ KindName.frame := by
    have e : (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 returned.H)).first =
        (G.prover returned.H).first := rfl
    rw [e, hG]
    exact return_no_frame hM
  have plain := fallSmall_k9_plain Z returned.Z places firstChain runValueBytes runValueBytes
    returned.B G returned.H scope live L (Yes := Relation)
    (fun _ _ => ∅) hB lookupElement noneNotGood (roundsBeforeK4 firstChain) fallsQ hF₁ hn e₂
    e₃ cut (hK3 returned hM firstChain hC Bs hB)
    (fun _ _ b _ u _ _ => fallsQ_quiet _ _ _ noneNotGood (fun _ => rfl) _)
    (fun _ _ b _ u _ _ => fallsQ_quiet _ _ _ noneNotGood (fun _ => rfl) _)
    (fun b _ u _ _ => fallsQ_quiet _ _ _ noneNotGood (fun _ => rfl) _)
    (fun _ _ _ => k4Zero_le) (fun b g => fallsQ_share b g)
  rw [hF₁, hG₀] at plain
  exact fallsMeasured_room_of_sum returned places firstChain hM h cut (lines returned hM)
    (qM := qMHead lookupElement headElement) qM_le_markPrice plain

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.theFallsArePaid
