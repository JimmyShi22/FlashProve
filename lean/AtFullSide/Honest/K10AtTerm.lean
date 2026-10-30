-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K10AtTerm.lean: the closing of a segment (kind K10) at T1's online filling and at
what the maker returns there (E2E/TheHonestProver.lean), and at the filling before it is read
through.

  `k10_only_wider`, `k10_only_through`   a lot of the filling has no half of the kind, or is the
                   closings' lot, read through or not
  `closings_at_term`   `closingsSLotThru` without its simulators is a lot of the online filling
  `closing_in_form_at_term`, `closing_in_form_at_base`   `ClosingInForm` (Honest/K10/AtFill.lean) at
                   each of the two returns, in scope and under the verifier's gate `protocolDataWellFormed`

No count at any closing rests on this file: see the head of Honest/K10/AtFill.lean. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import AtFullSide.Honest.K7AtTerm
import Johnson.Desc.ProofFile.Honest.K10.AtFill
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Thru

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (KindName Chain)
open ProofFile.Honest.K10 (ClosingInForm closing_in_form k10_ten)

section
variable {W₀ W₀' Rc' : Type}

/-- **A lot of the filling has no half of the kind, or is the closings' lot.** -/
theorem k10_only_wider (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o Sz O).lots,
      (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K10) ∨ M = closeLotAt I Sz := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · exact .inl (k10_ten I o Sz O Zq G M h)
  · exact .inr rfl
  · refine .inl fun x hx e => ?_
    have h := proxLotAt_kinds I Sz Zq G x hx
    rw [e] at h
    cases h
  · refine .inl fun x hx e => ?_
    rw [wLotAt_halves] at hx
    cases hmsg : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hmsg] at hx
      cases hx
    | some msg =>
      rw [hmsg] at hx
      obtain rfl := List.mem_singleton.1 hx
      cases e

/-- **The same read through.** -/
theorem k10_only_through (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀') (Zq : Pub) (G : Ground) :
    ∀ M ∈ (OnlineProverParts.through g rd d (onlineProverPartsInUse I o Sz O)).lots,
      (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K10) ∨
        M = HLot.thru (Local.thru g rd) (Local.thru g rd) (closeLotAt I Sz) := by
  intro M hM
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
  rcases k10_only_wider I o Sz O Zq G M₀ hM₀ with h | rfl
  · refine .inl fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact h y hy
  · exact .inr rfl

theorem closeLotAt_mem_wider (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : closeLotAt I Sz ∈ (onlineProverPartsInUse I o Sz O).lots := by
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (.head _)))

end

/-- **THE TIE AT THE BASE FILLING**: among the halves that the filling lays, those of the kind are the
halves of the closings' rows, as an equation of lists. -/
theorem closing_tie_wider {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    (firstOf Zq G (onlineProverPartsInUse I o Sz O).lots).filter (fun x => x.place.kind == .K10) =
      ((closingsSLotAt (X := Unit) I Sz).rows Zq G).map (·.half) := by
  have e1 : (((widerFillAt I o Sz O).lots).flatMap fun L => L.halves Zq G).filter
      (fun x => x.place.kind == .K10) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx e
    obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.1 hx
    exact k10_ten I o Sz O Zq G M hM x hxM (beq_iff_eq.1 e)
  have e2 : ((closeLotAt (X := Unit) I Sz).halves Zq G).filter (fun x => x.place.kind == .K10) =
      (closeLotAt (X := Unit) I Sz).halves Zq G := by
    rw [List.filter_eq_self]
    intro x hx
    exact beq_iff_eq.2 (closeLotAt_kinds I Sz Zq G x hx)
  have e3 : ((proxLotAt (X := Unit) I Sz).halves Zq G).filter (fun x => x.place.kind == .K10) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx e
    have h := proxLotAt_kinds I Sz Zq G x hx
    rw [beq_iff_eq.1 e] at h
    cases h
  have e4 : ((wLotAt (X := Unit) I o O).halves Zq G).filter (fun x => x.place.kind == .K10) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx e
    rw [wLotAt_halves] at hx
    cases hmsg : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hmsg] at hx
      cases hx
    | some msg =>
      rw [hmsg] at hx
      obtain rfl := List.mem_singleton.1 hx
      cases e
  unfold firstOf
  rw [widerFillAtCPUOWM_lots]
  simp only [List.flatMap_append, List.filter_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [e1, e2, e3, e4]
  simp only [List.append_nil, List.nil_append]
  have hT := congrArg (fun L : HLot _ _ Unit => L.halves Zq G)
    (closingsSLotAt_toHLot (X := Unit) I Sz)
  exact hT.symm

/-- **`closingsSLotThru` without its simulators is a lot of the online filling.** -/
theorem closings_at_term (files : VerifierAndGoals.PublicFiles) :
    (closingsSLotThru (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref id
      (tableCoins files)).toHLot ∈ (onlineFilling files).lots := by
  rw [closingsSLotThru_toHLot]
  exact List.mem_map.2 ⟨_, closeLotAt_mem_wider _ _ _ _, rfl⟩

variable {files : VerifierAndGoals.PublicFiles}

/-- **`ClosingInForm` at the term**, at the readers that the filling lays read through. -/
theorem closing_in_form_at_term {pp : Inst.Model.ScalesAndPolicy} {R : OnlineReturn files}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) (h : onlineMaker files = .ok R) :
    ∃ c : Chain VerifiableInference.Desc.First.S ProofFile.Cl, ProofFile.onlineFirstChainAt R.Z = .ok c ∧
      ClosingInForm R
        ((fun w : Local FullSizeMatrix IndexCommitterCoins Inst Cells => ⟨w.trace, matrixInput.weights R.Z w.w₀, w.rc⟩) ∘
          Local.thru id (tableCoins files))
        (widerRows OnBytes.HonestTrace.Sz.ref R.Z R.G)
        (K10.stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS R.Z ξ.pub) c := by
  obtain ⟨-, c, hc⟩ := online_made hS hR live h
  refine ⟨c, hc, ?_⟩
  exact closing_in_form hS hR h (plan_at_live live h) hc _ _ _
    (Lc := HLot.thru (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files))
      (closeLotAt matrixInput OnBytes.HonestTrace.Sz.ref))
    (List.mem_map.2 ⟨_, closeLotAt_mem_wider _ _ _ _, rfl⟩)
    (closeLotAt_thru_halves _ _ _ _ R.G hc)
    (fun M hM => (k10_only_through _ _ _ _ _ _ _ R.Z R.G M hM).imp_right fun e => by rw [e])

/-- **`ClosingInForm` at the base prover**, at the filling before it is read through. -/
theorem closing_in_form_at_base {pp : Inst.Model.ScalesAndPolicy} {R : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok R) :
    ∃ c : Chain VerifiableInference.Desc.First.S ProofFile.Cl, ProofFile.onlineFirstChainAt R.Z = .ok c ∧
      ClosingInForm R
        (fun w : Local FullSizeMatrix IndexCommitterCoins Inst Cells => ⟨w.trace, matrixInput.weights R.Z w.w₀, w.rc⟩)
        (widerRows OnBytes.HonestTrace.Sz.ref R.Z R.G)
        (K10.stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS R.Z ξ.pub) c := by
  obtain ⟨Bs, base, c, Sh, Se, O⟩ := atPure_open (X := Unit) h
  have hc := ToldDesc.pureChainAt_of_open O
  refine ⟨c, hc, ?_⟩
  exact closing_in_form hS hR h (plan_at_live live h) hc _ _ _
    (Lc := closeLotAt matrixInput OnBytes.HonestTrace.Sz.ref)
    (closeLotAt_mem_wider _ _ _ _) (closeLotAt_ok _ _ R.G hc)
    (fun M hM => (k10_only_wider _ _ _ _ R.Z R.G M hM).imp_right fun e => by rw [e])

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.k10_only_wider
#print axioms ProofFile.Honest.Term.k10_only_through
#print axioms ProofFile.Honest.Term.closeLotAt_mem_wider
#print axioms ProofFile.Honest.Term.closing_tie_wider
#print axioms ProofFile.Honest.Term.closings_at_term
#print axioms ProofFile.Honest.Term.closing_in_form_at_term
#print axioms ProofFile.Honest.Term.closing_in_form_at_base
