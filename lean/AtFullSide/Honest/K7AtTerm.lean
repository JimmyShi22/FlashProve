-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K7AtTerm.lean: the round that names the next token (kind K7) at T1's online
filling and at what the maker returns there (E2E/TheHonestProver.lean).

  `replyLot_mem_wider`, `k7_only_wider`   the lot stands among the filling's lots before it is read
                   through, and a half of the kind comes from that lot alone
  `reply_tie_wider`, `reply_tie_at_base`   at the filling before it is read through, the halves of the
                   kind are those of `replySLot`'s rows, as an equation of lists
  `replySLot_at_term`   `replySLot` without its simulators is a lot of the online filling
  `k7_only_at_term`   a half of the kind at the online filling comes from that lot alone
  `plan_at_live`   under the gate `protocolDataWellFormed`, a return of the maker passes its tests on the plan
  `reply_closing_at_term`, `reply_closing_at_base`   `reply_closing` (Honest/K7/AtFill.lean) at what
                   the maker returns at the online filling, and at the filling before it is read
                   through, in scope, under the gate
  `descZ_first`   the online description's first chain is the chain that it is made of
  `online_made`   both functions of `onlineProver`'s match return
  `reply_at_term`   where the maker returns, in scope: among the first chain's sides a half of the
                   kind is the kind's half, and the look-up by the place finds it

This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K7.AtFill
import Johnson.Goal.Description.ProofSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (KindName)

section
variable {W₀ : Type}

theorem replyLot_mem_wider (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : replyLot ∈ (onlineProverPartsInUse I o Sz O).lots := by
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (replyLot_mem I o Sz O)))

theorem k7_only_wider (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o Sz O).lots, ∀ x ∈ M.halves Zq G, x.place.kind = .K7 →
      M = replyLot := by
  intro M hM x hx hk
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · exact k7_only I o Sz O Zq G M h x hx hk
  · have h := closeLotAt_kinds I Sz Zq G x hx
    rw [hk] at h
    cases h
  · have h := proxLotAt_kinds I Sz Zq G x hx
    rw [hk] at h
    cases h
  · rw [wLotAt_halves] at hx
    cases hmsg : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hmsg] at hx
      cases hx
    | some msg =>
      rw [hmsg] at hx
      obtain rfl := List.mem_singleton.1 hx
      cases hk

end

variable (files : VerifierAndGoals.PublicFiles)

/-- **THE TIE AT THE BASE FILLING**: among the halves that the filling lays, those of the kind are the
halves of `replySLot`'s rows, as an equation of lists. -/
theorem reply_tie_wider {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    (firstOf Zq G (onlineProverPartsInUse I o Sz O).lots).filter (fun x => x.place.kind == .K7) =
      ((replySLot (W₀ := W₀) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit)).rows Zq G).map (·.half) := by
  have e1 : (((widerFillAt I o Sz O).lots).flatMap fun L => L.halves Zq G).filter
      (fun x => x.place.kind == .K7) = replyLot.halves Zq G := by
    rw [widerFillAt_lots, List.flatMap_map]
    refine filter_one_of_kind _ (FirstFill.widerKinds I o Sz O Zq G).all widerPairs_nodup ?_
    unfold widerPairs
    exact .tail _ (.tail _ (.head _))
  have e2 : ((closeLotAt (X := Unit) I Sz).halves Zq G).filter (fun x => x.place.kind == .K7) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx e
    have h := closeLotAt_kinds I Sz Zq G x hx
    rw [beq_iff_eq.1 e] at h
    cases h
  have e3 : ((proxLotAt (X := Unit) I Sz).halves Zq G).filter (fun x => x.place.kind == .K7) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx e
    have h := proxLotAt_kinds I Sz Zq G x hx
    rw [beq_iff_eq.1 e] at h
    cases h
  have e4 : ((wLotAt (X := Unit) I o O).halves Zq G).filter (fun x => x.place.kind == .K7) = [] := by
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
  simp only [List.append_nil]
  rfl

/-- **`replySLot` without its simulators is a lot of the online filling.** -/
theorem replySLot_at_term :
    (replySLot (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness) (Tr := Cells) (X := Unit)).toHLot ∈
      (onlineFilling files).lots :=
  replySLot_mem_through (replyLot_mem_wider _ _ _ _) id (tableCoins files) matrixInput.dummy

/-- **A half of the kind at the online filling comes from that lot alone.** -/
theorem k7_only_at_term (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineFilling files).lots, ∀ x ∈ M.halves Zq G, x.place.kind = .K7 →
      M = replyLot :=
  k7_only_through (k7_only_wider _ _ _ _ Zq G) id (tableCoins files) matrixInput.dummy

variable {files}

/-- **Where the verifier's gate says yes, a return of the maker passes its tests on the plan**, at
every filling: the description does not read the filling. -/
theorem plan_at_live {W₀ Rc Tr X₀ X : Type} {Fl : OnlineProverParts W₀ Rc Tr X₀ X} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL Fl = .ok R) : R.F.planOk = true := by
  obtain ⟨F, hF, hp, -⟩ := FlashProve.pseat_name files live
  obtain ⟨-, -, hd, -⟩ := atPure_ok h
  obtain rfl : F = R.F := Except.ok.inj (hF.symm.trans hd)
  exact hp

/-- **THE CLOSING AT THE TERM**: `reply_closing` at the online filling. -/
theorem reply_closing_at_term {pp : Inst.Model.ScalesAndPolicy} {R : OnlineReturn files}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : onlineMaker files = .ok R) : ReplyClosed R :=
  reply_closing hS hR h (plan_at_live live h) (replySLot_at_term files)
    (k7_only_at_term files R.Z R.G)

/-- **The online description's first chain is the chain that it is made of.** -/
theorem descZ_first (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) :
    (descZ Zp Np cF).first.blocksInOrder = cF.blocksInOrder := rfl

/-- **Where the maker returns, in scope, under the gate, `placesOfMade` and `onlineFirstChainAt` return**:
the two functions on which `onlineProver` matches behind the maker. -/
theorem online_made {pp : Inst.Model.ScalesAndPolicy} {R : OnlineReturn files}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : onlineMaker files = .ok R) :
    (∃ places, H2U.placesOfMade R.Z.made = .ok places) ∧
      ∃ firstChain, ProofFile.onlineFirstChainAt R.Z = .ok firstChain := by
  obtain ⟨hZ, -, hd, -⟩ := atPure_ok h
  obtain ⟨Z', N, hZ', hN, -, -⟩ := ToldDesc.shared_fits_descPure hd (plan_at_live live h)
  obtain rfl : Z' = R.Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain ⟨-, -, -, -, -, -, c, hc, -⟩ := reply_closing_at_term hS hR live h
  exact ⟨⟨N, hN⟩, c, hc⟩

/-- **THE CLOSING AT THE BASE PROVER**: `reply_closing` at the filling before it is read through, at
the matrices. -/
theorem reply_closing_at_base {pp : Inst.Model.ScalesAndPolicy} {R : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok R)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) : ReplyClosed R :=
  reply_closing hS hR h (plan_at_live live h) (replyLot_mem_wider _ _ _ _)
    (k7_only_wider _ _ _ _ R.Z R.G)

/-- **The tie at the return of the base filling.** -/
theorem reply_tie_at_base {R : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok R) :
    R.H.first.filter (fun x => x.place.kind == .K7) =
      ((replySLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit)).rows R.Z R.G).map (·.half) := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf]
  exact reply_tie_wider _ _ _ _ R.Z R.G

/-- **WHERE THE MAKER RETURNS, IN SCOPE**: among the first chain's sides a half of the kind is the
kind's half, and the look-up by the place finds it. -/
theorem reply_at_term {pp : Inst.Model.ScalesAndPolicy} {R : OnlineReturn files}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (h : onlineMaker files = .ok R) :
    R.H.first.find? (fun x => x.place == IM.k7Place) = some (replyHalf 24 1 R.G.W.hS.V) ∧
      ∀ x ∈ R.H.first, x.place.kind = .K7 → x = replyHalf 24 1 R.G.W.hS.V := by
  obtain ⟨hZ, hG, -, -, -, -, -, hf, -⟩ := atPure_ok h
  have hsz : R.G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  rw [hf]
  have hl : replyLot ∈ (onlineFilling files).lots := replySLot_at_term files
  have hu := k7_only_at_term files R.Z R.G
  exact ⟨reply_found_at hl hu hsz, reply_half_only hu hsz⟩

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.replyLot_mem_wider
#print axioms ProofFile.Honest.Term.k7_only_wider
#print axioms ProofFile.Honest.Term.reply_tie_wider
#print axioms ProofFile.Honest.Term.reply_tie_at_base
#print axioms ProofFile.Honest.Term.replySLot_at_term
#print axioms ProofFile.Honest.Term.k7_only_at_term
#print axioms ProofFile.Honest.Term.plan_at_live
#print axioms ProofFile.Honest.Term.reply_closing_at_term
#print axioms ProofFile.Honest.Term.descZ_first
#print axioms ProofFile.Honest.Term.online_made
#print axioms ProofFile.Honest.Term.reply_closing_at_base
#print axioms ProofFile.Honest.Term.reply_at_term
