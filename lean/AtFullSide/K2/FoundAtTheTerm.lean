-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FoundAtTheTerm.lean: what the prover that onlineProverFromPublicFiles returns holds at the places of the
code switch (the kind K2), at the filling onlineProverPartsInUse, with the index a letter.

  switchByPub        the kind's lot as the filling lays it
  k2_mem_wM          that lot is one of the filling's lots
  k2_hex             some lot of the filling has the kind's sides
  k2_ho              every lot of the filling has no side at a place of the kind, or the kind's
                     sides
  switchPlaces_kind  every member of switchPlaces stands at a place of the kind
  k2_found           at onlineProverFromPublicFiles's return, the search at a place of the kind finds the kind's side,
                     under the opening
  k2_side_is         every side of the kind at onlineProverFromPublicFiles's return is the kind's side at a place

Limits. The opening and onlineProverFromPublicFiles's return are premises. Nothing here says what the side plays, what
the verifier does at it, or that any state meets the thread's sentence.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K2.Law.HalfAtArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2.Term
open VerifiableInference.Desc (Chain Block KindName)
open P5J (TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

section Lots
variable {W₀ : Type} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
  (O : OnlineProverArguments) (Zq : ProofFile.Pub) (G : ProofFile.Ground)

/-- The kind's lot as the filling lays it. -/
abbrev switchByPub :
    HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit :=
  HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
    switchLot D fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩

/-- The kind's lot stands among the filling's pairs. -/
theorem switch_mem_pairs : (switchByPub I S, KindName.K2) ∈ widerPairs I o S O := by
  unfold widerPairs
  exact .tail _ (.head _)

/-- The kind's lot is one of the filling's lots. -/
theorem k2_mem_wM : switchByPub I S ∈ (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨(switchByPub I S, KindName.K2), switch_mem_pairs I o S O, rfl⟩)))

/-- **Some lot of the filling has the kind's sides.** -/
theorem k2_hex :
    ∃ M ∈ (onlineProverPartsInUse I o S O).lots, M.halves Zq G =
      (switchLot (X := Unit) (withSwitchData S (K1.lotData S) Zq G)
        fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells =>
          ⟨w.trace, I.weights Zq w.w₀, w.rc⟩).halves Zq G :=
  ⟨switchByPub I S, k2_mem_wM I o S O, rfl⟩

/-- Every side of W's lot stands at a place of the kind K1. -/
theorem wLotAt_kind :
    ∀ y ∈ (wLotAt (X := Unit) I o O).halves Zq G, y.place.kind = KindName.K1 := by
  intro y hy
  rw [wLotAt_halves] at hy
  cases hm : OnBytes.linMessageW Zq.first.lin with
  | none => simp [hm] at hy
  | some msg =>
    simp [hm] at hy
    subst hy
    rfl

/-- **Every lot of the filling has no side at a place of the kind, or the kind's sides.** -/
theorem k2_ho :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K2) ∨
        M.halves Zq G =
          (switchLot (X := Unit) (withSwitchData S (K1.lotData S) Zq G)
            fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells =>
              ⟨w.trace, I.weights Zq w.w₀, w.rc⟩).halves Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    by_cases k : q.2 = KindName.K2
    · have e' : q = (switchByPub I S, KindName.K2) :=
        List.inj_on_of_nodup_map widerPairs_nodup hq (switch_mem_pairs I o S O) k
      rw [e']
      exact .inr rfl
    · exact .inl fun x hx e =>
        k (((FirstFill.widerKinds I o S O Zq G).all q hq x hx).symm.trans e)
  · exact .inl fun x hx e =>
      absurd ((closeLotAt_kinds I S Zq G x hx).symm.trans e) (by decide)
  · exact .inl fun x hx e =>
      absurd ((proxLotAt_kinds I S Zq G x hx).symm.trans e) (by decide)
  · exact .inl fun x hx e =>
      absurd ((wLotAt_kind I o O Zq G x hx).symm.trans e) (by decide)

end Lots

/-- Every member of switchPlaces stands at a place of the kind. -/
theorem switchPlaces_kind {Zq : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zq G) : p.place.kind = KindName.K2 := by
  unfold switchPlaces at hp
  split at hp
  · obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hp
    exact eq_of_beq (List.mem_filter.1 hsp).2
  · cases hp

/-- **At onlineProverFromPublicFiles's return, the search at a place of the kind finds the kind's side.** Op: the
library's head over the public files. -/
theorem k2_found {W₀ : Type} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {Wp : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (Op : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (onlineProverPartsInUse I o S O) = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    (A.H.first.find? fun g => g.place == p.place) =
      some (switchHalf (coreSender freshTable) (withSwitchData S (K1.lotData S) Zp Bs.G₀)
        (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p) := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  obtain rfl : A.Z = Zp := Except.ok.inj (hZ.symm.trans Op.pub)
  have eG : A.G = Bs.G₀ := Option.some.inj (hG.symm.trans Op.blank)
  have hD : withSwitchData S (K1.lotData S) A.Z A.G =
      withSwitchData S (K1.lotData S) A.Z Bs.G₀ :=
    congrArg (withSwitchData S (K1.lotData S) A.Z) eG
  have hex := k2_hex I o S O A.Z A.G
  have ho := k2_ho I o S O A.Z A.G
  rw [hD] at hex ho
  exact switch_half_fill Op hA (withSwitchData S (K1.lotData S) A.Z Bs.G₀)
    (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) hex ho hp
    (switchPlaces_kind hp)

/-- **Every side of the kind at onlineProverFromPublicFiles's return is the kind's side at one of its places.** -/
theorem k2_side_is {W₀ : Type} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {Wp : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (Op : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (onlineProverPartsInUse I o S O) = .ok A)
    {g : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hg : g ∈ A.H.first) (hk : g.place.kind = KindName.K2) :
    ∃ p ∈ switchPlaces Zp Bs.G₀, g =
      switchHalf (coreSender freshTable) (withSwitchData S (K1.lotData S) Zp Bs.G₀)
        (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p := by
  obtain ⟨hZ, hG, -, -, -, -, -, eF, -⟩ := atPure_ok hA
  obtain rfl : A.Z = Zp := Except.ok.inj (hZ.symm.trans Op.pub)
  have eG : A.G = Bs.G₀ := Option.some.inj (hG.symm.trans Op.blank)
  rw [eF] at hg
  obtain ⟨M, hMl, hgM⟩ := List.mem_flatMap.1 hg
  have hgM' : g ∈ M.halves A.Z A.G := hgM
  rcases k2_ho I o S O A.Z A.G M hMl with hn | he
  · exact absurd hk (hn g hgM')
  · rw [he, eG] at hgM'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hgM'
    exact ⟨p, hp, rfl⟩

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.switch_mem_pairs
#print axioms AtFullSide.K2.Term.k2_mem_wM
#print axioms AtFullSide.K2.Term.k2_hex
#print axioms AtFullSide.K2.Term.wLotAt_kind
#print axioms AtFullSide.K2.Term.k2_ho
#print axioms AtFullSide.K2.Term.switchPlaces_kind
#print axioms AtFullSide.K2.Term.k2_found
#print axioms AtFullSide.K2.Term.k2_side_is
