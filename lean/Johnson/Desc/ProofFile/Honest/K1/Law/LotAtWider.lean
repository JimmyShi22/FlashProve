-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LotAtWider.lean: THE SHARED "SENDING" (the kind K1): AT THE
FILLING widerFillAt (Honest/AtPureWiderAt.lean) THE TWO PREMISES ON K1's LOTS (hex, ho of
RecordAtFill.lean; hexK, hoK of RecordAtJoin.lean and AtFullSide/K1/RecordAtFull.lean) ARE MET.
PUBLIC: which list of the filling has which halves, by place and kind. Two theorems; no definition.

The two theorems' text is laid by program.

  - hex_wider: the filling widerFillAt HOLDS K1's LOT: its first list's halves, at any public part
    and ground, ARE lotHalves at the filling's own reader, lotNo o Z and lotData S. No premise.
  - ho_wider: UNDER H2's PREMISE WiderKinds: ho's form at that filling: every list of it has these
    halves, or each half of it at a place of the kind K1 stands at a place without a link (the proof
    has more: no half at a place of that kind at all; the statement not). THAT PREMISE HAS A PAYER
    WITH NO PREMISE: H2's widerKinds (Honest/Thread/FirstFillAll.lean): not imported here.

Who calls. AtFullSide/K1/RecordAtBase.lean (hex_base, ho_base).

The road. widerFillAt_lots, widerPairs, WiderKinds.all, widerPairs_nodup (H2's
Honest/Thread/FirstFill.lean).

Limits. ONE NAMED FILLING, general in its four letters: a law at one filling carries over to no
wider one. At it the prover has no list of the kinds K9, K10, K12 and no side for K1 at W's place.
Nothing on what a half plays. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFill
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.K1.LotNoPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc

/-- **THE FILLING HOLDS K1's LOT.** -/
theorem hex_wider {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz₀ : OnBytes.HonestTrace.Sz)
    (O' : OnlineProverArguments) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    ∃ M ∈ (widerFillAt I o Sz₀ O').lots, M.halves Zq G =
      lotHalves (fun v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells =>
        ⟨v.x, ⟨v.trace, I.weights Zq v.w₀, v.rc⟩⟩) (lotNo o Zq) (lotData Sz₀) Zq G := by
  refine ⟨HLot.byPub I.weights (LongLots.plain o Sz₀ O').k1, ?_, rfl⟩
  rw [widerFillAt_lots]
  exact List.mem_map.2 ⟨_, List.Mem.head _, rfl⟩

/-- **EVERY OTHER LIST's HALVES STAND AT PLACES OF OTHER KINDS**, under WiderKinds. -/
theorem ho_wider {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {Sz₀ : OnBytes.HonestTrace.Sz}
    {O' : OnlineProverArguments} {Zq : ProofFile.Pub} {G : ProofFile.Ground} (K : WiderKinds I o Sz₀ O' Zq G) :
    ∀ M ∈ (widerFillAt I o Sz₀ O').lots,
      (∀ x ∈ M.halves Zq G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves Zq G = lotHalves (fun v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells =>
        ⟨v.x, ⟨v.trace, I.weights Zq v.w₀, v.rc⟩⟩) (lotNo o Zq) (lotData Sz₀) Zq G := by
  intro M hM
  rw [widerFillAt_lots] at hM
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
  by_cases hk : q.2 = .K1
  · right
    have e : q = (HLot.byPub I.weights (LongLots.plain o Sz₀ O').k1, .K1) :=
      List.inj_on_of_nodup_map widerPairs_nodup hq (List.Mem.head _) hk
    rw [e]
    rfl
  · left
    intro x hx e
    exact (hk ((K.all q hq x hx).symm.trans e)).elim

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.hex_wider
#print axioms ProofFile.Honest.K1.ho_wider
