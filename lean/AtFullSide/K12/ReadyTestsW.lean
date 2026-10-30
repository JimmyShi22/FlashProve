-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/ReadyTestsW.lean: `readyTests` (Honest/Frame.lean) AT THE PROVER THAT `onlineProverFromPublicFiles`
RETURNS AT THE WIDE FILLING: what of its tests is had under the head, and what stays.


  `twice_second_fill`   the last chain: no two sides at one place
  `twice_shared_fill`   the shared chain: the six, U's pair, O's pair: no two at one place
  `wLot_once`, `wLot_apart`   W's lot: no double; no place shared with the twelve others
  `readyTests_fillW`   under the head and hA: `readyTests` returns, at two premises: ht: no two
                 sides of the first chain at one place; hw: w₀ is in range

What stays. ht: paid in TwiceFirstW.lean (`twice_first_at`), with `wLot_once` and `wLot_apart` from
here. hw is on the request.

Limits.
- `readyTests` returning is not `ready` returning: `chainSteps` at the three chains is not read.
- The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. This file does not show
  that the maker returns at it. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.SecondMadeW
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain Place FileDescription)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K5
open ProofFile (Pub Ground SecondHashFunctionArgument)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem nodup_option {α V W X : Type} (o : Option α) (f : α → Placed V W X) :
    ((o.toList.map f).map (·.place)).Nodup := by
  cases o <;> simp

/-- **The last chain: no two sides at one place.** -/
theorem twice_second_fill {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    twice (secondW I o S O Z G : List (Placed _ _ Unit)) = [] := by
  refine twice_of_nodup ?_
  unfold secondW
  split
  · exact nodup_option _ _
  · simp

/-- The places of the shared chain's six. -/
theorem six_nodup {W₀ Rc Ky X : Type} (d : ProofFile.Honest.K14.Data) (A : ProofFile.Honest.K14.SendPub)
    (wt : W₀ → Weights) (rand : Rc → TableRand) :
    ((ProofFile.Honest.K14.proverSidesOfSharedRounds d wt ++ ProofFile.Honest.K14.proverSidesOfSharedSendings A wt rand :
        List (Placed Empty (Common W₀ Rc Ky) X)).map (·.place)).Nodup := by
  unfold ProofFile.Honest.K14.proverSidesOfSharedRounds ProofFile.Honest.K14.proverSidesOfSharedSendings
  split <;> simp <;> decide

/-- **The shared chain: no two sides at one place.** -/
theorem twice_shared_fill {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (I : WiderIn W₀) : twice (sharedWithUO I Zp) = [] := by
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp)
  rw [sharedWithUO_ok I h6, sharedWithU_ok I h6]
  refine twice_of_nodup ?_
  rw [List.map_append, List.map_append]
  have hs := six_nodup (Rc := IndexCommitterCoins) (Ky := OnBytes.TableKey) (X := Unit)
    { S := (VerifiableInference.Desc.K1.qAt Zp Np).S, atPoint := 0, atZeta := 6 }
    { P := VerifiableInference.Desc.K1.qAt Zp Np, atPoint := 0 } (I.weights Zp)
    (ProofFile.Honest.K14.randNow (VerifiableInference.Desc.K1.qAt Zp Np))
  have p6 := ProofFile.Honest.K14.six_places (Rc := IndexCommitterCoins) (Ky := OnBytes.TableKey) (X := Unit)
    { S := (VerifiableInference.Desc.K1.qAt Zp Np).S, atPoint := 0, atZeta := 6 }
    { P := VerifiableInference.Desc.K1.qAt Zp Np, atPoint := 0 } (I.weights Zp)
    (ProofFile.Honest.K14.randNow (VerifiableInference.Desc.K1.qAt Zp Np))
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hs, ?_, ?_⟩, ?_, ?_⟩
  · exact nodup_option _ _
  · intro a ha b hb e
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hb
    have q := p6 g hg
    rw [e, halfU_place _ _ Zp u hu] at q
    revert q
    decide
  · exact nodup_option _ _
  · intro a ha b hb e
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
      have q := p6 g hg
      rw [e, halfO_place _ Zp v hv] at q
      revert q
      decide
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
      rw [halfU_place _ _ Zp u hu, halfO_place _ Zp v hv] at e
      revert e
      decide

/-- **W's lot has no double.** -/
theorem wLot_once {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub)
    (G : Ground) :
    (((wLotAt (X := Unit) I o O).halves Z G).map (·.place)).Nodup := by
  rw [wLotAt_halves]
  cases OnBytes.linMessageW Z.first.lin <;> simp

/-- **W's lot shares no place with the twelve others.** -/
theorem wLot_apart {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ M ∈ ((widerFillAt I o S O).lots ++ [closeLotAt I S]) ++ [proxLotAt I S],
      ∀ g ∈ M.halves Z G, ∀ w ∈ (wLotAt (X := Unit) I o O).halves Z G, g.place ≠ w.place := by
  intro M hM g hg w hw e
  rw [wHalf_place I o O Z G w hw] at e
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with (h | rfl) | rfl
  · exact wider_none_at_w I o S O Z G M h g hg e
  · have hk := closeLotAt_kinds I S Z G g hg
    rw [e] at hk
    have hk' : VerifiableInference.Desc.KindName.K1 = .K10 := hk
    cases hk'
  · have hk := proxLotAt_kinds I S Z G g hg
    rw [e] at hk
    have hk' : VerifiableInference.Desc.KindName.K1 = .K12 := hk
    cases hk'

/-- **`readyTests` RETURNS, AT TWO PREMISES.** ht: no two sides of the first chain at one place; hw:
w₀ is in range. -/
theorem readyTests_fillW {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    (ht : twice A.H.first = []) {w₀ : W₀} (hw : A.H.inRange w₀ = true) :
    readyTests A.F A.B A.H w₀ = .ok () := by
  obtain ⟨hW, s1, s2, s3, hd⟩ := atPure_tests hA
  have hZ := (atPure_at_laid h.laid hA).1
  have hF := (atPure_at_laid h.laid hA).2
  obtain ⟨-, -, -, -, -, -, -, -, e2, e3, -⟩ := atPure_ok hA
  have t2 : twice A.H.shared = [] := by
    rw [e2, hZ]
    exact twice_shared_fill h I
  have t3 : twice A.H.second = [] := by
    rw [e3]
    exact twice_second_fill I o' S O _ _
  have hp : A.F.placesOk = true := by
    rw [hF]
    exact ProofFile.Honest.K12.Light.planOk_places h.laid.planOk
  simp only [List.isEmpty_iff] at s1 s2 s3
  unfold readyTests
  simp [s1, s2, s3, ht, t2, t3, hp, hd, hw, hW]

end AtFullSide.K12

#print axioms AtFullSide.K12.nodup_option
#print axioms AtFullSide.K12.twice_second_fill
#print axioms AtFullSide.K12.six_nodup
#print axioms AtFullSide.K12.twice_shared_fill
#print axioms AtFullSide.K12.wLot_once
#print axioms AtFullSide.K12.wLot_apart
#print axioms AtFullSide.K12.readyTests_fillW
