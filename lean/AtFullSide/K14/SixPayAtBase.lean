-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K14/SixPayAtBase.lean: kind K14: at the full size, at the prover that onlineProverFromPublicFiles makes of the
wide filling onlineProverPartsInUse (Honest/K1/Law/WSideAtFill.lean), and at that filling read through a
pair of maps g, rd on the index and on the committer's randomness (OnlineProverParts.through,
Honest/ThruK13.lean): in the shared chain every kind but K12 "pays" (KindPays,
Honest/Law/ReadyOfSides.lean): the frame's set-up routine chainSteps returns at each side of the
prover's own list whose place bears the kind. Calls; no definition.

The prover's list of sides in the shared chain is the six sides that stand at the eight
sub-protocols of the linear claim's shared rounds, then the sides of the two proximity tests
(base_shared, thru_shared, AtFullSide/K14/SixAtBase.lean). The six pay (six_sidePays,
AtFullSide/K14/SixSidesPay.lean). The two tests' sides stand at places of the kind K12.

  tests_kind          the two tests' sides stand at places of the kind K12
  kindPays_at_base    **at the prover made of the wide filling: every kind but K12 pays in the
                      shared chain.** At K14 and at K1 it speaks of four and of two sides
                      (six_at_places, AtFullSide/K14/SixSidesLent.lean); at the thirteen other names
                      of kinds it holds for want of a side (so at the frame's own kind, whose two
                      sub-protocols in this chain have no side)
  kindPays_through    **the same at the wide filling read through g and rd**
  six_there_at_base, six_there_through   against emptiness, at the named provers: each of the six
                      sides stands at the place of a sub-protocol of the shared chain, and a search
                      of the prover's own list by that place finds it

What it feeds. The field pays₂ of ReadyDebts (Honest/Law/ReadyOfSides.lean) at fifteen of the
sixteen names of kinds. Left for that field: the kind K12; and that the made prover's description
A.F is F0T OnBytes.secondHashFunction Zp Np cF, which is the second clause of makers_ahead_at_atPure
(AtFullSide/K14/MakersBookOne.lean).

Limits.
  * The premises h and hA, as in AtFullSide/K14/SixSidesLent.lean: hypotheses, not shown here.
  * onlineProverPartsInUse is defined in Honest/K1/Law/WSideAtFill.lean. Nothing here says that this
    prover is the protocol's honest
    prover.
  * Of the kind K12, the two proximity tests' sides, nothing is said. Each of the two lists may be
    empty.
  * "It pays" says that the set-up returns. It says nothing on whether a part plays, a round is
    reached or a verifier accepts.
  * The shared chain alone. Sides at places of the kind K1 in the first chain are not treated.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.K14.SixSidesPay
import AtFullSide.K14.SixAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- As in AtFullSide/K14/SixAtBase.lean: with this instance in scope two of the names below are read
-- at another type.
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open VerifiableInference.Desc (Chain KindName)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12.AtProof
open P5J (AtMgA TS F0T)

variable {W₀ W₀' Rc' : Type}

/-- The two proximity tests' sides stand at places of the kind K12. -/
theorem tests_kind (I : WiderIn W₀) (Zp : ProofFile.Pub) :
    ∀ g ∈ testSides I Zp, g.place.kind = .K12 := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · rw [AtFullSide.K12.halfU_place _ _ _ g hg]
    rfl
  · rw [AtFullSide.K12.halfO_place _ _ g hg]
    rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the prover that onlineProverFromPublicFiles makes of the wide filling: every kind but K12 pays in the shared
chain.** -/
theorem kindPays_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    (κ : KindName) (hκ : κ ≠ .K12) :
    KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder A.H.shared κ := by
  rw [base_shared h I o' S O hA]
  exact kindPays_beside h hA (planData (qAt Zp Np)) rfl 0 _ _ _ κ
    fun g hg e => hκ (e.symm.trans (tests_kind I Zp g hg))

/-- **The same at the wide filling read through g and rd.** -/
theorem kindPays_through (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o' S O)) = .ok A)
    (κ : KindName) (hκ : κ ≠ .K12) :
    KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder A.H.shared κ := by
  rw [thru_shared h I g rd d' o' S O hA]
  refine kindPays_beside h hA (planData (qAt Zp Np)) rfl 0 _ _ _ κ fun y hy e => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
  exact hκ (e.symm.trans (tests_kind I Zp s hs))

/-- **Against emptiness, at the prover made of the wide filling**: each of the six sides stands at
the place of a sub-protocol of the shared chain, and a search of the prover's own list by that place
finds it. -/
theorem six_there_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A) :
    ∀ s ∈ proverSidesOfSharedRounds (planData (qAt Zp Np)) (I.weights Zp) ++
        proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ (I.weights Zp) (randNow (qAt Zp Np)),
      (∃ b ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, b.place = s.place) ∧
        A.H.shared.find? (fun q => q.place == s.place) = some s := by
  intro s hs
  rw [base_shared h I o' S O hA]
  exact ⟨six_blocks_there h.toAtMg _ _ _ _ s hs, six_found _ _ _ _ _ s hs⟩

/-- **The same at the wide filling read through g and rd**, at the readers composed with g and
rd. -/
theorem six_there_through (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o' S O)) = .ok A) :
    ∀ s ∈ proverSidesOfSharedRounds (planData (qAt Zp Np)) (I.weights Zp ∘ g) ++
        proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ (I.weights Zp ∘ g) (randNow (qAt Zp Np) ∘ rd),
      (∃ b ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, b.place = s.place) ∧
        A.H.shared.find? (fun q => q.place == s.place) = some s := by
  intro s hs
  rw [thru_shared h I g rd d' o' S O hA]
  exact ⟨six_blocks_there h.toAtMg _ _ _ _ s hs, six_found _ _ _ _ _ s hs⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.tests_kind
#print axioms AtFullSide.K14.kindPays_at_base
#print axioms AtFullSide.K14.kindPays_through
#print axioms AtFullSide.K14.six_there_at_base
#print axioms AtFullSide.K14.six_there_through
