-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K14/SixSidesPay.lean: kind K14: at the full size, at the book of the honest prover that
onlineProverFromPublicFiles makes, each of the six sides that stand at the eight sub-protocols of the linear claim's
shared rounds "pays": the frame's set-up routine chainSteps returns at the sub-protocol at the
side's place. Calls; no definition.

SidePays and KindPays are the forms of Honest/Law/ReadyOfSides.lean. SidePays B ch bs g: at each
member b of the list bs at g's place, in whatever list of sides g is the first found at that place,
at every view and every run's coins, chainSteps returns at [b]. KindPays B ch bs hs κ: every side of
hs whose place bears the kind κ pays. They feed one thing: that the frame's routine "ready" returns
(ready_of_sides, the same file; beneath it lies Honest/Law/ReadyOfParts.lean). Both forms are taken
here as that file states them; nothing here says that they are fit for that use (on what the file
says of itself: its head).

  six_sidePays        **each of the six sides pays**, at every pair of readers and at all types of
                      the sides: sidePays_of_tests at six_tests_at_made
                      (AtFullSide/K14/SixSidesLent.lean)
  kindPays_beside     **a kind κ pays at a list that holds the six sides and, behind them, sides of
                      which none stands at a place of the kind κ.** Four of the six stand at places
                      of the kind K14, the two sendings' at places of the kind K1. At every other κ
                      the statement holds for want of a side of that kind
  kindPays_K14_shared, kindPays_K1_shared   that at these two kinds

Not empty: six_at_places, six_blocks_there and six_found (SixSidesLent.lean): at the full size the
sides are six, each stands at the place of a sub-protocol of the shared chain, and a search of the
list by that place finds it.

Limits.
  * The premises h and hA, as in AtFullSide/K14/SixSidesLent.lean: hypotheses, not shown here.
  * "It pays" says that the set-up returns. It says nothing on whether a part plays, a round is
    reached or a verifier accepts.
  * WHICH SIDES A PROVER's LIST HOLDS IS NOT SAID HERE. kindPays_beside takes the list in the form
    "the six, then others" and a premise on the others' places. Whoever names a prover shows both.
  * THE SHARED CHAIN ALONE (chain number 1, counted from 0). In the first chain other sides stand at
    places of the kind K1: nothing is said of them.
  * Where sides of the kind κ stand behind the six, nothing follows at κ: so at the proximity tests'
    kind K12.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.K14.SixSidesLent
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Chain KindName)
open P5J (TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {W₁ Rc₁ Ky₁ X₁ : Type}

/-- **Each of the six sides pays.** Dt, hS, a: as in six_tests_at_made. -/
theorem six_sidePays (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (Dt : Data)
    (hS : Dt.S = (qAt Zp Np).S) (a : Nat) (weights : W₁ → Weights) (rand : Rc₁ → TableRand) :
    ∀ g ∈ (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings ⟨qAt Zp Np, a⟩ weights rand :
        List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)),
      SidePays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder g :=
  fun g hg => sidePays_of_tests _ _ _ g (six_tests_at_made h hA Dt hS a weights rand g hg)

/-- **A kind pays, in the shared chain, at a list that holds the six sides and, behind them, sides
of which none stands at a place of that kind.** -/
theorem kindPays_beside (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (Dt : Data)
    (hS : Dt.S = (qAt Zp Np).S) (a : Nat) (weights : W₁ → Weights) (rand : Rc₁ → TableRand)
    (rest : List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)) (κ : KindName)
    (hr : ∀ g ∈ rest, g.place.kind ≠ κ) :
    KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings ⟨qAt Zp Np, a⟩ weights rand ++ rest) κ := by
  intro g hg hk
  rcases List.mem_append.1 hg with hg | hg
  · exact six_sidePays h hA Dt hS a weights rand g hg
  · exact absurd hk (hr g hg)

/-- The kind K14 pays there, in the shared chain. -/
theorem kindPays_K14_shared (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (Dt : Data)
    (hS : Dt.S = (qAt Zp Np).S) (a : Nat) (weights : W₁ → Weights) (rand : Rc₁ → TableRand)
    (rest : List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁))
    (hr : ∀ g ∈ rest, g.place.kind ≠ .K14) :
    KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings ⟨qAt Zp Np, a⟩ weights rand ++ rest) .K14 :=
  kindPays_beside h hA Dt hS a weights rand rest .K14 hr

/-- The kind K1 pays there, in the shared chain: its sides in that chain are the two sendings'. -/
theorem kindPays_K1_shared (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (Dt : Data)
    (hS : Dt.S = (qAt Zp Np).S) (a : Nat) (weights : W₁ → Weights) (rand : Rc₁ → TableRand)
    (rest : List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁))
    (hr : ∀ g ∈ rest, g.place.kind ≠ .K1) :
    KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings ⟨qAt Zp Np, a⟩ weights rand ++ rest) .K1 :=
  kindPays_beside h hA Dt hS a weights rand rest .K1 hr

end AtFullSide.K14

#print axioms AtFullSide.K14.six_sidePays
#print axioms AtFullSide.K14.kindPays_beside
#print axioms AtFullSide.K14.kindPays_K14_shared
#print axioms AtFullSide.K14.kindPays_K1_shared
