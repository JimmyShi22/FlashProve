-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HalfAtWiderAll.lean: THE HALF AT THE PLACE OF THE OUTPUT HEAD's
OWN SUB-PROTOCOL (K6), AT THE PROVER THAT `onlineProverFromPublicFiles` RETURNS AT `widerFillAt`, WITH NO PREMISE ON THE
FILLING's LISTS. CONDITIONAL: THE TWO TOPS STAND UNDER h, (hG,) AND hA; THAT `onlineProverFromPublicFiles` RETURNS (hA)
STAYS A HYPOTHESIS. Three theorems, each one call.

What is here. The two tops of Honest/K6/Law/HalfAtWider.lean carry a premise ho: every list of the
filling has no side at a place of the kind K6, or has the sides of K6's list.
Honest/K6/Law/HalfAtWiderK.lean has ho from `WiderKinds`. Honest/Thread/FirstFillAll.lean (another
sub-protocol's authors') has `WiderKinds` with no premise (`FirstFill.widerKinds`). So ho falls.

  `ho_wider`            **ho, WITH NO PREMISE**: at every function in the earlier hash's stead,
                        public part and ground
  `k6_half_wider_all`   `k6_half_wider` without ho: under h, hG and hA
  `k6_half_wider_all'`  `k6_half_wider'` without ho: under h and hA, at the returned prover's own
                        ground

Limits.
  * THAT `onlineProverFromPublicFiles` RETURNS IS NOT SHOWN: hA stays a hypothesis of the two tops, WHICH MAY HOLD
    EMPTILY.
  * "No premise" is said of the statement of `ho_wider`: the lemmas beneath `FirstFill.widerKinds`
    stand in files of several sub-protocols' authors beside the library.
  * `ho_wider` speaks of the sides that a list holds: A LIST MAY HOLD NONE, and the first arm is
    then true for nothing.
  * The two tops: THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, as the hypothesis h.
  * All limits of Honest/K6/Law/HalfAtWider.lean hold here too.
  * Nothing on what the half sends. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.HalfAtWiderK
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PREMISE ho OF `k6_half_wider`, WITH NO PREMISE**: every list of the filling has no side at
a place of the kind K6, or has the sides of K6's list. -/
theorem ho_wider (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAt I o S O).lots,
      (∀ y ∈ M.halves Zq G, y.place.kind ≠ .K6) ∨
        M.halves Zq G = (headLot headFitsB (headWit' id (I.weights Zq)) :
          HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G :=
  ho_of_widerKinds (FirstFill.widerKinds I o S O Zq G)

/-- CONDITIONAL: the hypothesis h; hG; hA: `onlineProverFromPublicFiles` returns: we know of no proof of it.
**`k6_half_wider` WITHOUT ho.** -/
theorem k6_half_wider_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I OnBytes.secondHashFunction S O) = .ok A) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id (I.weights Zp) Zp G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ :=
  k6_half_wider h hG hA (ho_wider I OnBytes.secondHashFunction S O A.Z A.G)

/-- CONDITIONAL: the hypothesis h; hA. **The same without hG, at the returned prover's own
ground.** -/
theorem k6_half_wider_all' (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {I : WiderIn W₀}
    {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I OnBytes.secondHashFunction S O) = .ok A) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id (I.weights Zp) Zp A.G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ :=
  k6_half_wider' h hA (ho_wider I OnBytes.secondHashFunction S O A.Z A.G)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.ho_wider
#print axioms ProofFile.Honest.K6.k6_half_wider_all
#print axioms ProofFile.Honest.K6.k6_half_wider_all'
