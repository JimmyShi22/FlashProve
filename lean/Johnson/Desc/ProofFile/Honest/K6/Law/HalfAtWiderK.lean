-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HalfAtWiderK.lean: THE HALF AT THE PLACE OF THE OUTPUT HEAD's
OWN SUB-PROTOCOL (K6), AT THE PROVER THAT `onlineProverFromPublicFiles` RETURNS AT `widerFillAt`, WITH `WiderKinds` IN
THE STEAD OF THE PREMISE ON THE OTHER LISTS' KINDS. CONDITIONAL. Three theorems.

What is here. The two tops of Honest/K6/Law/HalfAtWider.lean carry a premise ho: every list of the
filling has no side at a place of the kind K6, or has the sides of K6's list.
Honest/Thread/FirstFill.lean (another sub-protocol's authors') states `WiderKinds`: nine fields, a
list each: every side of the list stands at a place of the list's kind. That gives ho.

  `ho_of_widerKinds`    **`WiderKinds` gives ho**: GENERAL: no hypothesis on the first chain; at
                        every function in the earlier hash's stead, public part and ground
  `k6_half_wider_K`     `k6_half_wider` with `WiderKinds` in ho's stead
  `k6_half_wider_K'`    `k6_half_wider'` likewise, at the returned prover's own ground

The road of `ho_of_widerKinds`. The filling's lists are the first column of `widerPairs`
(`widerFillAt_lots`). A pair whose kind is K6 is the ninth, since no kind is listed twice
(`widerPairs_nodup`): its list's sides are K6's list's (`HLot.byPub_halves`). A pair of another kind
has, by `WiderKinds.all`, every side at a place of that kind.

Limits.
  * THAT `onlineProverFromPublicFiles` RETURNS IS NOT SHOWN: hA stays a hypothesis of the two tops, WHICH MAY HOLD
    EMPTILY.
  * `WiderKinds` STAYS A PREMISE HERE. `FirstFill.widerKinds` (Honest/Thread/FirstFillAll.lean)
    states it with no premise; that file is not imported here: it stands over files of several
    sub-protocols' authors; this file wants Honest/Thread/FirstFill.lean alone of that folder. The
    two tops without it, under h, (hG,) and hA alone: Honest/K6/Law/HalfAtWiderAll.lean.
  * The two tops: THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, as the hypothesis h.
  * All limits of Honest/K6/Law/HalfAtWider.lean hold here too.
  * Nothing on what the half sends. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.HalfAtWider
import Johnson.Desc.ProofFile.Honest.Thread.FirstFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (KindName)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on K. **`WiderKinds` GIVES THE PREMISE ho OF `k6_half_wider`**: every list of the
filling has no side at a place of the kind K6, or has the sides of K6's list. -/
theorem ho_of_widerKinds {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {Zq : Pub} {G : Ground} (K : WiderKinds I o S O Zq G) :
    ∀ M ∈ (widerFillAt I o S O).lots,
      (∀ y ∈ M.halves Zq G, y.place.kind ≠ .K6) ∨
        M.halves Zq G = (headLot headFitsB (headWit' id (I.weights Zq)) :
          HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G := by
  intro M hM
  rw [widerFillAt_lots] at hM
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
  by_cases hk : q.2 = KindName.K6
  · right
    have h9 : (HLot.byPub I.weights (LongLots.plain o S O).k6, KindName.K6) ∈
        widerPairs I o S O :=
      .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
    obtain rfl : q = (HLot.byPub I.weights (LongLots.plain o S O).k6, KindName.K6) :=
      List.inj_on_of_nodup_map widerPairs_nodup hq h9 hk
    exact HLot.byPub_halves I.weights (LongLots.plain o S O).k6 Zq G
  · left
    intro y hy e
    exact hk ((K.all q hq y hy).symm.trans e)

/-- CONDITIONAL: the hypothesis h; hG; hA: `onlineProverFromPublicFiles` returns: we know of no proof of it; K.
**`k6_half_wider` WITH `WiderKinds` IN ho's STEAD.** -/
theorem k6_half_wider_K (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I OnBytes.secondHashFunction S O) = .ok A)
    (K : WiderKinds I OnBytes.secondHashFunction S O A.Z A.G) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id (I.weights Zp) Zp G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ :=
  k6_half_wider h hG hA (ho_of_widerKinds K)

/-- CONDITIONAL: the hypothesis h; hA; K. **The same without hG, at the returned prover's own
ground.** -/
theorem k6_half_wider_K' (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {I : WiderIn W₀}
    {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I OnBytes.secondHashFunction S O) = .ok A)
    (K : WiderKinds I OnBytes.secondHashFunction S O A.Z A.G) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id (I.weights Zp) Zp A.G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ :=
  k6_half_wider' h hA (ho_of_widerKinds K)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.ho_of_widerKinds
#print axioms ProofFile.Honest.K6.k6_half_wider_K
#print axioms ProofFile.Honest.K6.k6_half_wider_K'
