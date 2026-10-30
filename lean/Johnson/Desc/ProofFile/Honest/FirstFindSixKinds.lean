-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FirstFindSixKinds.lean: the lemma of Honest/FirstFindPairs.lean at the
filling `nowFill` (Honest/AtPureSixKinds.lean), whose list has six lots, of the kinds K7, K11, K13, K3,
K5 and K6. At a place of one of these kinds, the prover's side that is found among the first chain's
sides of the prover that `onlineProverFromPublicFiles` returns is the one that is found in that kind's own lot. One
lemma; no definition.

  `now_first_find`   hypotheses: `onlineProverFromPublicFiles` returns `A` at `nowFill O`; for each of five lots, every
                     side of the lot is at a place of the lot's kind (`k11`, `k13`, `k3`, `k5`,
                     `k6`; for the sixth, `replyLot`, this is `replyLot_kind`); `q` is one of the
                     six pairs of a lot and its kind; the place is of that kind; `hg`: what the
                     lot's own list holds at the place

Limits.
  * The five hypotheses on the lots' kinds are for the caller to supply: each is a lemma of the
    authors of that kind's lot.
  * That `onlineProverFromPublicFiles` returns at any files, and what a lot's own list holds at the place, are
    hypotheses.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.FirstFindPairs
import Johnson.Desc.ProofFile.Honest.AtPureSixKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName)

theorem now_first_find {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {O : OnlineProverArguments}
    {A : OnlineProverWithDescription Weights IndexCommitterCoins Cells Unit Unit} (h : onlineProverFromPublicFiles o pol lay KL (nowFill O) = .ok A)
    (k11 : ∀ x ∈ (K11.headMergeLot O.claims id :
      HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G,
      x.place.kind = .K11)
    (k13 : ∀ x ∈ (K13.k13Lot id O.pile :
      HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G,
      x.place.kind = .K13)
    (k3 : ∀ x ∈ (K3.theLot id id O.req :
      HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G,
      x.place.kind = .K3)
    (k5 : ∀ x ∈ (K5.k5LotK id O.keyOf :
      HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G,
      x.place.kind = .K5)
    (k6 : ∀ x ∈ (K6.headLot K6.headFitsB (K6.headWit' id id) :
      HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G,
      x.place.kind = .K6)
    {q : HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit × KindName}
    (hq : q ∈ [(replyLot, KindName.K7), (K11.headMergeLot O.claims id, .K11),
      (K13.k13Lot id O.pile, .K13), (K3.theLot id id O.req, .K3), (K5.k5LotK id O.keyOf, .K5),
      (K6.headLot K6.headFitsB (K6.headWit' id id), .K6)])
    {p : Place} (hp : p.kind = q.2)
    {g : Placed (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit}
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g := by
  have hn : ([KindName.K7, .K11, .K13, .K3, .K5, .K6] : List KindName).Nodup := by decide
  refine atPure_first_find_pairs h (by rfl) (fun r hr => ?_) (by exact hn) hq hp hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact replyLot_kind A.Z A.G
  · exact k11
  · exact k13
  · exact k3
  · exact k5
  · exact k6

end ProofFile.Honest

#print axioms ProofFile.Honest.now_first_find
