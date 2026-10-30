-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HalfAtSixKinds.lean: WHICH HALF OF THE PROVER's STANDS AT THE PLACE
OF THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6), AT THE PROVER THAT `onlineProverFromPublicFiles` RETURNS AT THE FILLING
`nowFill` (Honest/AtPure.lean, Honest/AtPureSixKinds.lean), UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST
CHAIN.

WHAT IS HAD. `k6_half_now`: among that prover's halves of the first chain, the first that stands at
K6's place is this sub-protocol's row, at the reader `headWit' id id` of the small input and at the
library's own public numbers: the text of the premise `K6HalfAt` (Honest/K6/Law/SeatedAtHead.lean),
unfolded; that file is not imported here. `k6_half_now'`: the same without the premise hG, at the
returned prover's own ground. `headLot_one_half`: at the hypothesis' public part and ground the
lot's honest side lays one half, at K6's place, at every reader. `ground_at_blank`: the public
parameters of the ground that the maker of the IOP as written in Lean lays are the library's own:
THE LIBRARY's OWN LEMMA (`ProofFile.Law.blankBy_W`, Johnson/Desc/ProofFile/Law/MakerPublic.lean), under hG
alone.

WHAT IT IS NOT. hA, THAT `onlineProverFromPublicFiles` RETURNS AT THE HYPOTHESIS' THREE PUBLIC FILES, IS A HYPOTHESIS: NO
THEOREM ANYWHERE SHOWS IT: `k6_half_now` AND `k6_half_now'` MAY HOLD EMPTILY. It stands ONLY AT THE
FILLING's OWN LETTERS: W₀ is `Weights`, Rc is `IndexCommitterCoins`, Tr is `Cells`, X₀ and X are `Unit`, and both
shared readers are the identity. Four lemmas on the kinds of four other lots' places (k11, k13, k3,
k5) are named hypotheses, in the form in which `now_first_find` asks them: this file draws in none
of their files. That the filling's sixth lot is `headLot headFitsB (headWit' id id)` is taken as
`now_first_find`'s own list has it. NOTHING NEW IS REASONED: a joining of others' lemmas. Nothing on
what the half sends; nothing on any run. THE FULL SIZE ALONE. Nothing on any property.

WHO PAYS WHAT. That the prover's halves are the lots' halves at the hypothesis' own public part and
ground, and that no half of another lot stands at the place: `now_first_find`
(Honest/FirstFindSixKinds.lean) with `atPure_at_laid_ground` (Honest/AtHeadGround.lean) and
`headLot_kind_id` (Honest/K6/LotKind.lean). That the lot's own public test accepts:
`head_fits_at_ground`. That the lot lays its one half at K6's place, at the library's public
numbers: `head_lot_under_head` (both: Honest/K6/Law/RowsSeatedAtHead.lean). That there is a ground
under h: `head_ground_at_head` (Honest/K6/Law/RowsSeated.lean). OF THE HYPOTHESIS h these spend its
fields scope, reads and laid and its lemma `plans_written`: nothing of what `AtMgA` adds to `AtMg`.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.RowsSeatedAtHead
import Johnson.Desc.ProofFile.Honest.K6.LotKind
import Johnson.Desc.ProofFile.Honest.FirstFindSixKinds
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The ground's public parameters are the library's own**: the library's lemma
`ProofFile.Law.blankBy_W`, at its name `P5J.At.X` for that field. CONDITIONAL: hG: G is the ground that
the maker lays at the public part Zp. The hypothesis h is not asked. -/
theorem ground_at_blank {G : Ground} (hG : blankBy pureRoad.links Zp = some G) :
    G.W = P5J.At.X Zp :=
  ProofFile.Law.blankBy_W hG

/-- The lot's honest side lays just one half at that public part and ground: at K6's place.
CONDITIONAL: the hypothesis h; hG. -/
theorem headLot_one_half (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {W₀ Rc Tr X : Type}
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    (headLot (X := X) headFitsB wit).halves Zp G =
      [⟨IM.k6Place, headRow (wit Zp G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩] := by
  have hf : headFitsB Zp G = true := head_fits_at_ground h hG
  obtain ⟨hp, hpar⟩ := head_lot_under_head h hG
  unfold headLotPlaces at hp
  rw [if_pos hf] at hp
  obtain ⟨b, hb, hbp⟩ := List.map_eq_singleton_iff.1 hp
  have hbp' : b.place = IM.k6Place := hbp
  have e : (headLot (X := X) headFitsB wit).halves Zp G = (P4.k6Hear Zp G).map _ := if_pos hf
  rw [e, hb]
  show [(⟨b.place, headRow (wit Zp G) (headParAt G) b.place⟩ :
      Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)] = _
  rw [hbp', hpar]

/-- **THE HALF AT K6's PLACE, AT THE PROVER THAT `onlineProverFromPublicFiles` RETURNS AT `nowFill`.** CONDITIONAL: the
hypothesis h; hG; hA: `onlineProverFromPublicFiles` returns: SHOWN BY NO THEOREM; k11, k13, k3, k5: every half of four
other lots stands at a place of that lot's kind. -/
theorem k6_half_now (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {O : OnlineProverArguments}
    {A : OnlineProverWithDescription Weights IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (nowFill O) = .ok A)
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
      x.place.kind = .K5) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id id Zp G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ := by
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  refine now_first_find hA k11 k13 k3 k5 (headLot_kind_id A.Z A.G)
    (q := (headLot headFitsB (headWit' id id), .K6))
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) rfl ?_
  show ((headLot headFitsB (headWit' id id) :
      HLot (Local Weights IndexCommitterCoins Inst Cells) (Local Weights IndexCommitterCoins Inst Cells) Unit).halves A.Z
        A.G).find? (fun g => g.place == IM.k6Place) = _
  rw [eZ, eG, headLot_one_half h hG]
  exact List.find?_cons_of_pos (by simp)

/-- **The same without hG, at the returned prover's own ground**: under h there is such a ground
(`head_ground_at_head`), and hA pins it. CONDITIONAL: the hypothesis h; hA: SHOWN BY NO THEOREM;
k11, k13, k3, k5. -/
theorem k6_half_now' (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {O : OnlineProverArguments}
    {A : OnlineProverWithDescription Weights IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (nowFill O) = .ok A)
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
      x.place.kind = .K5) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id id Zp A.G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ := by
  obtain ⟨G, hG⟩ := head_ground_at_head h
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  rw [eG]
  exact k6_half_now h hG hA k11 k13 k3 k5

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.ground_at_blank
#print axioms ProofFile.Honest.K6.headLot_one_half
#print axioms ProofFile.Honest.K6.k6_half_now
#print axioms ProofFile.Honest.K6.k6_half_now'
