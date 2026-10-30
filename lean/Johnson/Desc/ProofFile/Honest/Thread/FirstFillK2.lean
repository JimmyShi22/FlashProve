-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillK2.lean: CONDITIONAL: WHICH PROVER's SIDE STANDS AT A
PLACE OF THE CODE SWITCH (kind K2) IN THE PROVER THAT onlineProverFromPublicFiles RETURNS AT THE FILLING widerFillAt. One
definition, a name for a term of the list's own text; statements with their proofs. General in the
three public files that onlineProverFromPublicFiles reads.

  k2SideAt: a definition: the side that the code switch's list (K2.switchLot, Honest/K2/AtPlan.lean)
    lays at one of its places: the list's own text at one place, so that the side has a name.
    k2_halves holds it to the list by rfl: a turn of the list's text breaks that line, aloud
  k2_places_sub, k2_place_of_spot, k2_place_there: names that stand for the lemmas of the same
    spelling in ProofFile.Honest.SwitchPlaces (Honest/Thread/SwitchPlaces.lean; one line `export`): no
    declarations here
  k2_places_once_of, k2_places_once: CONDITIONAL: no place comes twice among the list's sides: on
    "none comes twice among the plan's places of the kind"; on an opening of the description's
    maker's return (IM.Open, Johnson/IMR/SeatOpen.lean), which pays that
  k2_find_at: CONDITIONAL on an opening: what the list holds at one of its places
  k2_half_wider: CONDITIONAL: A.H.first.find? (fun g => g.place == p.place) = some (k2SideAt
    (widerRows S A.Z A.G) (fun w => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) A.Z A.G p)
  k2_half_wider_there: CONDITIONAL on h, K and "the description that onlineProverFromPublicFiles returns passes its own
    test on the plan": at the prover that onlineProverFromPublicFiles returns the list has that place, and the side found
    there is the list's: so hp of k2_half_wider is not empty there

The premises of k2_half_wider. h: onlineProverFromPublicFiles returns A at the filling · K: WiderKinds at A's public part
and ground · hp: p is one of the list's places at these. NO PREMISE ON THE PLAN's PLACES: that none
of the kind comes twice is had from h: where onlineProverFromPublicFiles returns, the description's maker has returned,
and at every opening of such a return the addresses of the kind's table are apart
(H2K12.table_apart, H2K12.places_apart, Johnson/Loose/H2K12/SpotsAtAll.lean: at every function that
stands for the earlier hash; no premise on scope).

WHY IT HAS TO COME FROM THE MAKER's RETURN. By the text of spotsFrom
(Johnson/Desc/ProofFile/Places.lean) a table of steps with the heads "A0", "F", "A1", "F" would lay
two places without a segment's number and with the piece 1. That is a reading of the text: that the
statement fails at such a table is not proved here.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

The lemmas on the list are lemmas on other authors' list, typed here off its text. Where the list's
authors have the like in a file of their own, theirs is the one to keep and this one to strike.
Called: find_own_place (Honest/K5/Law/LotFindAt.lean), k2_kind (Honest/Thread/FirstFillKinds.lean),
wider_first_find (Honest/Thread/FirstFill.lean), atPure_ok (Honest/AtPureLaw.lean), IM.seat_open
(Johnson/IMR/SeatOpen.lean), H2K12.table_apart, H2K12.places_apart
(Johnson/Loose/H2K12/SpotsAtAll.lean), k2_places_sub, k2_place_there
(Honest/Thread/SwitchPlaces.lean).

Limits. Conditional. Neither h nor K is proved here (on WiderKinds see
Honest/Thread/FirstFillKinds.lean). The place is the list's own term p.place, no numeral; which
places the list has but for the one of k2_place_there is not said. That the description passes its
own test on the plan is a premise of k2_half_wider_there, and of k2_place_there, which it calls:
neither onlineProverFromPublicFiles's text (Honest/AtPure.lean) nor the description's maker's
(Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean) names that test. That a sub-protocol stands at the place is not
said here. What the side does is not said. THROUGH ITS IMPORTS THE FILE STANDS ABOVE THE FILES UNDER
ThirdParty/ (lean/LIMITS.md, L15): they come in with Johnson/Loose/H2K12/SpotsAtAll.lean alone, and
there with its import of Johnson/P5J/MgAtAll.lean alone, which that file's last section needs; the
two theorems of that file that are called here (places_apart, table_apart) stand in front of that
section. A fact on import lines, walked by a program: what the proofs spend was not walked. The
statements are about lists and places. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillKinds
import Johnson.Desc.ProofFile.Honest.K5.Law.LotFindAt
import Johnson.Desc.ProofFile.Honest.Thread.SwitchPlaces
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.IMR.PlanOkFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)

export ProofFile.Honest.SwitchPlaces (k2_places_sub k2_place_of_spot k2_place_there)

section
variable {W₀ Rc Xi Tr X : Type} (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
  (Z : Pub) (G : Ground)

/-- **The side that the code switch's list lays at one of its places**: the list's own text
(`K2.switchLot`, Honest/K2/AtPlan.lean) at one place. A definition, so that the side has a name;
`k2_halves` holds it to the list by rfl. -/
def k2SideAt (p : K2.SwitchPlace) : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  K2.switchHalf (K2.coreSender K2.freshTable) D readers (fun p D R heard k =>
    (K2.ownLaid D G.first.layout p ((K2.segmentsOf Z G).take p.link)).bind fun _ =>
      K2.closingFor K2.freshTable ((K2.segmentsOf Z G).take p.link) p.sizes.kept
        (K2.ownBy D R p.addrs
          (fun s m => ((((K2.segmentsOf Z G)[s]?).map (·.ownShapes (s == 0))).getD []).getD m {})
          heard)
        heard k) p

/-- The list's sides are these, one a place. -/
theorem k2_halves : (K2.switchLot (X := X) D readers).halves Z G =
    (K2.switchPlaces Z G).map (k2SideAt D readers Z G) := rfl

/-- The side stands at the place's own place. -/
theorem k2SideAt_place (p : K2.SwitchPlace) :
    (k2SideAt (X := X) D readers Z G p).place = p.place := rfl

/-- No place comes twice among the list's sides where none comes twice among the plan's places of
the kind. -/
theorem k2_places_once_of (hN : ((P1K2.purePlaces Z).map (·.place)).Nodup) :
    (((K2.switchLot (X := X) D readers).halves Z G).map (·.place)).Nodup := by
  rw [k2_halves, List.map_map]
  exact (k2_places_sub Z G).nodup hN

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- **No place comes twice among the sides of the code switch's list.** CONDITIONAL: the
description's maker has returned at the public part Z, opened in its letters. At every function that
stands for the earlier hash; no premise on scope; at every ground. -/
theorem k2_places_once (O : IM.Open o pol lay KL F Z Bs base c A B) :
    (((K2.switchLot (X := X) D readers).halves Z G).map (·.place)).Nodup :=
  k2_places_once_of D readers Z G (H2K12.places_apart (H2K12.table_apart O).1)

/-- **What the list holds at one of its places.** CONDITIONAL: as above; hp: p is one of the list's
places. -/
theorem k2_find_at (O : IM.Open o pol lay KL F Z Bs base c A B) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Z G) :
    ((K2.switchLot (X := X) D readers).halves Z G).find? (fun g => g.place == p.place) =
      some (k2SideAt D readers Z G p) :=
  K5.find_own_place (x := k2SideAt D readers Z G p) (List.mem_map.2 ⟨p, hp, rfl⟩)
    (k2_places_once D readers Z G O)

end

variable {W₀ : Type} {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE SIDE THAT IS FOUND AT A PLACE OF THE CODE SWITCH.** CONDITIONAL: onlineProverFromPublicFiles returns A at the
filling; WiderKinds at A's public part and ground; p is one of the list's places at these. -/
theorem k2_half_wider (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces A.Z A.G) :
    A.H.first.find? (fun g => g.place == p.place) =
      some (k2SideAt (widerRows S A.Z A.G)
        (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) A.Z A.G p) := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok h
  obtain ⟨Z', Bs, base, c, A', B', Op⟩ := IM.seat_open hF
  obtain rfl : Z' = A.Z := Except.ok.inj (Op.pub.symm.trans hZ)
  refine wider_first_find h K
    (q := (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
      K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩, .K2))
    (by
      unfold widerPairs
      exact .tail _ (.head _))
    (k2_kind (X := Unit) (widerRows S A.Z A.G)
      (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) A.Z A.G _
      (List.mem_map.2 ⟨p, hp, rfl⟩)) ?_
  exact k2_find_at (widerRows S A.Z A.G)
    (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) A.Z A.G Op hp

/-- **AT THE PROVER THAT onlineProverFromPublicFiles RETURNS THE LIST HAS A PLACE, AND WHICH SIDE IS FOUND THERE**: at
the first place behind the segments. CONDITIONAL: h; K; hF: the description that onlineProverFromPublicFiles returns
passes its own test on the plan. So hp of `k2_half_wider` is not empty there. -/
theorem k2_half_wider_there (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) (hF : A.F.planOk = true) :
    ∃ p ∈ K2.switchPlaces A.Z A.G, p.place = ⟨1, none, 1, .K2⟩ ∧
      A.H.first.find? (fun g => g.place == ⟨1, none, 1, .K2⟩) =
        some (k2SideAt (widerRows S A.Z A.G)
          (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) A.Z A.G
          p) := by
  obtain ⟨hZ, hG, hD, -⟩ := atPure_ok h
  obtain ⟨Z', Bs, base, c, A', B', Op⟩ := IM.seat_open hD
  obtain rfl : Z' = A.Z := Except.ok.inj (Op.pub.symm.trans hZ)
  have eG : Bs.G₀ = A.G := Option.some.inj (Op.blank.symm.trans hG)
  obtain ⟨p, hp, e⟩ := k2_place_there A.Z Op hF
  rw [eG] at hp
  refine ⟨p, hp, e, ?_⟩
  rw [← e]
  exact k2_half_wider h K hp

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.k2_halves
#print axioms ProofFile.Honest.FirstFill.k2SideAt_place
#print axioms ProofFile.Honest.FirstFill.k2_places_once_of
#print axioms ProofFile.Honest.FirstFill.k2_places_once
#print axioms ProofFile.Honest.FirstFill.k2_find_at
#print axioms ProofFile.Honest.FirstFill.k2_half_wider
#print axioms ProofFile.Honest.FirstFill.k2_half_wider_there
