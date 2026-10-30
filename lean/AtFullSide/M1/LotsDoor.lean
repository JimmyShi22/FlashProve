-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsDoor.lean: the rule's door on the book at K1's senders, from the kernel's facts at
the written entries. At a public part and ground whose first numbers are the library's, at a book
with the entries rawAheadW, at the written description's order of places: every spending entry whose
owner is a sender of the lots passes lotsOkB. It has the form of handIn_of_live's premise, at orderOf WP:
the term's order and book are for the caller (orderOf_alike, bookWhole_carried_guess).


How far. The door speaks at two owners, the opening and W's sender, and is idle at the fifty other
jobs: no spending entry has them as owner (owners_written). OwnersWritten lets every owner outside
parsW pass: the shared chain's two senders, the key file's and a copy's lie outside it and are not
tested here. The rows of a spender are not tied here to the term's own sides. Who meets scope, the
gate and the return: the callers' (base_returns, makerReturns, the side library's named files).

  okFast_congr       the form reads the book's entries alone
  find_place         where places are distinct, find? by a member's place returns that member
  lotAt_open, lotAt_w   what lotAt returns at the two senders
  OwnersWritten      the kernel's fact to ask: a spending entry with a lots' owner is at one of the two
  door_written       the door

Limits: the premises hO, hW, hK are kernel facts of other files; that the term's book has these
entries and this order is for the caller.
-/
import AtFullSide.M1.LotsForm
import Johnson.HB.LLHARD.PlanAtQFull
import Johnson.SendSim.Seat.ReadsAtWritten
import Johnson.SendSim.Seat.LotPlaces
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K14 AtFullSide.K14
open OnBytes OnBytes.Params OnBytes.SendSim.At OnBytes.SendSim.Seat
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K1 (qFull LikeFull firstPar parW)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull)

theorem okFast_congr {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option Ride} {B B' : ProverCoinCounts}
    {ord : List Place} {o : Addr} (h : B.ahead = B'.ahead) :
    okFast P ride B ord o = okFast P ride B' ord o := by
  simp only [okFast, ownerSp, spendsOf, withinB, spenderFitsB, apartAt, spentApartB, ProverCoinCounts.spentBy,
    ProverCoinCounts.knownBy, h]

theorem find_place {R : Type} : ∀ {L : List (VerifiableInference.Desc.K1.Par × R)},
    (L.map (·.1.place)).Nodup → ∀ {x}, x ∈ L →
      L.find? (fun y => y.1.place == x.1.place) = some x
  | [], _, _, hx => by cases hx
  | a :: L, nd, x, hx => by
    rw [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp
    · have hne : a.1.place ≠ x.1.place := fun h =>
        nd.1 (by rw [h]; exact List.mem_map.2 ⟨x, hx', rfl⟩)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find_place nd.2 hx'

theorem lotAt_open {Z : ProofFile.Pub} {G : ProofFile.Ground} (hG : LikeFull G.first)
    (hg : VerifiableInference.Desc.K1.gpOf Z = gpFull) :
    lotAt Z G oOpen = some (firstPar qFull gpFull, rideOf (firstFold qFull)) := by
  have e : lotPars Z G = (firstPar G.first (VerifiableInference.Desc.K1.gpOf Z),
      rideOf (firstFold G.first)) :: ((laterPars Z G).map fun P => (P, rideOf none)) ++
      ((linMessageW Z.first.lin).map fun msg =>
        (parW Z.first (wGp Z) 4 msg, rideOf (wFold Z.first.lin))).toList := rfl
  unfold lotAt
  rw [if_pos (show (oOpen.part == 0) = true from rfl), e, List.cons_append, List.find?_cons_of_pos]
  · rw [VerifiableInference.Desc.K1.firstPar_full hG, hg, firstFold_shape (q' := qFull) hG.shape]
  · rfl

theorem lotAt_w {Z : ProofFile.Pub} {G : ProofFile.Ground} (hZ : LikeFull Z.first)
    (hg : VerifiableInference.Desc.K1.gpOf Z = gpFull) :
    lotAt Z G oW = some (parW qFull gpFull 4 wMsgFull, rideOf (wFold qFull.lin)) := by
  have hw : wGp Z = gpFull := hg
  have hm : linMessageW Z.first.lin = some wMsgFull :=
    (VerifiableInference.Desc.K1.wMsg_full hZ).trans VerifiableInference.Desc.K13.Law.wMsg_written
  have hx : (parW Z.first (wGp Z) 4 wMsgFull, rideOf (wFold Z.first.lin)) ∈ lotPars Z G := by
    unfold lotPars
    rw [hm]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have nd : ((lotPars Z G).map (·.1.place)).Nodup := of_decide_eq_true (lotPlacesApart Z G)
  have h := find_place nd hx
  unfold lotAt
  rw [if_pos (show (oW.part == 0) = true from rfl)]
  have e2 : (fun x : VerifiableInference.Desc.K1.Par × (Nat → Option Ride) => x.1.place == oW.place) =
      fun y => y.1.place == (parW Z.first (wGp Z) 4 wMsgFull, rideOf (wFold Z.first.lin)).1.place := rfl
  rw [e2, h, VerifiableInference.Desc.K1.parW_full hZ, hw, hZ.lin]
  rfl

/-- A spending entry with a lots' owner stands at one of the two senders. -/
def OwnersWritten : Prop :=
  (rawAheadW.all fun e => !e.once || e.owner == oOpen || e.owner == oW ||
    !(e.owner.part == 0 && parsW.any fun P => P.place == e.owner.place)) = true

/-- **THE DOOR.** -/
theorem door_written {Z : ProofFile.Pub} {G : ProofFile.Ground} (hG : LikeFull G.first) (hZ : LikeFull Z.first)
    (hg : VerifiableInference.Desc.K1.gpOf Z = gpFull)
    (hv : (G.built.toList.zipIdx.map fun x => (x.2, Johnson.AtFull.Desc.K1Lot.segView G x)) =
      Johnson.AtFull.Desc.K1Lot.viewW)
    (hO : okFast (firstPar qFull gpFull) (rideOf (firstFold qFull)) aheadBook (orderOf WP) oOpen = true)
    (hW : okFast (parW qFull gpFull 4 wMsgFull) (rideOf (wFold qFull.lin)) aheadBook (orderOf WP) oW =
      true)
    (hK : OwnersWritten) (Bk : ProverCoinCounts) (hA : Bk.ahead = rawAheadW) :
    ∀ e ∈ Bk.ahead, e.once = true → lotsMine Z G e.owner = true →
      lotsOkB Z G Bk (orderOf WP) e.owner = true := by
  intro e he ho hm
  rw [hA] at he
  have h1 := List.all_eq_true.1 hK e he
  simp only [ho, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  rcases h1 with (h | h) | h
  · rw [h]
    exact lotsOkB_of_okFast (lotPlacesApart Z G) (lotAt_open hG hg)
      ((okFast_congr (by rw [hA]; rfl)).trans hO)
  · rw [h]
    exact lotsOkB_of_okFast (lotPlacesApart Z G) (lotAt_w hZ hg)
      ((okFast_congr (by rw [hA]; rfl)).trans hW)
  · exfalso
    have hP := lotPars_written hG hZ hg hv
    unfold lotsMine lotAt at hm
    split_ifs at hm with h0
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hm
      have hmem := List.mem_of_find?_eq_some hx
      have hpl := List.find?_some hx
      have hany : (parsW.any fun P => P.place == e.owner.place) = true := by
        rw [← hP]
        exact List.any_eq_true.2 ⟨x.1, List.mem_map.2 ⟨x, hmem, rfl⟩, hpl⟩
      simp [hany, beq_iff_eq.1 h0] at h
    · simp at hm

end AtFullSide.M1

#print axioms AtFullSide.M1.door_written
