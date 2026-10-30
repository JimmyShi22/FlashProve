-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnSeat.lean: member 2 of the key file's last chain is the seat of the job of its own proximity test
(`jobKWAt`, E2E/KeyProverSideOfOwnTest.lean), and at a thread that stands at border 2 with the letter `saidLast` the seat's way in IS
that job's state on entry (`doorKW`): the twin at W of `seat_nine`, `enters_nine` (E2E/KeyDoorNine.lean).

Main names.
  `pre_key`: the blocks that `doorW` takes in front of the test are the chain's first two.
  `pre_rounds`: they have no round.
  `member_two`, `seat_own`: member 2, and that it is the job's seat.
  `enters_own`: the field `enters` of `K12Front`, from the pair.

What stays open. That a thread stands at border 2. The job's letters JI, JW, A, lift, ask stay letters: the door reads none
of them. No half is played here.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyProverSideOfOwnTest
import E2E.KeyLastSaid
import Johnson.ToldDescR.LastPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open ProofFile.Honest.K12 (SeatOf seatOf_inside frontOf)
open ProofFile.Honest.K12.Light (ManyJob doorW colsOpened enterOwn_returns)
open ProofFile.Honest.K12.AtProof (placeW idleT12)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource ownTest)
open AtPublicFiles.KeyLay (pWK doorKW jobKWAt)
open ProofFile.Honest.K14 (SendPub Ask)

variable (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)

/-- The place of the own test's block. -/
theorem own_place : (ownTest Pl : Block S₃ Unit).place = placeW := by
  show (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Pl.W) : Block T12 Unit).place = _
  exact (ToldDesc.k12_place _ _).trans (ToldDesc.p12At_place _ _)

/-- The places of the four members. -/
theorem places_last :
    (descriptionFromSource Xs Nr Pl).second.blocksInOrder.map (·.place) =
      [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, placeW, ⟨3, none, 3, .frame⟩] := by
  have e : (descriptionFromSource Xs Nr Pl).second.blocksInOrder.map (·.place) =
      [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩,
        { (ownTest Pl : Block S₃ Unit).place with chain := 3, link := none, piece := 2 },
        ⟨3, none, 3, .frame⟩] := rfl
  rw [e, own_place]
  rfl

/-- Four members at such places: `takeWhile` takes the first two. -/
theorem takeWhile_two {α : Type} (f : α → Place) (l : List α)
    (h : l.map f = [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, placeW, ⟨3, none, 3, .frame⟩]) :
    l.takeWhile (fun b => f b != placeW) = l.take 2 := by
  match l, h with
  | [a, b, c, d], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    obtain ⟨e0, e1, e2, -⟩ := h
    have n0 : (f a != placeW) = true := by
      rw [e0]
      decide
    have n1 : (f b != placeW) = true := by
      rw [e1]
      decide
    have n2 : (f c != placeW) = false := by
      rw [e2]
      decide
    simp only [List.takeWhile_cons, n0, n1, n2, if_true, Bool.false_eq_true, if_false, List.take]
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h

/-- **The blocks in front of the test.** -/
theorem pre_key : List.takeWhile
    (fun b : Block (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl => b.place != placeW)
    (descriptionFromSource Xs Nr Pl).second.blocksInOrder = (descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2 :=
  takeWhile_two (fun b : Block (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl => b.place) _ (places_last Xs Nr Pl)

/-- **They have no round.** -/
theorem pre_rounds : ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2).flatMap (·.rounds) = [] := rfl

section
variable {W₀ Rc Tr Y Wd : Type} (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub)
  (lift : Local W₀ Rc Xi Tr → Wd) (ask : Local W₀ Rc Xi Tr → Ask)

/-- **Member 2 is the job's seat.** -/
theorem seat_own :
    ∃ blk, (descriptionFromSource Xs Nr Pl).second.blocksInOrder[2]? = some blk ∧
      SeatOf blk (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest enterOwn leaveOwn := by
  have h := seatOf_inside (Cl := Unit) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest enterOwn leaveOwn
  refine ⟨_, rfl, ?_, h.rounds, h.oracles, h.decide⟩
  show { (ownTest Pl : Block S₃ Unit).place with chain := 3, link := none, piece := 2 } = (pWK Pl).place
  rw [own_place]
  exact (ToldDesc.p12At_place _ _).symm

variable {Bk : ProverCoinCounts} {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi}

/-- **At a stand of the pair at border 2 the seat's way in is the job's state on entry.** -/
theorem enters_own (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hft : T₃.ft = (descriptionFromSource Xs Nr Pl).lastChainFirstTreeNumber)
    (hfun : ∀ k w h s s', T₃.begun k w h s → T₃.begun k w h s' → s = s') {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) Y} {E : Env} (hT : Thr T₃ 2 k st m E)
    (hS : saidLast (descriptionFromSource Xs Nr Pl) T₃ 2 k m) :
    enterOwn st = .ok ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m)) := by
  obtain ⟨t, ht⟩ := enterOwn_returns st
  have e := door_of_said T₃ (List.takeWhile
      (fun b : Block (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl => b.place != placeW)
      (descriptionFromSource Xs Nr Pl).second.blocksInOrder)
    (by rw [hbs, pre_key]) (by rw [pre_key]; exact pre_rounds Xs Nr Pl) hft hfun enterOwn idleT12 hT hS ht
  have e' : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.rec₀ m.st.input (frontOf m) = t := e
  rw [e']
  exact ht

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.own_place
#print axioms AtPublicFiles.KeyLastChain.places_last
#print axioms AtPublicFiles.KeyLastChain.takeWhile_two
#print axioms AtPublicFiles.KeyLastChain.pre_key
#print axioms AtPublicFiles.KeyLastChain.pre_rounds
#print axioms AtPublicFiles.KeyLastChain.seat_own
#print axioms AtPublicFiles.KeyLastChain.enters_own
