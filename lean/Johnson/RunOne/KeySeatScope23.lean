-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatScope23.lean: THEOREMS. **The test on a seat finds no fault at the key file's three sampled messages of the shared chain: o_u at (6, 0) · o_omega at (7, 0) · o_sp at (8, 0), FROM SCOPE's EQUATIONS.**
OBJECT: seatFaultAt at the key file's own description, at the shapes Johnson.Top.H.shU | shO | shSp. USER: none yet (meant: other files' premises «what the description tells of the seat's tree» at these three seats, through seat_of_noFault). LETTERS: X N P · the tags.
THE PREMISES ARE OTHERS' CONCLUSIONS in scope: here they stand as equations: the planner's sized key is the written one · the description passes its test on the plan · its data are the written data · its first chain's blocks have the written numbers of rounds.
  told_bp          the shared chain's own eight blocks' telling does not read the list of what is fixed before the point
  parF | nums_k14 | nums_k14_no   by the kernel: at the written sizes they tell three trees: (24, 324, [(321, 0), (0, 3)]) · (22, 36, [(36, 0)]) · (13, 3, [(0, 3)]); a control
  told_shared      the shared chain's flat list tells first what these eight tell
  all_written | chain_last | first_tells_six   by the kernel: the written data's 18850 rounds send 6 trees: these are the rounds of the eighteen blocks in front of the seal (whose one round the data do not hold); the seal tells none, by its text; so the first chain tells six
  n345_scope       **the three seats**
What is not claimed. That scope's equations hold. Anything of the rider at (6, 1) (the first mask: a tenant without a sample) · of the trees that the proximity tests send · of the last chain's own messages. Nothing on soundness.

-/
import Johnson.RunOne.KeySeatScopeW2
import Johnson.Desc.Key.Chains23

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Sound (nTrees)
open Johnson.RunOne.Law.RoundsInFront (inFront)
open Johnson.Top.H (csKey shU shO shSp)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq sum_eq_sumE)
open Lk6.AtPlan (keyFull)

/-- The eight blocks' telling does not read the list of what is fixed before the point. -/
theorem told_bp (Q : _root_.Desc.K14.P14) (bp : List (ℕ × ℕ)) :
    (_root_.Desc.K14.blocksOr { Q with beforePoint := bp }).map (·.oracles) = (_root_.Desc.K14.blocksOr Q).map (·.oracles) := by
  unfold _root_.Desc.K14.blocksOr _root_.Desc.K14.blocks
  cases h : _root_.Desc.K14.withU Q.S with
  | none => simp [h]
  | some v =>
    simp [h]
    exact ⟨rfl, rfl⟩

theorem oraclesOf_of_map {S Cl S' Cl' : Type} (l : List (Block S Cl)) (l' : List (Block S' Cl')) (h : l.map (·.oracles) = l'.map (·.oracles)) :
    oraclesOf l = oraclesOf l' := by
  have e : ∀ {S Cl : Type} (l : List (Block S Cl)), oraclesOf l = (l.map (·.oracles)).flatMap fun o => o.flatMap id := by
    intro S Cl l
    unfold oraclesOf
    rw [List.flatMap_map]
  rw [e l, e l', h]

/-- The shared chain's parameters at the written sizes, nothing fixed before the point. -/
def parF : _root_.Desc.K14.P14 :=
  { set := keyFull.set, scope := if keyFull.once.lines.oneTime then .once else .shared, codes := keyFull.codes,
    S := keyFull.once.shape, item := 0, beforePoint := [] }

theorem nums_k14 : (oraclesOf (_root_.Desc.K14.blocksOr parF)).map numsOf =
    [(24, 324, [(321, 0), (0, 3)]), (22, 36, [(36, 0)]), (13, 3, [(0, 3)])] := by decide +kernel
theorem nums_k14_no : (oraclesOf (_root_.Desc.K14.blocksOr parF)).map numsOf ≠
    [(24, 324, [(322, 0), (0, 3)]), (22, 36, [(36, 0)]), (13, 3, [(0, 3)])] := by decide +kernel

/-- The shared chain's flat list tells first what its own eight blocks tell. -/
theorem told_shared (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) :
    ∃ R, oraclesOf (descriptionFromSource X N P).shared.blocksInOrder = oraclesOf (_root_.Desc.K14.blocksOr (sharedPar X.chains (beforeSharedPoint P))) ++ R := by
  refine ⟨oraclesOf (sharedTests P) ++ oraclesOf [VerifiableInference.Desc.K12.Seat.last (_root_.Desc.K14.blocksOr (sharedPar X.chains (beforeSharedPoint P)) ++ sharedTests P)], ?_⟩
  show oraclesOf ((sharedChain X.chains P).retype (Cl' := Claim)).blocksInOrder = _
  unfold Chain.blocksInOrder Chain.retype sharedChain
  simp only [oraclesOf, List.map_append, List.map_map, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.map_nil,
    List.append_nil, List.nil_append, List.flatMap_map, List.append_assoc]
  rfl

set_option maxRecDepth 1000000 in
theorem all_d : nTrees (dKeyFull.ds₁.take 18850) = 6 := by
  show ((dKeyFull.ds₁.take 18850).map (·.trees.length)).sum = 6
  rw [sum_eq_sumE]
  decide +kernel

theorem all_written : nTrees (writtenKFull.ds₁.take 18850) = 6 := by rw [writtenKFull_eq]; exact all_d

/-- A chain's flat list ends in its last block, whose telling is unturned. -/
theorem chain_last {S Cl : Type} (c : Chain S Cl) : ∃ (A : List (Block S Cl)) (e : Block S Cl), c.blocksInOrder = A ++ [e] ∧ e.oracles = c.last.oracles :=
  ⟨{ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } :: c.front.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
    c.links.flatMap Link.blocksInOrder ++ c.back.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }),
    { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }, rfl, rfl⟩

/-- The first chain tells six trees: the eighteen blocks in front of the seal tell six (the written data's 18850 rounds); the seal tells none (by its text). -/
theorem first_tells_six (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (descriptionFromSource X N P).planOk = true)
    (hD : (descriptionFromSource X N P).data "key file" = .ok writtenKFull) (hL : (descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) :
    (oraclesOf (descriptionFromSource X N P).first.blocksInOrder).length = 6 := by
  have i18 : inFront (descriptionFromSource X N P).first.blocksInOrder 18 = 18850 := (inFront_of _ _ hL 18).trans (by decide)
  have hlen : (descriptionFromSource X N P).first.blocksInOrder.length = 19 := by
    have := congrArg List.length hL
    rw [List.length_map] at this
    exact this
  have h := told_in_front _ _ _ hp hD 18 (by rw [i18, len_written])
  rw [i18, all_written] at h
  obtain ⟨A, e, hA, he⟩ := chain_last (descriptionFromSource X N P).first
  have hA18 : A.length = 18 := by
    have := congrArg List.length hA
    rw [hlen, List.length_append, List.length_singleton] at this
    omega
  have hseal : e.oracles.flatMap id = [] := by rw [he]; rfl
  rw [hA, List.take_left' hA18] at h
  rw [hA]
  unfold oraclesOf at h ⊢
  rw [List.flatMap_append, List.length_append, h, List.flatMap_singleton, hseal]
  rfl

/-- **The three seats of the shared chain, from scope's equations.** -/
theorem n345_scope (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hk : X.chains.made.sized.key = keyFull)
    (hp : (descriptionFromSource X N P).planOk = true) (hD : (descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (hL : (descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) (t3 t4 t5 : String) :
    seatFaultAt (descriptionFromSource X N P) csKey t3 shU 6 0 = none ∧ seatFaultAt (descriptionFromSource X N P) csKey t4 shO 7 0 = none ∧
      seatFaultAt (descriptionFromSource X N P) csKey t5 shSp 8 0 = none := by
  obtain ⟨R, hR⟩ := told_shared X N P
  have h6 := first_tells_six X N P hp hD hL
  have hpar : sharedPar X.chains (beforeSharedPoint P) = { parF with beforePoint := beforeSharedPoint P } := by
    unfold sharedPar parF
    rw [hk]
  have hT : (oraclesOf (_root_.Desc.K14.blocksOr (sharedPar X.chains (beforeSharedPoint P)))).map numsOf =
      [(24, 324, [(321, 0), (0, 3)]), (22, 36, [(36, 0)]), (13, 3, [(0, 3)])] := by
    rw [hpar, oraclesOf_of_map _ _ (told_bp parF (beforeSharedPoint P))]
    exact nums_k14
  have hnum : ∀ j, j < 3 → ((descriptionFromSource X N P).oracleAt (6 + j)).map numsOf =
      ([(24, 324, [(321, 0), (0, 3)]), (22, 36, [(36, 0)]), (13, 3, [(0, 3)])] : List (ℕ × ℕ × List (ℕ × ℕ)))[j]? := by
    intro j hj
    unfold FileDescription.oracleAt
    rw [← List.getElem?_map, hR]
    simp only [List.map_append, List.append_assoc, hT]
    rw [List.getElem?_append_right (by rw [List.length_map, h6]; omega), List.length_map, h6, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using hj)]
  refine ⟨?_, ?_, ?_⟩
  · exact noFault_of _ csKey t3 shU 6 0 24 324 321 0 [(321, 0), (0, 3)] (hnum 0 (by decide)) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noFault_of _ csKey t4 shO 7 0 22 36 36 0 [(36, 0)] (hnum 1 (by decide)) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noFault_of _ csKey t5 shSp 8 0 13 3 0 3 [(0, 3)] (hnum 2 (by decide)) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.told_bp
#print axioms Johnson.RunOne.KeyLetters.oraclesOf_of_map
#print axioms Johnson.RunOne.KeyLetters.nums_k14
#print axioms Johnson.RunOne.KeyLetters.nums_k14_no
#print axioms Johnson.RunOne.KeyLetters.told_shared
#print axioms Johnson.RunOne.KeyLetters.all_written
#print axioms Johnson.RunOne.KeyLetters.chain_last
#print axioms Johnson.RunOne.KeyLetters.first_tells_six
#print axioms Johnson.RunOne.KeyLetters.n345_scope
