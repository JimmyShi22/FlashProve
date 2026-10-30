-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatScopeW2.lean: THEOREMS. **The library's test on a seat finds no fault at the key file's third sampled message's seat (W's: tree 5, tenant 0), FROM SCOPE's EQUATIONS**; and the three seats' trees' numbers 0 · 1 · 5 as «the trees that the blocks in front tell».
OBJECT: seatFaultAt at the key file's own description. USER: none yet (meant: a premise of member_fk₁, Johnson/RunOne/KeyFillMeet.lean, a theorem on a member at the woven tables' reading; and one line that ties the hand-laid table of seats atSix, Johnson/RunOne/KeyFillBaseAt.lean, to the description). LETTERS: X N P · the tag. THE NUMBERS OF THE RANGES' TEST's PLACE (N) STAY A LETTER: the road never reads them.
THE PREMISES ARE OTHERS' CONCLUSIONS in scope, proved elsewhere (five_in_scope, Johnson/RunOne/Law/KeyInScope.lean · rounds_in_scope, Johnson/RunOne/Sound/KeyListsInScope.lean · laid_data_written, Johnson/Goal/Numbers/KeySeatLaidAt.lean · Key.laidFixed_is, Johnson/Desc/Key/SlotIs.lean; none imported here): here they stand as equations: the one-time chain's codes and shape are the written ones · the description passes its test on the plan · its data are the written data · its first chain's blocks have the written numbers of rounds.
  chain_tail     a chain whose back ends in w: its flat list ends in w and the chain's last block
  sendW_told     what W's sending tells: the sending kind's own telling
  flat₁ | oracleAt_flat₁   the first chain's flat list at its own types
  flat_tail      the two at the key file's first chain
  msgW_some | nums_w | nums_w_no   by the kernel: W's message is there; its tree's numbers are [(22, 12, [(3, 3), (0, 6)])]; a control
  front17        under the list of rounds: 17 blocks stand in front of W's sending, with 18848 rounds
  n2_scope       **the third seat**
  seats_scope    **the three seats' trees: the blocks in front of the three sendings tell 0 · 1 · 5 trees**
What is not claimed. That scope's equations hold. Anything on what is sent. Nothing on soundness.

-/
import Johnson.RunOne.KeySeatScopeW

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Sound (nTrees)
open Johnson.RunOne.Law.RoundsInFront (inFront)
open Johnson.Top.H (csKey)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)

/-- A chain whose back ends in w: its flat list ends in w and the chain's last block, as to what they tell. -/
theorem chain_tail {S Cl : Type} (c : Chain S Cl) (B : List (Block S Cl)) (w : Block S Cl) (h : c.back = B ++ [w]) :
    ∃ (A : List (Block S Cl)) (bw e : Block S Cl), c.blocksInOrder = A ++ [bw, e] ∧ bw.oracles = w.oracles := by
  refine ⟨{ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } :: c.front.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
    c.links.flatMap Link.blocksInOrder ++ B.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }), { w with planOk := w.planOk && w.hasNoClaimsAndNothingAfter },
    { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }, ?_, rfl⟩
  unfold Chain.blocksInOrder
  rw [h]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- What W's sending tells. -/
theorem sendW_told {β Cl : Type} (one : OneTime) (N : Pieces) (sent : ℕ) (g : List (List ℕ)) (msg : Array OracleNotice)
    (hm : linMessageW one.lin = some msg) :
    ∃ w : Block (ChainState β) Cl, sendW one N sent g = some w ∧
      w.oracles.flatMap id = (K1.oracles (sendingPar one N.w "W and what rides with it" msg g)).flatMap id := by
  unfold sendW
  rw [hm]
  exact ⟨_, rfl, rfl⟩

/-- The key file's first chain's flat list, at its own types (in the description they stand as the description's fields S₁ | Cl). -/
def flat₁ (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) : List (Block FirstState Claim) := (descriptionFromSource X N P).first.blocksInOrder

theorem oracleAt_flat₁ (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (j : ℕ) : (descriptionFromSource X N P).oracleAt j =
    (oraclesOf (flat₁ X N P) ++ oraclesOf (descriptionFromSource X N P).shared.blocksInOrder ++ oraclesOf (descriptionFromSource X N P).second.blocksInOrder)[j]? := rfl

/-- The key file's first chain ends in W's sending and the seal. -/
theorem flat_tail (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (msg : Array OracleNotice) (hm : linMessageW X.Y.k.oneTime.lin = some msg) :
    ∃ (A : List (Block FirstState Claim)) (g : List (List ℕ)) (bw e : Block FirstState Claim), flat₁ X N P = A ++ [bw, e] ∧
      bw.oracles.flatMap id = (K1.oracles (sendingPar X.Y.k.oneTime pieces.w "W and what rides with it" msg g)).flatMap id := by
  obtain ⟨w, hw, ht⟩ := sendW_told (β := LookupRecord) (Cl := Claim) X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) msg hm
  have hb : (descriptionFromSource X N P).first.back = [layRows X.Y.k.oneTime, rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N,
                       batchTableRows (·.keys) X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))] ++ [w] := by
    show _ ++ (sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))).toList = _
    rw [hw]
    rfl
  obtain ⟨A, bw, e, hA, ho⟩ := chain_tail _ _ w hb
  exact ⟨A, _, bw, e, hA, by rw [ho]; exact ht⟩

theorem some_getD {α : Type} (o : Option α) (d : α) (h : o.isSome = true) : o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl

theorem msgW_some : linMessageW keyFull.once.shape = some ((linMessageW keyFull.once.shape).getD #[]) :=
  some_getD _ _ (by decide +kernel)

theorem nums_w : ((K1.oracles (parAt ((linMessageW keyFull.once.shape).getD #[]))).flatMap id).map numsOf = [(22, 12, [(3, 3), (0, 6)])] := by decide +kernel
theorem nums_w_no : ((K1.oracles (parAt ((linMessageW keyFull.once.shape).getD #[]))).flatMap id).map numsOf ≠ [(22, 12, [(3, 3), (0, 7)])] := by decide +kernel

/-- The written numbers of rounds of the first chain's nineteen blocks. -/
def roundsL₁ : List ℕ := [2, 2, 0, 0, 9581, 0, 0, 0, 0, 0, 9220, 0, 0, 0, 0, 23, 20, 2, 1]

theorem inFront_of {S Cl : Type} (bs : List (Block S Cl)) (L : List ℕ) (h : bs.map (·.rounds.length) = L) (n : ℕ) : inFront bs n = (L.take n).sum := by
  unfold inFront
  rw [← h, List.map_take]

/-- **The trees that the blocks in front of the three sendings tell: 0 · 1 · 5.** -/
theorem seats_scope (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (descriptionFromSource X N P).planOk = true)
    (hD : (descriptionFromSource X N P).data "key file" = .ok writtenKFull) (hL : (descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) :
    (oraclesOf ((descriptionFromSource X N P).first.blocksInOrder.take 0)).length = 0 ∧ (oraclesOf ((descriptionFromSource X N P).first.blocksInOrder.take 1)).length = 1 ∧
      (oraclesOf ((descriptionFromSource X N P).first.blocksInOrder.take 17)).length = 5 := by
  have i1 : inFront (descriptionFromSource X N P).first.blocksInOrder 1 = 2 := (inFront_of _ _ hL 1).trans (by decide)
  have i17 : inFront (descriptionFromSource X N P).first.blocksInOrder 17 = 18848 := (inFront_of _ _ hL 17).trans (by decide)
  refine ⟨rfl, ?_, ?_⟩
  · rw [told_in_front _ _ _ hp hD 1 (by rw [i1, len_written]; decide), i1]
    exact one_written
  · rw [told_in_front _ _ _ hp hD 17 (by rw [i17, len_written]; decide), i17]
    exact five_written

/-- **The third sampled message's seat, from scope's equations.** -/
theorem n2_scope (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hc : X.Y.k.oneTime.codes = csKey)
    (hl : X.Y.k.oneTime.lin = keyFull.once.shape) (hp : (descriptionFromSource X N P).planOk = true)
    (hD : (descriptionFromSource X N P).data "key file" = .ok writtenKFull) (hL : (descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) (tag : String) :
    seatFaultAt (descriptionFromSource X N P) csKey tag Johnson.Top.H.shW 5 0 = none := by
  obtain ⟨A, g, bw, e, hA, hbw⟩ := flat_tail X N P ((linMessageW keyFull.once.shape).getD #[]) (by rw [hl]; exact msgW_some)
  have hlen : (flat₁ X N P).length = 19 := by
    have := congrArg List.length (show (flat₁ X N P).map (·.rounds.length) = roundsL₁ from hL)
    rw [List.length_map] at this
    exact this
  have hA17 : A.length = 17 := by
    rw [hA, List.length_append] at hlen
    simpa using hlen
  have h5 : (oraclesOf A).length = 5 := by
    have := (show (oraclesOf ((flat₁ X N P).take 17)).length = 5 from (seats_scope X N P hp hD hL).2.2)
    rwa [hA, List.take_left' hA17] at this
  have ew := (nums_eq (sendingPar X.Y.k.oneTime pieces.w "W and what rides with it" ((linMessageW keyFull.once.shape).getD #[]) g)
    (parAt ((linMessageW keyFull.once.shape).getD #[])) hc rfl).trans nums_w
  have hnum : ((descriptionFromSource X N P).oracleAt 5).map numsOf = some (22, 12, [(3, 3), (0, 6)]) := by
    rw [oracleAt_flat₁, ← List.getElem?_map, hA]
    have hs : oraclesOf (A ++ [bw, e]) = oraclesOf A ++ (bw.oracles.flatMap id ++ e.oracles.flatMap id) := by
      simp [oraclesOf, List.flatMap_append]
    rw [hs, hbw]
    simp only [List.map_append, List.append_assoc, ew]
    rw [List.getElem?_append_right (by rw [List.length_map, h5]), List.length_map, h5]
    rfl
  exact noFault_of _ csKey tag Johnson.Top.H.shW 5 0 22 12 3 3 [(3, 3), (0, 6)] hnum rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.chain_tail
#print axioms Johnson.RunOne.KeyLetters.sendW_told
#print axioms Johnson.RunOne.KeyLetters.flat_tail
#print axioms Johnson.RunOne.KeyLetters.msgW_some
#print axioms Johnson.RunOne.KeyLetters.nums_w
#print axioms Johnson.RunOne.KeyLetters.nums_w_no
#print axioms Johnson.RunOne.KeyLetters.seats_scope
#print axioms Johnson.RunOne.KeyLetters.n2_scope
