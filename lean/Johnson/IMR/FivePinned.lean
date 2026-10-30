-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/FivePinned.lean: NUMBER 354 OF THE FIRST CHAIN's 358 SUB-PROTOCOLS: THE LAST PROXIMITY
TEST's FIVE SENDINGS ARE THE WRITTEN FIVE, WHERE THE TEST madeRow ACCEPTS AND THE SUB-PROTOCOL's OWN
TEST ON THE PLAN ACCEPTS. It pays the one equation h354 that Johnson/IMR/SendsPinned.lean leaves.

HOW. (1) K12.Coin.sendsFrom p j st reads of the place p its list idx alone (the numbers of each stage's two codes), through K12.stageAt: sendsFrom_idx. (2) Where H2U.placesOfMade returns, the first chain's place has as idx the codes' numbers of the sized proof's request.last, and as stages the sized proof's last.stages (places_idx, Johnson/Desc/K12/Law/Sizes/IdxAtScope.lean, and places_nums, Johnson/Desc/K12/Law/PlacesNums.lean): both are functions of the sized proof alone. (3) Where madeRow Z = true the sized proof is the written one (IM.pins). (4) Where the sub-protocol's test on the plan accepts, the place is not the empty one: so placesOfMade has returned, and the place has the numbers that it was made of (idx_of_planOk, nums_of_planOk). (5) ONE CLOSED EQUATION BY THE KERNEL: five_written.

WHAT IS SAID.
  sendsFrom_idx        what is sent is a function of idx and of the stages
  p12W · stagesW       the closed terms
  five_written         the closed equation · five_can_fail: from one stage later it is false
  place_of_planOk      where the test on the plan accepts: placesOfMade has returned, and idx and nums are its L's
  five_pinned          THE EQUATION h354
  sends_pinned_paid    so sendsAreB … = true under O, madeRow and that test on the plan

THE PREMISES, AND WHOSE EACH IS. hy : PlanWritten.madeRow Z = true: a test on the public files, as in Johnson/IMR/SendsPinned.lean · hp : the test on the plan of proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) accepts: the end of IM.hp_of_planOk (Johnson/IMR/SendsFinal.lean), to the letter. At every o. THE GOALS' SCOPE IS NOT ASKED.

What is not claimed. hy and hp are shown nowhere here. Nothing on what the sub-protocol's blocks send in a run. No soundness.

-/
import Johnson.IMR.SendsPinned
import Johnson.Desc.K12.Law.Sizes.IdxAtScope
import Johnson.Desc.K12.Law.PlacesNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (madeRow)
open ProofFile (Cl)

/-- **What the test sends is a function of the codes' numbers and of the stages.** -/
theorem sendsFrom_idx {p q : P12} (h : p.idx = q.idx) :
    ∀ (st : List Fmt.M1.Stage) (j : Nat), Coin.sendsFrom p j st = Coin.sendsFrom q j st
  | [], _ => rfl
  | nxt :: rest, j => by
    show Coin.sendAt p j nxt rest.isEmpty :: Coin.sendsFrom p (j + 1) rest =
      Coin.sendAt q j nxt rest.isEmpty :: Coin.sendsFrom q (j + 1) rest
    rw [sendsFrom_idx h rest (j + 1)]
    unfold Coin.sendAt stageAt
    rw [h]

/-- The place with the written sized proof's codes' numbers; of its other fields nothing is read. -/
def p12W : P12 := { H2U.noP12 ⟨1, none, 2, .K12⟩ with idx := H2K.Sizes.nosOf zW.request.last }

/-- The written sized proof's stages of the last test. -/
def stagesW : List Fmt.M1.Stage := zW.last.stages.map H2U.stageNums

/-- **The closed equation, by the kernel.** -/
theorem five_written : Coin.sendsFrom p12W 0 stagesW.tail = fiveW := by decide +kernel

/-- The equation can fail: counted from one stage later it is false. -/
theorem five_can_fail : ¬ (Coin.sendsFrom p12W 1 stagesW.tail = fiveW) := by decide +kernel

theorem five_len : fiveW.length = 5 := by decide +kernel

/-- Where the test on the plan accepts, the maker of the four places has returned, and the place has
its numbers. -/
theorem place_of_planOk (m : Johnson.G.OfPlan.Made)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade m) : Block T12 Unit).planOk = true) :
    ∃ N, H2U.placesOfMade m = .ok N ∧ (H2U.p12OfMade m).idx = N.L.idx ∧
      (H2U.p12OfMade m).nums = N.L.nums := by
  unfold H2U.p12OfMade at hp ⊢
  cases hN : H2U.placesOfMade m with
  | error e =>
    rw [hN] at hp
    exact absurd hp (by simp [proximityTestKind, H2U.noP12])
  | ok N =>
    rw [hN] at hp
    exact ⟨N, rfl, H2K.Sizes.idx_of_planOk _ _ hp, H2K.Made.nums_of_planOk _ _ hp⟩

/-- **THE EQUATION AT NUMBER 354.** -/
theorem five_pinned {Z : ProofFile.Pub} (hy : madeRow Z = true)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Block T12 Unit).planOk = true) :
    Coin.sendsFrom (H2U.p12OfMade Z.made) 0 (H2U.p12OfMade Z.made).nums.stages.tail = fiveW := by
  obtain ⟨N, hN, e1, e2⟩ := place_of_planOk Z.made hp
  have hz : Z.made.p.chains.made.sized.proof = zW := (pins hy).1
  have i1 : (H2U.p12OfMade Z.made).idx = p12W.idx := by
    rw [e1, (H2K.Sizes.places_idx Z.made N hN).1, hz]
    rfl
  have s1 : (H2U.p12OfMade Z.made).nums.stages = stagesW := by
    rw [e2, (H2K.Made.places_nums Z.made N hN).1.1, hz]
    rfl
  rw [s1, sendsFrom_idx i1]
  exact five_written

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The test sendsAreB accepts, where madeRow and the last proximity test's test on the plan
accept.** -/
theorem sends_pinned_paid (O : Open o pol lay KL F Z Bs base c A B) (hy : madeRow Z = true)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Block T12 Unit).planOk = true) :
    sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true :=
  sends_pinned O hy (five_pinned hy hp)

end IM

#print axioms IM.sendsFrom_idx
#print axioms IM.five_written
#print axioms IM.five_can_fail
#print axioms IM.five_len
#print axioms IM.place_of_planOk
#print axioms IM.five_pinned
#print axioms IM.sends_pinned_paid
