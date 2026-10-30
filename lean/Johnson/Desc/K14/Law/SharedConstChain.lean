-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstChain.lean: THE SHARED CHAIN's FORM, AS Sh.X_reached ASKS IT
(Johnson/Desc/K14/Law/SharedConstReached.lean: six premises on which sub-protocol stands at which
number of the list, each in the form in which its accepting step is spent), PAID AT THE LIST THAT
THE IOP AS WRITTEN IN LEAN ITSELF HOLDS: the shared chain's flat list, carried to the file's type of
claims (flat_retype_all, Johnson/Desc/K14/Law/SharedFlat.lean), each sub-protocol in the wrap
"below" (every word shown is below the prime).

  Sh.rowOf c … πA πB lst    the twelve, written out
  Sh.rowOf_is          it IS ((chainOf c Q [the two proximity tests] lst).retype).blocksInOrder.map below
  Sh.form_h0, form_h8, form_h9, form_h10, form_len      five of the six, at every lst
  Sh.last_same, Sh.form_h11     the sixth, at the shared chain's own end (K12.Seat.last): its
                       accepting decision returns its state
  Sh.X_reached_flat    **so Sh.X holds at every state that is reached along that list**, with no
                       premise on the chain's form
  Sh.X_reached_seat    **AT THE SEAT: RchAt₂ (seatF …) k a → Sh.X (planAt Z N (seatF …)) k a.1.2 =
                       true**: "reached" at the shared chain, with no premise on
                       the chain's form or on its first state
HOW. Carrying a sub-protocol to another type of claims (Block.retype) and laying "it states no run"
to its test on its parameters (bareOf) turn neither its decision nor its rounds: by unfolding.
WHAT IS NOT HERE. No law. The six facts on the two proximity tests' parameters at the seat. That
the places N name a second proximity test (N.O = some nO): a premise.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstReached
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.K14.Law.SharedFlat
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.Desc.First.Walk.Tied (Reach RchAt₂)

namespace Sh

variable {Cl : Type} (c : Model.Verify.Chains) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (πA πB : P12) (lst : List (Block St Unit) → Block St Unit)

/-- **The twelve, written out.** -/
def rowOf : List (Block St Cl) :=
  [below (frontOf c), below b1.retype, below b2.retype, below b3.retype, below b4.retype,
    below b5.retype, below b6.retype, below b7.retype, below b8.retype,
    below (bareOf (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit)).retype),
    below (bareOf (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)).retype),
    below (bareOf (lst ([b1, b2, b3, b4, b5, b6, b7, b8] ++
      [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
        Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)])).retype)]

/-- **It is the carried chain's flat list, in the wrap.** -/
theorem rowOf_is (Q : P14) (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (((chainOf c Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
      Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)] lst).retype (Cl' := Cl)).blocksInOrder.map below) =
      rowOf c b1 b2 b3 b4 b5 b6 b7 b8 πA πB lst := by
  rw [flat_retype_all c Q b1 b2 b3 b4 b5 b6 b7 b8 _ lst hbl]
  rfl

theorem form_len : (rowOf (Cl := Cl) c b1 b2 b3 b4 b5 b6 b7 b8 πA πB lst).length = 12 := rfl

theorem form_h0 : ∀ b, (rowOf (Cl := Cl) c b1 b2 b3 b4 b5 b6 b7 b8 πA πB lst)[0]? = some b →
    ∀ s rs gs s', b.decide s rs gs = .ok s' →
      ∃ c' : Model.Verify.Chains, (frontBlock c').decide s rs gs = .ok s' := by
  intro b hb s rs gs s' hd
  obtain rfl : below (frontOf c) = b := Option.some.inj hb
  exact ⟨c, (below_open _ s s' rs gs hd).2⟩

theorem form_h8 : ∀ i b, i < 8 →
    (rowOf (Cl := Cl) c b1 b2 b3 b4 b5 b6 b7 b8 πA πB lst)[i + 1]? = some b →
    ∃ (c' : Block St Cl) (b' : Block St Unit), [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b' ∧
      b = below c' ∧ DecidesAs c' b' ∧ c'.rounds = b'.rounds := by
  intro i b hi hb
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  · exact ⟨_, b1, rfl, (Option.some.inj hb).symm, retype_as b1, rfl⟩
  · exact ⟨_, b2, rfl, (Option.some.inj hb).symm, retype_as b2, rfl⟩
  · exact ⟨_, b3, rfl, (Option.some.inj hb).symm, retype_as b3, rfl⟩
  · exact ⟨_, b4, rfl, (Option.some.inj hb).symm, retype_as b4, rfl⟩
  · exact ⟨_, b5, rfl, (Option.some.inj hb).symm, retype_as b5, rfl⟩
  · exact ⟨_, b6, rfl, (Option.some.inj hb).symm, retype_as b6, rfl⟩
  · exact ⟨_, b7, rfl, (Option.some.inj hb).symm, retype_as b7, rfl⟩
  · exact ⟨_, b8, rfl, (Option.some.inj hb).symm, retype_as b8, rfl⟩

theorem form_h9 : ∀ b, (rowOf (Cl := Cl) c b1 b2 b3 b4 b5 b6 b7 b8 πA πB lst)[9]? = some b →
    ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit)).decide s rs gs = .ok s' := by
  intro b hb s rs gs s' hd
  obtain rfl := Option.some.inj hb
  exact (below_open _ s s' rs gs hd).2

theorem form_h10 : ∀ b, (rowOf (Cl := Cl) c b1 b2 b3 b4 b5 b6 b7 b8 πA πB lst)[10]? = some b →
    ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)).decide s rs gs = .ok s' := by
  intro b hb s rs gs s' hd
  obtain rfl := Option.some.inj hb
  exact (below_open _ s s' rs gs hd).2

/-- The shared chain's end returns its state. -/
theorem last_same (front : List (Block St Unit)) (s : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : St)
    (h : (VerifiableInference.Desc.K12.Seat.last front).decide s rs gs = .ok s') : s' = s := by
  unfold VerifiableInference.Desc.K12.Seat.last VerifiableInference.Desc.ChainEnd.chainEnd at h
  dsimp only at h
  revert h
  generalize VerifiableInference.Desc.ChainEnd.refuse _ = r
  intro h
  cases r with
  | error e => simp [Except.map] at h
  | ok u => simpa [Except.map, eq_comm] using h

theorem form_h11 : ∀ b, (rowOf (Cl := Cl) c b1 b2 b3 b4 b5 b6 b7 b8 πA πB
    VerifiableInference.Desc.K12.Seat.last)[11]? = some b →
    ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s := by
  intro b hb s rs gs s' hd
  obtain rfl := Option.some.inj hb
  exact last_same ([b1, b2, b3, b4, b5, b6, b7, b8] ++
    [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
      Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]) s rs gs s' (below_open _ s s' rs gs hd).2

/-- **Sh.X at every state that is reached along the IOP's own list**, from the named tests on the
parameters and six facts on the two proximity tests' parameters. -/
theorem X_reached_flat {Xi P : Type} (A : ShPlan Xi) (hT : Tests A) (heA : πA.early = true)
    (ha1A : πA.answers = 1) (hftA : πA.nums.firstTree = A.Q.par.toGPar.firstTree)
    (heB : πB.early = true) (ha1B : πB.answers = 1)
    (hftB : πB.nums.firstTree = A.Q.par.toGPar.firstTree) (start : P → St)
    (hst : ∀ z, ∃ key, start z = first A.Q.codes key) (ft k : ℕ) (a : P × St)
    (hR : Reach ft (((chainOf c A.Q [Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit),
      Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)]
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder.map below) start k a) :
    X A k a.2 = true := by
  rw [rowOf_is c (bk A 0) (bk A 1) (bk A 2) (bk A 3) (bk A 4) (bk A 5) (bk A 6) (bk A 7) πA πB _ A.Q
    (tests_hbl8 A hT)] at hR
  exact X_reached A (tests_hUw A hT) (tests_hS A hT) (bk A 0) (bk A 1) (bk A 2) (bk A 3) (bk A 4)
    (bk A 5) (bk A 6) (bk A 7) (tests_hbl8 A hT) (tests_hlU A hT) (tests_hlO A hT) (tests_hm A hT)
    (tests_hp8 A hT) (tests_hok A hT) (tests_hC2 A hT) (tests_hC5 A hT) (tests_pyU A hT)
    (tests_pyO A hT) (tests_pyS A hT) πA πB heA ha1A hftA heB ha1B hftB (tests_hl A hT)
    (tests_hsU A hT) _ start hst (form_h0 c _ _ _ _ _ _ _ _ πA πB _)
    (form_h8 c _ _ _ _ _ _ _ _ πA πB _) (form_h9 c _ _ _ _ _ _ _ _ πA πB _)
    (form_h10 c _ _ _ _ _ _ _ _ πA πB _) (form_h11 c _ _ _ _ _ _ _ _ πA πB)
    (form_len c _ _ _ _ _ _ _ _ πA πB _) (tests_hpS A hT) ft k a hR

/-! ## At the seat -/

/-- The seat's two proximity tests, where the places name the second. -/
theorem tests_two (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    VerifiableInference.Desc.K12.Seat.tests N =
      [Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Block T12 Unit),
        Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit)] := by
  unfold VerifiableInference.Desc.K12.Seat.tests
  rw [hO]
  rfl

/-- **Sh.X at every state of the shared chain that the verifier's own accepting steps reach.** -/
theorem X_reached_seat (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (hT : Tests (planAt Z N (seatF o Z N B' cF)))
    (heA : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).early = true)
    (ha1A : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).answers = 1)
    (hftA : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U).nums.firstTree =
      (planAt Z N (seatF o Z N B' cF)).Q.par.toGPar.firstTree)
    (heB : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true)
    (ha1B : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1)
    (hftB : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree =
      (planAt Z N (seatF o Z N B' cF)).Q.par.toGPar.firstTree)
    {Str : Type} (k : ℕ)
    (a : (((seatF o Z N B' cF).XiPub × (seatF o Z N B' cF).S₁) × (seatF o Z N B' cF).S₂) × Str)
    (hR : RchAt₂ (seatF o Z N B' cF) k a) :
    X (planAt Z N (seatF o Z N B' cF)) k a.1.2 = true := by
  have h1 : Reach 0 (((chainOf Z.p.chains (planAt Z N (seatF o Z N B' cF)).Q
      (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := ProofFile.Cl)).blocksInOrder.map below)
      (fun p : (seatF o Z N B' cF).XiPub × (seatF o Z N B' cF).S₁ =>
        (seatF o Z N B' cF).start₂ p.1) k a.1 := hR.1
  rw [tests_two N nO hO] at h1
  exact X_reached_flat Z.p.chains _ _ (planAt Z N (seatF o Z N B' cF)) hT heA ha1A hftA heB ha1B
    hftB _ (fun z => ⟨z.1.key, rfl⟩) 0 k a.1 h1

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.rowOf_is
#print axioms Desc.K14.Law.Sh.form_h8
#print axioms Desc.K14.Law.Sh.form_h11
#print axioms Desc.K14.Law.Sh.X_reached_flat
#print axioms Desc.K14.Law.Sh.X_reached_seat
