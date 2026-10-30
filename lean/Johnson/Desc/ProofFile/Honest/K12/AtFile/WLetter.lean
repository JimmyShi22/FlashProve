-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WLetter.lean: `LetterAtW` (WAccepted.lean) at the library's
description: what the description's own text pays of the letters of the last chain's thread, at
number 2.

  `second_flat`    the description's last chain is its four blocks, each carried to the file's type of
                   claims
  `cut_at_F0T`     the blocks in front of the test are the list's first two
  `seat_at_W`      the third block is the kind's at its seat
  `sent_at_F0T`    the blocks in front declare no tree
  `front_at_F0T`   the rounds in front of the chain, at `lettersLast`
  `letter_at_W`    `LetterAtW` at `lettersLast`: what stays: the half at the place, the job's door, the
                   letter `taken`

By what. `last_blocks_in` (Johnson/ToldDescR/LastBlocks.lean); `retype_onOwn`
(Johnson/Flat/Last/RetypeK12.lean); `seatOf_inside` (K12/SaysYesSeat.lean); `cut_of_places` (WDoor.lean).

Limits. Facts on the description's text. Nothing on a run. Nothing on completeness, soundness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAccepted
import Johnson.ToldDescR.LastBlocks
import Johnson.ToldDescR.LastPlaces
import Johnson.Flat.Last.RetypeK12
import Johnson.Desc.ProofFile.Honest.Thread.LastHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart takenSources end₃)
open ProofFile.Honest.K12.AtProof (fourOf placeW p12At_place)
open ProofFile.Honest.K12.Light (ManyJob doorW)
open ProofFile.Honest.LastThread (lettersLast)
open ToldDesc (ownAt)
open P5J (F0T TS)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- **The description's last chain is these four blocks.** -/
theorem second_flat : (F0T o Zp Np cF).second.blocksInOrder =
    [batchLinearConstraintsSecondPart (ToldDesc.p14At Zp), takenSources (ownAt Np), ownAt Np,
      end₃ [batchLinearConstraintsSecondPart (ToldDesc.p14At Zp), takenSources (ownAt Np), ownAt Np]].map Block.retype :=
  ToldDesc.last_blocks_in o ProofFile.pureRoad.links Zp _ Np cF

/-- The third block stands at the test's place. -/
theorem ownAt_place_W : (ownAt Np).place = placeW := by
  show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt placeW Np.W) : Block T12 Unit).place = placeW
  exact (ToldDesc.k12_place _ _).trans (p12At_place _ _)

/-- **The blocks in front of the test are the list's first two.** -/
theorem cut_at_F0T : (F0T o Zp Np cF).second.blocksInOrder.take 2 =
    (F0T o Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW) := by
  refine cut_of_places _ ?_
  rw [second_flat]
  show [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, (ownAt Np).place, ⟨3, none, 3, .frame⟩] = _
  rw [ownAt_place_W]

/-- **The third block is the kind's at its seat.** -/
theorem seat_at_W {W X : Type} (J : TestJob W X) (hp : J.p = (fourOf Np).W) :
    SeatOf ((ownAt Np).retype : Block S₃ ProofFile.Cl) J enterOwn leaveOwn := by
  have k := seatOf_inside (Cl := ProofFile.Cl) J enterOwn leaveOwn
  rw [hp] at k
  have e := VerifiableInference.Desc.K12.retype_onOwn (Cl := Unit) (Cl' := ProofFile.Cl) guardedProximityTestParts
    (fourOf Np).W
  show SeatOf ((onOwn (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit)).retype : Block S₃ ProofFile.Cl) J
    enterOwn leaveOwn
  rw [e]
  exact k

/-- **The two blocks in front declare no tree.** -/
theorem sent_at_F0T : treesTo (F0T o Zp Np cF).second.blocksInOrder 2 = 0 := by
  rw [second_flat]
  rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop)
  (Kp : VerifiableInference.Desc.Place → S₃ → S₃ → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The rounds in front of the last chain, at the thread's letters.** -/
theorem front_at_F0T :
    (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.front =
      ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
        ((F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length := by
  show (declsTo (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length ++
    declsTo (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length).length = _
  unfold declsTo
  rw [List.length_append, List.take_length, List.take_length]

/-- **`LetterAtW` at the thread's letters**: the half at the place, the job's door and the letter
taken stay. A: the job, at the seated place. -/
theorem letter_at_W (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (hp : A.p = (fourOf Np).W)
    (hhalf : ((lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd
        Kp w).thread.hs.find? fun g => g.place == ((ownAt Np).retype : Block S₃ ProofFile.Cl).place) =
      some (proverSideOfProximityTest A.toRun.toTest :
        Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X).needsField)
    (hdoor : A.rec₀ = doorW (F0T OnBytes.secondHashFunction Zp Np cF) (·.x) enterOwn placeW
      ProofFile.Honest.K12.AtProof.idleT12)
    (ht : taken = takenLast) :
    LetterAtW (F0T OnBytes.secondHashFunction Zp Np cF)
      (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
        w).thread 2 A enterOwn leaveOwn ((ownAt Np).retype : Block S₃ ProofFile.Cl)
      ProofFile.Honest.K12.AtProof.idleT12 where
  member := by
    show (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder[2]? = _
    rw [second_flat]
    rfl
  seat := seat_at_W Np A.toRun.toTest hp
  half := hhalf
  door := hdoor
  ft := rfl
  front := front_at_F0T Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w
  cut := cut_at_F0T OnBytes.secondHashFunction Zp Np cF
  taken := ht
  sent := sent_at_F0T OnBytes.secondHashFunction Zp Np cF
  returns := fun _ => ⟨_, rfl⟩
  leaves := fun _ _ => ⟨_, rfl⟩

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.second_flat
#print axioms ProofFile.Honest.K12.AtFile.ownAt_place_W
#print axioms ProofFile.Honest.K12.AtFile.cut_at_F0T
#print axioms ProofFile.Honest.K12.AtFile.seat_at_W
#print axioms ProofFile.Honest.K12.AtFile.sent_at_F0T
#print axioms ProofFile.Honest.K12.AtFile.front_at_F0T
#print axioms ProofFile.Honest.K12.AtFile.letter_at_W
