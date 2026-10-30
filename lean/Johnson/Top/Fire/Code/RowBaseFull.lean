-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowBaseFull.lean: THE KEY FILE's ROW 1.17: «the piece's base at block 17 is st + 1» (Left117f's treeAt) FROM THREE EQUATIONS THAT OTHER FILES HOLD IN THE GOALS' SCOPE: BY CALLS.
  before_sum     the rounds that the first n blocks declare are the sum of the first n of the blocks' numbers of rounds (glue on «before»)
  base17_at      the maker's base at block 17 of the first chain is the number of trees that the first 18,848 rounds' data send: cutBase_held · cutBase_eq, at the written list of the blocks' numbers of rounds
  treeAt_full    **PROVED**: FROM q₁ · hL («the blocks' numbers of declared rounds are the written list»: rounds_in_scope) · hD («the record's data are the written data»: pin_at_seat over laid_data_written) · h1 («the ranges are the written key's»: five_in_scope): the base at 17 = (oneAt X).ranges.stages.length + 1: BY THE TWO KERNEL FACTS five_written (the first 18,848 rounds' written data send five trees) · stages_full (four stages): CALLED

Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowBase
import Johnson.RunOne.KeySeatScopeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyLetters (roundsL₁ five_written)

theorem before_sum {S Cl : Type} : ∀ (l : List (Block S Cl)) (b : Block S Cl) (n : ℕ), before b l n = (((b :: l).map (·.rounds.length)).take n).sum
  | _, _, 0 => by simp [before]
  | [], b, n + 1 => by simp [before]
  | b' :: l, b, n + 1 => by
    have ih := before_sum l b' n
    show b.rounds.length + before b' l n = _
    rw [ih]
    simp

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))

theorem base17_at (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hL : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) :
    (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) = nTrees ((DK.at frS.P.T.a).ds₁.take 18848) := by
  have hlen : 17 ≤ k₁.length := by
    have h := congrArg List.length hL
    rw [List.length_map, q₁] at h
    have h' : k₁.length + 1 = 19 := h
    omega
  rw [cutBase_held, cutBase_eq k₁ 17 0 _ c₁ hlen, before_sum, ← q₁, hL, Nat.zero_add]
  rfl

/-- **Left117f's treeAt.** -/
theorem treeAt_full (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hL : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = roundsL₁) (hD : DK.at frS.P.T.a = writtenKFull)
    (h1 : (oneAt X).ranges = keyFull.ranges.x) :
    (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) = (oneAt X).ranges.stages.length + 1 := by
  rw [base17_at X N P DK c₁ k₁ q₁ hL, hD, five_written, h1, Johnson.RunOne.KeyLetters.stages_full]

end

end LPFD

#print axioms LPFD.before_sum
#print axioms LPFD.base17_at
#print axioms LPFD.treeAt_full
