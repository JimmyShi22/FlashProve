-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfPlain.lean: the makers' tests on three lists of rounds (`okAt`,
OnBytes/Maker/Files.lean) from the record of a file's reading and what is left, in a third form:
`runFit` is brought down to `PlainRounds` of the first list.

Main names:
  `third_of_dry3`: the third list of the three dry runs is what the second chain's block states at
    made-up names.
  `LeftOf3`: what is left: nine fields. `okAt_of_read3`: the whole test.

The shared and the second chain's blocks note no opening with the mark "stored", at any start
(`plain_shared`, `plain_second`, OnBytes/Tie/Pv/Keeps/PlainOfBook.lean): so nothing has to be
carried from the reading's own third list.

Limits: `LeftOf3` is a premise, shown of no lists: at most two roots a message; the clauses on the
table of trees and on the labels' numbers; the two seals (kind, no item, no work); no other sealed
round; `storedFit`; two rounds in the first chain; `rowFitAt`. `OwnAlone R₁`, `PlainRounds R₁` and
`OwnBook` of the first chain's block are premises too. The lists are those of this reading's own
dry runs. Nothing on soundness.
-/
import OnBytes.Maker.OkOfTop
import OnBytes.Tie.Pv.Keeps.PlainOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK OnBytes.Tie.Pv.Keeps.Plain
open OnBytes.Three (tagChain rootsIn)
open OnBytes.Params (Rounds)

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- The third list of the three dry runs is what the second chain's block states at made-up
names. -/
theorem third_of_dry3
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    (secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (rootsIn R₂)))).rounds
      (secondStart p dry (tagChain 1 (rootsIn R₁))) = some R₃ := by
  unfold Three.dry3 at hd
  rw [T.shared_dry] at hd
  have hd' : (((secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (rootsIn R₂)))).rounds
    (secondStart p dry (tagChain 1 (rootsIn R₁)))).bind fun R₃ =>
      some (R₁, R₂, R₃)) = some (R₁, R₂, R₃) := hd
  cases hX : (secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (rootsIn R₂)))).rounds
      (secondStart p dry (tagChain 1 (rootsIn R₁))) with
  | none =>
    rw [hX] at hd'
    cases hd'
  | some Y =>
    rw [hX] at hd'
    have e : (R₁, R₂, Y) = (R₁, R₂, R₃) := Option.some.inj hd'
    rw [(Prod.mk.inj (Prod.mk.inj e).2).2]

/-- What of the makers' tests is not shown to follow from a reading: the third form. -/
structure LeftOf3 (a : ℕ) (R₁ R₂ R₃ : Rounds) : Prop where
  /-- no message has more than two roots: the format has no such bound -/
  few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ 2
  c3 : fits3 R₁ R₂ R₃ = true
  c4 : fits4 R₁ R₂ R₃ = true
  seal₁ : SealAt R₁
  seal₂ : SealAt R₂
  c6 : fits6 R₁ R₂ R₃ = true
  stored : storedFit a (Three.Whole.of R₁ R₂ R₃) = true
  /-- the first chain has a round beside its last -/
  two : 2 ≤ R₁.length
  row : rowFitAt a (Three.Whole.of R₁ R₂ R₃) = true

variable (a : ℕ)

/-- **The makers' tests pass at the lists of a file that was read, if what is left holds: the third
form.** `runFit` is brought down to pl₁: the shared and the second chain's blocks note no opening
with the mark "stored" at any start (OnBytes/Tie/Pv/Keeps/PlainOfBook.lean); of the first chain's
block the same is asked (pl₁). -/
theorem okAt_of_read3
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁) (pl₁ : PlainRounds R₁)
    (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (L : LeftOf3 a R₁ R₂ R₃) :
    okAt a (some (R₁, R₂, R₃)) = true := by
  have pl₂ : PlainRounds R₂ := plain_shared _ _ _ _ _ T.shared_dry
  have pl₃ : PlainRounds R₃ := plain_second _ _ _ _ _ (third_of_dry3 T R₃ hd)
  refine okAt_of_read2 a T hS₁ o₁ b₁ R₃ hd
    ⟨L.few, L.c3, L.c4, L.seal₁, L.seal₂, L.c6, L.stored, fun x hx => ?_, L.two, L.row⟩
  rcases List.mem_append.1 hx with h | h
  · exact pl₁ x h
  · rcases List.mem_append.1 h with h | h
    · exact pl₂ x h
    · exact pl₃ x h

end Read

end OnBytes.Maker

#print axioms OnBytes.Maker.okAt_of_read3
