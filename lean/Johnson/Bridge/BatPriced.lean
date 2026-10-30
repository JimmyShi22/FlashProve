-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/BatPriced.lean: the batching in front of a proximity test, in numbers: from two tests
on natural numbers: the bound on lists that the batching's block asks of the first stage's tables,
at the smaller of the stage's two distances; and the round's error count, that bound times the
number of rows less one, is at most 2^-128 of the round's written verifier messages, without the
planner.

This file stands above Cb/Bridge/CodeListRSProved.lean through its imports, and so above the files
under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15). The statement on codes is not used in its own
proofs: the Johnson bound on lists is the library's theorem from the distance.
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Why. Another comparison for this round (`bat_share_joh`, OnBytes/Slice/PricedRound.lean) goes by
the planner's price and asks that the stage's distance be that of its main rows (`Sg.AsGroup`). A
test's first stage can be one at which the repeated mask code gives the distance
(Johnson/Bridge/MaskRuled.lean [not in this library]). Here the list is taken at `Sg.d`, whichever
code gives it.

Main names:
  `BatPlace`: a test's first stage, its radius, the number of rows that are batched.
  `BatPlace.cnt`: the Johnson bound's list times the number of rows less one: the number in
    `batErr` and `batErrR` (OnBytes/Slice/BatSem.lean, BatSemRec.lean) in front of the sampler's.
  `BatPlace.good`, `BatPlace.priced`: the tests.
  `BatPlace.listIn`: the lists of the stage's tables.
  `BatPlace.below`: the clause `RoundBelow` in a written round that is the format's «BAT» with
    that number of rows (`Fmt.M2.rBatN`).
  `BatPlace.Paid`, `BatPlace.paid`: both, from both tests.

Limits: NO PLACE IS WRITTEN HERE: that both tests say yes is shown of no place
(Johnson/Bridge/BatAtWritten.lean [not in this library] has thirty-eight). `priced` WITHOUT `good`
SAYS NOTHING: at a
radius that is not below the stage's Johnson radius `Sg.lstJ` is 0 by Lean's convention on division
(`listMax`, Cb/Gen/JohnsonList.lean), and `cnt` with it; so too at fewer than two rows. That the
round in front of a test is the format's «BAT» and no other is asked of the written round (`IsRd`
asks the whole entry, the name too). THAT THE COUNT IS A BLOCK's IS BY READING: no block is taken
off here. That a place's numbers are those of a file's plan is not said. No work is counted:
the round has none. No sum over rounds. Nothing on a verifier or a file.


-/
import Johnson.Bridge.FoldPriced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb Iop _root_.Run
open scoped ENNReal

/-- A test's first stage, its radius, and the number of rows that are batched. -/
structure BatPlace where
  s : Sg
  e : ℕ
  rows : ℕ

namespace BatPlace
variable (x : BatPlace)

/-- The count: the Johnson bound's list at the stage's distance, times the number of rows less
one. -/
def cnt : ℕ := x.s.lstJ x.e * (x.rows - 1)

/-- The test on sizes and radius. -/
def good : Bool := Johnson.Top.H.sizedB x.s && Johnson.Top.H.inJB x.s x.e

/-- The comparison of `below_of_num`. -/
def priced : Bool :=
  decide (x.cnt * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65))

variable {x}

/-- The lists of the stage's tables: the Johnson bound's, at the smaller of the two distances. -/
theorem listIn (h : x.good = true) : x.s.cIn.ListAt x.e (x.s.lstJ x.e) := by
  simp only [good, Bool.and_eq_true] at h
  exact Sg.listJ_of (Sg.fit_cIn (Johnson.Top.H.sized_of h.1))
    ⟨(Johnson.Top.H.inJ_of h.2).1, (Johnson.Top.H.inJ_of h.2).2⟩

/-- **The round's count is at most 2^-128 of its written verifier messages.** -/
theorem below (h : x.priced = true) {d : PQ.RD} (hd : IsRd d (Fmt.M2.rBatN x.rows)) :
    RoundBelow x.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_isOne _ (of_decide_eq_true h) hd (Nat.zero_le 64) rfl rfl rfl rfl rfl
    (by decide : Fmt.Kind.elems ≠ .seeds) (by decide : Fmt.Kind.elems ≠ .sealed)

/-- What is said of one place. -/
structure Paid (x : BatPlace) : Prop where
  /-- the lists of the stage's tables, which the batching's block asks -/
  listIn : x.s.cIn.ListAt x.e (x.s.lstJ x.e)
  /-- the round's count -/
  below : ∀ d : PQ.RD, IsRd d (Fmt.M2.rBatN x.rows) →
    RoundBelow x.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem paid (hg : x.good = true) (hp : x.priced = true) : x.Paid :=
  ⟨listIn hg, fun _ hd => below hp hd⟩

end BatPlace

end Johnson.Bridge

#print axioms Johnson.Bridge.BatPlace.listIn
#print axioms Johnson.Bridge.BatPlace.below
#print axioms Johnson.Bridge.BatPlace.paid
