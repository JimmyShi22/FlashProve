-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/LocAtWritten.lean: the rounds «LOC» of a key file and a proof file, which draw
positions alone, at two sizes, as written numbers: the count (n - e - 1)^t of lists of t positions
among n that miss every one of e + 1 places is at most 2^-128 of the round's written verifier
messages, the bits of work counted, without the planner.

Arithmetic: no statement on codes is used in this file's own proofs. Through its imports the file
stands above Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Main names:
  `PosPlace`: the logarithm of the number of positions, the number of draws, a radius, the bits of
    work. `PosPlace.cnt`: the count. `PosPlace.priced`: the comparison of `below_of_num`.
  `PosPlace.below`: its yes gives the clause `RoundBelow` in every written round that draws these
    positions and nothing else with that work.
  `posFull`, `posSmall`: three places each: the key file's round on the table's columns; a round of
    a proof file's link (25 alike at full size, 5 at the small size); the proof file's round on the
    table's columns. `pos_priced`: all six pass. `pos_teeth`: with one draw less none does.
  `pos_ties`: which of the numerals equal numbers written elsewhere in this library.
  `LocPlacesPaid`, `locPlacesPaid`: THE STATEMENT.

Limits: THAT THE COUNT IS A BLOCK's IS NOT SAID HERE: by reading it is that of `ldLoc_know`
(Cb/Ld/LdSwitchLocProofs.lean) and of `LdLinP.errLoc` (Cb/Ld/LdLin.lean), each at its own letter for
the radius; that a block stands at the radius written here is not said (Cb/Ld/LdLin.lean has a
second regime, e' = d - eM - 1, where the count is another). THAT THESE NUMBERS ARE THOSE OF A
FILE's PLAN IS NOT PROVED HERE, and that they are rounds of the description of the protocol that a
verifier runs is open. By Lean the numerals are tied to typed numbers alone (`pos_ties`): the
tables' radii to `recordRadius` and `smallRecordRadius` (OnBytes/Params/RecordRound.lean,
RecordRoundSmall.lean), the links' length, draws and radius to the links' groups of
Johnson/Bridge/FoldAtWritten.lean; the tables' draws and lengths and all bits of work to nothing.
Draws, lengths and work were read off a print of the plans' entries «LOC» made by evaluating this
library's port of the planner at the public files that the head of Johnson/Bridge/BaseAtWritten.lean
names. Of the 128 bits, 32, 20 or 28 are proof of work. The tightest are the links' rounds: 128.27
bits at full size, 128.13 at the small size. The rounds «SEND seed» in front of the links' rounds
«LOC» (Fmt/M2Plan.lean, `linkRounds`) are not here. The entry file's round «LINK» is not here:
OnBytes/Slice/FullRecNum.lean and SmallRecNum.lean have it. No sum over rounds. Nothing on a
verifier or a file.

-/
import Johnson.Bridge.FoldAtWritten
import OnBytes.Params.RecordRound
import OnBytes.Params.RecordRoundSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb _root_.Run
open scoped ENNReal

/-- A round that draws positions alone: 2^a positions, t draws, a radius, the bits of work. -/
structure PosPlace where
  a : ℕ
  t : ℕ
  e : ℕ
  work : ℕ

namespace PosPlace
variable (x : PosPlace)

/-- The lists of t positions that miss every one of e + 1 places. -/
def cnt : ℕ := (2 ^ x.a - x.e - 1) ^ x.t

/-- The comparison of `below_of_num`; and positions have at most 64 bits. -/
def priced : Bool :=
  decide (x.cnt * 2 ^ 193 + 3 * (0 + 0) * (2 ^ x.a) ^ x.t ≤ (2 ^ x.a) ^ x.t * 2 ^ (x.work + 65)) &&
    decide (x.a ≤ 64)

variable {x}

/-- **The count against 2^-128**, in every written round that draws these positions and nothing
else, with that work. -/
theorem below (h : x.priced = true) (d : PQ.RD) (hE : d.entry.drawE = 0)
    (hZ : d.entry.drawNZ = 0) (hT : d.entry.trits = 0) (hL : d.entry.logN = x.a)
    (hP : d.entry.poss = x.t) (hW : d.entry.work = x.work) (hk1 : d.kind ≠ .seeds)
    (hk2 : d.kind ≠ .sealed) : RoundBelow x.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  unfold priced at h
  have h1 := of_decide_eq_true (Bool.and_eq_true_iff.1 h).1
  have h2 : x.a ≤ 64 := of_decide_eq_true (Bool.and_eq_true_iff.1 h).2
  exact LastPlace.below_pos x.cnt _ x.work (pow_pos (Nat.two_pow_pos _) _) h1 d (hL.le.trans h2) hE
    hZ hW (by rw [nVals_positions hE hZ hT hk1 hk2, hL, hP])

end PosPlace

/-- The rounds «LOC» at full size. -/
def posFull : List PosPlace := [
  -- key file, shared chain: the table's columns
  ⟨32, 62, 2852142980, 32⟩,
  -- proof file, first chain: a link's group
  ⟨23, 219, 2433820, 20⟩,
  -- proof file, shared chain: the table's columns
  ⟨32, 64, 2852142980, 28⟩]

/-- The rounds «LOC» at the small size. -/
def posSmall : List PosPlace := [
  -- key file, shared chain: the table's columns
  ⟨23, 51, 6137119, 32⟩,
  -- proof file, first chain: a link's group
  ⟨18, 218, 76267, 20⟩,
  -- proof file, shared chain: the table's columns
  ⟨23, 53, 6137119, 28⟩]

theorem pos_priced : ((posFull ++ posSmall).all fun x => x.priced) = true := by decide +kernel

/-- With one draw less every one of the six says no. -/
theorem pos_teeth :
    ((posFull ++ posSmall).all fun x => !({ x with t := x.t - 1 } : PosPlace).priced) = true := by
  decide +kernel

/-- The tables' radii are those of OnBytes/Params/; the links' places are made of the links'
groups of Johnson/Bridge/FoldAtWritten.lean (the first of each size), with 20 bits of work. -/
theorem pos_ties :
    ((posFull.map PosPlace.e).head? = some OnBytes.Params.recordRadius ∧
      (posFull.map PosPlace.e).getLast? = some OnBytes.Params.recordRadius ∧
      (posFull.drop 1).take 1 =
        ((foldFull.drop 18).take 1).map fun x => ⟨x.s.C.a, x.s.t, x.e, 20⟩) ∧
    ((posSmall.map PosPlace.e).head? = some OnBytes.Params.smallRecordRadius ∧
      (posSmall.map PosPlace.e).getLast? = some OnBytes.Params.smallRecordRadius ∧
      (posSmall.drop 1).take 1 =
        ((foldSmall.drop 11).take 1).map fun x => ⟨x.s.C.a, x.s.t, x.e, 20⟩) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **The rounds «LOC» against 2^-128, at the written numbers.** -/
def LocPlacesPaid : Prop :=
  ∀ x ∈ posFull ++ posSmall, ∀ d : PQ.RD, d.entry.drawE = 0 → d.entry.drawNZ = 0 →
    d.entry.trits = 0 → d.entry.logN = x.a → d.entry.poss = x.t → d.entry.work = x.work →
    d.kind ≠ .seeds → d.kind ≠ .sealed → RoundBelow x.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem locPlacesPaid : LocPlacesPaid := fun x hx d =>
  PosPlace.below (List.all_eq_true.1 pos_priced x hx) d

end Johnson.Bridge

#print axioms Johnson.Bridge.pos_priced
#print axioms Johnson.Bridge.locPlacesPaid
