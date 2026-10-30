-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/GroupFit.lean: a stage of the proximity test beside a group of the planner.

The planner prices the rounds of a fold and of the base case by a group's sizes (`Params.GroupSize`,
OnBytes/Params/Group.lean). It reads a code as a length 2^logN and a number k (`Params.Word`,
OnBytes/Params/Distance.lean): for the main code, at its own length, the dimension less 1
(`wordOf`); for the mask code repeated to the main code's length, that number times the number of
copies (`repeated`). It takes the source `third` for a code where 3 times the number of errors is
below n - k. The theorems on the blocks speak of a stage (`Sg`, OnBytes/Slice/Stage.lean) with the
two distances `Sg.dC` and `Sg.dZ` (OnBytes/Slice/Numbers.lean). This file says when a stage and a
group have the same sizes (`Sg.FitsGroup`) and shows that then, for a stage whose sizes are in order
(`Sg.Sized`) and whose two codes each have a coefficient (`Sg.Pos`), n - k of the planner's two
words are the stage's two distances. So the counts by source of OnBytes/Slice/BlocksBySource.lean
split on the planner's own test (the mask code's, for a group that has a mask code).

Main definition: `Sg.FitsGroup`.
Main theorems.
 `Sg.FitsGroup.main_n`, `main_dist`   the main word has the length 2^a and n - k = dC.
 `Sg.FitsGroup.mask_n`, `mask_dist`   the repeated mask word has the length 2^a, a the main code's,
                    and n - k = dZ.
 `Sg.FitsGroup.cntC_eq`, `cntZ_eq`   the two counts, written with the planner's words.
 `Sg.FitsGroup.hasMask_iff`   the group has a mask code exactly if the stage's mask code has a
                    message.

Not claimed. Nothing on the planner's bounds, on its number of errors, on its error terms or on a
plan: all is in natural numbers, on sizes. That a stage of a file's plan fits the group that the
planner prices there is a hypothesis here. Of the six stages of the full-size example, against the
stages that the planner solves at that example's typed lines, it is not shown in this library; nor
is it shown from the codes that a program's stage names. A
group without a mask code fits only a stage whose mask code has no message. For such a group the
planner reads no mask word and has no mask term, while the blocks of
OnBytes/Slice/BlocksBySource.lean always have a mask row: `cntZ_eq` then speaks of a word that the
planner does not read. The fields `rows` and `maskRows` are read by no theorem here. The fields
`slots`, `rule` and `m` of a group, `overE` of its codes and t of a stage are tied to nothing.

-/
import OnBytes.Params.Group
import OnBytes.Slice.BlocksBySource

set_option autoImplicit false

namespace OnBytes.Slice
open Params (GroupSize wordOf repeated)

/-- **A stage and a group of the planner have the same sizes**: lengths, messages and random tails
of the two codes, and the numbers of row variables. -/
structure Sg.FitsGroup (s : Sg) (g : GroupSize) : Prop where
  mainLog : g.main.logN = s.C.a
  mainEll : g.main.ell = s.C.l
  mainR : g.main.r = s.C.r
  maskLog : g.mask.logN = s.Z.a
  maskEll : g.mask.ell = s.Z.l
  maskR : g.mask.r = s.Z.r
  rows : g.k = s.h + s.g
  maskRows : g.h = s.h

namespace Sg.FitsGroup
variable {s : Sg} {g : GroupSize}

/-- The k of the main code: the dimension less 1, if the code has a coefficient. -/
theorem main_k (f : s.FitsGroup g) (hp : s.Pos) : g.main.k = s.C.r + s.C.l - 1 := by
  have h0 : g.main.dim = s.C.l + s.C.r := by
    unfold Params.CodeSize.dim
    rw [f.mainEll, f.mainR]
  have h1 := hp.someC
  unfold Params.CodeSize.k
  rw [h0, if_neg (by simp; omega)]
  omega

/-- The k of the mask code: the dimension less 1, if the code has a coefficient. -/
theorem mask_k (f : s.FitsGroup g) (hp : s.Pos) : g.mask.k = s.Z.r + s.Z.l - 1 := by
  have h0 : g.mask.dim = s.Z.l + s.Z.r := by
    unfold Params.CodeSize.dim
    rw [f.maskEll, f.maskR]
  have h1 := hp.someZ
  unfold Params.CodeSize.k
  rw [h0, if_neg (by simp; omega)]
  omega

/-- The main word has the main code's length. -/
theorem main_n (f : s.FitsGroup g) : (wordOf g.main).n = 2 ^ s.C.a := by
  show 2 ^ g.main.logN = 2 ^ s.C.a
  rw [f.mainLog]

/-- For the main word n - k is the main code's distance. -/
theorem main_dist (f : s.FitsGroup g) (hs : s.Sized) (hp : s.Pos) :
    (wordOf g.main).n - (wordOf g.main).k = s.dC := by
  have h1 := hp.someC
  have h2 := hs.roomC
  show 2 ^ g.main.logN - g.main.k = 2 ^ s.C.a - (s.C.r + s.C.l) + 1
  rw [f.mainLog, f.main_k hp]
  omega

/-- The repeated mask word has the main code's length. -/
theorem mask_n (f : s.FitsGroup g) (hs : s.Sized) :
    (repeated g.mask g.main.logN).n = 2 ^ s.C.a := by
  have hab := hs.short
  unfold repeated
  rw [f.mainLog, f.maskLog]
  by_cases hc : s.C.a ≤ s.Z.a
  · rw [if_pos hc]
    show 2 ^ g.mask.logN = 2 ^ s.C.a
    rw [f.maskLog, le_antisymm hab hc]
  · rw [if_neg hc]
    rfl

/-- For the repeated mask word n - k is the repeated mask code's distance. -/
theorem mask_dist (f : s.FitsGroup g) (hs : s.Sized) (hp : s.Pos) :
    (repeated g.mask g.main.logN).n - (repeated g.mask g.main.logN).k = s.dZ := by
  have hk := f.mask_k hp
  have h1 := hp.someZ
  have h2 := hs.roomZ
  have hab := hs.short
  have ha := hs.small
  have hd : 2 ^ s.Z.a - (s.Z.r + s.Z.l) + 1 = 2 ^ s.Z.a - (s.Z.r + s.Z.l - 1) := by omega
  unfold repeated
  rw [f.mainLog, f.maskLog]
  by_cases hc : s.C.a ≤ s.Z.a
  · rw [if_pos hc]
    show 2 ^ g.mask.logN - g.mask.k =
      2 ^ (s.C.a - s.Z.a) * (2 ^ s.Z.a - (s.Z.r + s.Z.l) + 1)
    rw [f.maskLog, hk, hd, Nat.sub_eq_zero_of_le hc, pow_zero, one_mul]
  · rw [if_neg hc]
    show 2 ^ s.C.a - g.mask.k * 2 ^ (s.C.a - s.Z.a) % 2 ^ 64 =
      2 ^ (s.C.a - s.Z.a) * (2 ^ s.Z.a - (s.Z.r + s.Z.l) + 1)
    have hpow : 2 ^ s.C.a = 2 ^ (s.C.a - s.Z.a) * 2 ^ s.Z.a := by
      rw [← pow_add]
      congr 1
      omega
    have hlt : g.mask.k * 2 ^ (s.C.a - s.Z.a) < 2 ^ 64 :=
      calc g.mask.k * 2 ^ (s.C.a - s.Z.a) < 2 ^ s.Z.a * 2 ^ (s.C.a - s.Z.a) :=
            Nat.mul_lt_mul_of_pos_right (by rw [hk]; omega) (Nat.two_pow_pos _)
        _ = 2 ^ s.C.a := by rw [hpow, Nat.mul_comm]
        _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) ha
        _ < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt hlt, hk, hd, hpow, Nat.mul_sub, Nat.mul_comm (s.Z.r + s.Z.l - 1)]

/-- The count for a main row, written with the planner's main word: it splits on the planner's test
for the source `third`. -/
theorem cntC_eq (f : s.FitsGroup g) (hs : s.Sized) (hp : s.Pos) (e : ℕ) :
    s.cntC e =
      if 3 * e < (wordOf g.main).n - (wordOf g.main).k then e + 1 else (wordOf g.main).n := by
  unfold Sg.cntC
  rw [f.main_dist hs hp, f.main_n]

/-- The count for a mask row, written with the planner's repeated mask word: it splits on the
planner's test for the source `third`. Beyond a third the planner's count for a mask row is one list
size more than n. -/
theorem cntZ_eq (f : s.FitsGroup g) (hs : s.Sized) (hp : s.Pos) (e : ℕ) :
    s.cntZ e =
      if 3 * e < (repeated g.mask g.main.logN).n - (repeated g.mask g.main.logN).k then e + 1
      else (repeated g.mask g.main.logN).n := by
  unfold Sg.cntZ
  rw [f.mask_dist hs hp, f.mask_n hs]

/-- The group has a mask code exactly if the stage's mask code has a message. -/
theorem hasMask_iff (f : s.FitsGroup g) : g.hasMask = true ↔ 0 < s.Z.l := by
  unfold GroupSize.hasMask
  rw [f.maskEll]
  simp [Nat.pos_iff_ne_zero]

end Sg.FitsGroup

end OnBytes.Slice
