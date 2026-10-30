-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlGuardTower.lean: pieces of small concrete towers over p = 2^64 - 2^32 + 1: a fold on rows
under one Reed-Solomon code of length 8, and the base code and the mask code of a group.







Definitions and proofs; no parameter of a protocol.


The fields and the code: F = the integers modulo p, E = F[x] / (x^3 - 2); `C8`
(Cb/GlVal/GlToyBase.lean): Reed-Solomon on the subgroup of order 8, dimension 3 (one message
symbol, two uniform coefficients), distance 6, hides 2 positions; rows under it, read as they stand
(`toyLd8 R`).

Main names:
  1. Plain, for every h, g (k = h + g folded variables), every finite R, any form sl:
    `fold8 h g R St sl`: the fold with its masks (degree 2, challenges from all of E, the packing
    into 2^h rows); `plc8`: each column of the packing in its own coordinate of the mask code's
    message; `Nw8`: the coordinates of the new message.


  2. On a group's complex (namespace `G8T`): `Cb8`, `Zb8`: the base code and the mask code, under
    toyLd8; `c0`, `c1`: `GlC` of `toyLd8 R` at the distance 6, at t = 0 and t = 1.













Limits: no tower is built here, and no instance of `TowGl`, `TowGGl` (Cb/GlVal/GlThird.lean) or
`RunGl` (Cb/Gl/GlOff.lean) is given. It says nothing on errors.


Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlGuard
import Cb.GlVal.GlToyMsg
import Cb.Ld.LdTowerToyKit
import Cb.Ld.LdSumPackProofs
import Cb.Ld.LdGroupToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR Cb.Ood

/-- each column of the packing in its own coordinate of the mask code's message -/
def plc8 (h g : ℕ) : PCol h g 1 → (toyLd8 (PCol h g 1)).J := fun c => toyPlace8 (PCol h g 1) c

theorem plc8_inj (h g : ℕ) : Function.Injective (plc8 h g) := (toyPlace8 (PCol h g 1)).injective

/-! ## 1. The plain tower -/

section Plain
variable (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St : Type)

/-- the message coordinates of the input code -/
abbrev JIn8 : Type :=
  (((toyLd8 R).il (Fin (h + g) → Bool)).pair ((toyLd8 (PCol h g 1)).il (Fin h → Bool))).J

variable (sl : Slf E St (JIn8 h g R))

/-- The fold. -/
def fold8 : SumPar E P8 where
  h := h
  g := g
  n := 2
  Ch := E
  val := id
  C := toyLd8 R
  Z := toyLd8 (PCol h g 1)
  AaW := (toyLd8 (PCol h g 1)).Aa
  TW := (toyLd8 (PCol h g 1)).T
  srcW := (toyLd8 (PCol h g 1)).src
  St := St
  StS := St
  sl := Slf.left sl
  slS := Slf.right sl
  pk := pkAt (plc8 h g) (pkC h g 1)
  Qw := QwAt (plc8 h g) (QwC h g 1)

instance finAa8 : Fintype (fold8 h g R St sl).Cout.Aa :=
  inferInstanceAs (Fintype ((toyLd8 R).Aa ⊕ ((toyLd8 (PCol h g 1)).Aa ⊕ (toyLd8 (PCol h g 1)).Aa)))
instance decAa8 : DecidableEq (fold8 h g R St sl).Cout.Aa := Classical.decEq _

/-- the coordinates of the new message = the rows of the new word -/
abbrev Nw8 : Type := ((fold8 h g R St sl).Cout.J ⊕ (fold8 h g R St sl).Cout.Q) ⊕ Unit

end Plain

/-! ## 2. On a group's complex -/

namespace G8T
open LdGToy (Mem Rm Rz corner)

/-- the base code (two rows: a base row has two message entries), the mask code -/
abbrev Cb8 : LdCode E P8 := toyLd8 Bool
abbrev Zb8 : LdCode E P8 := toyLd8 (PCol 1 1 1)

theorem c0 (R : Type) [Fintype R] [DecidableEq R] : GlC (toyLd8 R) 6 0 :=
  glC_mono P8 _ 6 2 6 0 (glC8 R) le_rfl (Nat.zero_le _)
theorem c1 (R : Type) [Fintype R] [DecidableEq R] : GlC (toyLd8 R) 6 1 :=
  glC_mono P8 _ 6 2 6 1 (glC8 R) le_rfl (by norm_num)

end G8T

end Cb.Gl
