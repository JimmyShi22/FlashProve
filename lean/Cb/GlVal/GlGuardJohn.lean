-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlGuardJohn.lean: the hypothesis `GlJ` of Cb/GlVal/GlJohn.lean at
a small code, at a radius not within half the distance (2 · 3 = 6), below the Johnson radius, over
p = 2^64 - 2^32 + 1.



In standard terms: a small concrete instance of one hypothesis on codes: rows under one Reed-Solomon
code of length 8, at a decoding radius not below a half of the distance. Which hypotheses are not
covered: Limits.


Definitions and proofs; no parameter of a protocol.


The fields and the code: F, E of Cb/Gl/GlField.lean; `C8` (Cb/GlVal/GlToyBase.lean): Reed-Solomon
on the subgroup of order 8, dimension 3 = one message symbol + two uniform coefficients (they fill
the dimension), distance 6, hides 2 positions. Radius 3: 2 · 3 is not below 6; 8 · (8
- 6) = 16 < 25 = (8 - 3)²: below the Johnson radius.

Main names:
  `b8`: the count of the statement on codes at (8, 2, 3), rounded down: it stands in `GlJ` as
    data.
  `inJ83`: the radius 3 is below the Johnson radius at the distance 6, on the subgroup of order 8.
  `glJ8`, `glJ80`, `glJ81`: `GlJ (toyLd8 R) 6 t 3 b8` at t = 2, 0, 1; the radius is within neither a
    third nor a half (2 · 3 = 6).







Limits: what these toys do not show: a radius with 2 e above d: they stand at the radius 3 of the
distance 6 (2 · 3 = 6).
BCHKS46F F itself stays a hypothesis of the theorems of Cb/GlVal/GlJohn.lean. That `b8` is below the
number of elements of E is not said here. (|E| is above 2^191.) The constructors `GlJ.sub` (a proper
subcode), `GlJ.fam`, `GlJ.up` are met by no instance here. Nor are
`GlJ.copy`, `GlJ.il`, `GlJ.pair`. No instance of `TowGlJ`, `TowGGlJ` or `RunGlJ` is given here. This
file does not guard the offline phase as a whole, and says nothing on it.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlJohn
import Cb.GlVal.GlGuardTower
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR Cb.Ood

/-- the count of the statement on codes at length 8, degree 2, radius 3, rounded down -/
def b8 : ℕ := ⌊Cb.bchksBound (2 ^ 3) 2 3⌋₊

theorem inJ83 : InJohnson (Fintype.card P8) 6 3 := by
  rw [card8]
  unfold InJohnson
  norm_num

theorem glJ8 (R : Type) [Fintype R] [DecidableEq R] : GlJ (toyLd8 R) 6 2 3 b8 :=
  .base (glJ_one 3 2 1 2 3 R (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by  norm_num))

theorem glJ80 (R : Type) [Fintype R] [DecidableEq R] : GlJ (toyLd8 R) 6 0 3 b8 :=
  glJ_mono P8 _ 6 2 3 b8 0 (glJ8 R) (Nat.zero_le _)
theorem glJ81 (R : Type) [Fintype R] [DecidableEq R] : GlJ (toyLd8 R) 6 1 3 b8 :=
  glJ_mono P8 _ 6 2 3 b8 1 (glJ8 R) (by norm_num)

/-! ## 1. The plain tower -/

/-! ## 2. On a group's complex -/

namespace G8J
open LdGToy (Mem Rm Rz corner)
open G8T (Cb8 Zb8)

end G8J

end Cb.Gl
