--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/DotUB.lean: the third of the claims that stand behind "LIN point", as a test
with code: (Dot)'s equation with what is read off the folded row u at the point's low part
(Johnson/Desc/K14/Law/Borders.lean: DotUAt).

  dotUB          computes the equation's two sides by the program's arithmetic
                 (Johnson/Desc/K14/Law/NearB.lean: sumE, eqE) and compares them. gE: the weights on
                 the matrix's rows; VE: the vector; mE: the words; all as the program's elements.
  dotUAt_of_B    a yes gives DotUAt at these, read by the library's reading (Reading.gl).

What is not claimed. The converse. That any words are an honest prover's. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.NearB
import Johnson.Desc.K14.Law.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

/-- The left side of (Dot)'s equation with what is read off u at psi_lo, computed. -/
def dotL (S : LinShape) (gE : Nat → E) (l : Lin) (mE : Words E) : E :=
  sumE S.matrixRows fun y => mulE (gE y) (sumE (2 ^ S.kLo) fun t =>
    mulE (eqE (l.psiSh.take S.kLo) t) (mE l.oU.oracle .main (l.oU.lay.index (t + 2 ^ S.kLo * y))))

/-- Its right side. -/
def dotR (S : LinShape) (l : Lin) (VE : Nat → E) : E :=
  sumE (2 ^ S.kCol) fun c => mulE (eqE l.psiSh c) (VE c)

/-- The equation, computed. -/
def dotUB (S : LinShape) (gE : Nat → E) (l : Lin) (mE : Words E) (VE : Nat → E) : Bool :=
  decide (dotL S gE l mE = dotR S l VE)

theorem dotUAt_of_B (S : LinShape) (gE : Nat → E) (l : Lin) (mE : Words E) (VE : Nat → E)
    (h : dotUB S gE l mE VE = true) :
    DotUAt S (fun y => OnBytes.Model.Reading.gl.val (gE y)) l
      (wordsOf OnBytes.Model.Reading.gl mE) (fun c => OnBytes.Model.Reading.gl.val (VE c)) := by
  simp only [dotUB, decide_eq_true_eq] at h
  have e := congrArg OnBytes.Model.Reading.gl.val h
  simp only [dotL, dotR, OnBytes.Model.Reading.gl.mul, val_sumE, val_eqE] at e
  unfold DotUAt uOf
  exact e

end Desc.K14.Law
