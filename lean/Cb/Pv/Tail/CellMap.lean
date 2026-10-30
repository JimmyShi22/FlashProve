-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/CellMap.lean: a named map from the committed messages to the cells, as elements of the
field, with which every committed read agrees.

Cb/Pv/Tail/Agree.lean has the agreement for cells that stand under "there are". Under the three
inequalities of Cb/Pv/Tail/Unique.lean the cells are `cellsOf`, a function of the committed symbols.

Main names:
  `cellVal Λ msg`: the cells behind the committed symbols, as elements of the field.
  `agree_cellVal`: before the round every committed read is the value of its form (`affRead`) at
    `cellVal Λ msg`.
  `small_cellVal`: before the round every entry of `cellVal Λ msg` is the image of an integer below
    twice the shift in absolute value.
  `agree_gl`: the first at the shift 2 ^ 17 and the radix 2 ^ 20 over `Cb.Gl.E`.

Limits: `cellVal` is found by choice: no program is given.

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Agree
import Cb.Pv.Tail.Unique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {K : Type} [Field K] {s : Size} (Λ : Letters K s)

/-- The cells behind the committed symbols, as elements of the field. -/
noncomputable def cellVal (msg : Λ.M) : JCell s → K :=
  fun j => ((cellsOf Λ msg j.1 j.2.1 j.2.2 : ℤ) : K)

theorem agree_cellVal (p : ℕ) [CharP K p] (hu : s.Uniq p) {x : Λ.X} {msg : Λ.M}
    (h : relIn Λ x msg) :
    ∀ j : JTab s, Λ.tab msg j.1 j.2.1 j.2.2 = (affRead Λ x j).val (cellVal Λ msg) :=
  agree_of_cells Λ (cellsOK_cellsOf Λ p hu h)

theorem small_cellVal (p : ℕ) [CharP K p] (hu : s.Uniq p) {x : Λ.X} {msg : Λ.M}
    (h : relIn Λ x msg) (j : JCell s) : Cb.Rng.Short (2 * (s.beta : ℤ)) (cellVal Λ msg j) :=
  ⟨cellsOf Λ msg j.1 j.2.1 j.2.2, (cellsOK_cellsOf Λ p hu h).1 j.1 j.2.1 j.2.2, rfl⟩

theorem agree_gl {s : Size} (Λ : Letters Cb.Gl.E s) (hb : s.beta = 2 ^ 17) (hr : s.rad = 2 ^ 20)
    {x : Λ.X} {msg : Λ.M} (h : relIn Λ x msg) :
    ∀ j : JTab s, Λ.tab msg j.1 j.2.1 j.2.2 = (affRead Λ x j).val (cellVal Λ msg) :=
  agree_cellVal Λ Cb.Gl.p (uniq_gl hb hr) h

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.agree_cellVal
#print axioms Cb.Pv.Tail.small_cellVal
#print axioms Cb.Pv.Tail.agree_gl
