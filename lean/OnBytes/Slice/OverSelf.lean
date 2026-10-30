-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OverSelf.lean: a table that holds the oracle's own values changes nothing: the oracle
with it put over is the oracle, and a part whose checker is answered by it has its own checker's
value.

`over S T g` (OnBytes/Slice/AtSet.lean) is g with the values of the table T at the strings of S;
`pinOn S T c` answers c's queries there by the table; `Part.on` (OnBytes/Slice/PartChainOn.lean) is
a part with such a checker. General in the length of digests.

Main theorems.
 `over_of_eq`, `over_self`   if T has g's values at the strings of S, `over S T g = g`; so at g's
                        own function as the table.
 `det_pinOn_of_eq`      `pinOn S T c` has under g the value of c under g.
 `Part.on_chk_of_eq`, `Part.on_chk_self`   the checker of `s.on S T` has under g the value of the
                        checker of s under g.

What is not claimed. The values are those of the run in which every coin toss yields 0
(`OComp.det`). The two checkers' LOGS differ: `pinOn` does not ask at the strings of S. Nothing on
tables that differ from g somewhere on S. No probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.PartChainOn

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Compile Compile.Batch

variable {lam : ℕ} {α γ Sg : Type}

/-- A table that has g's own values at the strings of S changes nothing: g with it put over is
g. -/
theorem over_of_eq (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (h : ∀ x ∈ S, T x = g () x) : over S T g = g := by
  funext o x
  cases o
  by_cases hx : x ∈ S
  · rw [over_mem T g hx, h x hx]
  · rw [over_not_mem T g hx]

/-- So g's own function, as a table. -/
theorem over_self (S : Finset (List Bool)) (g : Fam (rom lam)) :
    over S (fun x => g () x) g = g :=
  over_of_eq S _ g fun _ _ => rfl

/-- The algorithm that answers by such a table has under g the value of the algorithm itself. -/
theorem det_pinOn_of_eq (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (h : ∀ x ∈ S, T x = g () x) (c : OComp (rom lam) α) : (pinOn S T c).det g = c.det g := by
  rw [det_pinOn, over_of_eq S T g h]

/-- A part whose checker is answered by such a table: its checker has under g the value of the
part's own checker under g. -/
theorem Part.on_chk_of_eq (s : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (g : Fam (rom lam)) (h : ∀ x ∈ S, T x = g () x) (x : γ) :
    ((s.on S T).chk x).det g = (s.chk x).det g :=
  det_pinOn_of_eq S T g h _

/-- At g's own function as the table. -/
theorem Part.on_chk_self (s : Part lam γ Sg) (S : Finset (List Bool)) (g : Fam (rom lam)) (x : γ) :
    ((s.on S fun y => g () y).chk x).det g = (s.chk x).det g :=
  s.on_chk_of_eq S _ g (fun _ _ => rfl) x

end OnBytes.Slice
