-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedDrawnCode.lean: `seedOfDrawn` (OnBytes/Slice/SeedDrawn.lean), the seeds off the
format's records of what a round has drawn, WITH CODE: a twin that Lean compiles, and the equation.

WHY. `seedOfDrawn` and the three definitions beneath it (`gv`, `nzOf`, `readFlat`,
OnBytes/Slice/SeedTie.lean) are marked as without code. A run of the entry's judge compares the
seeds that its chain draws with the seeds in its instance: for that the value must be computed.
Nothing in these definitions needs a choice: the extension field's elements, its 0, its 1, and the
test whether two elements are equal have code.

Main definitions: `gvC`, `nzOfC`, `readFlatC`, `seedOfDrawnC`: the four texts again, the test "is it
0" by the field's own test of equality.
Main theorems.
 `gvC_eq`, `nzOfC_eq`, `readFlatC_eq`   each is the definition whose name it bears.
 `seedOfDrawnC_eq`      `seedOfDrawnC lg s = seedOfDrawn lg s`.

What is not claimed. How long a run takes. Nothing on soundness; no probability; nothing on any hash
function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.SeedDrawn

set_option autoImplicit false

namespace OnBytes.Slice

/-- `gv` (OnBytes/Slice/SeedTie.lean), with code. -/
def gvC : Fmt.Val → GE
  | .ext e => toE e
  | _ => 0

/-- It is `gv`. -/
theorem gvC_eq (x : Fmt.Val) : gvC x = gv x := by
  cases x <;> rfl

/-- `nzOf`, with code: the test "is it 0" is the field's own. -/
def nzOfC (x : GE) : NZ := if h : x = 0 then ⟨1, one_ne_zero⟩ else ⟨x, h⟩

/-- It is `nzOf`. -/
theorem nzOfC_eq (x : GE) : nzOfC x = nzOf x := by
  unfold nzOfC nzOf
  by_cases h : x = 0
  · rw [dif_pos h, dif_neg (not_not.2 h)]
  · rw [dif_neg h, dif_pos h]

/-- `readFlat`, with code. -/
def readFlatC (lg : ℕ) : (s : ℕ) → List Fmt.Val → Fin s → (Fin lg → GE) × NZ
  | 0, _ => fun i => i.elim0
  | s + 1, l =>
    Fin.cons (fun c => gvC (l.getD c.val dV), nzOfC (gvC (l.getD lg dV)))
      (readFlatC lg s (l.drop (lg + 1)))

/-- It is `readFlat`. -/
theorem readFlatC_eq (lg : ℕ) : ∀ (s : ℕ) (l : List Fmt.Val), readFlatC lg s l = readFlat lg s l
  | 0, _ => rfl
  | s + 1, l => by
    have e : (fun c : Fin lg => gvC (l.getD c.val dV)) = fun c => gv (l.getD c.val dV) :=
      funext fun c => gvC_eq _
    rw [readFlatC, readFlat, readFlatC_eq lg s, e, nzOfC_eq, gvC_eq]

/-- `seedOfDrawn` (OnBytes/Slice/SeedDrawn.lean), WITH CODE: s seeds off the format's records of
what was drawn. -/
def seedOfDrawnC (lg s : ℕ) (l : List Fmt.Drawn) : Fin s → (Fin lg → GE) × NZ :=
  readFlatC lg s ((l.headD ⟨[], [], [], none⟩).elems.map Fmt.Val.ext)

/-- It is `seedOfDrawn`. -/
theorem seedOfDrawnC_eq (lg s : ℕ) : seedOfDrawnC lg s = seedOfDrawn lg s :=
  funext fun _ => readFlatC_eq lg s _

end OnBytes.Slice
