-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/EntCnt.lean: a bound from above for the count `Cb.bchksBound n k e` (Cb/Gen/CodeListRS.lean),
from a record of five natural numbers: the library's check `Cb.CntLe`, with its last five arguments
as one record.

`Cb.bchksBound n k e` is the count in the theorem on codes that is taken as given: a real number,
written with a square root and a ceiling. A table of parameters needs a natural number that is at
least that count. `Cb.CntLe n k e m a b D N` is ten inequalities between natural numbers, which can
be decided, and gives ⌊bchksBound n k e⌋₊ ≤ N (`floor_le_of_cntLe`). A table has one such tuple
(m, a, b, D, N) for each code: here it is a record, so that lists of them can be written.

Main names:
  `CntW`: the five numbers: m; lo, hi, den (lo / den and hi / den bracket the square root of k / n
    from below and from above); N, the bound.
  `c.Ok n k e`: `CntLe n k e c.m c.lo c.hi c.den c.N` (decidable): n, k, lo, den are positive; the
    two brackets; hi / den + e / n < 1; m is at least hi / den divided by 1 - hi / den - e / n, and
    at least 3; N is at least the count's formula at m and lo / den.
  `Spec.cntW_bound`: `c.Ok n k e` → bchksBound n k e ≤ c.N.
  `Spec.cntW_floor`: `c.Ok n k e` → ⌊bchksBound n k e⌋₊ ≤ c.N.
No theorem proves these under these names. Since `c.Ok` is `CntLe` by definition, what they say
follows from `bound_le_of_cntLe` and `floor_le_of_cntLe` (Cb/Ref/CntLe.lean).

Limits: this is arithmetic on a formula. The theorem on codes itself is neither used nor stated
here: nothing says that words agree with a code at so many points at most. Not that a given c is the
best: any m, brackets and N that meet the ten inequalities will do. Not that e is below the Johnson
radius of a code: the seventh inequality is near to it, but no code stands here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ref.CntLe

set_option autoImplicit false

namespace Cb

/-- Five numbers from which a bound for `bchksBound` is checked. -/
structure CntW where
  /-- at least the number m of the count's formula -/
  m : ℕ
  /-- lo / den is at most the square root of k / n -/
  lo : ℕ
  /-- hi / den is at least the square root of k / n -/
  hi : ℕ
  /-- the common denominator -/
  den : ℕ
  /-- the bound -/
  N : ℕ

/-- The ten inequalities of `CntLe`, at the record's five numbers. -/
def CntW.Ok (c : CntW) (n k e : ℕ) : Prop := CntLe n k e c.m c.lo c.hi c.den c.N

/-- The ten inequalities can be decided. -/
instance CntW.decOk (c : CntW) (n k e : ℕ) : Decidable (c.Ok n k e) := by
  unfold CntW.Ok; infer_instance

namespace Spec

/-- The count is at most N. -/
def cntW_bound : Prop := ∀ (c : CntW) (n k e : ℕ), c.Ok n k e → bchksBound n k e ≤ c.N

/-- The count, rounded down, is at most N. -/
def cntW_floor : Prop := ∀ (c : CntW) (n k e : ℕ), c.Ok n k e → ⌊bchksBound n k e⌋₊ ≤ c.N

end Spec
end Cb
