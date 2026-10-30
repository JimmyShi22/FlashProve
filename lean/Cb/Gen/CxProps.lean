-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CxProps.lean: the hypothesis `Cx.Props` of Cb/Gen/Code.lean, met at a concrete complex.

`props_one`: a complex of one component has `Cx.Props` if the code of that component has
`Code.Enc.Props`. `props_one_rs`: so has a complex of one component over a Reed–Solomon code: F a
finite field of characteristic p, E any finite field that is an algebra over F, conditions on the
numbers, any number of rows. `props_closed`: the guard: one row over ZMod 101, with nothing empty.
-/
import Cb.Gen.Code
import Code.RS
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace Cb.Cx

section
variable {F : Type} [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

/-- A complex of one component has the properties of a code with encoder if the code of that
component has them. -/
theorem props_one (c : Comp F) (h : c.code.Props E) : (Cx.one c).Props E := fun _ => h

/-- A complex of one component over a Reed–Solomon code has the properties. F is a finite field of
characteristic p > n, E any finite field that is an algebra over F, the points are 1, ..., n,
msg + r ≤ k ≤ n and 3e < n - k + 1. The code's count of bad values is e + 1, its distance is
n - k + 1 and it hides r positions; the number of rows and the flag are free. -/
theorem props_one_rs {n k msg r e : ℕ} (p : ℕ) [CharP F p] (hn : n < p) (hp : msg + r ≤ k)
    (hkn : k ≤ n) (he : 3 * e < n - k + 1) (rows : ℕ) (overF : Bool) :
    (Cx.one (Comp.fin (Code.RS.code (Code.RS.natPoints F n) k msg r e (e + 1)) rows overF)).Props
      E :=
  props_one E _ (Code.RS.props_natPoints p hn hp hkn he)

end

local instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- The complex of the guard: one row of a Reed–Solomon code over ZMod 101 at the points 1, ..., 6:
dimension 2, one message symbol, one symbol of randomness, one error. -/
abbrev closed : Cx (ZMod 101) :=
  Cx.one (Comp.fin (Code.RS.code (Code.RS.natPoints (ZMod 101) 6) 2 1 1 1 2) 1 true)

/-- The guard: `Cx.Props` holds of a concrete complex, with a row, a message symbol, a hidden
position and an error: distance 5, at most 2 bad values. -/
theorem props_closed : closed.Props (ZMod 101) :=
  props_one_rs (F := ZMod 101) (ZMod 101) (n := 6) (k := 2) (msg := 1) (r := 1) (e := 1) 101
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 true

end Cb.Cx

#print axioms Cb.Cx.props_one
#print axioms Cb.Cx.props_one_rs
#print axioms Cb.Cx.props_closed
