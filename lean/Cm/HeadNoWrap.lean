-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/HeadNoWrap.lean: a ring map on the plain head (Cm/Head.lean).

Main names:
  `map_mg'`, `map_idn'`: a ring map f takes the margin and the identities of a trace to those of
    the image of the trace.

Terms: lean/GLOSSARY.md.
-/
import Cm.Head
import Inst.Model.Head.NoWrapProgram

set_option autoImplicit false

namespace Cm.Plain

open Inst.Model Inst.Model.Head Finset

section Map
variable {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (np : NormPar) (t : Cells K)
  (H : ℕ → ℕ → K) (y : Req)

theorem map_mg' (v i : ℕ) : f (mg t H y v i) = mg (t.map f) (fun j v => f (H j v)) y v i := by
  simp only [mg, map_mul, map_sub, map_lg, map_intCast]
  split_ifs <;> simp

theorem map_idn' (i k : ℕ) : f (idn np t i k) = idn np (t.map f) i k := by
  unfold idn
  rw [Ledger.map_idn]
  have e1 : (fun s => f (Ledger.Wsum nD (fun l j => bl t l j i) s)) =
      Ledger.Wsum nD fun l j => bl (t.map f) l j i :=
    funext fun s => Ledger.map_Wsum f _ _ s
  have e2 : (fun m => f (Dv t m i)) = fun n => Dv (t.map f) n i := funext fun n => map_Dv f t n i
  rw [e1, e2]

end Map

end Cm.Plain
