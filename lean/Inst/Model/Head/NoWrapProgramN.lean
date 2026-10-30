-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/NoWrapProgramN.lean: for every final normalisation, a ring homomorphism commutes
with the head's identities (`N.map_idn'`).

Notation:
  `np : NormPar` (Inst/Model/Program.lean): exponent of the reciprocal (M); shift (K); constant (ϵ)
    of a normalisation.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.NoWrapProgram

set_option autoImplicit false

namespace Inst.Model.Head.N

open Finset

section Map
variable {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (np : NormPar) (t : Cells K)
  (H : ℕ → ℕ → K) (y : Req)

theorem map_idn' (i k : ℕ) : f (idn np t i k) = idn np (t.map f) i k := by
  unfold idn
  rw [Ledger.map_idn]
  have e1 : (fun s => f (Ledger.Wsum nD (fun l j => bl t l j i) s)) =
      Ledger.Wsum nD fun l j => bl (t.map f) l j i :=
    funext fun s => Ledger.map_Wsum f _ _ s
  have e2 : (fun m => f (Dv t m i)) = fun n => Dv (t.map f) n i := funext fun n => map_Dv f t n i
  rw [e1, e2]

end Map

end Inst.Model.Head.N
