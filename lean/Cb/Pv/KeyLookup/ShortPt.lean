-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/ShortPt.lean: the point that the short sumcheck's verifier reads off a transcript
holds, at place j, the challenge drawn in round j.

Main names:
  `chS l t τ j`    the value of the challenge drawn in round j of a transcript of the short rounds
                  of
                   the list l of variables, followed by the rounds t.
  `ppGet_vFinT`    place j of the point that `TWhole.vFinT` reads is `chS l t τ j`.
Limits: general in the list of variables and in t. Nothing on the other values that are read.

-/
import Cb.Pv.KeyLookup.PtGet
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Iop IOR Hiop Prob Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E]

/-- the value of the challenge drawn in round j of a transcript of the short rounds of l, then t -/
def chS : (l : List (PFmt E)) → (t : Shape) → Tr (sRounds l ++ t) → ℕ → E
  | [], _, _, _ => 0
  | f :: _, _, (_, c, _), 0 => f.val c
  | _ :: l, t, (_, _, τ), j + 1 => chS l t τ j

theorem ppGet_vFinT : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E) (t :
    Shape)
    (τ : Tr (sRounds l ++ t)) (j : ℕ), ppGet l (TWhole.vFinT l d F σ t τ).1.2 j = chS l t τ j
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, _, _, _, _, (_, _, _), 0 => rfl
  | f :: l, d, F, σ, t, (m, c, τ), j + 1 =>
    ppGet_vFinT l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ j

end Lk6

#print axioms Lk6.ppGet_vFinT
