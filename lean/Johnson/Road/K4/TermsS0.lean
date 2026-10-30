-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/TermsS0.lean: at the library's value of a layers' sub-proof's own rounds the summand
of the sumcheck of the terms has no term in shown maps alone: its part S0 is 0. One theorem.

  `terms_S0`: at every `MidPar`, state, point and values: `P.ip.Y3.S0 st X v = 0`
    (Cb/Pv/Lay/At/Terms.lean lays `t0 := []`).

Limits. An unfolding of definitions.
-/
import Cb.Pv.Lay.At.Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay.At
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

theorem terms_S0 (P : MidPar E M X) (st : P.ip.Y3.St) (Xp : HPt (P.ip.Y3.vars st))
    (v : P.ip.Y3.A → E) : P.ip.Y3.S0 st Xp v = 0 := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.terms_S0
