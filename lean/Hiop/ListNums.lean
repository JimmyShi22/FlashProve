-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/ListNums.lean: the numbers that the parameter list of a sub-protocol carries.

Definitions only. Hiop/RecSubs.lean states the parameter lists; these are their numbers.

Main names: `PreNums`: of a preamble; `LinBNums`: of an IOPP at at most N instances; `LinkNums`: of
the link.

Terms: lean/GLOSSARY.md.
-/
import Hiop.Enc
import Hiop.Interface

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

/-- The numbers of a preamble. -/
structure PreNums {Xi Xo : Type} {Ei Eo : ExtSpec} (F : IOR Xi Ei Xo Eo) where
  err  : Err F.shape
  pBad : ℝ≥0∞
  pHid : ℝ≥0∞
  bud  : Rho F.shape → Finset (OPos F.shape) → Prop

/-- The numbers of an IOPP at at most N instances: errors (on statements whose encoded index
decodes), a bound on the probability of the public bad set, a bound on the number of positions read
in the encoded index, and the budget, which is on the family of the slots' further reads (a shared
oracle is read by all of them). -/
structure LinBNums (s : Shape) (N : ℕ) where
  err    : Err s
  pBad   : ℝ≥0∞
  q      : ℕ
  bud    : BudB s N

/-- The numbers of the link. -/
structure LinkNums (s : Shape) where
  err  : Err s
  pBad : ℝ≥0∞
  qpar : ℕ
  qch  : ℕ
  bud  : Rho s → Finset (OPos s) → Prop

end Hiop
