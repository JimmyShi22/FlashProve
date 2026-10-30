-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/AnyP.lean: the frame's `MarkDebt`
(Honest/Law/CoverJoin.lean) at the condition "true" on the challenges in front
gives it at every condition. One theorem.

What is shown.
  `markDebt_any`: the step.

Hypotheses that remain. `h`: the bound at "true".

Imported: Honest/Law/CoverJoin.lean.

Users. `k3Marks_debt_cap` (Honest/K3/Good/H3/Member.lean).

Limits. An implication.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-- A bound at "true" is a bound at every P. -/
theorem markDebt_any (C : CK) (mk : Mark) (dsb : List RDT) (q : ℝ≥0∞)
    (h : MarkDebt C mk dsb (fun _ => True) q) (P : List Fmt.Drawn → Prop) :
    MarkDebt C mk dsb P q := fun fr _ => h fr trivial

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.markDebt_any
