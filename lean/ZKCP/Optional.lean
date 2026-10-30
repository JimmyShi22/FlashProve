-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Optional.lean: two optional additions to the definition of ZKCP/Defs.lean, as definitions:
`HasSessionAugmentedBinding` (index binding for many sessions) and `HasExtractionError` (i* = i for
the honest committer). The requirements of this file are optional additions of the work
that this protocol builds on (lean/CREDITS.md, "Further work"); the experiment and the error δ of
the second are this library's.

Neither is used by `IsZKCPArg`. One more, a well-formedness predicate, is not defined in this
library. Also not defined in this library: computational index privacy (it needs a notion of running
time).

Notation (C~, P~, i*, E_i, E_w): ZKCP/Defs.lean, `Extractor`, `bindingExp`.
-/
import ZKCP.Defs

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP
section Optional
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-- Run V on every pair; output the list of (V's bit, x_j). -/
def verifyAll (ivk : IVK) : List (X × Pf) → OComp lam (List (Bool × X))
  | [] => pure []
  | (x, π) :: rest => do
      let b ← A.V ivk x π
      let bs ← verifyAll ivk rest
      pure ((b, x) :: bs)

/-- The experiment for many sessions (after that work): a single run in which P~
outputs any number of instances with
proofs, (x_j, π_j), and V is run on every one; the run's output is i* and, for each of them, V's bit
and x_j. The number N and the budget t_P appear in the next definition. -/
def multiBindingExp {St : Type} (Ei : IVK → Trace lam → Option I) (Ct : OComp lam (IVK × St))
    (Pt : St → OComp lam (List (X × Pf))) : OComp lam (Option I × List (Bool × X)) := do
  let ((ivk, st), trC) ← Ct.withTrace
  let pairs ← Pt st
  let bs ← verifyAll A ivk pairs
  pure (Ei ivk trC, bs)

/-- Index binding for many sessions (from that work): [after that work: there is one E_i
(no E_w is asked for) such that, for all t_C, t_P and N, every C~ with at most t_C queries and every
P~ with at most t_P queries: Pr[ at most N pairs were output and some accepted x_j ∉ L(i*) ] ≤
ε(t_C, t_P, N).] A longer list is never bad. -/
def HasSessionAugmentedBinding (ε : ℕ → ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ Ei : IVK → Trace lam → Option I,
    ∀ (tC tP N : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (List (X × Pf))),
      Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
        Pr (multiBindingExp A Ei Ct Pt)
          (fun _ => {o | o.2.length ≤ N ∧ ∃ bx ∈ o.2, bx.1 = true ∧ bx.2 ∉ R.L o.1}) ≤ ε tC tP N

/-- The optional requirement of that work: [after that work: i* = i for the honest
committer]. That work gives no formula; this experiment and the error δ are this library's; they
are not part of the definition in ZKCP/Defs.lean. -/
def HasExtractionError (E : Extractor lam I X W IVK Pf) (δ : ℝ≥0∞) : Prop :=
  ∀ i, Pr (A.C i).withTrace (fun _ => {o | E.Ei o.1.1 o.2 ≠ some i}) ≤ δ

end Optional
end ZKCP
