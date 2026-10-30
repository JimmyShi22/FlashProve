-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportPrint.lean: the prover's proofs put through any function, the verifier replaced by any
verifier: the privacy clause is carried over with the same bound.

Definitions and two statements (`Run.Spec.pr_privacy`, `Run.Spec.pr_wr`); the proofs are in
Run/TransportPrintProofs.lean. Generic. A scheme is an argument `A : Arg lam I X W IVK ISK Pf`
(ZKCP/Defs.lean) with its committer C, prover P and verifier V.

Why: the experiments of privacy (ZKCP/Defs.lean: `realExp`, `idealExp`) run C and P alone: V does
not occur in them. So the step "the proofs are written as strings" needs, for privacy, nothing of a
parser: not that what is printed parses back, not that printing is injective. Made for a format in
which printing drops parts of a typed proof (lengths, chain values) which the parser makes again by
asking the oracle (Run/TransportO.lean).

Main names:
  `prArg pr V' A`: C is A's; P puts A's proof through pr; V is V', any verifier on the new type of
    proofs.
  `prSim pr S`: S's, with its proofs put through pr.
  `Spec.pr_privacy`: HasStrongIndexPrivacyWith R A S ζ ⇒ HasStrongIndexPrivacyWith R (prArg pr V'
    A) (prSim pr S) ζ.
  `Spec.pr_wr`: Run/Transport.lean's scheme and simulator are these, by definition.

Limits: this file says nothing on completeness, index binding: they read V'.
-/
import Run.Transport
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

section
variable {lam : ℕ} {I X W PP IVK ISK Pf B : Type}

/-- A's committer; A's prover, its proofs put through pr; any verifier. -/
def prArg (pr : Pf → B) (V' : IVK → X → B → OComp lam Bool) (A : Arg lam I X W IVK ISK Pf) :
    Arg lam I X W IVK ISK B where
  C := A.C
  P := fun isk x w => (A.P isk x w).mapO pr
  V := V'

/-- The simulator. -/
def prSim (pr : Pf → B) (S : Simulator lam PP IVK X Pf) :
    Simulator lam PP IVK X B where
  St := S.St
  init := S.init
  answer := S.answer
  prove := fun s x => (S.prove s x).map fun o => (pr o.1, o.2)

end

namespace Spec

/-- Under the hypotheses below, privacy needs nothing of a parser. -/
def pr_privacy : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (pr : Pf → B) (V' : IVK → X → B → OComp lam Bool)
      (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
      (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞),
    HasStrongIndexPrivacyWith R A S ζ → HasStrongIndexPrivacyWith R (prArg pr V' A) (prSim pr S) ζ

/-- States: the plain case (Run/Transport.lean) is an instance, by definition. -/
def pr_wr : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : Wr Pf B)
      (A : Arg lam I X W IVK ISK Pf) (S : Simulator lam PP IVK X Pf),
    c.arg A = prArg c.print (c.arg A).V A ∧ c.sim S = prSim c.print S

end Spec
end Run
