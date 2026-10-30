-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Job.lean: a summand in the form of
Johnson/Desc/K5/Honest/Terms.lean as what the masked sumcheck's part asks of its caller (`SumJob`,
Honest/Sum.lean). One definition with code; no theorem.

All variables of an attention segment's sumchecks are summed plainly, so a job has no points. The
summand and the lead are handed the input and `Front`: what stands in front of the part.

Limits. Nothing holds a summand against the verifier's text here, or its counts against the call's
shape (`Summand.fits`).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.K5.Honest.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open H2K5.Honest (Summand)

variable {W X : Type}

/-- **A summand as a caller's job.** shape: the call's public shape; lead: the true values of the
scalars that are sent at the head of the sumcheck's first message; S: the summand. -/
def jobOf (shape : Call) (lead : W → Front X → List E) (S : W → Front X → Summand) : SumJob W X :=
  { shape := shape, points := fun _ _ => [], lead := lead
    round := fun w fr rs => (S w fr).round rs
    inY := fun w fr rs m => (S w fr).inY rs m
    ends := fun w fr rs => (S w fr).endsAt rs }

end ProofFile.Honest.K5
