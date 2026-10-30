-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GenWit.lean: from a scheme without witnesses to the syntax with witnesses.

Definitions and statements; the proofs are in CompileK/GenWitProofs.lean. Generic in the scheme.
A scheme (`Arg`, ZKCP/Gen.lean) is a committer C, a prover P of batches and a verifier V, all over a
family of oracles.
The compiler of Compile/Batch builds schemes whose prover is handed pairs (x, ()). `withW W A` is A
in the syntax with witnesses of the type W: its prover ignores the witness that it is handed. Under
the hypotheses of their statements, completeness and privacy carry over from the relation "x has a
witness" (`Spec.withW_completeness`, `Spec.withW_privacy`). Index binding does not: it needs an
extractor for witnesses (CompileK/KnowExt.lean, CompileK/KnowBinding.lean).
DECLARED DIFFERENCE to the paper, where the prover is handed the cells.
-/
import ZKCP.Gen

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen
open Rom (OSpec)

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- The witnesses forgotten. -/
def forgetW (b : List (X × W)) : List (X × Unit) := b.map fun xw => (xw.1, ())

/-- A in the syntax with witnesses; the prover ignores them. -/
def withW (W : Type) (A : Arg S I X Unit IVK ISK Pf) : Arg S I X W IVK ISK Pf where
  C := A.C
  P := fun k b =>
    (A.P k (forgetW b)).bind fun l => .pure ⟨l.val, l.property.trans (List.length_map _)⟩
  V := A.V

/-- Two relations with witnesses, no public parameters. -/
def relPairW (Ryes Rno : I → X → W → Prop) (sub : ∀ i x w, Ryes i x w → Rno i x w) :
    RelPair I X W Unit :=
  ⟨Ryes, Rno, sub, fun _ => ()⟩

namespace Spec

def withW_completeness : Prop :=
  ∀ (S : OSpec) (I X W PP IVK ISK Pf : Type) (R : RelPair I X W PP) (R₀ : RelPair I X Unit PP)
      (A : Arg S I X Unit IVK ISK Pf) (B : ℕ) (α : ℝ≥0∞),
    (∀ i x w, R.yes i x w → R₀.yes i x ()) →
    HasCompletenessError R₀ A B α → HasCompletenessError R (withW W A) B α

def withW_privacy : Prop :=
  ∀ (S : OSpec) (I X W PP IVK ISK Pf : Type) (R : RelPair I X W PP) (R₀ : RelPair I X Unit PP)
      (A : Arg S I X Unit IVK ISK Pf) (B : ℕ) (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞),
    (∀ i x w, R.yes i x w → R₀.yes i x ()) → R.pp = R₀.pp → HasIndexPrivacyWith R₀ A B Sim ζ →
    HasIndexPrivacyWith R (withW W A) B Sim ζ

end Spec
end ZKCP.Gen
