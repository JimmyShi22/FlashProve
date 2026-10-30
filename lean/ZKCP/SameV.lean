-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/SameV.lean: the binding properties of a scheme depend on its verifier only.

In the experiments of index binding (ZKCP/Defs.lean, `HasIndexBinding`), of index binding for many
sessions (ZKCP/Optional.lean) and of "no two answers" (ZKCP/TwoIndices.lean) committer and prover
are the adversary's; of the scheme only V is run. So two schemes with the same verifier share these
properties, with the same extractor and bounds, even if their committers and provers differ and
their keys isk have different types (which ZKCP/SameRun.lean does not allow). The experiments are
equal as terms (`bindingExp_eq`, `verifyAll_eq`, `multiBindingExp_eq`).

Limits: The hypothesis is an equality of functions, A.V = A'.V. Nothing is said of completeness or
privacy, which run C and P. Nothing here says that two given schemes have the same verifier.

After ZKCP/Defs.lean, `HasIndexBinding`, and index binding for many sessions of ZKCP/Optional.lean.
Definitions are cited by their names in ZKCP/Defs.lean.
-/
import ZKCP.TwoIndices

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP
namespace SameV

variable {lam : ℕ} {I X W PP IVK ISK ISK' Pf K Y : Type} {A : Arg lam I X W IVK ISK Pf}
  {A' : Arg lam I X W IVK ISK' Pf} (hV : A.V = A'.V)
include hV

/-! ## The experiments -/

theorem bindingExp_eq {St : Type} (E : Extractor lam I X W IVK Pf)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    bindingExp A E Ct Pt = bindingExp A' E Ct Pt := by
  unfold bindingExp
  rw [hV]

theorem verifyAll_eq (ivk : IVK) : ∀ l : List (X × Pf), verifyAll A ivk l = verifyAll A' ivk l
  | [] => rfl
  | (x, π) :: rest => by
      unfold verifyAll
      rw [hV, verifyAll_eq ivk rest]

theorem multiBindingExp_eq {St : Type} (Ei : IVK → Trace lam → Option I)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (List (X × Pf))) :
    multiBindingExp A Ei Ct Pt = multiBindingExp A' Ei Ct Pt := by
  unfold multiBindingExp
  simp only [verifyAll_eq hV]

/-! ## The properties: the same relation, extractor and bounds on both sides -/

variable (R : IndexedRelation I X W PP)

/-- If A.V = A'.V: index binding with the extractor named, for A exactly if for A'. -/
theorem hasIndexBindingWith_iff (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWith R A E ε ↔ HasIndexBindingWith R A' E ε := by
  unfold HasIndexBindingWith
  simp only [bindingExp_eq hV]

theorem hasIndexBinding_iff (ε : ℕ → ℕ → ℝ≥0∞) : HasIndexBinding R A ε ↔ HasIndexBinding R A' ε :=
  exists_congr fun E => hasIndexBindingWith_iff hV R E ε

/-- If A.V = A'.V: index binding for many sessions, for A exactly if for A'. -/
theorem hasSessionAugmentedBinding_iff (ε : ℕ → ℕ → ℕ → ℝ≥0∞) :
    HasSessionAugmentedBinding R A ε ↔ HasSessionAugmentedBinding R A' ε := by
  unfold HasSessionAugmentedBinding
  simp only [multiBindingExp_eq hV]

omit R in
/-- If A.V = A'.V: "no two answers", for A exactly if for A'. -/
theorem noTwoAnswers_iff (key : X → K) (val : X → Y) (ε : ℕ → ℕ → ℕ → ℝ≥0∞) :
    NoTwoAnswers A key val ε ↔ NoTwoAnswers A' key val ε := by
  unfold NoTwoAnswers
  simp only [multiBindingExp_eq hV]

end SameV
end ZKCP
