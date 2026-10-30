-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionAtTheBase.lean: the two structures on the rows of the attention segments' own rounds at a
return of the base maker, the maker at the filling that the online filling reads through. It stays
conditional on that return and on the library's head. The rows are at the base filling's types.

What the two structures say and do not say is in the heads of Honest/K5/Law/AttentionAtAFilling.lean
and Honest/K5/Law/AttentionBookAtAFilling.lean: of Good they speak at every first condition that holds nowhere, and
exact is the spender's half. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.AttentionLawAtTheTerm
import E2E.AttentionBookAtBase

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.Attention
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (baseMaker)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

/-- **The law and the book at a return of the base maker.** CONDITIONAL: hA; h. -/
theorem attention_at_base {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl} {description : OnBytes.Maker.WholeD}
    {run : LPFD.Full.RunPF} {x : VerifiableInference.Desc.First.Look.Place}
    (hA : baseMaker files = .ok A)
    (h : AtMgA OnBytes.secondHashFunction files description run A.Z places firstChain x) :
    AttentionLawAt A ∧ AttentionBookAt A :=
  ⟨attention_law_at_base hA h, attention_book_at_base hA h⟩

end AtPublicFiles.AtFiles.HonestTerm.Attention

#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attention_at_base
