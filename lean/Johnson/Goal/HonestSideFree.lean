-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/HonestSideFree.lean: soundness under the public files' policy (`SoundUnderPolicyAt`,
`G8bits`) reads of a description's honest side the type of its randomness alone. A description that
differs from `D` in the four fields `Rand`, `sample`, `commit` and `prove` alone has `D`'s verifier
and extractor, and soundness under the public files' policy passes from `D` to it. Statements with
short proofs, general in `D`; then at `theDescription`. No definition: no new goal is stated.
"Binding" in this file is the opening form, `BindsWith` (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give.
Why. `theDescription`'s own honest side is hollow. Whoever lays a committer into a description (to
state the goal on binding, `G9bits`, of it) needs the goal on soundness, `G8bits`, of the same
description, at the same extractor. The library has that step for descriptions of one form
(`withTerms`: `soundUnderPolicyAt_withTerms`, Johnson/Goal/Conditions/DescribeTermsSound.lean, under
a premise on the extractor; `reBound`, with and without `withTerms`:
Johnson/Goal/Conditions/ReBoundGoals.lean). Here it is had for any values of these four fields.
  `verify_honestSide`, `extractor_honestSide`, `verifierWithin_honestSide`: the verifier, the
    extractor and the bound on the verifier's own queries are `D`'s: by definition.
  **`soundUnderPolicyAt_honestSide`**: `SoundUnderPolicyAt` (Ladder.lean) passes over, at the same
    error. One direction alone. The one premise: the new type of randomness has a member. The
    sampler yields one (`firstResult`, DescribeTermsSound.lean); it is kept as a premise, so that
    this file need not import that one.
  `g8bits_honestSide`: so the goal `G8bits` (Ladder/Bits.lean), for a family of descriptions.
  **`g8bits_theDescription_honestSide`**: `G8bits` of `theDescription` with any honest side laid in,
    from `g8bits_of_verify` (Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean).
  `bindsWith_bits_of_square`: binding at the error `epsBind honestBudget (t + q)`, with q at most
    2^40 (a round bound: the lemma that is called allows q up to 2^49 - 2), gives binding at the
    goals' own error `bindingErrorInQueries` (`BindsWith.min_one`, `epsBind_min_le_bitsBinding`,
    Ladder/FitBindsBits.lean). It only loses: at t = 0 and q = 0 the error goes from about 2^-156 to
    about 2^-101. Whoever wants the number cites the first error.
Limits. Nothing on binding, completeness or hiding is shown of any honest side: these statements
hold whatever committer, sampler and prover are laid in, a committer that does not bind among them.
So `G8bits` of such a description says of its committer nothing at all; it means something only
together with `G9bits` at the same extractor and `G3'pol` (the head of Ladder.lean, 6). "any honest
side" means these four fields. The fields `P` (the three protocols' honest provers, which stand in
the types of keys and proofs; at `theDescription` they are `Files.fixedMessageProvers`), `Shown`, `shown`, `Form`
and `parse` stay `D`'s: a description with other provers in `P`, another form or another parser is
not reached by these statements. `SoundAt`, and so the goals `G7'` and `G7'bits`, are not treated
here. No honest side is written here, and none is tied to a program. All limits of
SoundOfVerifyPolicy.lean hold of `g8bits_theDescription_honestSide`: among them that no theorem says
that `protocolDataWellFormed` says yes at other files than the written copies (AtFullSide/Top/), that a verifier
that rejects everything meets the goal, and that files on coding theory adapted from third-party
Lean (lean/LIMITS.md, L15) stand beneath it. `bindsWith_bits_of_square` is arithmetic on a bound: it
shows binding of nothing.

-/
import Johnson.Goal.Skeleton.SoundOfVerifyPolicy
import Ladder.FitBindsBits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

section One
variable (D : Description) (R : Type) (sa : RandomizedAlgorithm R)
  (co : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → R →
    DeterministicAlgorithm Commitment)
  (pr : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → R → List Token → List Token →
    RandomizedAlgorithm D.Form)

/-- The verifier is `D`'s. -/
theorem verify_honestSide (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form) :
    verify { D with Rand := R, sample := sa, commit := co, prove := pr } Z parse =
      verify D Z parse := rfl

/-- The extractor is `D`'s. -/
theorem extractor_honestSide :
    ({ D with Rand := R, sample := sa, commit := co, prove := pr } : Description).extractor =
      D.extractor := rfl

/-- The bound on the verifier's own queries is `D`'s. -/
theorem verifierWithin_honestSide :
    VerifierWithin { D with Rand := R, sample := sa, commit := co, prove := pr } ↔
      VerifierWithin D := Iff.rfl

/-- **Soundness under the files' policy passes over**, at the same error and the same extractor,
whatever is laid into the four fields. It says nothing of what is laid in. -/
theorem soundUnderPolicyAt_honestSide (ρ₀ : R) (eps : ℕ → ℕ → ℝ≥0∞)
    (h : SoundUnderPolicyAt D eps) :
    SoundUnderPolicyAt { D with Rand := R, sample := sa, commit := co, prove := pr } eps :=
  fun Z pp scope read =>
    ⟨(h Z pp scope read).1, fun Form prove parse n within =>
      (h Z pp scope read).2 Form (fun w _ prompt output => prove w ρ₀ prompt output) parse n
        within⟩

end One

/-- **The goal `G8bits` passes over**, for a family of descriptions. -/
theorem g8bits_honestSide (D : SecondHashFunctionType → Description) (R : Type) (ρ₀ : R)
    (sa : RandomizedAlgorithm R)
    (co : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → R →
      DeterministicAlgorithm Commitment)
    (pr : ∀ o, PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → R → List Token →
      List Token → RandomizedAlgorithm (D o).Form)
    (h : G8bits D) :
    G8bits fun o => { D o with Rand := R, sample := sa, commit := co, prove := pr o } :=
  ⟨h.1, soundUnderPolicyAt_honestSide (atSecondHashFunction D) R sa co (pr OnBytes.secondHashFunction) ρ₀ soundnessErrorInQueries h.2⟩

/-- **From the square form to the goals' own error.** Arithmetic on a bound. -/
theorem bindsWith_bits_of_square {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} (q : ℕ) (hq : q ≤ 2 ^ 40)
    (h : BindsWith system extractor fun t => epsBind honestBudget (t + q)) :
    BindsWith system extractor bindingErrorInQueries :=
  BindsWith.mono (BindsWith.min_one h) fun t =>
    epsBind_min_le_bitsBinding honestBudget q (by
      have h1 : honestBudget = 2 ^ 48 := rfl
      have h2 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
      have h3 : (2 : ℕ) ^ 50 = 1125899906842624 := by norm_num
      have h4 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
      rw [h4] at hq
      rw [h1, h2, h3]
      omega) t

end VerifierAndGoals.Fit

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **`G8bits` OF `theDescription` WITH ANY HONEST SIDE LAID IN**: any values of the four fields
`Rand`, `sample`, `commit` and `prove`; the protocols' provers in `P`, the form and the parser stay.
It says nothing of that honest side: see the head. -/
theorem g8bits_theDescription_honestSide (R : Type) (ρ₀ : R) (sa : RandomizedAlgorithm R)
    (co : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → R →
      DeterministicAlgorithm Commitment)
    (pr : ∀ o, PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → R → List Token →
      List Token → RandomizedAlgorithm (theDescription o).Form) :
    G8bits fun o =>
      { theDescription o with Rand := R, sample := sa, commit := co, prove := pr o } :=
  g8bits_honestSide theDescription R ρ₀ sa co pr g8bits_of_verify

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.Fit.verify_honestSide
#print axioms VerifierAndGoals.Fit.extractor_honestSide
#print axioms VerifierAndGoals.Fit.verifierWithin_honestSide
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_honestSide
#print axioms VerifierAndGoals.Fit.g8bits_honestSide
#print axioms VerifierAndGoals.Fit.bindsWith_bits_of_square
#print axioms VerifierAndGoals.AtTheName.g8bits_theDescription_honestSide
