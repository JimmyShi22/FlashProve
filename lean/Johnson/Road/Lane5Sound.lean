-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5Sound.lean

From the named hypotheses of Lane5Holes.lean to a statement on a prompt and output tokens: if the
request built from them has a witness of the relation, the output meets the policy under the scores
of the weights that the index holds; at the policy of exact match, the output tokens are the
integer model's.

Two steps, both taken as they stand. "language_of_holes" (Lane5Holes.lean): a request with a witness
is true under its policy. "Policy.meetsPolicy_of_isTrueUnder" (Policy/Front/TrueUnder.lean): the
request built from a prompt, output tokens and a padding is true under a policy, so the output meets
the policy.

Main theorems:
* "sound_of_holes": at a lawful table of scales, valid settings that are the table's
  ("tie : settingsOf scales = settings"), a policy with "Policy.PolCond", and under "MeanHoles":
  for every index, prompt, output, padding and request: if "requestOfTokens" builds the request and
  the request has a witness, then "Policy.MeetsPolicy" holds of prompt and output at the weights
  that the index holds.
* "sound_of_holes_exact": the same at "AcceptancePolicy.exact", at the table's own settings, in the words of the
  integer model: for every position of the output, "IntegerModel.nextToken" at the table and the
  index's tensors, on the prompt followed by the output before that position, is the output's token
  there.

Not claimed: that "MeanHoles" holds of any relation; see Lane5Holes.lean. What "MeetsPolicy" is
worth under a given policy: see the head of Policy/Front/MeetsPolicy.lean and part 5 of
Policy/Front/MeetsPolicyGuards.lean. Nothing on probabilities, extractors
or protocols. The statement with "nextToken" is for exact match alone: under another policy the
output need not be the model's first choice.

-/
import Johnson.Road.Lane5Holes
import Policy.Front.TrueUnder
import Policy.Front.MeetsPolicyGuards
import IntegerModel.Arrays.SameModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open VerifiableInference

/-- **Sound**: a built request with a witness, so the output meets the policy. This is said under
the hypotheses that stand in the statement itself, which this comment does not list; it is no claim
that they hold. -/
theorem sound_of_holes {W : Type} {scales : Cm.Scales} (lawful : scales.Lawful)
    {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    (tie : settingsOf scales = settings) {pol : AcceptancePolicy} (hpol : Policy.PolCond pol)
    {Rno : Cm.Idx → Instance ppref → W → Prop} {mx : Cm.Idx → Instance ppref → W → ℕ → Mx}
    (H : MeanHoles scales pol Rno mx) :
    ∀ (i : Cm.Idx) (x' : List Token × List Token) (a : List Token) (x : Instance ppref),
      requestOfTokens x' a = some x → (∃ w, Rno i x w) →
        Policy.MeetsPolicy settings pol (weightsOfIndex valid i) x'.1 x'.2 :=
  fun i x' _ x built ⟨w, h⟩ =>
    Policy.meetsPolicy_of_isTrueUnder lawful valid tie pol i (prompt := x'.1) (output := x'.2)
      built (language_of_holes lawful hpol H i x w h)

/-- **Sound at exact match**: a built request with a witness, so the output tokens are the integer
model's. This is said under the hypotheses that stand in the statement itself, which this comment
does not list; it is no claim that they hold. -/
theorem sound_of_holes_exact {W : Type} {scales : Cm.Scales} (lawful : scales.Lawful)
    {Rno : Cm.Idx → Instance ppref → W → Prop} {mx : Cm.Idx → Instance ppref → W → ℕ → Mx}
    (H : MeanHoles scales AcceptancePolicy.exact Rno mx) :
    ∀ (i : Cm.Idx) (x' : List Token × List Token) (a : List Token) (x : Instance ppref),
      requestOfTokens x' a = some x → (∃ w, Rno i x w) →
        ∀ position (h : position < x'.2.length),
          IntegerModel.nextToken scales i.index (x'.1 ++ x'.2.take position) =
            some x'.2[position] :=
  fun i x' a x built hw position h => by
    rw [← modelNextToken_eq_nextToken lawful (settingsAreValid_settingsOf lawful) rfl i]
    exact ((Policy.meetsPolicy_exact_iff
      (weightsOfIndex (settingsAreValid_settingsOf lawful) i) x'.1 x'.2).1
      (sound_of_holes lawful (settingsAreValid_settingsOf lawful) rfl AcceptancePolicy.exact_ok H i x' a x
        built hw)).2 position h

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.sound_of_holes
#print axioms OnBytes.Road.L5.sound_of_holes_exact
