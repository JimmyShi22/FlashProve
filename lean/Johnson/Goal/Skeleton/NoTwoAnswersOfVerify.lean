-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/NoTwoAnswersOfVerify.lean: UNDER ONE COMMITMENT AND ONE SET OF PUBLIC FILES
THAT STATE EXACT MATCH, NO PROMPT GETS TWO DIFFERENT ACCEPTED OUTPUTS OF THE SAME LENGTH, but for a
stated error. A consequence of the soundness theorem on `verify` (`sound_of_verify_at`,
SoundOfVerifyAt.lean), in a form that this library defines (`ZKCP.NoTwoAnswers`,
ZKCP/TwoIndices.lean). No definition; it adds nothing beneath `verify`. IT STATES NO GOAL OF THE
PROJECT: it is a theorem about what is proved.

  isModelOutput_unique: for every argument system: at given weights and a given prompt there is at
      most one list of output tokens of a given length that is the model's. (Every start of the
      model's output is the model's output too, so the length has to be part of the question.)
  noTwoAnswers_of_verify_at: at public files Z in scope that are read and state exact match: for
      every committer with at most tC queries to the hash function and every prover with at most tP
      queries, which hands in one list of requests with proofs under the committer's one commitment:
      the probability that the list has at most N entries and `verify` accepts two of them with the
      same prompt, outputs of the same length, and different outputs is at most `N * soundnessErrorInQueries (tC + tP)
      1`. N bounds the length of the WHOLE list, not the number of proofs that collide; tP bounds
      the prover's queries for the whole list. For a list of two: `2 * soundnessErrorInQueries (tC + tP) 1`, where tP
      bounds the queries for both proofs together. It is `ZKCP.noTwoAnswers_of` at
      `sessionAugmented_union_of_verify_at` (SoundOfVerifyForms.lean).

What it does not say. IT IS NO BINDING OF THE COMMITMENT AS A COMMITMENT: it does not say that a
commitment can be opened only to the extractor's weights (`BindsWith`), nor that nobody opens one
commitment to two sets of weights (`NoTwoOpenings`; both in VerifiableInference/MoreStatements.lean;
this library proves them of other systems); no committer's algorithm occurs in it; two sets of
weights with the same outputs are not told apart. Nor does it say that an accepted output is the
output of the weights that an honest committer put in (correctness of extraction). Nothing on two
proofs under two commitments, or at two sets of public files. Nothing at a policy other than exact
match: there two different outputs can both meet the policy. Of outputs of different lengths this
form says nothing (by soundness for many proofs the shorter of two accepted outputs on one prompt is
a start of the longer, but for the same error: an argument; no theorem here states it). The prover
hands in one list at once, sees no decision of the verifier before, and sees no honest proof.
`ZKCP.NoTwoAnswers` begins with "there is a function Ei", because its experiment puts out that
function's value; the event does not read it.
Limits. `soundnessErrorInQueries t n` (Ladder/Bits.lean) is 16 (t + n + 2^23) / 2^128 + (t + n + 2^23 + 2)^2 / 2^256:
never below about 2^-101. The limits of SoundOfVerifyAt.lean and SoundOfVerifyForms.lean travel
whole: where `protocolDataWellFormed` says no, `verify` rejects everything and the statement holds for that reason;
THAT `protocolDataWellFormed` SAYS YES AT THE RELEASE'S FILES AS BYTES, AND THAT THE HONEST PROOF IS ACCEPTED
THERE, IS EVALUATED, NOT PROVED; the public files are fixed before the hash function is drawn; the
format's second hash function is a fixed function; at the full size alone; the verifier with
fourteen entry tests; the description's own parser; beneath some of the theorems that the soundness
theorem calls stand files on coding theory adapted from third-party Lean (lean/LIMITS.md, L15).


-/
import Johnson.Goal.Skeleton.SoundOfVerifyForms
import ZKCP.TwoIndices

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace VerifiableInference

/-- At given weights and a given prompt, two lists of output tokens of one length that are both the
model's are equal. -/
theorem isModelOutput_unique (system : ArgumentSystem) (weights : system.Weights)
    (prompt output output' : List Token) (h : system.IsModelOutput weights prompt output)
    (h' : system.IsModelOutput weights prompt output') (hl : output.length = output'.length) :
    output = output' := by
  have key : ∀ n, n ≤ output.length → output.take n = output'.take n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn1 : n < output.length := hn
      have hn2 : n < output'.length := hl ▸ hn1
      have e := ih (Nat.le_of_lt hn1)
      have a := h n hn1
      have b := h' n hn2
      rw [e] at a
      have hEq : output[n] = output'[n] := Option.some.inj (a.symm.trans b)
      rw [List.take_succ_eq_append_getElem hn1, List.take_succ_eq_append_getElem hn2, e, hEq]
  have all := key output.length le_rfl
  rw [List.take_length, hl, List.take_length] at all
  exact all

end VerifiableInference

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference

/-- **UNDER ONE COMMITMENT, AT ONE SET OF PUBLIC FILES, IN SCOPE, READ, WITH EXACT MATCH: NO PROMPT
GETS TWO DIFFERENT ACCEPTED OUTPUTS OF THE SAME LENGTH.** The question is the prompt with the
output's length; the answer is the output. -/
theorem noTwoAnswers_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    ZKCP.NoTwoAnswers
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadArgument
      (fun x : List Token × List Token => (x.1, x.2.length))
      (fun x : List Token × List Token => x.2)
      fun tC tP N => N * VerifierAndGoals.soundnessErrorInQueries (tC + tP) 1 :=
  ZKCP.noTwoAnswers_of
    (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadRelation _ _ _ _
    (fun weights x x' hx hx' hk => by
      obtain ⟨_, hx⟩ := hx
      obtain ⟨_, hx'⟩ := hx'
      obtain ⟨h1, h2⟩ := Prod.mk.inj hk
      have hx'' : (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).IsModelOutput
          weights x.1 x'.2 := h1 ▸ hx'
      exact isModelOutput_unique _ weights x.1 x.2 x'.2 hx hx'' h2)
    (sessionAugmented_union_of_verify_at Z pp scope read exact)

end VerifierAndGoals.AtTheName

#print axioms VerifiableInference.isModelOutput_unique
#print axioms VerifierAndGoals.AtTheName.noTwoAnswers_of_verify_at
