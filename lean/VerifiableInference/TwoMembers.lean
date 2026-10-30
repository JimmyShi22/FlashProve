-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/TwoMembers.lean

A bound on the probability that one commitment is accepted by two argument systems of a family, if
each system's verifier compares the commitment with the hash of a string that names the system.

Let `system t` be an argument system for each `t` of a type `Member`. Suppose that each proof of
`system t` determines a bit string `code t proof`, that the verifier of `system t` accepts a
commitment only if the hash function's value at that string is the commitment, and that strings
for different `t` are different. Then an algorithm that makes at most `queries` queries and outputs
one commitment with two members of the family, each with a prompt, output tokens and a proof, has
both verifiers accept, at two different members, with probability at most (queries + 2)² / 2^256.
The two members are outputs of the algorithm: it may pick them after its queries.

The file is general: it reads no protocol and no model.
-/
import VerifiableInference.Bridge
import Compile.DigestKeyBinding

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

open RandomizedAlgorithm

/-- What an algorithm claims of one member of a family of argument systems: the member, a prompt,
output tokens and a proof. -/
structure ClaimAt {Member : Type} (system : Member → ArgumentSystem) where
  member : Member
  prompt : List Token
  output : List Token
  proof : (system member).Proof

/-- The experiment: the algorithm outputs a commitment and two claims; the verifier of each claim's
member is run on the commitment and the claim. The result is the two members and the two
decisions. -/
def twoMembersExperiment {Member : Type} (system : Member → ArgumentSystem)
    (algorithm : RandomizedAlgorithm (Commitment × ClaimAt system × ClaimAt system)) :
    RandomizedAlgorithm (Member × Member × Bool × Bool) :=
  algorithm.bind fun out =>
    ((system out.2.1.member).verify out.1 out.2.1.prompt out.2.1.output
      out.2.1.proof).toRandomized.bind fun first =>
    ((system out.2.2.member).verify out.1 out.2.2.prompt out.2.2.output
      out.2.2.proof).toRandomized.bind fun second =>
    .done (out.2.1.member, out.2.2.member, first, second)

/-- Under two hypotheses on the family, an algorithm that makes at most `queries` queries has one
commitment accepted at two different members of the family with probability at most (queries + 2)² /
2^256. `accepts_only`: a member's verifier accepts only if the hash function's value at the code of
the proof is the commitment. `apart`: codes at different members are different. -/
theorem Prob_twoMembers_le {Member : Type} (system : Member → ArgumentSystem)
    (code : ∀ t, (system t).Proof → BitString)
    (accepts_only : ∀ (t : Member) (hash : Hash) (commitment : Commitment)
      (prompt output : List Token) (proof : (system t).Proof),
      (system t).accepts hash commitment prompt output proof = true →
        hash (code t proof) = commitment)
    (apart : ∀ (t t' : Member) (proof : (system t).Proof) (proof' : (system t').Proof),
      code t proof = code t' proof' → t = t')
    (queries : ℕ)
    (algorithm : RandomizedAlgorithm (Commitment × ClaimAt system × ClaimAt system))
    (bound : algorithm.QueryBound queries) :
    Prob (twoMembersExperiment system algorithm)
        {result | result.1 ≠ result.2.1 ∧ result.2.2.1 = true ∧ result.2.2.2 = true}
      ≤ (((queries + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  let codes : Commitment × ClaimAt system × ClaimAt system → ZKCP.Str × ZKCP.Str :=
    fun out => (code out.2.1.member out.2.1.proof, code out.2.2.member out.2.2.proof)
  refine le_trans (MeasureTheory.lintegral_mono fun hash => ?_)
    (ZKCP.Pr_answerRepeats_le ((algorithm.toUpload.mapO codes).bind ZKCP.DigestKey.askTwo)
      (queries + 2)
      (ZKCP.OComp.QueryBound.bind ZKCP.DigestKey.askTwo 2 ZKCP.DigestKey.queryBound_askTwo _
        queries (ZKCP.OComp.QueryBound.mapO _ _ queries ((queryBound_toUpload _ _).2 bound))))
  show ZKCP.prob ((twoMembersExperiment system algorithm).run hash) _
    ≤ ZKCP.prob (((algorithm.toUpload.mapO codes).bind ZKCP.DigestKey.askTwo).withTrace.run hash) _
  refine le_trans ?_ (ZKCP.DigestKey.prob_two_strings_le hash (algorithm.toUpload.mapO codes))
  let decisions : Commitment × ClaimAt system × ClaimAt system → Member × Member × Bool × Bool :=
    fun out => (out.2.1.member, out.2.2.member,
      (system out.2.1.member).accepts hash out.1 out.2.1.prompt out.2.1.output out.2.1.proof,
      (system out.2.2.member).accepts hash out.1 out.2.2.prompt out.2.2.output out.2.2.proof)
  have e : (twoMembersExperiment system algorithm).run hash
      = (algorithm.run hash).map decisions := by
    unfold twoMembersExperiment
    rw [run_bind]
    show (algorithm.run hash).bind _ = (algorithm.run hash).bind fun out => PMF.pure (decisions out)
    refine congrArg (PMF.bind (algorithm.run hash)) (funext fun out => ?_)
    rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_bind,
      DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
    rfl
  rw [e, ZKCP.OComp.run_mapO, run_toUpload, ZKCP.prob_map, ZKCP.prob_map]
  refine ZKCP.prob_mono _ fun out h => ?_
  obtain ⟨hne, h1, h2⟩ := h
  exact ⟨fun hc => hne (apart _ _ _ _ hc),
    (accepts_only _ hash out.1 _ _ _ h1).trans (accepts_only _ hash out.1 _ _ _ h2).symm⟩

end VerifiableInference

#print axioms VerifiableInference.Prob_twoMembers_le
