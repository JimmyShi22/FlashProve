-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfVerifyForms.lean: the two soundness theorems on `verify`
(`sound_of_verify_at`, SoundOfVerifyAt.lean; `soundUnderPolicy_of_verify_at`,
SoundOfVerifyPolicy.lean), said again in forms that this library already defines. No new definition;
no goal is stated; nothing beneath `verify` changes. The proofs are calls of theorems of this
library, but for five lemmas on every argument system (section 1).

THE SYSTEM is `systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)`: the verifier is
`verify` with the description's own parser, at one set of public files Z. In the form of
ZKCP/Defs.lean (`uploadRelation`, `uploadArgument`, VerifiableInference/Agreement.lean): the index
is the weights; an instance is a prompt with output tokens; there is no witness; the index
verification key is the commitment, 256 bits; all else that a prover hands in, the key file among
it, is part of the proof.

THE ERROR. `soundnessErrorInQueries t n` (Ladder/Bits.lean) is 16 (t + n + 2^23) / 2^128 + (t + n + 2^23 + 2)^2 /
2^256: that is 16 / 2^128, or 124 bits, for each query, and never below about 2^-101. t counts the
adversary's queries to the hash function; n = 1 bounds those of the description's own parser; the
2^23 is a fixed allowance for the verifier's own queries (`VerifierWithin`). Below, tC bounds the
committer's queries and tP the prover's.

  indexBinding_of_verify_at: INDEX-BINDING KNOWLEDGE SOUNDNESS, FOR A CLAIM WITHOUT A WITNESS
      (`ZKCP.HasIndexBinding`), at files in scope that are read and state exact match, with the
      error `soundnessErrorInQueries (tC + tP) 1`. There is one index extractor, shown the commitment and the
      committer's queries to the hash function with their answers alone (a function: no bound on its
      running time is asked); but for that error, no output is accepted where it gives no weights,
      or that is not the model's at the weights that it gives. It is `sound_of_verify_at` through
      `sound_iff`. The statement has the extractor under "there is": it need not be the
      description's own, and a statement on what the extractor gives back at an honest commitment
      cannot be joined to it. The name does not mean that a prover knew the weights: knowledge
      soundness with a witness, the model's run read off a proof and the prover's queries, is not
      this theorem.
  indexBindingWith_of_verify_at: the same WITH THE EXTRACTOR NAMED: the description's own
      (`ZKCP.HasIndexBindingWith`). It is `soundUnderPolicy_of_verify_at` at exact match, where an
      output that meets the policy is the model's (`Policy.meetsPolicy_exact_iff`).
  soundManyProofs_union_of_verify_at, sessionAugmented_union_of_verify_at: MANY PROOFS UNDER ONE
      COMMITMENT, BY A UNION BOUND, in this library's two forms (`SoundManyProofs`,
      VerifiableInference/MoreStatements.lean; `ZKCP.HasSessionAugmentedBinding`,
      ZKCP/Optional.lean), with the error `N * soundnessErrorInQueries t 1`, where t = tC + tP. No further premise. Of
      the experiment: the prover hands in ONE list of requests with proofs, at once; tP bounds its
      queries for the WHOLE list; it sees no decision of the verifier before it hands the list in.
      The extractor is fixed before N. In the first form entries behind the first N are not checked;
      in the second a list of more than N entries is never counted as a failure. An experiment with
      N separate sessions of at most tP queries EACH is another one: laid into this one, if its
      prover sees no decision between sessions, that prover has N * tP queries, and the bound reads
      `N * soundnessErrorInQueries (tC + N * tP) 1` (an argument; no theorem). The bound is never below about N *
      2^-101.
  soundManyProofs_of_verify_at, sessionAugmented_of_verify_at: THE FORM WITH NO FACTOR N IN FRONT.
      Stated in the same two forms, in the same experiment: the error is that of one proof at
      N * q more queries, `soundnessErrorInQueries (t + N * q) 1`. It is the smaller of the two bounds where t is large
      against q, and the larger one at N = 1 (arithmetic; no theorem). BOTH HAVE ONE PREMISE MORE: q
      bounds the queries to the hash function of one run of `verify`, at every commitment, request
      and proof. No theorem of this library gives such a q: `VerifierWithin` (Ladder/Bits.lean)
      counts the queries of `innerCompiledVerifier` as the compiler counts them, in typed queries, and a typed
      query costs one query to the hash function for each digest of its answer. So these two say
      nothing unless a q is shown.
  indexBindingUnderPolicy_of_verify_at: the first form again for the files' acceptance policy, at
      all files in scope that are read, with the same error: the relation is "the output meets the
      policy at these weights" (`Policy.MeetsPolicy`), written as `ZKCP.languageRelation`; the
      extractor is named: the description's own.

Limits. What these are worth is what the restated theorems are worth: the limits of
SoundOfVerifyAt.lean and SoundOfVerifyPolicy.lean travel whole. Where `protocolDataWellFormed` says no, `verify`
rejects everything and the statements hold for that reason; THAT `protocolDataWellFormed` SAYS YES AT THE RELEASE'S
FILES AS BYTES, AND THAT THE HONEST PROOF IS ACCEPTED THERE, IS EVALUATED, NOT PROVED. Z is a
parameter of the system: the public files are fixed before the hash function is drawn, and the
extractor may depend on them. So the commitment fixes an index only together with Z: no theorem
bars one commitment from being accepted at two sets of public files, with two indices. The
format's second hash function is a fixed function. At the full size alone; the verifier with
fourteen entry tests; the description's own parser. Beneath some of the theorems that the two
restated theorems call stand files on coding theory adapted from third-party Lean (lean/LIMITS.md,
L15).
The empty output is the model's at all weights: at exact
match the forms for "the output is the model's" do not bar an accepted empty output once weights are
extracted. In this system the honest committer and the honest prover are empty placeholders, and
none of these forms reads them: so completeness, correctness of extraction (that the extracted
weights are the honest committer's own) and index privacy cannot be stated of it with content.
The theorem under the policy, alone, is weak: under a tolerant policy some choice of weights,
all-zero weights for one, lets every well-formed output meet the policy, and the theorem speaks of
the weights that its extractor reads off the commitment and the committer's hash queries, whoever
made the commitment. So it means something only together with correctness of extraction at the same
extractor (the heads of SoundOfVerifyPolicy.lean and Ladder.lean say "binding" and `G9` for that
partner), which cannot be stated with content of this system, whose committer is a placeholder,
and with knowing who made the commitment, which no theorem says. At a committer that is written in
Lean beside the description and corresponds to no program of the release, it is proved at the same
extractor: `extracts_atOlder`, `extractor_atOlder` (Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean), with
that file's limits.

-/
import Johnson.Goal.Skeleton.SoundOfVerifyAt
import Johnson.Goal.Skeleton.SoundOfVerifyPolicy
import VerifiableInference.Agreement
import VerifiableInference.ManyProofs
import VerifiableInference.SeveralCommitments
import ZKCP.ManyOfOne
import ZKCP.LanguageRelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal
open MeasureTheory

noncomputable section

/-! ## 1. Five lemmas on every argument system -/

namespace VerifiableInference
open RandomizedAlgorithm

/-- A deterministic algorithm, in the form of ZKCP/Defs.lean, draws no coin. -/
theorem drawsNoCoin_toUpload {α : Type} :
    ∀ algorithm : DeterministicAlgorithm α, algorithm.toRandomized.toUpload.DrawsNoCoin
  | .done _ => trivial
  | .query _ next => fun answer => drawsNoCoin_toUpload (next answer)

/-- Soundness for a claim with a named extractor gives index binding with that extractor
(`ZKCP.HasIndexBindingWith`), for every relation without witnesses that holds wherever the claim
holds (the larger the relation, the less the conclusion says). The other direction:
`soundForWith_of_indexBindingWith` (AgreementWith.lean). The proof is
that of `indexBinding_of_sound` (Agreement.lean), with a claim in the place of "the output tokens
are the model's". -/
theorem indexBindingWith_of_soundForWith (system : ArgumentSystem) {PP : Type}
    (R : ZKCP.IndexedRelation system.Weights (List Token × List Token) Unit PP)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop)
    (hR : ∀ (weights : system.Weights) (x : List Token × List Token), claim weights x.1 x.2 →
      R.rel weights x ())
    (ε : ℕ → ℝ≥0∞) (h0 : SoundForWith system extractor claim ε) :
    ZKCP.HasIndexBindingWith R system.uploadArgument ⟨extractor, fun _ _ _ _ _ => ()⟩
      (fun tC tP => ε (tC + tP)) := by
  classical
  intro tC tP St Ct Pt hC hP
  have b1 := h0 tC tP St (ofUpload Ct) ((queryBound_ofUpload Ct tC).mpr hC)
    (fun state => (ofUpload (Pt state)).bind fun xp => .done (xp.1.1, xp.1.2, xp.2))
    (fun state => queryBound_map _ (ofUpload (Pt state)) tP
        ((queryBound_ofUpload (Pt state) tP).mpr (hP state)))
  refine le_trans ?_ b1
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun H => ?_
  have e1 : (Ct.withTrace.bind fun c => (Pt c.1.2).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, extractor c.1.1 c.2, p.1.1, ()⟩ : ZKCP.BindingOutcome system.Weights
              (List Token × List Token) Unit)).run H
      = ((ofUpload Ct).withQueryLog.run H).bind fun c =>
          ((ofUpload (Pt c.1.2)).withQueryLog.run H).bind fun p =>
          PMF.pure ⟨(system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H, extractor c.1.1 c.2,
              p.1.1, ()⟩ := by
    simp only [ZKCP.run_bind, run_toUpload, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
        run_ofUpload_withQueryLog]
    rfl
  have e2 : ((ofUpload Ct).withQueryLog.bind fun c =>
        ((ofUpload (Pt c.1.2)).bind fun xp => RandomizedAlgorithm.done (xp.1.1, xp.1.2, xp.2)).bind
            fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H
      = ((ofUpload Ct).withQueryLog.run H).bind fun c =>
          ((ofUpload (Pt c.1.2)).withQueryLog.run H).bind fun p =>
          PMF.pure (extractor c.1.1 c.2, p.1.1.1, p.1.1.2,
              (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
        PMF.bind_bind]
    refine congrArg _ (funext fun c => ?_)
    rw [run_withQueryLog_bind_fst H (ofUpload (Pt c.1.2))
      (fun xp => PMF.pure (extractor c.1.1 c.2, xp.1.1, xp.1.2,
          (system.verify c.1.1 xp.1.1 xp.1.2 xp.2).evaluate H))]
  show ZKCP.prob ((Ct.withTrace.bind fun c => (Pt c.1.2).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, extractor c.1.1 c.2, p.1.1, ()⟩ : ZKCP.BindingOutcome system.Weights
              (List Token × List Token) Unit)).run H) _
    ≤ ZKCP.prob (((ofUpload Ct).withQueryLog.bind fun c =>
        ((ofUpload (Pt c.1.2)).bind fun xp => RandomizedAlgorithm.done (xp.1.1, xp.1.2, xp.2)).bind
            fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
  rw [e1, e2, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun p => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le ?_
  rintro ⟨hAccepted, hBad⟩
  show (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H = true
    ∧ ¬ ∃ weights, extractor c.1.1 c.2 = some weights ∧ claim weights p.1.1.1 p.1.1.2
  refine ⟨hAccepted, ?_⟩
  rintro ⟨weights, hWeights, hClaim⟩
  change p.1.1 ∉ R.L (extractor c.1.1 c.2) ∨ ¬ R.rel' (extractor c.1.1 c.2) p.1.1 () at hBad
  rw [hWeights] at hBad
  rcases hBad with hb | hb
  · exact hb ⟨(), hR weights p.1.1 hClaim⟩
  · exact hb (hR weights p.1.1 hClaim)

/-- From one proof to many by a union bound, for every argument system, extractor and claim: if
soundness for the claim holds with the bound ε, then soundness for a list of proofs holds with the
same extractor and the bound `proofCount * ε queries`. No bound on the verifier's queries is asked
(`SoundForWith.manyProofs`, ManyProofs.lean, asks one and has no factor in front). For each place
below `proofCount`: the prover for one proof that runs the prover for many and returns the entry at
that place. -/
theorem SoundForWith.manyProofsUnion (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε) :
    SoundForManyProofsWith system extractor claim fun queries proofCount =>
      proofCount * ε queries := by
  classical
  intro committerQueries proverQueries proofCount State committer committerBound prover proverBound
  show Prob _ _ ≤ (proofCount : ℝ≥0∞) * ε (committerQueries + proverQueries)
  by_cases hProof : Nonempty system.Proof
  · obtain ⟨proof₀⟩ := hProof
    have one := fun index : ℕ => sound committerQueries proverQueries State committer
      committerBound
      (fun state => (prover state).bind fun sent => .done (sent.getD index ([], [], proof₀)))
      (fun state => queryBound_map _ (prover state) proverQueries (proverBound state))
    have total : ∑ _index ∈ Finset.range proofCount, ε (committerQueries + proverQueries)
        = proofCount * ε (committerQueries + proverQueries) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← total]
    refine le_trans ?_ (Finset.sum_le_sum fun index _ => one index)
    unfold Prob
    refine le_trans ?_ (le_of_eq (lintegral_finset_sum (Finset.range proofCount)
      fun index _ => measurable_eventProbability_run _ _))
    refine lintegral_mono fun H => ?_
    show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun sent =>
          (system.verifyEach c.1.1 (sent.take proofCount)).bind fun checked =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, checked)).run H) _
      ≤ ∑ index ∈ Finset.range proofCount,
        ZKCP.prob ((committer.withQueryLog.bind fun c =>
          ((prover c.1.2).bind fun sent =>
            RandomizedAlgorithm.done (sent.getD index ([], [], proof₀))).bind fun y =>
          (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
    simp only [run_bind, run_verifyEach, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
      run_done, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_pure]
    rw [← ZKCP.expect_finset_sum]
    refine ZKCP.expect_mono _ fun c => ?_
    rw [← ZKCP.expect_finset_sum]
    refine ZKCP.expect_mono _ fun sent => ?_
    split_ifs with bad
    · obtain ⟨prompt, output, hMem, hBad⟩ := bad
      obtain ⟨entry, hEntry, hEq⟩ := List.mem_map.1 hMem
      obtain ⟨rfl, hEq'⟩ := Prod.mk.inj hEq
      obtain ⟨rfl, hAccepted⟩ := Prod.mk.inj hEq'
      obtain ⟨index, hIndex, hAt⟩ :=
        exists_getD_of_mem_take ([], [], proof₀) proofCount sent entry hEntry
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_range.2 hIndex))
      refine le_of_eq (if_pos ?_).symm
      rw [hAt]
      exact And.intro hAccepted hBad
    · exact zero_le _
  · -- No proof exists: every list is empty, and the event has probability 0.
    refine le_trans (le_of_eq (Prob_eq_zero _ _ fun hash => ?_)) (zero_le _)
    show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun sent =>
          (system.verifyEach c.1.1 (sent.take proofCount)).bind fun checked =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, checked)).run hash) _ = 0
    refine le_antisymm ?_ (zero_le _)
    rw [run_bind, ZKCP.prob_bind]
    refine le_trans (ZKCP.expect_mono _ fun c => ?_) (le_of_eq (ZKCP.expect_const _ 0))
    rw [run_bind, ZKCP.prob_bind]
    refine le_trans (ZKCP.expect_mono _ fun sent => ?_) (le_of_eq (ZKCP.expect_const _ 0))
    rw [run_bind, run_verifyEach, PMF.pure_bind, run_done, ZKCP.prob_pure]
    refine le_of_eq (if_neg ?_)
    rintro ⟨prompt, output, hMem, -⟩
    obtain ⟨entry, -, -⟩ := List.mem_map.1 hMem
    exact hProof ⟨entry.2.2⟩

/-- `Sound` gives `SoundManyProofs` with the bound `proofCount * ε queries`. -/
theorem Sound.manyProofsUnion (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) (sound : Sound system ε) :
    SoundManyProofs system fun queries proofCount => proofCount * ε queries := by
  obtain ⟨extractor, soundWith⟩ := sound
  exact ⟨extractor, SoundForWith.manyProofsUnion system extractor system.IsModelOutput ε soundWith⟩

/-- `SoundManyProofs` gives index binding for many sessions in the form of ZKCP/Optional.lean
(`ZKCP.HasSessionAugmentedBinding`), with the bound ε (tC + tP) N; the proof takes the same
extractor. That form's event, "at most N pairs were handed in, and one that is accepted is wrong",
lies inside "one of the first N is accepted and wrong". -/
theorem sessionAugmented_of_soundManyProofs (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞)
    (h : SoundManyProofs system ε) :
    ZKCP.HasSessionAugmentedBinding system.uploadRelation system.uploadArgument
      (fun tC tP N => ε (tC + tP) N) := by
  classical
  obtain ⟨extractor, h0⟩ := h
  refine ⟨extractor, fun tC tP N St Ct Pt hC hP => ?_⟩
  have b1 := h0 tC tP N St (ofUpload Ct) ((queryBound_ofUpload Ct tC).mpr hC)
    (fun state => (ofUpload (Pt state)).bind fun pairs =>
      .done (pairs.map fun e => (e.1.1, e.1.2, e.2)))
    (fun state => queryBound_map _ (ofUpload (Pt state)) tP
        ((queryBound_ofUpload (Pt state) tP).mpr (hP state)))
  refine le_trans ?_ b1
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun H => ?_
  have hval : ∀ (v : Commitment) (x : List Token × List Token) (π : system.Proof),
      (system.uploadArgument.V v x π).run H
        = PMF.pure ((system.verify v x.1 x.2 π).evaluate H) := fun v x π =>
    (run_toUpload H _).trans (DeterministicAlgorithm.run_toRandomized H _)
  show ZKCP.prob ((Ct.withTrace.bind fun c => (Pt c.1.2).bind fun pairs =>
        (ZKCP.verifyAll system.uploadArgument c.1.1 pairs).bind fun bs =>
          ZKCP.OComp.pure (extractor c.1.1 c.2, bs)).run H) _
    ≤ ZKCP.prob (((ofUpload Ct).withQueryLog.bind fun c =>
        ((ofUpload (Pt c.1.2)).bind fun pairs =>
          RandomizedAlgorithm.done (pairs.map fun e => (e.1.1, e.1.2, e.2))).bind fun sent =>
        (system.verifyEach c.1.1 (sent.take N)).bind fun checked =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, checked)).run H) _
  rw [ZKCP.run_bind, run_bind, run_ofUpload_withQueryLog, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.run_bind, run_bind, run_bind, run_ofUpload, PMF.bind_bind, ZKCP.prob_bind,
    ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun pairs => ?_
  rw [ZKCP.run_bind, ZKCP.ManyOfOne.run_verifyAll system.uploadArgument H _ hval, PMF.pure_bind,
    run_done, PMF.pure_bind, run_bind, run_verifyEach, PMF.pure_bind, run_done]
  show ZKCP.prob (PMF.pure _) _ ≤ ZKCP.prob (PMF.pure _) _
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le ?_
  rintro ⟨hLen, bx, hMem, hAcc, hNot⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hMem
  refine ⟨e.1.1, e.1.2, ?_, ?_⟩
  · rw [List.take_of_length_le (by simpa using hLen)]
    refine List.mem_map.2 ⟨(e.1.1, e.1.2, e.2), List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩
    show (e.1.1, e.1.2, system.accepts H c.1.1 e.1.1 e.1.2 e.2) = (e.1.1, e.1.2, true)
    rw [show system.accepts H c.1.1 e.1.1 e.1.2 e.2 = true from hAcc]
  · rintro ⟨weights, hWeights, hOutput⟩
    apply hNot
    show e.1 ∈ system.uploadRelation.L (extractor c.1.1 c.2)
    rw [hWeights]
    exact ⟨(), hOutput⟩

end VerifiableInference

/-! ## 2. The forms, at `verify` -/

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference

/-- **INDEX-BINDING KNOWLEDGE SOUNDNESS OF `verify`'s SYSTEM, AT ONE SET OF PUBLIC FILES, IN SCOPE,
READ, WITH EXACT MATCH.** (NO WITNESS PART: THE RELATION IS A LANGUAGE.) -/
theorem indexBinding_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    ZKCP.HasIndexBinding
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadRelation
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadArgument
      fun tC tP => VerifierAndGoals.soundnessErrorInQueries (tC + tP) 1 :=
  (sound_iff _ _).mp (sound_of_verify_at Z pp scope read exact)

/-- **MANY PROOFS UNDER ONE COMMITMENT, BY A UNION BOUND: N TIMES THE ERROR OF ONE PROOF AT THE
BUDGET OF THE WHOLE LIST.** -/
theorem soundManyProofs_union_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundManyProofs (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun queries proofCount => proofCount * VerifierAndGoals.soundnessErrorInQueries queries 1 :=
  Sound.manyProofsUnion _ _ (sound_of_verify_at Z pp scope read exact)

/-- **The same in the form of ZKCP/Optional.lean.** -/
theorem sessionAugmented_union_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    ZKCP.HasSessionAugmentedBinding
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadRelation
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadArgument
      fun tC tP N => N * VerifierAndGoals.soundnessErrorInQueries (tC + tP) 1 :=
  sessionAugmented_of_soundManyProofs _ _ (soundManyProofs_union_of_verify_at Z pp scope read exact)

/-- **THE FORM WITH NO FACTOR IN FRONT, GIVEN A BOUND q ON ONE RUN OF `verify`.** -/
theorem soundManyProofs_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (q : ℕ)
    (verifierBound : ∀ commitment prompt output proof,
      ((systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).verify commitment prompt
        output proof).toRandomized.QueryBound q) :
    SoundManyProofs (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun queries proofCount => VerifierAndGoals.soundnessErrorInQueries (queries + proofCount * q) 1 :=
  Sound.manyProofs _ _ (sound_of_verify_at Z pp scope read exact) q verifierBound

/-- **The same in the form of ZKCP/Optional.lean.** -/
theorem sessionAugmented_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (q : ℕ)
    (verifierBound : ∀ commitment prompt output proof,
      ((systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).verify commitment prompt
        output proof).toRandomized.QueryBound q) :
    ZKCP.HasSessionAugmentedBinding
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadRelation
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadArgument
      fun tC tP N => VerifierAndGoals.soundnessErrorInQueries (tC + (tP + N * q)) 1 := by
  obtain ⟨E, hE⟩ := indexBinding_of_verify_at Z pp scope read exact
  exact ZKCP.sessionAugmented_of_binding hE
    (fun commitment x proof => (RandomizedAlgorithm.queryBound_toUpload _ q).mpr
      (verifierBound commitment x.1 x.2 proof))
    (fun commitment x proof => drawsNoCoin_toUpload _) ([], [])
    (⟨[], .empty, .empty, .empty, .empty, .empty⟩ : FlashProve.FormBytes)

/-- **INDEX-BINDING KNOWLEDGE SOUNDNESS FOR THE FILES' ACCEPTANCE POLICY, AT ONE SET OF PUBLIC
FILES, IN SCOPE, READ; THE EXTRACTOR IS THE DESCRIPTION's.** (NO WITNESS PART. ALONE IT IS WEAK
UNDER A TOLERANT POLICY: THE HEAD.) -/
theorem indexBindingUnderPolicy_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp) :
    ZKCP.HasIndexBindingWith
      (ZKCP.languageRelation fun
        (weights : (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).Weights)
        (x : List Token × List Token) =>
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol weights x.1 x.2)
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadArgument
      ⟨(atSecondHashFunction theDescription).extractor Z (settingsOfRead pp), fun _ _ _ _ _ => ()⟩
      fun tC tP => VerifierAndGoals.soundnessErrorInQueries (tC + tP) 1 :=
  indexBindingWith_of_soundForWith _ _ _ _ (fun _ _ h => h) _
    ((soundUnderPolicy_of_verify_at Z pp scope read).2 _ _ _ 1
      (theDescription_within OnBytes.secondHashFunction Z))

/-- **THE FIRST FORM WITH THE EXTRACTOR NAMED: THE DESCRIPTION's OWN**, at one set of public files,
in scope, read, with exact match. (NO WITNESS PART: THE RELATION IS A LANGUAGE.) -/
theorem indexBindingWith_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    ZKCP.HasIndexBindingWith
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadRelation
      (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).uploadArgument
      ⟨(atSecondHashFunction theDescription).extractor Z (settingsOfRead pp), fun _ _ _ _ _ => ()⟩
      fun tC tP => VerifierAndGoals.soundnessErrorInQueries (tC + tP) 1 := by
  refine indexBindingWith_of_soundForWith
    (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)) _ _
    (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (fun weights x hm => ?_) _
    ((soundUnderPolicy_of_verify_at Z pp scope read).2 _ _ _ 1
      (theDescription_within OnBytes.secondHashFunction Z))
  rw [exact] at hm
  exact ((Policy.meetsPolicy_exact_iff weights x.1 x.2).1 hm).2

end VerifierAndGoals.AtTheName

#print axioms VerifiableInference.drawsNoCoin_toUpload
#print axioms VerifiableInference.indexBindingWith_of_soundForWith
#print axioms VerifiableInference.SoundForWith.manyProofsUnion
#print axioms VerifiableInference.Sound.manyProofsUnion
#print axioms VerifiableInference.sessionAugmented_of_soundManyProofs
#print axioms VerifierAndGoals.AtTheName.indexBinding_of_verify_at
#print axioms VerifierAndGoals.AtTheName.soundManyProofs_union_of_verify_at
#print axioms VerifierAndGoals.AtTheName.sessionAugmented_union_of_verify_at
#print axioms VerifierAndGoals.AtTheName.soundManyProofs_of_verify_at
#print axioms VerifierAndGoals.AtTheName.sessionAugmented_of_verify_at
#print axioms VerifierAndGoals.AtTheName.indexBindingUnderPolicy_of_verify_at
#print axioms VerifierAndGoals.AtTheName.indexBindingWith_of_verify_at
