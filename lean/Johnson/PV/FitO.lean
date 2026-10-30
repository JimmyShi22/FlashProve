-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FitO.lean: the fit of Johnson/PV/Fit.lean with an extractor that may find nothing.
`SoundForWith.bindWeights`: soundness passes to an extractor followed by a partial map on what it
finds, if the claim is carried along the map. `ToldAtO`: `ToldAt` with such a map from indices to
weights. `soundUnderPolicyAt_of_toldO`, `G8_of_toldO`, `G7_of_toldO`: the goals from it.
Conditional: every hypothesis of the told law stays a hypothesis here. No description is built here
(one is: `VerifierAndGoals.theDescription`), and nothing is shown of a verifier that runs or ships.

-/
import Johnson.PV.Fit
import Ladder.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference
open scoped ENNReal
open MeasureTheory
open RandomizedAlgorithm

/-- Soundness for a claim, for a given extractor, carries over along a map of weights INTO Option
that says some, with the new claim, wherever the old claim holds. The new extractor is the old one,
then bind. -/
theorem SoundForWith.bindWeights (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
    (commit : NewWeights → system.CommitmentRandomness → DeterministicAlgorithm Commitment)
    (prove : NewWeights → system.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm system.Proof)
    (map : system.Weights → Option NewWeights)
    (newClaim : NewWeights → List Token → List Token → Prop)
    (carries : ∀ (weights : system.Weights) (prompt output : List Token),
      claim weights prompt output → ∃ w, map weights = some w ∧ newClaim w prompt output) :
    SoundForWith (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
        commit prove)
      (fun commitment queryLog => (extractor commitment queryLog).bind map) newClaim ε := by
  intro committerQueries proverQueries State committer committerBound prover proverBound
  refine le_trans ?_ (sound committerQueries proverQueries State committer committerBound prover
      proverBound)
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done ((extractor c.1.1 c.2).bind map, y.1, y.2.1, accepted)).run hash)
              _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, PMF.pure_bind,
      run_done, run_done, ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  refine ⟨h1, fun hw => h2 ?_⟩
  obtain ⟨weights, he, ho⟩ := hw
  obtain ⟨w, hm, hn⟩ := carries weights _ _ ho
  exact ⟨w, by rw [he]; exact hm, hn⟩

end VerifiableInference

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K (Pub)
open scoped ENNReal

variable (D : Description) (Z : PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))

/-- **THE FIT, G8's body at one Z, THE MAP INTO Option, THE EXTRACTOR BY bind.** ψ: a total filler
for the honest side of an auxiliary system: soundness does not read it. -/
theorem soundForWith_system_of_toldO (s : IntegerTransformer.Settings)
    (pair : Digest → D.More → T.D)
    (fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (claim : (D.input Z c₀ m₀).Index → List Token → List Token → Prop) (Wn : Type)
    (Rno : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Wn → Prop) (x₀ : (D.input Z c₀ m₀).Instance)
    (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, (D.input Z c₀ m₀).buildInstance x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (word : ∀ d d', T.part d = T.part d' →
      (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample (D.input Z c₀ m₀).queryLayout)).Ei =
        (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample (D.input Z c₀ m₀).queryLayout)).Ei)
    (code : ZKCP.CodeIsOneToOne T.encT)
    (reads : ∀ hash : Hash, (readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (q₀ : ℕ) (hq₀ : (readBoth D Z c₀ m₀ T pair).toRandomized.QueryBound q₀)
    (φ : (D.input Z c₀ m₀).Index → Option (ModelWeights s)) (ψ : (D.input Z c₀ m₀).Index → ModelWeights s)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (carries : ∀ i prompt output, claim i prompt output →
      ∃ w, φ i = some w ∧ newClaim w prompt output)
    -- D's own extractor is the told one, then φ, by bind
    (hext : D.extractor Z s = fun commitment queryLog => (T.extractor commitment queryLog).bind φ)
    (Form : Type)
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundForWith (system D Z s Form prove parse) (D.extractor Z s) newClaim fun t =>
      soundnessBoundOverTypedOracles (D.input Z c₀ m₀).queryLayout εs (t + (q₀ + n)) 0 + epsCode (t + (q₀ + n)) := by
  have within : ∀ prompt output form,
      (T.readerBehindReadingAndParser (readBoth D Z c₀ m₀ T pair) (fun _ => parse) prompt output
        form).toRandomized.QueryBound (q₀ + n) := by
    intro prompt output form
    unfold LayoutsByPublicReading.readerBehindReadingAndParser
    refine queryBound_andThen _ _ q₀ n hq₀ fun d => ?_
    have h := queryBound_andThen (parse prompt output form)
      (fun proof => (DeterministicAlgorithm.done (proof.1, ((T.part d, proof.2.1), proof.2.2)) :
        DeterministicAlgorithm T.system.Proof)) n 0 (hn prompt output form) (fun _ => trivial)
    simpa using h
  have yes : ∀ hash commitment prompt output form,
      (verify D Z parse commitment prompt output form).evaluate hash = true →
        (T.verifyBehindReadingAndParser (readBoth D Z c₀ m₀ T pair) (fun _ => parse) commitment prompt output
          form).evaluate hash = true := by
    intro hash commitment prompt output form h
    unfold verify verifyAt at h
    split at h
    · simp only [andThen_eq, DeterministicAlgorithm.evaluate_andThen] at h
      have e : (readBoth D Z c₀ m₀ T pair).evaluate hash =
          pair ((readConfig Z).evaluate hash)
            ((D.readMore Z ((readConfig Z).evaluate hash)).evaluate hash) := by
        unfold readBoth
        rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
        rfl
      unfold LayoutsByPublicReading.verifyBehindReadingAndParser
      rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen, e]
      rw [fits] at h
      exact h
    · exact absurd h (by simp [DeterministicAlgorithm.evaluate])
  have key := verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor T claim Wn Rno x₀ εs core meaning noCoin asks once spare word
      code
    (fun i => D.shown s (ψ i)) (fun i => modelNextToken s (ψ i)) D.sample (fun i => D.commit Z s (ψ
        i))
    (fun i => prove (ψ i)) (verify D Z parse)
    (readBoth D Z c₀ m₀ T pair) reads (fun _ => parse) (q₀ + n) within yes id claim
    (fun _ _ _ h => h)
  have e : D.extractor Z s =
      fun commitment queryLog => ((T.extractor commitment queryLog).map id).bind φ := by
    rw [hext]
    funext commitment queryLog
    rw [Option.map_id]
    rfl
  rw [e]
  exact SoundForWith.bindWeights _ _ _ _ key (ModelWeights s) D.Shown (D.shown s) (modelNextToken s)
    (D.commit Z s) prove φ newClaim carries



/-- All that the fit asks at one Z, THE MAP INTO Option: for a claim on weights: data, then
hypotheses. φ may say none; «carries» asks that it says some where the claim holds. ψ: a total
filler; soundness does not read it. No field says that a verifier ever says yes. -/
structure ToldAtO (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (newClaim : ModelWeights s → List Token → List Token → Prop) where
  c₀ : Digest
  m₀ : D.More
  T : LayoutsByPublicReading (D.input Z c₀ m₀)
  pair : Digest → D.More → T.D
  claim : (D.input Z c₀ m₀).Index → List Token → List Token → Prop
  Wn : Type
  Rno : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Wn → Prop
  x₀ : (D.input Z c₀ m₀).Instance
  εs : ℝ≥0∞
  q₀ : ℕ
  φ : (D.input Z c₀ m₀).Index → Option (ModelWeights s)
  ψ : (D.input Z c₀ m₀).Index → ModelWeights s
  fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
    innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
      innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof
  core : ∀ d, CompilerSoundnessConditions (T.beside Wn Rno x₀ εs d)
  meaning : ∀ i (x' : List Token × List Token) a x, (D.input Z c₀ m₀).buildInstance x' a = some x →
    (∃ w, Rno i x w) → claim i x'.1 x'.2
  noCoin : T.Pub.NoCoin
  asks : T.Pub.AsksIn fun _ s => T.Pt s
  once : NoRepeat T.Pub
  spare : ∀ d s, T.Pt s → IsOther (T.m d) s
  word : ∀ d d', T.part d = T.part d' →
    (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample (D.input Z c₀ m₀).queryLayout)).Ei =
      (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample (D.input Z c₀ m₀).queryLayout)).Ei
  code : ZKCP.CodeIsOneToOne T.encT
  reads : ∀ hash : Hash, (readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash
  hq₀ : (readBoth D Z c₀ m₀ T pair).toRandomized.QueryBound q₀
  carries : ∀ i prompt output, claim i prompt output → ∃ w, φ i = some w ∧ newClaim w prompt output

/-- The error that the fit gives at one Z: t the adversary's queries, n the parser's. -/
def ToldAtO.err {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (A : ToldAtO D Z s newClaim)
    (t n : ℕ) : ℝ≥0∞ :=
  soundnessBoundOverTypedOracles (D.input Z A.c₀ A.m₀).queryLayout A.εs (t + (A.q₀ + n)) 0 + epsCode (t + (A.q₀ + n))

/-- The extractor that the fit gives at one Z. -/
def ToldAtO.extractor {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (A : ToldAtO D Z s newClaim) :
    Commitment → QueryLog → Option (ModelWeights s) :=
  fun commitment queryLog => (A.T.extractor commitment queryLog).bind A.φ


/-- **The stored `SoundUnderPolicyAt`**, likewise, where D's extractor is the fit's. -/
theorem soundUnderPolicyAt_of_toldO (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAtO D Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within (D.parse Z) honestBudget)
    (hext : ∀ Z pp h₁ h₂, D.extractor Z (settingsOfRead pp) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n) :
    SoundUnderPolicyAt D eps := by
  intro Z pp h₁ h₂
  refine ⟨ownParser Z pp h₁ h₂, ?_⟩
  intro Form prove parse n hn
  have key := soundForWith_system_of_toldO D Z (A Z pp h₁ h₂).c₀ (A Z pp h₁ h₂).m₀
    (A Z pp h₁ h₂).T (settingsOfRead pp) (A Z pp h₁ h₂).pair (A Z pp h₁ h₂).fits
    (A Z pp h₁ h₂).claim (A Z pp h₁ h₂).Wn (A Z pp h₁ h₂).Rno (A Z pp h₁ h₂).x₀
    (A Z pp h₁ h₂).εs (A Z pp h₁ h₂).core (A Z pp h₁ h₂).meaning
    (A Z pp h₁ h₂).noCoin (A Z pp h₁ h₂).asks (A Z pp h₁ h₂).once
    (A Z pp h₁ h₂).spare (A Z pp h₁ h₂).word (A Z pp h₁ h₂).code
    (A Z pp h₁ h₂).reads (A Z pp h₁ h₂).q₀ (A Z pp h₁ h₂).hq₀ (A Z pp h₁ h₂).φ (A Z pp h₁ h₂).ψ
    (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (A Z pp h₁ h₂).carries (hext Z pp h₁ h₂)
    Form prove parse n hn
  exact fun cq pq St c hc p hp => le_trans (key cq pq St c hc p hp) (bound Z pp h₁ h₂ _ n)


/-- **THE STORED G8**, likewise. -/
theorem G8_of_toldO (D : SecondHashFunctionType → Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAtO (atSecondHashFunction D) Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((atSecondHashFunction D).parse Z) honestBudget)
    (hext : ∀ Z pp h₁ h₂, (atSecondHashFunction D).extractor Z (settingsOfRead pp) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n) : G8 D :=
  ⟨eps, ceil, soundUnderPolicyAt_of_toldO (atSecondHashFunction D) eps A ownParser hext bound⟩


/-- **THE GOAL G7**, from the same, by `g7_of_g8`. -/
theorem G7_of_toldO (D : SecondHashFunctionType → Description) (h : G8 D) : G7 D := g7_of_g8 D h

end VerifierAndGoals.Fit

#print axioms VerifiableInference.SoundForWith.bindWeights
#print axioms VerifierAndGoals.Fit.soundForWith_system_of_toldO
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_of_toldO
#print axioms VerifierAndGoals.Fit.G8_of_toldO
