-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/Fit.lean: from a told record to the ladder's goals on soundness, general in the
description.
`ToldAt D Z s claim`: what is asked of a description D at public files Z: a told record
(Johnson/Top/InnerCompiledVerifierByPublicReading.lean) whose member at what the two public readings return is D's input,
whose public reading is D's, whose extractor is D's, and the told law's hypotheses as fields.
`soundAt_of_told`, `soundUnderPolicyAt_of_told`: the ladder's `SoundAt` and `SoundUnderPolicyAt` at
such files. `G7_of_told`, `G8_of_told`: the goals G7 and G8 from a `ToldAt` at every Z in scope, a
bound on the error and a bound on the own parser's queries. `ToldAt.commitment`: of the core's
fifteen clauses the one on the commitment follows from the one on the code.
Conditional: every hypothesis of the told law stays a hypothesis. No description is built, and
nothing is shown of a verifier that runs or ships.

-/
import Ladder
import Johnson.Top.InnerCompiledVerifierByPublicReading
import Johnson.Top.Seam.ReaderWith
import Johnson.Top.SoundReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K (Pub)
open scoped ENNReal

/-- The ladder's `andThen` is the library's. -/
theorem andThen_eq {α β : Type} (f : α → DeterministicAlgorithm β) :
    ∀ a : DeterministicAlgorithm α, VerifierAndGoals.andThen a f = a.andThen f
  | .done _ => rfl
  | .query s k => by
      show DeterministicAlgorithm.query s (fun d => VerifierAndGoals.andThen (k d) f) =
        DeterministicAlgorithm.query s fun d => (k d).andThen f
      congr 1
      funext d
      exact andThen_eq f (k d)

variable (D : Description) (Z : PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))

/-- The ladder's two public readings as one, with their values laid into the told record's type. -/
def readBoth (pair : Digest → D.More → T.D) : DeterministicAlgorithm T.D :=
  (readConfig Z).andThen fun c => (D.readMore Z c).andThen fun m => .done (pair c m)

/-- **THE FIT, G7's body at one Z.** -/
theorem sound_system_of_told (s : IntegerTransformer.Settings)
    (pair : Digest → D.More → T.D)
    -- the narrow kind, as far as a verifier's answers go
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
    (φ : (D.input Z c₀ m₀).Index → ModelWeights s)
    (carries : ∀ i prompt output, claim i prompt output → ModelOutput s (φ i) prompt output)
    (Form : Type)
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (n : ℕ) (hn : parse.Within n) :
    Sound (system D Z s Form prove parse) fun t =>
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
  exact verifierAcceptingNoMoreThanBehindReadingAndParser_sound T claim Wn Rno x₀ εs core meaning noCoin asks once spare word code
    (D.shown s) (modelNextToken s) D.sample (D.commit Z s) prove (verify D Z parse)
    (readBoth D Z c₀ m₀ T pair) reads (fun _ => parse) (q₀ + n) within yes φ carries

/-- **THE FIT, G8's body at one Z.** -/
theorem soundForWith_system_of_told (s : IntegerTransformer.Settings)
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
    (φ : (D.input Z c₀ m₀).Index → ModelWeights s)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (carries : ∀ i prompt output, claim i prompt output → newClaim (φ i) prompt output)
    -- D's own extractor is the told one, then φ
    (hext : D.extractor Z s = fun commitment queryLog => (T.extractor commitment queryLog).map φ)
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
  rw [hext]
  exact verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor T claim Wn Rno x₀ εs core meaning noCoin asks once spare word code
    (D.shown s) (modelNextToken s) D.sample (D.commit Z s) prove (verify D Z parse)
    (readBoth D Z c₀ m₀ T pair) reads (fun _ => parse) (q₀ + n) within yes φ newClaim carries


/-- All that the fit asks at one Z, for a claim on weights: data, then hypotheses. No field says
that a verifier ever says yes. -/
structure ToldAt (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
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
  φ : (D.input Z c₀ m₀).Index → ModelWeights s
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
  carries : ∀ i prompt output, claim i prompt output → newClaim (φ i) prompt output

/-- The error that the fit gives at one Z: t the adversary's queries, n the parser's. -/
def ToldAt.err {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (A : ToldAt D Z s newClaim)
    (t n : ℕ) : ℝ≥0∞ :=
  soundnessBoundOverTypedOracles (D.input Z A.c₀ A.m₀).queryLayout A.εs (t + (A.q₀ + n)) 0 + epsCode (t + (A.q₀ + n))

/-- The extractor that the fit gives at one Z. -/
def ToldAt.extractor {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (A : ToldAt D Z s newClaim) :
    Commitment → QueryLog → Option (ModelWeights s) :=
  fun commitment queryLog => (A.T.extractor commitment queryLog).map A.φ

/-- **core's clause «commitment» follows from «code», at the fit's own T, at every d**: by
`LayoutsByPublicReading.commitment_of_code` (Johnson/Top/InnerCompiledVerifierByPublicReading.lean:246). So of CompilerSoundnessConditions's fifteen a
builder owes fourteen beside `code`. -/
theorem ToldAt.commitment {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (A : ToldAt D Z s newClaim) (d :
        A.T.D) :
    CompilerSoundnessConditionStatements.commitment (A.T.beside A.Wn A.Rno A.x₀ A.εs d) :=
  A.T.commitment_of_code A.code A.Wn A.Rno A.x₀ A.εs d

/-- **The stored `SoundAt`**, from a told record at every Z in scope that states exact match, and
one bound. -/
theorem soundAt_of_told (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact →
      ToldAt D Z (settingsOfRead pp) (ModelOutput (settingsOfRead pp)))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact → Parser.Within (D.parse Z) honestBudget)
    (bound : ∀ Z pp h₁ h₂ h₃ t n, (A Z pp h₁ h₂ h₃).err t n ≤ eps t n) : SoundAt D eps := by
  intro Z pp h₁ h₂ h₃
  refine ⟨ownParser Z pp h₁ h₂ h₃, ?_⟩
  intro Form prove parse n hn
  refine sound_mono (sound_system_of_told D Z (A Z pp h₁ h₂ h₃).c₀ (A Z pp h₁ h₂ h₃).m₀
    (A Z pp h₁ h₂ h₃).T (settingsOfRead pp) (A Z pp h₁ h₂ h₃).pair (A Z pp h₁ h₂ h₃).fits
    (A Z pp h₁ h₂ h₃).claim (A Z pp h₁ h₂ h₃).Wn (A Z pp h₁ h₂ h₃).Rno (A Z pp h₁ h₂ h₃).x₀
    (A Z pp h₁ h₂ h₃).εs (A Z pp h₁ h₂ h₃).core (A Z pp h₁ h₂ h₃).meaning
    (A Z pp h₁ h₂ h₃).noCoin (A Z pp h₁ h₂ h₃).asks (A Z pp h₁ h₂ h₃).once
    (A Z pp h₁ h₂ h₃).spare (A Z pp h₁ h₂ h₃).word (A Z pp h₁ h₂ h₃).code
    (A Z pp h₁ h₂ h₃).reads (A Z pp h₁ h₂ h₃).q₀ (A Z pp h₁ h₂ h₃).hq₀ (A Z pp h₁ h₂ h₃).φ
    (A Z pp h₁ h₂ h₃).carries Form prove parse n hn) fun t => bound Z pp h₁ h₂ h₃ t n

/-- **The stored `SoundUnderPolicyAt`**, likewise, where D's extractor is the fit's. -/
theorem soundUnderPolicyAt_of_told (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAt D Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within (D.parse Z) honestBudget)
    (hext : ∀ Z pp h₁ h₂, D.extractor Z (settingsOfRead pp) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n) :
    SoundUnderPolicyAt D eps := by
  intro Z pp h₁ h₂
  refine ⟨ownParser Z pp h₁ h₂, ?_⟩
  intro Form prove parse n hn
  have key := soundForWith_system_of_told D Z (A Z pp h₁ h₂).c₀ (A Z pp h₁ h₂).m₀
    (A Z pp h₁ h₂).T (settingsOfRead pp) (A Z pp h₁ h₂).pair (A Z pp h₁ h₂).fits
    (A Z pp h₁ h₂).claim (A Z pp h₁ h₂).Wn (A Z pp h₁ h₂).Rno (A Z pp h₁ h₂).x₀
    (A Z pp h₁ h₂).εs (A Z pp h₁ h₂).core (A Z pp h₁ h₂).meaning
    (A Z pp h₁ h₂).noCoin (A Z pp h₁ h₂).asks (A Z pp h₁ h₂).once
    (A Z pp h₁ h₂).spare (A Z pp h₁ h₂).word (A Z pp h₁ h₂).code
    (A Z pp h₁ h₂).reads (A Z pp h₁ h₂).q₀ (A Z pp h₁ h₂).hq₀ (A Z pp h₁ h₂).φ
    (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (A Z pp h₁ h₂).carries (hext Z pp h₁ h₂)
    Form prove parse n hn
  exact fun cq pq St c hc p hp => le_trans (key cq pq St c hc p hp) (bound Z pp h₁ h₂ _ n)

/-- **THE GOAL G7**, from such a family at the format's second hash function, one bound, and the
ceiling up to the budgets. -/
theorem G7_of_told (D : SecondHashFunctionType → Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact →
      ToldAt (atSecondHashFunction D) Z (settingsOfRead pp) (ModelOutput (settingsOfRead pp)))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact → Parser.Within ((atSecondHashFunction D).parse Z) honestBudget)
    (bound : ∀ Z pp h₁ h₂ h₃ t n, (A Z pp h₁ h₂ h₃).err t n ≤ eps t n) : G7 D :=
  ⟨eps, ceil, soundAt_of_told (atSecondHashFunction D) eps A ownParser bound⟩

/-- **THE STORED G8**, likewise. -/
theorem G8_of_told (D : SecondHashFunctionType → Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAt (atSecondHashFunction D) Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((atSecondHashFunction D).parse Z) honestBudget)
    (hext : ∀ Z pp h₁ h₂, (atSecondHashFunction D).extractor Z (settingsOfRead pp) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n) : G8 D :=
  ⟨eps, ceil, soundUnderPolicyAt_of_told (atSecondHashFunction D) eps A ownParser hext bound⟩

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.andThen_eq
#print axioms VerifierAndGoals.Fit.sound_system_of_told
#print axioms VerifierAndGoals.Fit.soundForWith_system_of_told
#print axioms VerifierAndGoals.Fit.ToldAt.commitment
#print axioms VerifierAndGoals.Fit.soundAt_of_told
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_of_told
#print axioms VerifierAndGoals.Fit.G7_of_told
#print axioms VerifierAndGoals.Fit.G8_of_told
