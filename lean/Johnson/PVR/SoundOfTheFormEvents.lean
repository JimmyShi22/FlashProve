-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/SoundOfTheFormEvents.lean: THE CHAIN: the executable form of the verifier (`verdictThe`
at `rideOf letsThe`, Johnson/PVR/RideThe.lean) is sound in the sense of `SoundOfDecision` (below),
at the bound of `sound_of_verify_at` (Johnson/Goal/Skeleton/SoundOfVerifyAt.lean), under its three
hypotheses: the public files are in scope, they are read, and they state exact match. IT STATES NO
GOAL: it is a file of theorems about the library's `Sound`.

Why a form of words of its own. `Sound` (VerifiableInference/Statements.lean) speaks of a verifier
that asks the hash function query by query, as a step of the experiment. The executable form is a
plain function that is handed the hash function whole. So it cannot stand inside that experiment.
Here the decision is moved out of the experiment into the event, at the drawn hash function.

Main names.
* `ProbAt`: the text of `Prob` for an event that may read the drawn hash function.
* `SoundOfDecision system decides ε`: the text of `Sound`, line by line, with that one change: the
  same type of extractor, the same two budgets of queries, the same committer and prover, the same
  probability (over a uniform hash function and the adversary's random choices), the same failure
  ("accepted, and the output tokens are not those of the model with the extracted weights").
* `prob_at_hash`, `measurable_at_accepts`: under one hash function `Sound`'s experiment and event,
  and the shorter experiment with the system's own decision in the event, have one probability; so
  at that decision the integrand is measurable.
* `soundOfDecision_accepts_iff`: THE ANCHOR: at the system's own decision (`ArgumentSystem.accepts`)
  it is `Sound`, in both directions. So `SoundOfDecision` says neither more nor less than
  `Sound` where both speak.
* `SoundOfDecision.mono`: a decision that accepts only where another accepts inherits its soundness,
  at the same bound.
* `formAccepts rep Z`: the executable form's decision: accept just where `verdictThe` says "some
  true". rep gives, for each hash function on bit strings, a function on bytes that stands for it.
* `formAccepts_le`: where the form accepts, `verify` accepts at the same hash function (by the tie
  `verdictThe_is_theDescription`).
* `formAccepts_eq`, `soundOfDecision_form_iff`: at a rep whose answers have 32 bytes the form's
  decision IS `verify`'s, at every hash function and on all inputs (by `verdictThe_of_stands`,
  Johnson/PVR/RideEveryHash.lean); so there "the form is sound" and "`verify` is sound" are one
  statement.
* `sound_of_the_form_events`: THE CHAIN, for every rep with `hashOf (rep h) = h`.
  `sound_of_the_form_events_oOf`: at the library's own rep.

Limits. WHAT IT DOES NOT GIVE: anything on how the form is run (Lean's evaluator, compiled code) · a
program · the reader of files in front of the form · completeness · anything at a real hash
function: the hash function is drawn at random. THIS FILE SAYS NOTHING ON WHICH TERM ANY RUN HAS
EXECUTED: whether a run executed this very term (`rideOf letsThe`), and at which function on bytes,
is for that run's own print and its driver's text to show. The runs that Johnson/PVR/RideThe.lean's
head tells rode working copies of the form's files and a driver outside this library: their tie to
these theorems is by name and statement, not by bytes. In `sound_of_the_form_events` "no verdict"
counts as no accept; that the form returns a verdict wherever the function on bytes answers with 32
bytes is not shown here but in Johnson/PVR/RideEveryHash.lean (`verdictThe_some`), and it is said of
the value, not of a run's ending. `ProbAt` IS A LOWER INTEGRAL: at a free decision nothing says that
the integrand is measurable, and there "≤ ε" bounds the lower integral alone; at the system's own
decision, and so at the form with a rep of 32-byte answers (`formAccepts_eq`), the integrand is
`Sound`'s own, which is measurable. No statement here says that the extractor is
`sound_of_verify_at`'s; the proofs hand it on. All limits of `sound_of_verify_at` stand: one set of
public files at a time, fixed before the hash function is drawn; exact match; the full size alone;
the description's own parser. The library's rep `Run.oOf` has no code, and nothing says that a
uniform function on bytes stands for a uniform hash function. Calls and one short calculation
(`prob_at_hash`): what it is worth is what the called theorems and the definitions in their
statements are worth.
Credit. The calculation under one hash
function follows the pattern of
VerifiableInference/Checks.lean.
Sources. `SoundOfDecision` and `ProbAt` write out the text of `Sound`
(VerifiableInference/Statements.lean) and of `Prob` (VerifiableInference/RandomOracleModel.lean), as
their comments say; the statements of `prob_at_hash` and `measurable_at_accepts` write the same
experiment out again; the calculation in `prob_at_hash` follows VerifiableInference/Checks.lean.




-/
import Johnson.PVR.RideEveryHash
import Johnson.Goal.Skeleton.SoundOfVerifyAt
import Johnson.Goal.Tie.HashOfEvery
import VerifiableInference.Checks

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace PV.Ride
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-! ## 1 The form of words -/

/-- The probability that the result of an experiment lies in an event THAT MAY READ THE DRAWN HASH
FUNCTION. It is the text of `Prob` (VerifiableInference/RandomOracleModel.lean) with "event hash"
where that has "event". As there, a lower integral: at an event that reads the hash function
nothing says that the integrand is measurable (at the system's own decision it is:
`measurable_at_accepts`). -/
def ProbAt {α : Type} (experiment : RandomizedAlgorithm α) (event : Hash → Set α) : ℝ≥0∞ :=
  ∫⁻ hash, eventProbability (experiment.run hash) (event hash) ∂uniformHash

/-- The text of `Sound` (VerifiableInference/Statements.lean) for a decision that is handed the hash
function whole, where `Sound`'s verifier asks it query by query. Line by line it is `Sound`'s, but:
the experiment ends behind the prover and hands on the commitment and the proof; the decision
stands in the event, at the drawn hash function. A definition: a form of words. It is none of the
library's goals. -/
def SoundOfDecision (system : ArgumentSystem)
    (decides : Hash → Commitment → List Token → List Token → system.Proof → Bool)
    (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        ProbAt (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            pure (extractor commitment queryLog, commitment, prompt, output, proof))
          (fun hash => {(extracted, commitment, prompt, output, proof) |
            decides hash commitment prompt output proof = true ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output})
          ≤ ε (committerQueries + proverQueries)

/-! ## 2 The anchor, and the one general law -/

/-- Under one hash function: `Sound`'s experiment and event, and the shorter experiment with the
system's own decision in the event, have one probability. -/
theorem prob_at_hash (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (State : Type)
    (committer : RandomizedAlgorithm (Commitment × State))
    (prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof)) (hash : Hash) :
    eventProbability ((do
        let ((commitment, state), queryLog) ← committer.withQueryLog
        let (prompt, output, proof) ← prover state
        let accepted ← (system.verify commitment prompt output proof).toRandomized
        pure (extractor commitment queryLog, prompt, output, accepted) :
          RandomizedAlgorithm _).run hash)
      {(extracted, prompt, output, accepted) |
        accepted = true ∧
        ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output} =
    eventProbability ((do
        let ((commitment, state), queryLog) ← committer.withQueryLog
        let (prompt, output, proof) ← prover state
        pure (extractor commitment queryLog, commitment, prompt, output, proof) :
          RandomizedAlgorithm _).run hash)
      {(extracted, commitment, prompt, output, proof) |
        system.accepts hash commitment prompt output proof = true ∧
        ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output} := by
  classical
  show ZKCP.prob ((committer.withQueryLog.bind fun x => (prover x.1.2).bind fun y =>
      (system.verify x.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
        RandomizedAlgorithm.done (extractor x.1.1 x.2, y.1, y.2.1, accepted)).run hash) _ =
    ZKCP.prob ((committer.withQueryLog.bind fun x => (prover x.1.2).bind fun y =>
      RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, y.1, y.2.1, y.2.2)).run hash) _
  simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
    ZKCP.prob_bind, ZKCP.prob_pure]
  rfl

/-- At the system's own decision the integrand of `ProbAt` is measurable: it is `Sound`'s own
(`prob_at_hash`), of which VerifiableInference/Bridge.lean shows it. -/
theorem measurable_at_accepts (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (State : Type)
    (committer : RandomizedAlgorithm (Commitment × State))
    (prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof)) :
    Measurable fun hash : Hash => eventProbability ((do
        let ((commitment, state), queryLog) ← committer.withQueryLog
        let (prompt, output, proof) ← prover state
        pure (extractor commitment queryLog, commitment, prompt, output, proof) :
          RandomizedAlgorithm _).run hash)
      {(extracted, commitment, prompt, output, proof) |
        system.accepts hash commitment prompt output proof = true ∧
        ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output} := by
  have e := funext fun hash => prob_at_hash system extractor State committer prover hash
  rw [← e]
  exact measurable_eventProbability_run _ _

/-- **THE ANCHOR: at the system's own decision the form `SoundOfDecision` IS `Sound`.** -/
theorem soundOfDecision_accepts_iff (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) :
    SoundOfDecision system system.accepts ε ↔ Sound system ε := by
  constructor
  · rintro ⟨extractor, h⟩
    refine ⟨extractor, fun cq pq State committer hC prover hP => ?_⟩
    refine le_trans (le_of_eq ?_) (h cq pq State committer hC prover hP)
    exact lintegral_congr fun hash => prob_at_hash system extractor State committer prover hash
  · rintro ⟨extractor, h⟩
    refine ⟨extractor, fun cq pq State committer hC prover hP => ?_⟩
    refine le_trans (le_of_eq ?_) (h cq pq State committer hC prover hP)
    exact lintegral_congr fun hash =>
      (prob_at_hash system extractor State committer prover hash).symm

/-- A decision that accepts only where another accepts inherits its soundness: same bound. -/
theorem SoundOfDecision.mono {system : ArgumentSystem}
    {d₁ d₂ : Hash → Commitment → List Token → List Token → system.Proof → Bool} {ε : ℕ → ℝ≥0∞}
    (h : SoundOfDecision system d₂ ε)
    (le : ∀ hash commitment prompt output proof, d₁ hash commitment prompt output proof = true →
      d₂ hash commitment prompt output proof = true) : SoundOfDecision system d₁ ε := by
  obtain ⟨extractor, h⟩ := h
  refine ⟨extractor, fun cq pq State committer hC prover hP => ?_⟩
  refine le_trans (lintegral_mono fun hash => ?_) (h cq pq State committer hC prover hP)
  exact (PMF.toOuterMeasure _).mono fun x hx => ⟨le hash _ _ _ _ hx.1, hx.2⟩

/-! ## 3 The chain -/

/-- The executable form's decision at a hash function: "accept" just where `verdictThe` says
"some true". rep: for each hash function on bit strings a function on bytes that stands for it. -/
def formAccepts (rep : Hash → ByteArray → ByteArray) (Z : PublicFiles) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) : Bool :=
  verdictThe Z (rep hash) B (rideOf letsThe Z (rep hash) B commitment prompt output) == some true

/-- Where the form accepts, `verify` accepts at the same hash function. -/
theorem formAccepts_le (rep : Hash → ByteArray → ByteArray) (hrep : ∀ h, hashOf (rep h) = h)
    (Z : PublicFiles) (s : IntegerTransformer.Settings) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (B : FormBytes)
    (h : formAccepts rep Z hash commitment prompt output B = true) :
    (systemOfRecord (atSecondHashFunction theDescription) Z s).accepts hash commitment prompt output B =
      true := by
  have h' : verdictThe Z (rep hash) B (rideOf letsThe Z (rep hash) B commitment prompt output) =
      some true := by simpa [formAccepts] using h
  have k := verdictThe_is_theDescription Z (rep hash) B commitment prompt output true h'
  rw [hrep] at k
  exact k.symm

/-- **At a rep with 32-byte answers the form's decision IS `verify`'s**, at every hash function,
on all inputs (by `verdictThe_of_stands`, Johnson/PVR/RideEveryHash.lean). -/
theorem formAccepts_eq (rep : Hash → ByteArray → ByteArray) (h32 : ∀ h b, (rep h b).size = 32)
    (hrep : ∀ h, hashOf (rep h) = h) (Z : PublicFiles) (s : IntegerTransformer.Settings) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    formAccepts rep Z hash commitment prompt output B =
      (systemOfRecord (atSecondHashFunction theDescription) Z s).accepts hash commitment prompt output B := by
  unfold formAccepts
  rw [verdictThe_of_stands Z hash (rep hash) (h32 hash) (hrep hash) B commitment prompt output]
  show (some _ == some true) = (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z
    ((atSecondHashFunction theDescription).parse Z) commitment prompt output B).evaluate hash
  cases (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
    prompt output B).evaluate hash <;> rfl

/-- **So, at such a rep, "the form is sound" and "`verify` is sound" are one statement**, at
every set of public files, every setting and every bound. -/
theorem soundOfDecision_form_iff (rep : Hash → ByteArray → ByteArray)
    (h32 : ∀ h b, (rep h b).size = 32) (hrep : ∀ h, hashOf (rep h) = h) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) (ε : ℕ → ℝ≥0∞) :
    SoundOfDecision (systemOfRecord (atSecondHashFunction theDescription) Z s) (formAccepts rep Z) ε ↔
      Sound (systemOfRecord (atSecondHashFunction theDescription) Z s) ε := by
  rw [← soundOfDecision_accepts_iff]
  have e : formAccepts rep Z = (systemOfRecord (atSecondHashFunction theDescription) Z s).accepts := by
    funext hash commitment prompt output B
    exact formAccepts_eq rep h32 hrep Z s hash commitment prompt output B
  rw [e]
/-- **THE CHAIN: the executable form meets `SoundOfDecision` at the bound of `sound_of_verify_at`,
under its three hypotheses**, at each rep with `hashOf (rep h) = h`. With 32-byte answers that is
`Sound`'s own sense (`soundOfDecision_form_iff`); else it says less: it bounds a lower integral. -/
theorem sound_of_the_form_events (rep : Hash → ByteArray → ByteArray)
    (hrep : ∀ h, hashOf (rep h) = h)
    (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundOfDecision (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      (formAccepts rep Z) fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  ((soundOfDecision_accepts_iff _ _).2
    (VerifierAndGoals.AtTheName.sound_of_verify_at Z pp scope read exact)).mono
    fun hash commitment prompt output B h =>
      formAccepts_le rep hrep Z _ hash commitment prompt output B h
/-- There is such a rep: the library's own (`Run.oOf`; it has no code). Its answers have 32 bytes
(`Run.size_oOf`), so here the statement is `Sound`'s own sense (`soundOfDecision_form_iff`). -/
theorem sound_of_the_form_events_oOf (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundOfDecision (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      (formAccepts (fun h => _root_.Run.oOf fun _ => h) Z) fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_the_form_events _ hashOf_oOf Z pp scope read exact

end PV.Ride

#print axioms PV.Ride.prob_at_hash
#print axioms PV.Ride.measurable_at_accepts
#print axioms PV.Ride.soundOfDecision_accepts_iff
#print axioms PV.Ride.SoundOfDecision.mono
#print axioms PV.Ride.formAccepts_le
#print axioms PV.Ride.formAccepts_eq
#print axioms PV.Ride.soundOfDecision_form_iff
#print axioms PV.Ride.sound_of_the_form_events
#print axioms PV.Ride.sound_of_the_form_events_oOf
