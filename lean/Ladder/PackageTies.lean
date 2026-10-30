-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/PackageTies.lean: what the goals of Ladder.lean give of the goals of Ladder/Package.lean,
which apply the six top statements of VerifiableInference/Statements.lean by name to `D`'s own
verifier (`systemOfRecord`). Theorems with proofs. General in `D`.

Why. Of these six statements Ladder.lean applies one to its verifier by name: `Sound` (G7, G7').
`SoundAndBinding` is asked in two pieces: its first clause as `SoundForWith` at a claim that is a
parameter (G8), of the system at every parser; its second as `BindsWith` (G9), of the system of
record. This file joins the two at the system of record, and lays the other ties beside it.

THE SIX, AND WHAT THE GOALS OF Ladder.lean GIVE OF EACH (the forms: Ladder/Package.lean).
  statement                     the nearest form follows from   at which error
  `Sound`                       G7 (so also from G8)            at most 1/4 up to 2^64 queries
  `SoundAndBinding`             G8 and G9                       at most 1/4 up to 2^64 queries
  `SoundOpened`                 G8 and G9                       at most 1/2 up to 2^64 queries
  `Complete`                    no nearest form is stated; G3'pol gives `CompleteOn` at `CanServe`
                                (`completeOn_of_completeFor`, Ladder/Ties.lean: where 2^8 ≤ theta)
  `ZeroKnowledge`               from no goal of Ladder.lean
  `CompleteSoundZeroKnowledge`  not: `Complete` and `ZeroKnowledge` are missing
FOR THE THREE STATEMENTS ON SOUNDNESS THE NEAREST FORM IS THE STATEMENT OF
VerifiableInference/Statements.lean ITSELF, UNCHANGED, of the verifier's system at each set of files
in scope that states exact match: one premise more (pp.pol = AcceptancePolicy.exact) in front of the same
constant. That file's statements know no files and no policy: NONE OF THE THREE HAD TO BE WEAKENED.
What `Package…` adds is OUR family of files: the same constant at ALL files in scope, those with a
lenient policy among them. Of these forms nothing follows here. TWO OF THEM ARE SHOWN NOT TO HOLD AT
A SMALL ERROR TOGETHER WITH OUR OWN GOAL G3'pol, given `FilesRead`: `PackageSoundOpened` has an
error of at least 1 - `completenessErrorBound`, and `PackageSoundAndBinding` of at least half of that, at some number
of queries within the honest side's budget (2^48): at a lenient policy the honest side is to have
outputs accepted that are not the model's (G3'pol). These two bars speak of that family with that
goal, not of the statements themselves. Of `PackageSound` no such theorem is here: its extractor
may give other weights than the committed ones.

THE ARROWS RUN DOWNHILL. Each tie drops a part of its goal, and among what is dropped are the goals'
guards on budgets: the ties from G9 drop "the committer stays within `honestBudget`". No nearest
form bounds an honest party's queries; `G3'pol`'s first half asks such a bound of `D`, at the two
named sets of files, and `repliesFit` (AtFullSide/Face/TheSixLines.lean) proves one of the compiled
system, at public files in use. So each of the five single forms on soundness, completeness and zero
knowledge SAYS LESS THAN the goals of Ladder.lean: by its head, 4 and 6, a description with one very
hard proof of work and nothing of the model is ruled out by these bounds alone (an argument there;
no theorem). This is inherited: the statements of VerifiableInference/Statements.lean bound no
honest party.

What this file states.
  `soundFor_and_binds_of_record`: from `SoundUnderPolicyAt` at an error epsS and `BindsAt` at an
    error epsB: at all public files in scope that the reader reads, AT EVERY POLICY: `D`'s one
    extractor meets both `SoundForWith`, for the files' policy, at the error epsS t honestBudget,
    and `BindsWith`, at epsB: of `systemOfRecord`. This is `SoundAndBinding`'s form
    (`soundAndBinding_iff`, VerifiableInference/Binds.lean) with the claim "the output meets the
    files' policy" where that statement has "the output tokens are the model's".
  **`soundAndBinding_of_record`**: at the files that state exact match: `SoundAndBinding` of
    `systemOfRecord`, at the larger of the two errors (`joinError`).
  **`soundOpened_of_record`**: there: `SoundOpened`, at twice that error.
  **`nearestSoundAndBinding_of_g8_g9`**, **`nearestSoundOpened_of_g8_g9`**: so from G8 and G9: one
    error for all files in scope that state exact match, at most the ceiling (for `SoundOpened`:
    twice the ceiling) up to the budget of queries. `two_mul_ceiling`: twice the ceiling is 1/2.
  `nearestSound_of_g7`: the short tie.
  `nearestSound_of_nearestSoundAndBinding`, `nearestSoundOpened_of_nearestSoundAndBinding`: among
    the nearest forms themselves.
  `nearestSound_of_at`, `nearestSoundAndBinding_of_at`, `nearestSoundOpened_of_at`: the same ties
    WITH THE ERROR KEPT: from `SoundAt` | `SoundUnderPolicyAt` and `BindsAt` at given errors.
  `nearest…_of_package` (three): the form at all files gives the nearest form.
  `nearest…_at_full` (three): given `FilesRead`, a nearest form speaks of the system of the stored
    full-size files by name.
  `soundAndBinding_of_record_exactKind`, `soundOpened_of_record_exactKind`: at every policy with
    theta = 2^8 ≤ C and (cap = 0 or 2^8 < C), not at `AcceptancePolicy.exact` alone.
  `sound_everyOlder_of_g7'`: from G7': `Sound` at every function in the second hash function's
    place.
  **`packageSoundOpened_bar`**, **`packageSoundAndBinding_bar`**: what cannot hold at all files, by
    `one_sub_le_of_completeFor_soundOpened` (general in the system): where the honest side is
    accepted at an output that is not the model's, it is itself an adversary of `SoundOpened`
    (`honestOpener`, `accepted_le_opened`; `queryBound_then` counts its queries).

Which premises. The goals that each theorem names, and nothing else: no hypothesis is added by name;
the two bars and the three `nearest…_at_full` also take `FilesRead`, which Ladder/Guards.lean
evaluates and `VerifierAndGoals.filesRead` proves.
The join spends the first conjunct of `SoundUnderPolicyAt` (`D`'s own parser stays within
`honestBudget`): it brings `D`'s own parser under "every parser with at most n queries".

What it does not show. That any goal of Ladder.lean holds of any description: these are
conditionals. Nothing at a policy other than exact match in the words of
VerifiableInference/Statements.lean: `SoundAndBinding` and `SoundOpened` speak of `IsModelOutput`,
and under another policy an accepted output need not be the model's; what holds there is the first
theorem. Nothing on `Complete`, `ZeroKnowledge` or `CompleteSoundZeroKnowledge`. The ceiling, which
Ladder.lean sets at one quarter (1/4), is a bar on the error, no security level; twice the ceiling
is one half (1/2). The queries of `D`'s own parser, of `readConfig`, `readMore` and `innerCompiledVerifier`,
and in binding of `commit`, are in nobody's count: the error has to cover them, as in the goals.
The public files are fixed before the hash function is drawn. Nothing on acceptance: a verifier
that refuses everything meets the first clause.

-/
import Ladder.Package
import Ladder.Ties
import VerifiableInference.Binds
import VerifiableInference.Checks
import VerifiableInference.ProbabilityGuards
import ZKCP.ManyOfOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals
open VerifiableInference Inst.Model
open RandomizedAlgorithm
open scoped ENNReal
open MeasureTheory

/-- The error of the join: the larger of the error of soundness, at a parser with at most
`honestBudget` queries, and the error of binding. -/
noncomputable def joinError (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞) (t : ℕ) : ℝ≥0∞ :=
  max (epsS t honestBudget) (epsB t)

/-- **At every policy: `D`'s one extractor meets soundness for the files' policy and binding, of
`D`'s own verifier.** -/
theorem soundFor_and_binds_of_record (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt D epsS) (binds : BindsAt D epsB) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp) :
    SoundForWith (systemOfRecord D Z (settingsOfRead pp)) (D.extractor Z (settingsOfRead pp))
        (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (fun t => epsS t honestBudget) ∧
      BindsWith (systemOfRecord D Z (settingsOfRead pp)) (D.extractor Z (settingsOfRead pp)) epsB :=
  ⟨(sound Z pp scope read).2 D.Form (D.prove Z (settingsOfRead pp)) (D.parse Z) honestBudget
      (sound Z pp scope read).1,
    (binds Z pp scope read).2⟩

/-- **At exact match: `SoundAndBinding` of `D`'s own verifier**, from soundness under
the files' policy and binding; the extractor behind the ∃ is `D`'s. -/
theorem soundAndBinding_of_record (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt D epsS) (binds : BindsAt D epsB) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundAndBinding (systemOfRecord D Z (settingsOfRead pp)) (joinError epsS epsB) := by
  obtain ⟨h1, hb⟩ := soundFor_and_binds_of_record D epsS epsB sound binds Z pp scope read
  rw [exact] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) (D.prove Z (settingsOfRead pp)) id
    (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_exact_iff w p o).1 hm).2)
  have e : (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) =
      D.extractor Z (settingsOfRead pp) := by
    funext c q
    simp
  have h3 : SoundForWith (systemOfRecord D Z (settingsOfRead pp))
      (D.extractor Z (settingsOfRead pp))
      (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput (fun t => epsS t honestBudget) :=
    e ▸ h2
  exact soundAndBinding_of_le _ _ _ _ _ h3 hb (fun _ => le_max_left _ _) (fun _ => le_max_right _ _)

/-- **At exact match: `SoundOpened` of `D`'s own verifier**, at twice the error. -/
theorem soundOpened_of_record (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt D epsS) (binds : BindsAt D epsB) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundOpened (systemOfRecord D Z (settingsOfRead pp)) fun t => 2 * joinError epsS epsB t :=
  soundOpened_of_soundAndBinding _ _
    (soundAndBinding_of_record D epsS epsB sound binds Z pp scope read exact)

/-- The honest side's budget is within the parsers' budget. -/
theorem honestBudget_le_parserBudget : honestBudget ≤ parserBudget :=
  Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- Twice the ceiling is one half. -/
theorem two_mul_ceiling : 2 * ceiling = 2⁻¹ := by
  unfold ceiling
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- **G8 and G9 give `SoundAndBinding` of `D`'s own verifier, in its nearest form**: at all public
files in scope that state exact match: one error, at most the ceiling (1/4) up to the budget of
queries. -/
theorem nearestSoundAndBinding_of_g8_g9 (D : SecondHashFunctionType → Description) (h8 : G8 D) (h9 : G9 D) :
    ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ ceiling) ∧
      NearestSoundAndBinding D eps := by
  obtain ⟨epsS, belowS, sound⟩ := h8
  obtain ⟨epsB, belowB, binds⟩ := h9
  exact ⟨joinError epsS epsB,
    fun t ht => max_le (belowS t honestBudget ht honestBudget_le_parserBudget) (belowB t ht),
    fun Z pp scope read exact =>
      soundAndBinding_of_record _ epsS epsB sound binds Z pp scope read exact⟩

/-- Among the nearest forms: `SoundAndBinding` gives `SoundOpened`, at twice the error. -/
theorem nearestSoundOpened_of_nearestSoundAndBinding (D : SecondHashFunctionType → Description) (eps : ℕ → ℝ≥0∞)
    (h : NearestSoundAndBinding D eps) : NearestSoundOpened D fun t => 2 * eps t :=
  fun Z pp scope read exact => soundOpened_of_soundAndBinding _ _ (h Z pp scope read exact)

/-- Among the nearest forms: `SoundAndBinding` gives `Sound`, at the same error. -/
theorem nearestSound_of_nearestSoundAndBinding (D : SecondHashFunctionType → Description) (eps : ℕ → ℝ≥0∞)
    (h : NearestSoundAndBinding D eps) : NearestSound D eps :=
  fun Z pp scope read exact => sound_of_soundAndBinding _ _ (h Z pp scope read exact)

/-- **G8 and G9 give `SoundOpened` of `D`'s own verifier, in its nearest form**: at all public files
in scope that state exact match: one error, at most twice the ceiling (1/2) up to the budget of
queries. -/
theorem nearestSoundOpened_of_g8_g9 (D : SecondHashFunctionType → Description) (h8 : G8 D) (h9 : G9 D) :
    ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ 2⁻¹) ∧ NearestSoundOpened D eps := by
  obtain ⟨eps, below, h⟩ := nearestSoundAndBinding_of_g8_g9 D h8 h9
  exact ⟨fun t => 2 * eps t,
    fun t ht => two_mul_ceiling ▸ mul_le_mul' le_rfl (below t ht),
    nearestSoundOpened_of_nearestSoundAndBinding D eps h⟩

/-- **G7 gives `Sound` of `D`'s own verifier, in its nearest form**, at an error that is at most the
ceiling (1/4) up to the budget of queries. -/
theorem nearestSound_of_g7 (D : SecondHashFunctionType → Description) (h : G7 D) :
    ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ ceiling) ∧ NearestSound D eps := by
  obtain ⟨eps, below, sound⟩ := h
  exact ⟨fun t => eps t honestBudget,
    fun t ht => below t honestBudget ht honestBudget_le_parserBudget,
    fun Z pp scope read exact =>
      (sound Z pp scope read exact).2 _ _ _ honestBudget (sound Z pp scope read exact).1⟩

/-! ## Ties that keep the error -/

/-- `SoundAt` gives `Sound` in its nearest form, at the error eps t honestBudget. -/
theorem nearestSound_of_at (D : SecondHashFunctionType → Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundAt (atSecondHashFunction D) eps) : NearestSound D fun t => eps t honestBudget :=
  fun Z pp scope read exact =>
    (sound Z pp scope read exact).2 _ _ _ honestBudget (sound Z pp scope read exact).1

/-- `SoundUnderPolicyAt` and `BindsAt` give `SoundAndBinding` in its nearest form, at
`joinError`. -/
theorem nearestSoundAndBinding_of_at (D : SecondHashFunctionType → Description) (epsS : ℕ → ℕ → ℝ≥0∞)
    (epsB : ℕ → ℝ≥0∞) (sound : SoundUnderPolicyAt (atSecondHashFunction D) epsS)
    (binds : BindsAt (atSecondHashFunction D) epsB) : NearestSoundAndBinding D (joinError epsS epsB) :=
  fun Z pp scope read exact =>
    soundAndBinding_of_record _ epsS epsB sound binds Z pp scope read exact

/-- Likewise `SoundOpened`, at twice `joinError`. -/
theorem nearestSoundOpened_of_at (D : SecondHashFunctionType → Description) (epsS : ℕ → ℕ → ℝ≥0∞)
    (epsB : ℕ → ℝ≥0∞) (sound : SoundUnderPolicyAt (atSecondHashFunction D) epsS)
    (binds : BindsAt (atSecondHashFunction D) epsB) :
    NearestSoundOpened D fun t => 2 * joinError epsS epsB t :=
  fun Z pp scope read exact => soundOpened_of_record _ epsS epsB sound binds Z pp scope read exact

/-! ## From the forms at all files to the nearest forms -/

theorem nearestSound_of_package (D : SecondHashFunctionType → Description) (eps : ℕ → ℝ≥0∞)
    (h : PackageSound D eps) : NearestSound D eps := fun Z pp scope read _ => h Z pp scope read

theorem nearestSoundAndBinding_of_package (D : SecondHashFunctionType → Description) (eps : ℕ → ℝ≥0∞)
    (h : PackageSoundAndBinding D eps) : NearestSoundAndBinding D eps :=
  fun Z pp scope read _ => h Z pp scope read

theorem nearestSoundOpened_of_package (D : SecondHashFunctionType → Description) (eps : ℕ → ℝ≥0∞)
    (h : PackageSoundOpened D eps) : NearestSoundOpened D eps :=
  fun Z pp scope read _ => h Z pp scope read

/-! ## At the stored full-size files

Given `FilesRead` (proved: `VerifierAndGoals.filesRead`, Johnson/Goal/Files/FilesReadProof.lean) a nearest
form speaks of one system by name: that of the stored full-size files. Without `FilesRead` no goal
of Ladder/Package.lean is known to speak of any file. -/

theorem nearestSound_at_full (facts : FilesRead) (D : SecondHashFunctionType → Description) (eps : ℕ → ℝ≥0∞)
    (h : NearestSound D eps) : ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      Sound (systemOfRecord (atSecondHashFunction D) storedPublicFiles (settingsOfRead pp)) eps :=
  let ⟨scope, pp, read, exact⟩ := facts.full
  ⟨pp, read, h storedPublicFiles pp scope read exact⟩

theorem nearestSoundAndBinding_at_full (facts : FilesRead) (D : SecondHashFunctionType → Description)
    (eps : ℕ → ℝ≥0∞) (h : NearestSoundAndBinding D eps) : ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      SoundAndBinding (systemOfRecord (atSecondHashFunction D) storedPublicFiles (settingsOfRead pp)) eps :=
  let ⟨scope, pp, read, exact⟩ := facts.full
  ⟨pp, read, h storedPublicFiles pp scope read exact⟩

theorem nearestSoundOpened_at_full (facts : FilesRead) (D : SecondHashFunctionType → Description)
    (eps : ℕ → ℝ≥0∞) (h : NearestSoundOpened D eps) : ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      SoundOpened (systemOfRecord (atSecondHashFunction D) storedPublicFiles (settingsOfRead pp)) eps :=
  let ⟨scope, pp, read, exact⟩ := facts.full
  ⟨pp, read, h storedPublicFiles pp scope read exact⟩

/-! ## At every policy that claims the model's own output

`AcceptancePolicy.exact` is one of many policies under which `Policy.MeetsPolicy` says "the output is not empty,
and every output token is the model's": those with theta = 2^8 ≤ C and (cap = 0 or 2^8 < C)
(`Policy.meetsPolicy_iff_of_exactKind`). The two theorems at one Z hold at all of them. That the
nearest forms say `pp.pol = AcceptancePolicy.exact` is a choice. That files with another such policy are
in scope is not shown. -/

theorem soundAndBinding_of_record_exactKind (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞)
    (epsB : ℕ → ℝ≥0∞) (sound : SoundUnderPolicyAt D epsS) (binds : BindsAt D epsB) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (mean : pp.pol.theta = 2 ^ 8) (clip : 2 ^ 8 ≤ pp.pol.C)
    (limit : pp.pol.cap = 0 ∨ 2 ^ 8 < pp.pol.C) :
    SoundAndBinding (systemOfRecord D Z (settingsOfRead pp)) (joinError epsS epsB) := by
  obtain ⟨h1, hb⟩ := soundFor_and_binds_of_record D epsS epsB sound binds Z pp scope read
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) (D.prove Z (settingsOfRead pp)) id
    (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_iff_of_exactKind mean clip limit w p o).1 hm).2)
  have e : (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) =
      D.extractor Z (settingsOfRead pp) := by
    funext c q
    simp
  have h3 : SoundForWith (systemOfRecord D Z (settingsOfRead pp))
      (D.extractor Z (settingsOfRead pp))
      (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput (fun t => epsS t honestBudget) :=
    e ▸ h2
  exact soundAndBinding_of_le _ _ _ _ _ h3 hb (fun _ => le_max_left _ _) (fun _ => le_max_right _ _)

theorem soundOpened_of_record_exactKind (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞)
    (epsB : ℕ → ℝ≥0∞) (sound : SoundUnderPolicyAt D epsS) (binds : BindsAt D epsB) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (mean : pp.pol.theta = 2 ^ 8) (clip : 2 ^ 8 ≤ pp.pol.C)
    (limit : pp.pol.cap = 0 ∨ 2 ^ 8 < pp.pol.C) :
    SoundOpened (systemOfRecord D Z (settingsOfRead pp)) fun t => 2 * joinError epsS epsB t :=
  soundOpened_of_soundAndBinding _ _
    (soundAndBinding_of_record_exactKind D epsS epsB sound binds Z pp scope read mean clip limit)

/-! ## Whatever function stands in the second hash function's place -/

/-- **G7' gives `Sound` of `D`'s own verifier at every function o in the second hash function's
place**, at all public files in scope that state exact match: one error, at most the ceiling (1/4)
up to the budget of queries. Every goal of Ladder/Package.lean stands at the format's own second
hash function (`atSecondHashFunction`), a fixed function; Ladder.lean has a form for every function for `Sound`
alone. -/
theorem sound_everyOlder_of_g7' (D : SecondHashFunctionType → Description) (h : G7' D) :
    ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ ceiling) ∧
      ∀ (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
        pp.pol = Inst.Model.AcceptancePolicy.exact →
        Sound (systemOfRecord (D o) Z (settingsOfRead pp)) eps := by
  obtain ⟨eps, below, sound⟩ := h
  exact ⟨fun t => eps t honestBudget,
    fun t ht => below t honestBudget ht honestBudget_le_parserBudget,
    fun o Z pp scope read exact =>
      (sound o Z pp scope read exact).2 _ _ _ honestBudget (sound o Z pp scope read exact).1⟩

/-! ## What cannot hold at all files in scope -/

/-- The honest side as one adversary of `SoundOpened`: it samples the randomness, commits, proves,
and names the commitment, the weights with the randomness, and the request with the proof. -/
def honestOpener (system : ArgumentSystem) (weights : system.Weights) (prompt output : List Token) :
    RandomizedAlgorithm (Commitment × (system.Weights × system.CommitmentRandomness) ×
      (List Token × List Token × system.Proof)) :=
  system.sampleCommitmentRandomness.bind fun randomness =>
    (system.commit weights randomness).toRandomized.bind fun commitment =>
      (system.prove weights randomness prompt output).bind fun proof =>
        .done (commitment, (weights, randomness), (prompt, output, proof))

/-- One algorithm, then another: the bounds on their queries add. -/
theorem queryBound_then {α β : Type} (first : RandomizedAlgorithm α)
    (next : α → RandomizedAlgorithm β) (a b : ℕ) (ha : first.QueryBound a)
    (hb : ∀ result, (next result).QueryBound b) : (first.bind next).QueryBound (a + b) := by
  refine (queryBound_toUpload _ _).1 ?_
  rw [toUpload_bind]
  exact ZKCP.OComp.QueryBound.bind (fun result => (next result).toUpload) b
    (fun result => (queryBound_toUpload _ _).2 (hb result)) _ a ((queryBound_toUpload _ _).2 ha)

/-- At an output that is not the model's: whenever the honest side is accepted, it wins the
experiment of `SoundOpened`. -/
theorem accepted_le_opened (system : ArgumentSystem) (weights : system.Weights)
    (prompt output : List Token) (notModel : ¬ system.IsModelOutput weights prompt output) :
    Prob (do
        let randomness ← system.sampleCommitmentRandomness
        let commitment ← (system.commit weights randomness).toRandomized
        let proof ← system.prove weights randomness prompt output
        (system.verify commitment prompt output proof).toRandomized)
      {accepted | accepted = false}ᶜ
    ≤ Prob (do
          let (commitment, (weights, randomness), (prompt, output, proof)) ←
            honestOpener system weights prompt output
          let recomputed ← (system.commit weights randomness).toRandomized
          let accepted ← (system.verify commitment prompt output proof).toRandomized
          pure (commitment, recomputed, weights, prompt, output, accepted))
        {(commitment, recomputed, weights, prompt, output, accepted) |
          recomputed = commitment ∧ accepted = true ∧
            ¬ system.IsModelOutput weights prompt output} := by
  classical
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
        (system.commit weights randomness).toRandomized.bind fun commitment =>
          (system.prove weights randomness prompt output).bind fun proof =>
            (system.verify commitment prompt output proof).toRandomized).run hash) _
    ≤ ZKCP.prob (((honestOpener system weights prompt output).bind fun x =>
        (system.commit x.2.1.1 x.2.1.2).toRandomized.bind fun recomputed =>
          (system.verify x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).toRandomized.bind fun accepted =>
            RandomizedAlgorithm.done
              (x.1, recomputed, x.2.1.1, x.2.2.1, x.2.2.2.1, accepted)).run hash) _
  unfold honestOpener
  simp only [run_bind, run_done, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
    PMF.bind_bind]
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun randomness _ => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun proof _ => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  exact ind_le fun hb => ⟨rfl, Bool.eq_true_of_not_eq_false hb, notModel⟩

/-- **Completeness for a claim that an output meets which is not the model's bars `SoundOpened`.**
If the honest side is accepted but for α at a request that meets the claim and whose output is not
the model's, and makes at most `queries` queries there, then `SoundOpened` can hold only at an error
of at least 1 - α at that number of queries. The subtraction is truncated: at α ≥ 1 this says
nothing. -/
theorem one_sub_le_of_completeFor_soundOpened (system : ArgumentSystem)
    (claim : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (complete : CompleteFor system claim α) (opened : SoundOpened system ε)
    (weights : system.Weights) (prompt output : List Token) (holds : claim weights prompt output)
    (notModel : ¬ system.IsModelOutput weights prompt output) (queries : ℕ)
    (bound : (honestOpener system weights prompt output).QueryBound queries) :
    1 - α ≤ ε queries :=
  le_trans (one_sub_le_Prob_compl _ _ (complete weights prompt output holds))
    (le_trans (accepted_le_opened system weights prompt output notModel)
      (opened queries (honestOpener system weights prompt output) bound))

/-- **`SoundOpened` as written, at all files in scope, cannot hold at a small error together with
G3'pol**, given `FilesRead`: at some number of queries within the honest side's budget its error is
at least 1 - `completenessErrorBound`. The files are `zGap`: their policy is not exact match, and some output there
can be served, meets the policy and is not the model's (`fixedFacts`). `FilesRead` is a premise:
that the reader reads these files as expected. It is checked by evaluation (Ladder/Guards.lean) and
proved (`VerifierAndGoals.filesRead`, Johnson/Goal/Files/FilesReadProof.lean). -/
theorem packageSoundOpened_bar (facts : FilesRead) (D : SecondHashFunctionType → Description) (g3 : G3'pol D)
    (eps : ℕ → ℝ≥0∞) (h : PackageSoundOpened D eps) :
    ∃ t, t ≤ honestBudget ∧ 1 - completenessErrorBound ≤ eps t := by
  obtain ⟨scope, pp, read, pol⟩ := facts.other
  obtain ⟨w, prompt, output, serve, meets, notModel⟩ := fixedFacts.otherClaim pp read pol
  obtain ⟨⟨qSample, qCommit, qProve, qMore, qParse, le, hs, hc, hp, -⟩, complete⟩ :=
    g3 zGap pp (Or.inr rfl) scope read
  refine ⟨qSample + (qCommit + (qProve + 0)), by omega, ?_⟩
  exact one_sub_le_of_completeFor_soundOpened _ _ completenessErrorBound eps complete (h zGap pp scope read) w
    prompt output ⟨serve, meets⟩ notModel _
    (queryBound_then _ _ qSample _ hs fun ρ =>
      queryBound_then _ _ qCommit _ (hc w ρ) fun _ =>
        queryBound_then _ _ qProve 0 (hp w ρ prompt output) fun _ => trivial)

/-- **`SoundAndBinding` as written, at all files in scope, cannot hold at a small error together
with G3'pol**, given `FilesRead`: at some number of queries within the honest side's budget twice
its error is at least 1 - `completenessErrorBound`. `FilesRead` is a premise, as at `packageSoundOpened_bar`; it is
checked by evaluation and proved (`VerifierAndGoals.filesRead`). -/
theorem packageSoundAndBinding_bar (facts : FilesRead) (D : SecondHashFunctionType → Description) (g3 : G3'pol D)
    (eps : ℕ → ℝ≥0∞) (h : PackageSoundAndBinding D eps) :
    ∃ t, t ≤ honestBudget ∧ 1 - completenessErrorBound ≤ 2 * eps t :=
  packageSoundOpened_bar facts D g3 (fun t => 2 * eps t) fun Z pp scope read =>
    soundOpened_of_soundAndBinding _ _ (h Z pp scope read)

end VerifierAndGoals

#print axioms VerifierAndGoals.soundFor_and_binds_of_record
#print axioms VerifierAndGoals.soundAndBinding_of_record
#print axioms VerifierAndGoals.soundOpened_of_record
#print axioms VerifierAndGoals.two_mul_ceiling
#print axioms VerifierAndGoals.nearestSoundAndBinding_of_g8_g9
#print axioms VerifierAndGoals.nearestSoundOpened_of_nearestSoundAndBinding
#print axioms VerifierAndGoals.nearestSound_of_nearestSoundAndBinding
#print axioms VerifierAndGoals.nearestSoundOpened_of_g8_g9
#print axioms VerifierAndGoals.nearestSound_of_g7
#print axioms VerifierAndGoals.accepted_le_opened
#print axioms VerifierAndGoals.one_sub_le_of_completeFor_soundOpened
#print axioms VerifierAndGoals.packageSoundOpened_bar
#print axioms VerifierAndGoals.packageSoundAndBinding_bar
#print axioms VerifierAndGoals.nearestSound_of_at
#print axioms VerifierAndGoals.nearestSoundAndBinding_of_at
#print axioms VerifierAndGoals.nearestSoundOpened_of_at
#print axioms VerifierAndGoals.nearestSound_of_package
#print axioms VerifierAndGoals.nearestSoundAndBinding_of_package
#print axioms VerifierAndGoals.nearestSoundOpened_of_package
#print axioms VerifierAndGoals.nearestSound_at_full
#print axioms VerifierAndGoals.nearestSoundAndBinding_at_full
#print axioms VerifierAndGoals.nearestSoundOpened_at_full
#print axioms VerifierAndGoals.soundAndBinding_of_record_exactKind
#print axioms VerifierAndGoals.soundOpened_of_record_exactKind
#print axioms VerifierAndGoals.sound_everyOlder_of_g7'
#print axioms VerifierAndGoals.honestBudget_le_parserBudget
#print axioms VerifierAndGoals.queryBound_then
