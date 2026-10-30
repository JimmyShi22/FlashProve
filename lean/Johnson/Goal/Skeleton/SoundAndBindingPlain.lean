-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundAndBindingPlain.lean: `SoundAndBinding`, `SoundOpened` and
`Sound` (VerifiableInference/Statements.lean) of `plainSystemAt OnBytes.secondHashFunction Z …`
(Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean), from `KeySound` and `ProofSound`
(Johnson/Goal/Conditions/RowsAtTheRecord.lean), at every set of public files Z in scope whose policy
is exact match. First at one Z, from the two hypotheses at that Z alone
(Johnson/Goal/Skeleton/TopAtZ.lean: `KeySoundAt Z`, `ProofSoundAt Z`): "…_plain_at"; then from
`KeySound` and `ProofSound`: "…_plain_of_two", one call each.

Why. The goals' `NearestSoundAndBinding` reads a description's own committer, and
`VerifierAndGoals.theDescription`'s is hollow. The two statements that read openings are had at stand-ins
(`theBound K`, `theWide K W`, `theWideDigits`). `plainSystemAt o Z s b sample prove` is nearer the
name: it is the name's own system of record (its verifier with its own parser, its model, its type
of proofs) with one thing changed: the committer is the written one (`committerAt`), and its
randomness is all coins (`CoinsAt`: pads with tails, and salts of the wire's length at the tree's
places).

How. One extractor serves both halves: the name's own.
  soundness: `soundUnderPolicyAtZ_of_two` is at `(atSecondHashFunction theDescription).extractor`, and soundness
    for a claim reads neither committer nor prover (`SoundForWith.otherRandomness`, by definition);
  binding: `bindsWith_atOlder` is at `extractorAt`, which is that extractor (`extractor_atOlder`).

Main names (namespace `VerifierAndGoals.AtTheName`).
  `soundForWith_record_within`: general in D: from `SoundUnderPolicyAtZ D eps Z pp`, at exact match,
    where D's own parser is within n queries: soundness for "the output tokens are the model's" of
    D's system of record at D's own extractor, at eps t n. (The first half of
    `soundAndBinding_of_record_within`, Ladder/PackageBits.lean, stated by itself.)
  `plainError t` := the larger of `VerifierAndGoals.soundnessErrorInQueries t 1` and `epsBind honestBudget t`, that is of
    16 (t + 1 + 2^23) / 2^128 with its square term (Ladder/Bits.lean) and
    3 (t + 2 · 2^48 + 2)² / 2^256 (Ladder/FitBinds.lean).
  **`soundAndBinding_plain_at`**, `soundOpened_plain_at` (at twice the error), `sound_plain_at`.
  `soundAndBinding_plain_of_two`, `soundOpened_plain_of_two`, `sound_plain_of_two`.

Limits. The two hypotheses, at one Z or at all, are premises, and each is itself an assumption of
soundness: nothing in this file shows that they can be met. Elsewhere in this library `KeySoundAt Z`
is a theorem at every Z in scope (`keySound_at_live_holds`,
Johnson/Goal/Conditions/KeyOpenHolds.lean), and `ProofSoundAt Z` at every Z in scope whose files are
read (`proofSoundAt_of_verify`, SoundOfVerifyMore.lean; of the verifier with fourteen entry tests):
each under the live test's yes, which is evaluated at the release's files, not proved: so the
theorems may still be empty. What these are worth is told in the head of SoundOfVerifyAt.lean. The
statements are not the goals': they end in the top statements of `plainSystemAt`, not in
`NearestSoundAndBinding` of a description. The committer stands beside the description, not in it,
and is tied to no program (Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean's limits travel whole). b (what
fills the tree's spare leaves), sample and prove are letters under "for all": no statement here
reads sample or prove. At
`OnBytes.secondHashFunction` alone. Nothing on completeness or hiding. The public files are fixed before the
hash function is drawn.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.TopAtZ
import Johnson.Goal.Conditions.BindsAtSecondHashFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference

/-- **Soundness for "the output tokens are the model's" reads neither the committer nor the
prover**: it carries over to another type of committer's randomness, with any sampler, committer and
prover. By definition. -/
theorem SoundForWith.otherRandomness (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor system.IsModelOutput ε) (Coins : Type)
    (sample : RandomizedAlgorithm Coins)
    (commit : system.Weights → Coins → DeterministicAlgorithm Commitment)
    (prove : system.Weights → Coins → List Token → List Token →
      RandomizedAlgorithm system.Proof) :
    SoundForWith (system.withRandomness Coins sample commit prove) extractor
      (system.withRandomness Coins sample commit prove).IsModelOutput ε := sound

/-- Soundness and binding at one extractor give `SoundAndBinding` at the larger error. -/
theorem soundAndBinding_of_max (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε₁ ε₂ : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor system.IsModelOutput ε₁)
    (binds : BindsWith system extractor ε₂) :
    SoundAndBinding system fun t => max (ε₁ t) (ε₂ t) :=
  soundAndBinding_of_le system extractor ε₁ ε₂ _ sound binds (fun _ => le_max_left _ _)
    (fun _ => le_max_right _ _)

end VerifiableInference

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **At exact match: soundness for "the output tokens are the model's" of D's system of record, at
D's own extractor**, where D's own parser is within n queries. General in D. -/
theorem soundForWith_record_within (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (sound : SoundUnderPolicyAtZ D eps Z pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (n : ℕ) (hn : Parser.Within (D.parse Z) n) :
    SoundForWith (systemOfRecord D Z (settingsOfRead pp)) (D.extractor Z (settingsOfRead pp))
      (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput fun t => eps t n := by
  have h1 := sound.2 D.Form (D.prove Z (settingsOfRead pp)) (D.parse Z) n hn
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
  exact e ▸ h2

/-- The error: the larger of the error of soundness, at the name's own parser's one query, and the
error of binding. -/
def plainError (t : ℕ) : ℝ≥0∞ := max (VerifierAndGoals.soundnessErrorInQueries t 1) (epsBind honestBudget t)

/-- The half on soundness, at `extractorAt`. -/
theorem soundForWith_plain_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundForWith (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      (FlashProve.extractorAt OnBytes.secondHashFunction Z (settingsOfRead pp))
      (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove).IsModelOutput
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 := by
  have h := soundForWith_record_within (theDescriptionO OnBytes.secondHashFunction) VerifierAndGoals.soundnessErrorInQueries Z pp
    (soundUnderPolicyAtZ_of_two Z pp scope hr kS pS) exact 1
    (theDescription_within OnBytes.secondHashFunction Z)
  rw [extractor_atOlder OnBytes.secondHashFunction Z (settingsOfRead pp)] at h
  exact SoundForWith.otherRandomness _ _ _ h (CoinsAt OnBytes.secondHashFunction Z) sample
    (committerAt OnBytes.secondHashFunction Z (settingsOfRead pp) b) prove

/-- The same, in the form in which `soundAndBinding_of_max` returns it. (Left to itself Lean opens
the two errors to compare them, and runs out of time.) -/
theorem plainError_eq :
    plainError = fun t => max ((fun t => VerifierAndGoals.soundnessErrorInQueries t 1) t) (epsBind honestBudget t) := rfl

/-- **THE STATEMENT `SoundAndBinding` OF THE NAME's SYSTEM OF RECORD WITH THE COMMITTER WRITTEN IN
LEAN BESIDE THE IOP, A PLACEHOLDER THAT CORRESPONDS TO NO PROGRAM OF THE RELEASE**, AT ONE Z in
scope whose policy is exact match, from the two hypotheses at that Z alone. The extractor behind the
∃ is the name's own. -/
theorem soundAndBinding_plain_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError := by
  have hs := soundForWith_plain_at Z pp scope hr exact kS pS b sample prove
  have hb := bindsWith_atOlder OnBytes.secondHashFunction Z pp hr b sample prove
  rw [plainError_eq]
  exact soundAndBinding_of_max _ _ _ _ hs hb

/-- **`SoundOpened` of it**, at twice the error. -/
theorem soundOpened_plain_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_of_soundAndBinding _ _
    (soundAndBinding_plain_at Z pp scope hr exact kS pS b sample prove)

/-- `Sound` of it, at the same error. -/
theorem sound_plain_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    Sound (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove) plainError :=
  sound_of_soundAndBinding _ _
    (soundAndBinding_plain_at Z pp scope hr exact kS pS b sample prove)

/-- **The same from `KeySound` and `ProofSound`**, at every Z in scope whose policy is exact match.
-/
theorem soundAndBinding_plain_of_two (kS : KeySound) (pS : ProofSound) (Z : PublicFiles) (pp :
        Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError :=
  soundAndBinding_plain_at Z pp scope hr exact (kS Z scope) (pS Z scope) b sample prove

/-- `SoundOpened` of it from `KeySound` and `ProofSound`, at twice the error. -/
theorem soundOpened_plain_of_two (kS : KeySound) (pS : ProofSound) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_plain_at Z pp scope hr exact (kS Z scope) (pS Z scope) b sample prove

/-- `Sound` of it from `KeySound` and `ProofSound`, at the same error. -/
theorem sound_plain_of_two (kS : KeySound) (pS : ProofSound) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    Sound (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove) plainError :=
  sound_plain_at Z pp scope hr exact (kS Z scope) (pS Z scope) b sample prove

end VerifierAndGoals.AtTheName

#print axioms VerifiableInference.SoundForWith.otherRandomness
#print axioms VerifiableInference.soundAndBinding_of_max
#print axioms VerifierAndGoals.AtTheName.soundForWith_record_within
#print axioms VerifierAndGoals.AtTheName.soundForWith_plain_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_at
#print axioms VerifierAndGoals.AtTheName.sound_plain_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_of_two
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_of_two
#print axioms VerifierAndGoals.AtTheName.sound_plain_of_two
