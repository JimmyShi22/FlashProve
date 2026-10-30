-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingProof.lean: binding and extraction at compile's own committer: the proof's
text for FinalBindingGoal and FinalBindingLabelled (FinalBindingStatement.lean of this folder).

 1. At every hash function compile's committer gives the value of the written committer
    (LayoutsByPublicReading.commitAtCoins) at the first table's randomness and salts, which are the first two digits
    of its number, read at the public reading's value: evaluate_commit_frontArgKF_atFiles
    (CommitValueF.lean). compile's committer asks of a failed try of a search the first hash block
    alone; the first table's queries are asked whole, so its value does not turn.
 2. Of the written committer binding in the opening form is a theorem, at salts of any one length:
    bindsWith_of_laws (Johnson/Goal/Conditions/BindsTold.lean).
 3. Binding passes along a committer of the same values: BindsWith.ofCommit (Ladder/FitBinds.lean), at
    the eight queries of the public reading more.
 4. The first clause is finalSoundAtExtractor (FinalSoundAtExtractor.lean), at the same extractor.
 5. Extraction follows from binding: the honest committer is one of the makers of a commitment:
    BindsWith.extractsDrawn (Johnson/Bind/ExtractsDrawn.lean).
 6. The six lines pass to the system with a word beside each proof: its committer is the same, and
    its verifier drops the word (VerifiableInference/LabelledSound.lean).
-/
import Johnson.Face.FinalBindingStatement
import Johnson.Face.CommitValueF
import Johnson.Face.FinalSoundAtExtractor
import VerifiableInference.LabelledSound
import Johnson.Goal.Conditions.BindsTold
import Johnson.Bind.Cpp.OfTie
import Johnson.Bind.ExtractsDrawn
import VerifiableInference.Checks
import Johnson.Top.FrontBinds
import VerifiableInference.NoTwoOpenings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve VerifierAndGoals.Fit FlashProve VerifiableInference.OnPublicFiles OnBytes.FrontRoad
open OnBytes.WholeKey Johnson.Face
open IntegerTransformer (Settings)
open scoped ENNReal

/-! ## 1. The written committer at salts of one length -/

/-- The written committer's coins: a table's randomness, and salts of the given length at the tree's
places. -/
def WrittenCoins (files : PublicFiles) (length : ℕ) : Type :=
  { x : (R₀ files).protocol.EncodingRandomness × (ℕ → Rom.Bits) //
    ∀ j, j < 2 ^ (R₀ files).queryLayout.depth → (x.2 j).length = length }

/-- The verifier's own system with the written committer at these coins. -/
def writtenSystem (files : PublicFiles) (settings : Settings) (length : ℕ) (filler : (R₀ files).LeafBody)
    (sample : RandomizedAlgorithm (WrittenCoins files length))
    (prove : ModelWeights settings → WrittenCoins files length → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) : ArgumentSystem :=
  (systemOfRecord flashProveDescription files settings).withRandomness (WrittenCoins files length) sample
    (fun weights x => (T₀ files).commitAtCoins filler (backThe files settings weights) x.1.1 x.1.2)
    prove

section Written

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem

/-- Binding of the written committer, at salts of any one length. -/
theorem bindsWith_writtenAtLength (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (read : readFiles files = .ok parameters) (length : ℕ) (filler : (R₀ files).LeafBody)
    (sample : RandomizedAlgorithm (WrittenCoins files length))
    (prove : ModelWeights (settingsOfRead parameters) → WrittenCoins files length → List Token →
      List Token → RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith (writtenSystem files (settingsOfRead parameters) length filler sample prove)
      ((T₀ files).extractorOn (phiThe files (settingsOfRead parameters)))
      (epsBind honestBudget) := by
  unfold writtenSystem
  rw [← T_the placeHolderNumberCoins files]
  exact bindsWith_of_laws (theTerms placeHolderNumberCoins)
    (bindLaws_the placeHolderNumberCoins hE_the files parameters read) filler
    (WrittenCoins files length) (fun x => x.1.1) (fun x => x.1.2) length (fun x => x.2) sample prove

end Written

/-! ## 2. From compile's number to the written committer's coins -/

variable {files : PublicFiles} {settings : Settings}

/-- compile's honest side at a value of the public reading. -/
abbrev honestSideAt (honest : HonestProversAndSettingsAtFiles files settings)
    (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) :=
  (honestSide ((flashProveWiring files settings honest.fallbackInstance).layoutAtReading reading)
    honest.provers (honest.compiledSettings reading)).side

/-- The first table's salts have the length of the public start with the free bits. -/
theorem length_firstSalts (honest : HonestProversAndSettingsAtFiles files settings) (length : ℕ)
    (salts : TableSaltsHaveLength honest length) (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D)
    (n j : ℕ) (hj : j < 2 ^ (R₀ files).queryLayout.depth) :
    (firstSalts (honestSideAt honest reading) (2 ^ (R₀ files).queryLayout.depth) n j).length = length := by
  unfold firstSalts cutS
  rw [if_pos hj]
  show (if h : j < 2 ^ (R₀ files).queryLayout.depth then
    (honest.compiledSettings reading).coinNumbers.pre₀ ++ List.ofFn _ else []).length = length
  rw [dif_pos hj, List.length_append, List.length_ofFn]
  exact salts reading

/-- The written committer's coins at a value of the public reading and a number. -/
def writtenCoinsAt (honest : HonestProversAndSettingsAtFiles files settings) (length : ℕ)
    (salts : TableSaltsHaveLength honest length) (n : ℕ)
    (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) : WrittenCoins files length :=
  ⟨(firstRandomness (honestSideAt honest reading) n,
      firstSalts (honestSideAt honest reading) (2 ^ (R₀ files).queryLayout.depth) n),
    fun j hj => length_firstSalts honest length salts reading n j hj⟩

/-- The algorithm that makes them of a number: the public reading, and no further query. -/
def writtenCoinsOf (honest : HonestProversAndSettingsAtFiles files settings) (length : ℕ)
    (salts : TableSaltsHaveLength honest length) (n : ℕ) :
    DeterministicAlgorithm (WrittenCoins files length) :=
  deterministicOf ((Rom.ofRom (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).Pub).mapO
    (writtenCoinsAt honest length salts n))

theorem evaluate_writtenCoinsOf (honest : HonestProversAndSettingsAtFiles files settings) (length : ℕ)
    (salts : TableSaltsHaveLength honest length) (n : ℕ) (hash : Hash) :
    (writtenCoinsOf honest length salts n).evaluate hash =
      writtenCoinsAt honest length salts n
        ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).Pub.det (_root_.Run.famOne hash)) := by
  unfold writtenCoinsOf
  rw [OnBytes.Maker.ParsedRead.evaluate_deterministicOf_det]
  show ((Rom.ofRom (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).Pub).bind fun a => .pure _).det hash = _
  rw [ZKCP.OComp.det_bind, _root_.Run.det_ofRom]
  rfl

theorem writtenCoinsOf_within (honest : HonestProversAndSettingsAtFiles files settings) (length : ℕ)
    (salts : TableSaltsHaveLength honest length) (n : ℕ) :
    (writtenCoinsOf honest length salts n).toRandomized.QueryBound 8 :=
  queryBound_deterministicOf _ 8
    (ZKCP.OComp.QueryBound.mapO _ _ 8 (Rom.queryBound_ofRom _ 8 (familyLaws_the files).eight))

/-! ## 3. Binding at compile's committer -/

/-- compile's committer, written out: the scheme's committer at the number, the commitment alone kept.
-/
theorem compile_commit_is (part : HonestProversAndSettingsAtFiles files settings) (weights : ModelWeights settings)
    (n : Fin (part.coinBound + 1)) :
    (compile (flashProveAtFiles files settings part)).commit weights n =
      deterministicOf ((((committerAndProverOverOneHash (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) (honestSideAt part)
        (flashFirstBlockTest files) (backThe files settings) part.fallbackInstance (fun id _ => id)
        (fun key proof => bytesWriter files ([], (lowKey key, lowPrf key proof)))
        (fun commitment request form =>
          (compiledVerifier (flashProvePublic files settings) (flashProveDescription.parse files) commitment request.1
            request.2 form).toRandomized.toUpload)).C weights).withCoins n.val).mapO Prod.fst) :=
  id rfl

/-- compile's sampler draws one number. -/
theorem compile_sample_is (part : HonestProversAndSettingsAtFiles files settings) :
    (compile (flashProveAtFiles files settings part)).sampleCommitmentRandomness =
      .sample part.coinBound fun t => .done (id t) :=
  id rfl

/-- A prover for the written system, which no statement on binding reads. -/
def idleProver (length : ℕ) : ModelWeights settings → WrittenCoins files length → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form :=
  fun _ _ _ _ => .done noProofForm

theorem bitsBinding_le_finalBindingError : ∀ queries, bindingErrorInQueries queries ≤ finalBindingError queries :=
  fun _ => le_max_right _ _

/-- **compile's committer has the written committer's value**, at every hash function. -/
theorem commit_value (part : HonestProversAndSettingsAtFiles files settings) (length : ℕ)
    (salts : TableSaltsHaveLength part length) (filler : (R₀ files).LeafBody)
    (weights : ModelWeights settings) (n : Fin (part.coinBound + 1)) (hash : Hash) :
    ((compile (flashProveAtFiles files settings part)).commit weights n).evaluate hash =
      ((T₀ files).commitAtCoins filler (backThe files settings weights)
        ((writtenCoinsOf part length salts n.val).evaluate hash).1.1
        ((writtenCoinsOf part length salts n.val).evaluate hash).1.2).evaluate hash := by
  rw [evaluate_writtenCoinsOf, compile_commit_is,
    evaluate_commit_frontArgKF_atFiles files (honestSideAt part) (backThe files settings)
      part.fallbackInstance]
  exact congrArg (fun c => DeterministicAlgorithm.evaluate hash c)
    (commitAtCoins_filling (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) _ filler (leaves_R₀ files) _ _ _)

section Carried

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem LayoutsByPublicReading.commitAtCoins layoutsOfBuiltDescription

/-- **BINDING AT compile's OWN COMMITTER**, in the opening form, at the description's extractor, at
public files that are read. -/
theorem finalBinds (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (read : readFiles files = .ok parameters)
    (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (length : ℕ)
    (salts : TableSaltsHaveLength part length) :
    BindsWith (compile (flashProveAtFiles files (settingsOfRead parameters) part))
      (finalExtractor files (settingsOfRead parameters)) finalOpeningError := by
  have written := bindsWith_writtenAtLength files parameters read length (placeHolderNumberCoins.b₀ files)
    (writtenCoinsOf part length salts 0).toRandomized (idleProver length)
  have carried := BindsWith.ofCommit _ (compile (flashProveAtFiles files (settingsOfRead parameters) part))
    _ _ written some id (fun n => writtenCoinsOf part length salts n.val) 8
    (fun n => writtenCoinsOf_within part length salts n.val) (fun _ => rfl)
    (fun weights n hash => commit_value part length salts _ weights n hash)
  unfold finalExtractor
  exact (Bind.Cpp.extractor_fold files (settingsOfRead parameters)) ▸ carried

/-! ## 4. The theorem -/

/-- **Correctness of extraction at compile's own committer**, at every bound on its queries. -/
theorem finalExtracts (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (read : readFiles files = .ok parameters)
    (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (length : ℕ)
    (salts : TableSaltsHaveLength part length) (queries : ℕ)
    (within : CommitterWithin (compile (flashProveAtFiles files (settingsOfRead parameters) part)) queries) :
    ExtractsCommittedWeights (compile (flashProveAtFiles files (settingsOfRead parameters) part))
      (finalExtractor files (settingsOfRead parameters)) (finalOpeningError queries) :=
  (finalBinds files parameters read part length salts).extractsDrawn part.coinBound id
    (compile_sample_is part) queries within

/-- Binding at the error of the top line's second half. -/
theorem finalBinds_bits (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (read : readFiles files = .ok parameters)
    (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (length : ℕ)
    (salts : TableSaltsHaveLength part length) :
    BindsWith (compile (flashProveAtFiles files (settingsOfRead parameters) part))
      (finalExtractor files (settingsOfRead parameters)) bindingErrorInQueries :=
  bindsWith_bits_of_square 8 (by norm_num) (finalBinds files parameters read part length salts)

/- And these. -/
attribute [local irreducible] soundnessErrorInQueries bindingErrorInQueries epsBind levelError finalExtractor

/-- **Soundness and binding at compile's own committer**, as the top line has them. -/
theorem finalBoth (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (taken : FilesTaken files parameters)
    (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (length : ℕ)
    (salts : TableSaltsHaveLength part length) :
    SoundAndBinding (compile (flashProveAtFiles files (settingsOfRead parameters) part))
      finalBindingError :=
  soundAndBinding_of_le (compile (flashProveAtFiles files (settingsOfRead parameters) part))
    (finalExtractor files (settingsOfRead parameters)) finalSoundnessError bindingErrorInQueries
    finalBindingError (finalSoundAtExtractor files parameters taken part)
    (finalBinds_bits files parameters taken.read part length salts)
    finalSoundnessError_le_finalBindingError bitsBinding_le_finalBindingError

/-- **BINDING AND EXTRACTION AT compile's OWN COMMITTER.** -/
theorem finalBindingGoal : FinalBindingGoal :=
  fun files parameters taken part length salts =>
    { sound := finalSoundAtExtractor files parameters taken part
      binds := finalBinds files parameters taken.read part length salts
      soundAndBinding := finalBoth files parameters taken part length salts
      soundOpened := soundOpened_of_soundAndBinding _ _
        (finalBoth files parameters taken part length salts)
      noTwoOpenings := (finalBinds files parameters taken.read part length salts).noTwoOpenings
      extracts := finalExtracts files parameters taken.read part length salts }

/-- The six lines pass to the system with a word beside each proof, whatever the rule for the word.
-/
theorem BindingOf.labelled {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} (h : BindingOf system extractor)
    {Label : Type} (label : system.Weights → List Token × List Token → Label) :
    BindingOf (VerifiableInference.labelled system label) extractor where
  sound := soundForWith_labelled system label extractor system.IsModelOutput _ h.sound
  binds := (bindsWith_labelled_iff system label extractor _).2 h.binds
  soundAndBinding := soundAndBinding_labelled system label _ h.soundAndBinding
  soundOpened := soundOpened_labelled system label _ h.soundOpened
  noTwoOpenings := h.noTwoOpenings
  extracts := fun queries within =>
    (extractsCommittedWeights_labelled_iff system label extractor _).2 (h.extracts queries within)

/-- **THE SAME OF THE COMPILED SYSTEM WITH A WORD BESIDE EACH PROOF.** -/
theorem finalBindingLabelled : FinalBindingLabelled :=
  fun files parameters taken part length salts _ label =>
    (finalBindingGoal files parameters taken part length salts).labelled label

end Carried

/-! ## 5. Controls -/

/-- **A control: the line on binding can fail.** An extractor that never gives some weights binds at
no error below 1 at a bound on the committer's queries. That bound is a premise: this file shows no
case of it. -/
theorem never_does_not_bind_compile (part : HonestProversAndSettingsAtFiles files settings)
    (extractor : Commitment → QueryLog → Option (ModelWeights settings)) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith (compile (flashProveAtFiles files settings part)) extractor ε)
    (weights : ModelWeights settings) (never : ∀ c l, extractor c l ≠ some weights) (queries : ℕ)
    (within : CommitterWithin (compile (flashProveAtFiles files settings part)) queries) : 1 ≤ ε queries :=
  binds.one_le_of_never weights never (0 : Fin (part.coinBound + 1))
    (within weights (0 : Fin (part.coinBound + 1)))

/-- **A control: the law on salts can be met.** It reads two numbers of the honest part: where these
do not hang on the public reading, it holds. -/
theorem tableSaltsHaveLength_of_constant (part : HonestProversAndSettingsAtFiles files settings)
    (start : Rom.Bits) (free : ℕ)
    (same : ∀ reading, (part.compiledSettings reading).coinNumbers.pre₀ = start ∧
      (part.compiledSettings reading).coinNumbers.ℓ = free) :
    TableSaltsHaveLength part (start.length + free) :=
  fun reading => by rw [(same reading).1, (same reading).2]

/-- A system whose honest side stays within a budget has its committer within it. -/
theorem committerWithin_of_withinBudget {system : ArgumentSystem} {budget : ℕ}
    (within : AtEveryRequest.WithinBudget system budget) : CommitterWithin system budget := by
  obtain ⟨sampling, committing, proving, le, -, bound, -⟩ := within
  exact fun weights randomness =>
    queryBound_mono_det _ committing budget (by omega) (bound weights randomness)

/-- **Correctness of extraction where the honest side stays within its budget**: the error at 2^48,
about 2^-155.2. -/
theorem BindingOf.extractsWithinBudget {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} (h : BindingOf system extractor)
    (within : AtEveryRequest.WithinBudget system honestQueryBudget) :
    ExtractsCommittedWeights system extractor (finalOpeningError honestQueryBudget) :=
  h.extracts honestQueryBudget (committerWithin_of_withinBudget within)

/-- **The law on salts follows from the laws on coins that completeness asks** (CoinsFit.len₀,
Johnson/WholeKey/Premises.lean), at the length of the verifier's strict format. -/
theorem tableSaltsHaveLength_of_coinsFit (part : HonestProversAndSettingsAtFiles files settings)
    (fit : ∀ reading, CoinsFit (R₀ files).queryLayout (R₀ files).compilerParameters
      (honestSide ((flashProveWiring files settings part.fallbackInstance).layoutAtReading reading)
        part.provers (part.compiledSettings reading))
      (part.compiledSettings reading).coinNumbers) :
    TableSaltsHaveLength part (R₀ files).compilerParameters.sMT :=
  fun reading => (fit reading).len₀

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.compile_commit_is
#print axioms VerifiableInference.Compilation.compile_sample_is
#print axioms VerifiableInference.Compilation.tableSaltsHaveLength_of_coinsFit
#print axioms VerifiableInference.Compilation.committerWithin_of_withinBudget
#print axioms VerifiableInference.Compilation.BindingOf.extractsWithinBudget
#print axioms VerifiableInference.Compilation.bindsWith_writtenAtLength
#print axioms VerifiableInference.Compilation.commit_value
#print axioms VerifiableInference.Compilation.finalBinds
#print axioms VerifiableInference.Compilation.finalExtracts
#print axioms VerifiableInference.Compilation.finalBinds_bits
#print axioms VerifiableInference.Compilation.finalBoth
#print axioms VerifiableInference.Compilation.finalBindingGoal
#print axioms VerifiableInference.Compilation.BindingOf.labelled
#print axioms VerifiableInference.Compilation.finalBindingLabelled
#print axioms VerifiableInference.Compilation.length_firstSalts
#print axioms VerifiableInference.Compilation.never_does_not_bind_compile
#print axioms VerifiableInference.Compilation.tableSaltsHaveLength_of_constant
