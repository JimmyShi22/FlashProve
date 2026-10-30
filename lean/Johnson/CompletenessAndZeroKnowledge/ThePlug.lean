-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ThePlug.lean: ALL THAT HOLDS BY THEOREM, LAID IN, SO THAT WHAT STAYS A PREMISE SHOWS.

1.  thePlug: the honest part at every set of public files and settings, out of one letter, the three
    provers at each set of files, made to refuse what is not served. Where the files read as
    parameters the provers read them too; where they do not, nothing is claimed, and the part is idle.
2.  final_at_the_plug: from what PlugLeft lists, the two honest lines of the final statement.
3.  Shown inside, no premise: what is public; the settings' lengths, paths, range, copies and sessions;
    the budget of hash queries; the model's tie; that a refused request is not served; that the provers refuse; the guards.
4.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the
    protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.FinalRoadProof
import Johnson.CompletenessAndZeroKnowledge.TheSettingsFit
import Johnson.CompletenessAndZeroKnowledge.FormatStarts
import Johnson.Face.NeverBuilt
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestTies
import VerifiableInference.Final.ModelTieAtFiles
import VerifiableInference.Final.TheSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles
open VerifiableInference.AtEveryRequest (WithinBudget)
open IntegerTransformer (Settings)

variable {Index Instance : Type} {protocol : _root_.Iop.HolographicProtocol Index Instance}
  {provers : HonestProvers protocol}

/-- The starts read the provers' coins alone, so they stand under refusal. -/
def SaltStarts.underRefusal (starts : SaltStarts provers) (Served : Index → Instance → Prop) :
    SaltStarts (provers.refuseUnserved Served) where
  RunValues := starts.RunValues
  wellFormed := starts.wellFormed
  runValuesOffline := starts.runValuesOffline
  runValuesLink := starts.runValuesLink
  runValuesOnline := starts.runValuesOnline
  readOffline := starts.readOffline
  readLink := starts.readLink
  readOnline := starts.readOnline
  saltStartOffline := starts.saltStartOffline
  saltStartLink := starts.saltStartLink
  saltStartOnline := starts.saltStartOnline

/-- Their lengths stand too. -/
theorem SaltStarts.LengthsFit.underRefusal {starts : SaltStarts provers} {n m : ℕ}
    (h : starts.LengthsFit n m) (Served : Index → Instance → Prop) :
    (starts.underRefusal Served).LengthsFit n m :=
  ⟨h.valuesOffline, h.valuesLink, h.valuesOnline, h.startsOffline, h.startsLink, h.startsOnline⟩

/-! ## 1 From the road's fields at theHonestPartOf -/

section AtTheHonestPart
variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
  (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout)

local notation "𝕙" =>
  theHonestPartOf files settings fallbackInstance provers starts limits slotSalts

/-- **What theHonestPartOf gives of the two halves.** -/
theorem theHonestPart_road (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (h : starts.LengthsFit 256 256)
    (slots : ∀ reading, slotSalts.Fit (flashLayout files settings fallbackInstance reading))
    (zeroKnowledgeError : ℝ≥0∞) (l : RoadLetters files)
    (zeroKnowledge : ∀ reading, HonestVerifierZeroKnowledge
      (flashLayout files settings fallbackInstance reading).work provers l.simulators l.inRange
      l.Served l.budget)
    (runValues : ∀ reading, RunValuesAreSent (flashLayout files settings fallbackInstance reading)
      provers (theSettings files settings fallbackInstance provers starts limits slotSalts reading)
      l.inRange)
    (range : ∀ weights, l.inRange (backThe files settings weights))
    (tie : TieOn flashProveDescription files allZeroDigest [] settings (backThe files settings) l.back (CanServe settings)
      l.Served)
    (refusesUnserved : provers.RefusesUnserved l.Served)
    (refusedIsUnserved : ∀ weights request,
      VerifiableInference.AtEveryRequest.requestOutcome settings weights request = .refused →
      ¬ l.Served (backThe files settings weights)
        (instOf (flashProveDescription.input files allZeroDigest []) fallbackInstance request))
    (hidingBelow : ∀ reading asked replies, asked ≤ finalVerifierQueries →
      replies ≤ finalReplyCount →
      indexPrivacyError (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers starts limits slotSalts reading)
        l.budget 688127 (asked + 1) replies ≤ zeroKnowledgeError) :
    RoadZeroKnowledgePremises files settings 𝕙 zeroKnowledgeError l where
  zeroKnowledge := zeroKnowledge
  runValues := runValues
  coins := fun reading => (theSettings_fit files settings fallbackInstance provers limits slotSalts
    scope live starts h reading (slots reading)).coins
  copies := fun _ => show 0 + 1 ≤ 710324 by norm_num
  sessions := le_refl _
  coinRange := coinsRange_dvd_theCoinBound files settings fallbackInstance provers starts limits
    slotSalts
  range := range
  tie := tie
  refusesUnserved := refusesUnserved
  refusedIsUnserved := refusedIsUnserved
  hidingBelow := hidingBelow

/-- **What theHonestPartOf gives of the completeness half.** -/
theorem theHonestPart_complete (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (h : starts.LengthsFit 256 256)
    (slots : ∀ reading, slotSalts.Fit (flashLayout files settings fallbackInstance reading))
    (l : RoadLetters files) (γ : ℝ≥0∞)
    (complete : ∀ reading, CompleteBeforeHashingAt
      (flashLayout files settings fallbackInstance reading) provers l.Served l.errors)
    (parserUpTo : UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (honestPartSide files settings 𝕙) (backThe files settings) l.Served (flashProveDescription.parse files)
      (bytesWriter files) γ)
    (tie : TieOn flashProveDescription files allZeroDigest [] settings (backThe files settings) l.back (CanServe settings)
      l.Served)
    (below : ∀ reading, completenessError (flashLayout files settings fallbackInstance reading)
      provers (theSettings files settings fallbackInstance provers starts limits slotSalts reading)
      l.errors + γ ≤ finalCompletenessError) :
    RoadCompletePremises files settings 𝕙 l
      (⨆ reading, completenessError (flashLayout files settings fallbackInstance reading)
        provers (theSettings files settings fallbackInstance provers starts limits slotSalts reading)
        l.errors) γ :=
  haveI : Nonempty (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D := ⟨Prod.mk allZeroDigest []⟩
  { complete := complete
    parserUpTo := parserUpTo
    lengths := fun reading => (theSettings_fit files settings fallbackInstance provers limits
      slotSalts scope live starts h reading (slots reading)).lengths
    coinRange := coinsRange_dvd_theCoinBound files settings fallbackInstance provers starts limits
      slotSalts
    tie := fun w p o hd hm => (tie w p o hd hm).imp fun _ z => ⟨z.1, z.2.1⟩
    errorAtReading := fun reading => le_iSup (fun reading => completenessError
      (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts reading) l.errors) reading
    errorsBelow := by
      rw [ENNReal.iSup_add]
      exact iSup_le below }

end AtTheHonestPart

/-! ## 2 The letters and the part -/

/-- **The letters that stay**: the provers at each set of files, before they refuse; the starts; what
stands behind a slot's value. The search limits are writtenLimits. -/
structure PlugLetters where
  provers : (files : PublicFiles) → HonestProvers (protocolAtFiles files)
  starts : (files : PublicFiles) → SaltStarts (provers files)
  slotSalts : PublicFiles → RequestLeafSaltLayout

/-- The lengths that the letters owe. -/
structure PlugLetters.Fits (P : PlugLetters) : Prop where
  lengths : ∀ files, (P.starts files).LengthsFit 256 256
  slots : ∀ files (settings : Settings) (x₀ : (flashProveDescription.C files).X) (reading : FlashReading files),
    (P.slotSalts files).Fit (flashLayout files settings x₀ reading)

/-- **A TEST VALUE**: plain starts, no slot salts. -/
def plainLetters (provers : (files : PublicFiles) → HonestProvers (protocolAtFiles files)) : PlugLetters :=
  ⟨provers, fun files => zeroSaltStarts (provers files), fun _ => plainSlotSalts⟩

/-- Plain letters owe nothing. -/
theorem plainLetters_fits (provers : (files : PublicFiles) → HonestProvers (protocolAtFiles files)) :
    (plainLetters provers).Fits :=
  ⟨fun files => plainStarts_lengthsFit (provers files) 256,
    fun _ _ _ _ => plainSlotSalts_fit _⟩

/-- **THE FORMAT'S VALUE**, with the provers' run values as letters. -/
def formatLetters (provers : (files : PublicFiles) → HonestProvers (protocolAtFiles files)) (rounds : PublicFiles → FormatRounds)
    (runsOffline : (files : PublicFiles) → (provers files).offlineProver.Coin → FormatRuns)
    (runsOnline : (files : PublicFiles) → (provers files).onlineProver.Coin → FormatRuns)
    (linkRuns : PublicFiles → FormatRuns)
    (readOffline : (files : PublicFiles) → _root_.Iop.Plains (FlashProtocol files).offline.shape → FormatRuns)
    (readOnline : (files : PublicFiles) → _root_.Iop.Plains (FlashProtocol files).onlineBatch.loc.shape → FormatRuns)
    (saltBytes : PublicFiles → ℕ) : PlugLetters :=
  ⟨provers, fun files => formatStarts (provers files) (rounds files)
      (runsOffline files) (runsOnline files) (linkRuns files) (readOffline files) (readOnline files),
    fun files => formatRequestLeafSaltLayout (saltBytes files) (flashProveDescription.input files allZeroDigest []).queryLayout.depthReq⟩

/-- The format's letters owe the sizes of the run values, and nothing else. -/
theorem formatLetters_fits (provers : (files : PublicFiles) → HonestProvers (protocolAtFiles files)) (rounds : PublicFiles → FormatRounds)
    (runsOffline : (files : PublicFiles) → (provers files).offlineProver.Coin → FormatRuns)
    (runsOnline : (files : PublicFiles) → (provers files).onlineProver.Coin → FormatRuns)
    (linkRuns : PublicFiles → FormatRuns)
    (readOffline : (files : PublicFiles) → _root_.Iop.Plains (FlashProtocol files).offline.shape → FormatRuns)
    (readOnline : (files : PublicFiles) → _root_.Iop.Plains (FlashProtocol files).onlineBatch.loc.shape → FormatRuns)
    (saltBytes : PublicFiles → ℕ)
    (sizeOffline : ∀ files κ, (runsOffline files κ).1.size = 32 ∧ (runsOffline files κ).2.size = 32)
    (sizeOnline : ∀ files κ, (runsOnline files κ).1.size = 32 ∧ (runsOnline files κ).2.size = 32)
    (sizeLink : ∀ files, (linkRuns files).1.size = 32 ∧ (linkRuns files).2.size = 32) :
    (formatLetters provers rounds runsOffline runsOnline linkRuns readOffline readOnline
      saltBytes).Fits :=
  ⟨fun files => formatStarts_lengthsFit (sizeOffline files) (sizeOnline files) (sizeLink files),
    fun files settings x₀ reading => formatSlotSalts_fit (flashLayout files settings x₀ reading)
      (saltBytes files)⟩

/-- The honest part where the files read as parameters. -/
def plugPartAt (P : PlugLetters) (files : PublicFiles) (settings : Settings) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp) : HonestProversAndSettingsAtFiles files settings :=
  theHonestPartOf files settings neverBuiltRequest (proversAtFiles files hr (P.provers files))
    ((P.starts files).underRefusal (ServedRequest committerCoinCountLessOne files hr)) (writtenLimits files)
    (P.slotSalts files)

/-- The honest part where they do not: nothing is claimed there. -/
def plugIdle (P : PlugLetters) (files : PublicFiles) (settings : Settings) :
    HonestProversAndSettingsAtFiles files settings :=
  theHonestPartOf files settings neverBuiltRequest (P.provers files)
    (P.starts files) (writtenLimits files) (P.slotSalts files)

open Classical in
/-- **THE HONEST PART, at every set of public files and settings.** -/
def thePlug (P : PlugLetters) : HonestProversAndSettings := fun files settings =>
  if h : ∃ pp, readFiles files = .ok pp then plugPartAt P files settings h.choose_spec
  else plugIdle P files settings

/-- Where the files read as parameters, the plug is the part at them. -/
theorem thePlug_at (P : PlugLetters) {files : PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp) (settings : Settings) :
    thePlug P files settings = plugPartAt P files settings hr := by
  have h : ∃ pp, readFiles files = .ok pp := ⟨pp, hr⟩
  have same : ∀ (q : Inst.Model.ScalesAndPolicy) (hq : readFiles files = .ok q), q = pp →
      plugPartAt P files settings hq = plugPartAt P files settings hr := by
    rintro q hq rfl
    rfl
  have e : h.choose = pp := by
    have hc := hr.symm.trans h.choose_spec
    injection hc with z
    exact z.symm
  unfold thePlug
  rw [dif_pos h]
  exact same _ _ e

/-! ## 3 What stays a premise, and the final lines -/

section Left
variable (P : PlugLetters) (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)

/-- **WHAT STAYS A PREMISE at one set of files**: see the end of this file. -/
structure PlugLeft (zeroKnowledgeError offlineStops linkStops onlineStops parserError : ℝ≥0∞) :
    Prop where
  complete : CompleteOnServedRequests files hr (P.provers files)
  zeroKnowledge : ZeroKnowledgeOnServedRequests files hr (P.provers files) offlineStops linkStops
    onlineStops
  runValues : ∀ reading, RunValuesAreSent
    (flashLayout files (settingsOfRead pp) neverBuiltRequest reading)
    (proversAtFiles files hr (P.provers files))
    ((plugPartAt P files (settingsOfRead pp) hr).compiledSettings reading) rangeAtFiles
  parserUpTo : UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
    (honestPartSide files (settingsOfRead pp) (plugPartAt P files (settingsOfRead pp) hr))
    (backThe files (settingsOfRead pp)) (Seam.servedAt files hr) (flashProveDescription.parse files)
    (bytesWriter files) parserError
  completenessBelow : ∀ E : CompletenessErrors,
    E.offline + E.link + E.online ≤ completenessTarget → ∀ reading,
      completenessError (flashLayout files (settingsOfRead pp) neverBuiltRequest reading)
        (proversAtFiles files hr (P.provers files))
        ((plugPartAt P files (settingsOfRead pp) hr).compiledSettings reading) E + parserError ≤ finalCompletenessError
  hidingBelow : ∀ reading asked replies, asked ≤ finalVerifierQueries →
    replies ≤ finalReplyCount →
    indexPrivacyError (flashLayout files (settingsOfRead pp) neverBuiltRequest reading)
      (proversAtFiles files hr (P.provers files))
      ((plugPartAt P files (settingsOfRead pp) hr).compiledSettings reading)
      (budgetAtFiles offlineStops linkStops onlineStops) 688127 (asked + 1) replies ≤
      zeroKnowledgeError

/-- The road's letters at one set of files. -/
def plugLetters (simulators : RunSimulators (protocolAt files)) (offlineStops linkStops onlineStops : ℝ≥0∞)
    (errors : CompletenessErrors) (parserError : ℝ≥0∞) : RoadLetters files where
  inRange := rangeAtFiles
  Served := Seam.servedAt files hr
  simulators := simulators
  offlineStops := offlineStops
  linkStops := linkStops
  onlineStops := onlineStops
  errors := errors
  parserError := parserError
  back := backTok committerCoinCountLessOne files

variable (simulators : RunSimulators (protocolAt files)) (offlineStops linkStops onlineStops : ℝ≥0∞)
  (errors : CompletenessErrors) (parserError : ℝ≥0∞)

/-- The model's tie at these letters. -/
theorem plug_tie (scope : InScope files = true) :
    TieOn flashProveDescription files allZeroDigest [] (settingsOfRead pp) (backThe files (settingsOfRead pp))
      (plugLetters files hr simulators offlineStops linkStops onlineStops errors
        parserError).back
      (CanServe (settingsOfRead pp))
      (plugLetters files hr simulators offlineStops linkStops onlineStops errors
        parserError).Served :=
  fun w p o hd hm => Seam.tie_at files hr scope w p o hd hm

/-- The zero-knowledge half at the plug. -/
theorem plug_zeroKnowledge (fits : P.Fits) (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (zeroKnowledgeError : ℝ≥0∞)
    (left : PlugLeft P files hr zeroKnowledgeError offlineStops linkStops onlineStops parserError)
    (hSim : ∀ reading, HonestVerifierZeroKnowledge
      (flashLayout files (settingsOfRead pp) neverBuiltRequest reading).work
      (proversAtFiles files hr (P.provers files)) simulators rangeAtFiles (Seam.servedAt files hr)
      (budgetAtFiles offlineStops linkStops onlineStops)) :
    RoadZeroKnowledgePremises files (settingsOfRead pp) (plugPartAt P files (settingsOfRead pp) hr)
      zeroKnowledgeError
      (plugLetters files hr simulators offlineStops linkStops onlineStops errors
        parserError) :=
  theHonestPart_road files (settingsOfRead pp) neverBuiltRequest
    (proversAtFiles files hr (P.provers files))
    ((P.starts files).underRefusal (ServedRequest committerCoinCountLessOne files hr)) (writtenLimits files)
    (P.slotSalts files) scope live ((fits.lengths files).underRefusal (ServedRequest committerCoinCountLessOne files hr))
    (fits.slots files (settingsOfRead pp) neverBuiltRequest) zeroKnowledgeError
    (plugLetters files hr simulators offlineStops linkStops onlineStops errors parserError)
    hSim left.runValues (fun w => Seam.range_at files (settingsOfRead pp) w)
    (plug_tie files hr simulators offlineStops linkStops onlineStops errors parserError scope)
    (refusesUnserved_refuseUnserved (P.provers files)
      (ServedRequest committerCoinCountLessOne files hr))
    (fun w request href => Seam.refusedIsUnserved_of files hr neverBuiltRequest
      (fun p o => buildReq_ne_neverBuilt (p, o)) w request href) left.hidingBelow

/-- The completeness half at the plug. -/
theorem plug_complete (fits : P.Fits) (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (zeroKnowledgeError : ℝ≥0∞)
    (left : PlugLeft P files hr zeroKnowledgeError offlineStops linkStops onlineStops parserError)
    (hParts : ∀ reading, CompleteBeforeHashingAt
      (flashLayout files (settingsOfRead pp) neverBuiltRequest reading)
      (proversAtFiles files hr (P.provers files)) (Seam.servedAt files hr) errors)
    (hSum : errors.offline + errors.link + errors.online ≤ completenessTarget) :
    ∃ α, RoadCompletePremises files (settingsOfRead pp) (plugPartAt P files (settingsOfRead pp) hr)
      (plugLetters files hr simulators offlineStops linkStops onlineStops errors
        parserError) α parserError :=
  ⟨_, theHonestPart_complete files (settingsOfRead pp) neverBuiltRequest
    (proversAtFiles files hr (P.provers files))
    ((P.starts files).underRefusal (ServedRequest committerCoinCountLessOne files hr)) (writtenLimits files)
    (P.slotSalts files) scope live ((fits.lengths files).underRefusal (ServedRequest committerCoinCountLessOne files hr))
    (fits.slots files (settingsOfRead pp) neverBuiltRequest)
    (plugLetters files hr simulators offlineStops linkStops onlineStops errors parserError)
    parserError hParts left.parserUpTo
    (plug_tie files hr simulators offlineStops linkStops onlineStops errors parserError scope)
    (left.completenessBelow errors hSum)⟩

/-- The layout at a reading has the seam's wiring. -/
theorem flashLayout_eq_wiringAt (settings : Settings) (x₀ : (flashProveDescription.C files).X)
    (reading : FlashReading files) :
    flashLayout files settings x₀ reading = Seam.wiringAt files reading := rfl

/-- The work bits do not move with the reading. -/
theorem flashLayout_work (settings : Settings) (x₀ : (flashProveDescription.C files).X)
    (reading : FlashReading files) :
    (flashLayout files settings x₀ reading).work = ((layoutOf flashProveDescription files allZeroDigest []).toHashLayout).work := by
  rw [flashLayout_eq_wiringAt]
  exact (Seam.work_eq files reading).trans (Seam.work_ofInput_eq files).symm

/-- The seam's premise on completeness is the road's. -/
theorem plug_parts (settings : Settings) (x₀ : (flashProveDescription.C files).X) (Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop)
    (provers : HonestProvers (FlashProtocol files)) (E : CompletenessErrors)
    (h : ∀ reading, CompleteInParts (Seam.inputAt files).protocol provers (Seam.wiringAt files reading).work
      ((Seam.familyAt files).Sd reading).num Served E.offline E.link E.online)
    (reading : FlashReading files) :
    CompleteBeforeHashingAt (flashLayout files settings x₀ reading) provers Served E := by
  rw [flashLayout_eq_wiringAt]
  exact h reading

/-- From what stays a premise at one set of files in use, the road's two halves on one set of letters. -/
theorem plug_road (fits : P.Fits) (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (zeroKnowledgeError : ℝ≥0∞)
    (left : PlugLeft P files hr zeroKnowledgeError offlineStops linkStops onlineStops parserError) :
    ∃ (l : RoadLetters files) (α γ : ℝ≥0∞),
      RoadZeroKnowledgePremises files (settingsOfRead pp)
          (plugPartAt P files (settingsOfRead pp) hr) zeroKnowledgeError l ∧
        RoadCompletePremises files (settingsOfRead pp) (plugPartAt P files (settingsOfRead pp) hr)
          l α γ := by
  obtain ⟨offlineError, linkError, onlineError, hSum, hParts⟩ :=
    Seam.road_complete files hr (P.provers files) left.complete
  obtain ⟨simulators', hSim⟩ :=
    Seam.road_zeroKnowledge files hr (P.provers files) offlineStops linkStops onlineStops
      left.zeroKnowledge
  have hP := plug_parts files (settingsOfRead pp) neverBuiltRequest
    (Seam.servedAt files hr) (proversAtFiles files hr (P.provers files))
    ⟨offlineError, linkError, onlineError⟩ hParts
  have hZ : ∀ reading, HonestVerifierZeroKnowledge
      (flashLayout files (settingsOfRead pp) neverBuiltRequest reading).work
      (proversAtFiles files hr (P.provers files)) simulators' rangeAtFiles (Seam.servedAt files hr)
      (budgetAtFiles offlineStops linkStops onlineStops) := fun reading => by
    rw [flashLayout_work]
    exact hSim
  obtain ⟨α, hC⟩ := plug_complete P files hr simulators' offlineStops linkStops onlineStops
    ⟨offlineError, linkError, onlineError⟩ parserError fits scope live zeroKnowledgeError
    left hP hSum
  exact ⟨_, α, parserError,
    plug_zeroKnowledge P files hr simulators' offlineStops linkStops onlineStops
      ⟨offlineError, linkError, onlineError⟩ parserError fits scope live zeroKnowledgeError
      left hZ, hC⟩

end Left

/-- **THE TWO HONEST LINES AT THE PLUG.** -/
theorem final_at_the_plug (P : PlugLetters) (fits : P.Fits) (zeroKnowledgeError : ℝ≥0∞)
    (left : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops parserError : ℝ≥0∞,
        PlugLeft P files inUse.read zeroKnowledgeError offlineStops linkStops onlineStops
          parserError) :
    FinalCompleteAtEveryRequest (thePlug P) ∧ FinalZeroKnowledgeOneBit (thePlug P) zeroKnowledgeError :=
  final_of_the_two_upTo_holds (thePlug P) zeroKnowledgeError fun files parameters inUse => by
    obtain ⟨a, b, c, γ, hLeft⟩ := left files parameters inUse
    rw [thePlug_at P inUse.read (settingsOfRead parameters)]
    exact plug_road P files inUse.read a b c γ fits inUse.inScope inUse.pass zeroKnowledgeError hLeft

/-- One copy and 688127 sessions fit each table's budget. -/
theorem tableBudgetFits_oneCopy : TableBudgetFits 0 688127 := by
  constructor <;> norm_num [AtPublicFiles.Premises.indexPrivacyNumbers]

/-- **THE REPLIES FIT AT THE PLUG**: the copy bears them, the columns fit, the budget holds. -/
theorem plug_repliesFit (P : PlugLetters) (fits : P.Fits) : RepliesFit (thePlug P) := by
  intro files parameters inUse
  show finalReplyCount ≤ (thePlug P files (settingsOfRead parameters)).onlineRunsPerCopy ∧
    (∀ reading, TableBudgetFits
      ((thePlug P files (settingsOfRead parameters)).compiledSettings reading).furtherCopies
      (thePlug P files (settingsOfRead parameters)).onlineRunsPerCopy) ∧
    WithinBudget (compile (flashProveAtFiles files (settingsOfRead parameters)
      (thePlug P files (settingsOfRead parameters)))) honestQueryBudget
  rw [thePlug_at P inUse.read (settingsOfRead parameters)]
  exact ⟨le_refl _, fun _ => tableBudgetFits_oneCopy,
    compile_withinBudget files (settingsOfRead parameters) neverBuiltRequest
      (proversAtFiles files inUse.read (P.provers files))
      ((P.starts files).underRefusal (ServedRequest committerCoinCountLessOne files inUse.read)) (P.slotSalts files)
      inUse.inScope inUse.pass
      ((fits.lengths files).underRefusal (ServedRequest committerCoinCountLessOne files inUse.read))
      (fits.slots files (settingsOfRead parameters) neverBuiltRequest)⟩

/-- **THE TWO HONEST LINES AT THE PLUG**, with the replies fitting. -/
theorem final_lines_at_the_plug (P : PlugLetters) (fits : P.Fits) (zeroKnowledgeError : ℝ≥0∞)
    (left : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops parserError : ℝ≥0∞,
        PlugLeft P files inUse.read zeroKnowledgeError offlineStops linkStops onlineStops
          parserError) :
    (FinalComplete (thePlug P) ∧ FinalZeroKnowledge (thePlug P) zeroKnowledgeError) ∧
      RepliesFit (thePlug P) :=
  ⟨final_lines_of_beneath _ _ (final_at_the_plug P fits zeroKnowledgeError left),
    plug_repliesFit P fits⟩

/-
WHAT STAYS A PREMISE. The fields of PlugLeft, each with what it says. None is proved here.
  complete            the honest provers (E2E/TheHonestProver.lean) are complete as an interactive oracle proof on the served requests.
  zeroKnowledge       the honest provers are honest-verifier zero knowledge as an interactive oracle proof.
  runValues           the run values stand in the plain parts: SendsItsRunValues, at the honest provers
                      (runValuesAreSent_formatStarts); by definition at plain starts.
  parserUpTo          the parser undoes the writer up to an error: the bridge from the byte format's
                      UndoOnBut (Johnson/CompletenessAndZeroKnowledge/UndoUpToOfBut.lean).
  completenessBelow   the written error and the parser's, below 2 ^ -40: the numbers.
  hidingBelow         the written error at the named verifier queries and replies: the numbers, with the
                      three measures of the stops in that zero-knowledge statement.
BESIDE THEM, on the letters: PlugLetters.Fits: nothing at plainLetters; the sizes of the run values at
formatLetters.
-/

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.plainLetters_fits
#print axioms VerifiableInference.Compilation.formatLetters_fits
#print axioms VerifiableInference.Compilation.SaltStarts.underRefusal
#print axioms VerifiableInference.Compilation.theHonestPart_road
#print axioms VerifiableInference.Compilation.theHonestPart_complete
#print axioms VerifiableInference.Compilation.thePlug
#print axioms VerifiableInference.Compilation.thePlug_at
#print axioms VerifiableInference.Compilation.plug_tie
#print axioms VerifiableInference.Compilation.plug_zeroKnowledge
#print axioms VerifiableInference.Compilation.plug_complete
#print axioms VerifiableInference.Compilation.plug_road
#print axioms VerifiableInference.Compilation.final_at_the_plug
#print axioms VerifiableInference.Compilation.tableBudgetFits_oneCopy
#print axioms VerifiableInference.Compilation.plug_repliesFit
#print axioms VerifiableInference.Compilation.final_lines_at_the_plug
