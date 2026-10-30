-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean: the road at the honest provers (E2E/TheHonestProver.lean).

1.  honestProversAndSettingsOf: honestProversAndSettingsAtFiles (Johnson/Face/HonestProversWithCompiledPart.lean) at the honest provers, with theSettings at the format's starts and slots.
    The starts are carried from the provers' arm to their term (AtFullSide/CompletenessAndZeroKnowledge/PlugAtTerm.lean: saltStartsAtHonestProvers).
2.  termHonest_eq: at files that read, honestProversAndSettingsOf is the plug's part: the refusal at ServedAt is the refusal at ServedRequest, by servedAt_eq.
3.  plugLeft_term: the fields of PlugLeft there, from completeness and honest-verifier zero knowledge as interactive oracle proofs and one inequality.
4.  served_at_T1: of the system compile (flashProveAtFiles …) at honestProversAndSettingsOf: completeness and zero knowledge on the requests that can be served.
    final_at_T1: of that same system: the two lines at every request, the simulator told the outcome.
5.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the protocol. This file shows TermLeft at no value of
    parts; and these are two or three of FinalStatement's six fields, at one copy, with the error and parts as parameters.
-/
import AtFullSide.CompletenessAndZeroKnowledge.PrintsAtTerm
import Johnson.CompletenessAndZeroKnowledge.NumbersAtTerm
import Johnson.CompletenessAndZeroKnowledge.ServedByCompile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest (WithinBudget)
open Johnson.Face
open IntegerTransformer (Settings)

theorem chain_le {a e t c γ f : ℝ≥0∞} (h1 : a ≤ c + e) (h2 : e ≤ t) (h3 : c + t + γ ≤ f) : a + γ ≤ f :=
  le_trans (add_le_add (le_trans h1 (add_le_add le_rfl h2)) le_rfl) h3

theorem hide_le {a s x y r R c z : ℝ≥0∞} (h1 : a ≤ s + (x + y + r * c)) (h2 : r ≤ R)
    (h3 : s + (x + y + R * c) ≤ z) : a ≤ z :=
  le_trans h1 (le_trans (add_le_add le_rfl (add_le_add le_rfl (mul_le_mul' h2 le_rfl))) h3)

theorem numbers_at_target :
    71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + completenessTarget + sixTimes ≤ finalCompletenessError :=
  numbers_hold

variable (parts : (files : PublicFiles) → Parts files)

/-- What compilation adds at the honest provers. -/
def compiledPartAtHonestProvers (files : PublicFiles) (settings : Settings) : CompiledPart files settings (parts files) where
  compiledSettings := theSettings files settings neverBuiltRequest (theProvers files settings (parts files))
    ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files settings)) (writtenLimits files)
    (flashProveRequestLeafSaltLayout files 40)
  coinBound := theCoinBound files settings neverBuiltRequest (theProvers files settings (parts files))
    ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files settings)) (writtenLimits files)
    (flashProveRequestLeafSaltLayout files 40)
  onlineRunsPerCopy := 688127

/-- **THE HONEST PART**: honestProversAndSettingsAtFiles at the honest provers. -/
def honestProversAndSettingsOf : HonestProversAndSettings := fun files settings =>
  honestProversAndSettingsAtFiles files settings (parts files) (compiledPartAtHonestProvers parts files settings)

/-- At files that read, it is the plug's part. -/
theorem termHonest_eq (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    honestProversAndSettingsOf parts files (settingsOfRead pp) = plugPartAt (termLetters parts) files (settingsOfRead pp) hr := by
  have key : ∀ R : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop, R = Seam.servedAt files hr →
      theHonestPartOf files (settingsOfRead pp) neverBuiltRequest
        ((HonestProvers.ofThreeProvers (honestProvers files (parts files))).refuseUnserved R)
        ((saltStartsAtHonestProvers files (parts files)).underRefusal R) (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) =
      plugPartAt (termLetters parts) files (settingsOfRead pp) hr := by
    rintro _ rfl
    rfl
  exact key _ (Seam.servedAt_eq files hr)

section Left
variable (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)

/-- **The fields of PlugLeft at the honest provers.** -/
theorem plugLeft_term (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (hComplete : CompleteOnServedRequests files hr ((termLetters parts).provers files))
    (hZero : ZeroKnowledgeOnServedRequests files hr ((termLetters parts).provers files) offlineStops linkStops onlineStops)
    (hStops : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤ zeroKnowledgeError) :
    PlugLeft (termLetters parts) files hr zeroKnowledgeError offlineStops linkStops onlineStops sixTimes where
  complete := hComplete
  zeroKnowledge := hZero
  runValues := term_runValues parts files hr scope live
  parserUpTo := term_parserUpTo parts files hr scope live (termPrints parts files hr)
  completenessBelow := fun E hE reading =>
    chain_le (completenessError_theSettings files (settingsOfRead pp) neverBuiltRequest _ _ _ scope live E reading) hE
      numbers_at_target
  hidingBelow := fun reading asked replies ha hrp =>
    hide_le (indexPrivacyError_theSettings files (settingsOfRead pp) neverBuiltRequest _ _ _ scope live
      (budgetAtFiles offlineStops linkStops onlineStops) 688127 (asked + 1) replies reading (Nat.succ_le_succ ha) hrp hrp)
      (by exact_mod_cast hrp) hStops

end Left

/-- What stays a premise at the honest provers, at one set of files in use. -/
structure TermLeft (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    (zeroKnowledgeError : ℝ≥0∞) : Prop where
  stops : ∃ offlineStops linkStops onlineStops : ℝ≥0∞,
    CompleteOnServedRequests files inUse.read ((termLetters parts).provers files) ∧
    ZeroKnowledgeOnServedRequests files inUse.read ((termLetters parts).provers files) offlineStops linkStops onlineStops ∧
    (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤ zeroKnowledgeError

/-- **THE ROAD's PREMISES, FIELD BY FIELD, AT THE PLUG**, from what PlugLeft lists. -/
theorem plug_roadPremises (P : PlugLetters) (fits : P.Fits) (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp) (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {zeroKnowledgeError offlineStops linkStops onlineStops parserError : ℝ≥0∞}
    (left : PlugLeft P files hr zeroKnowledgeError offlineStops linkStops onlineStops parserError) :
    ∃ l : RoadLetters files, RoadPremises files (settingsOfRead pp) (plugPartAt P files (settingsOfRead pp) hr)
      zeroKnowledgeError l ∧ ∀ i x, l.Served i x → l.inRange i := by
  obtain ⟨offlineError, linkError, onlineError, hSum, hParts⟩ :=
    Seam.road_complete files hr (P.provers files) left.complete
  obtain ⟨simulators, hSim⟩ :=
    Seam.road_zeroKnowledge files hr (P.provers files) offlineStops linkStops onlineStops left.zeroKnowledge
  have hP := plug_parts files (settingsOfRead pp) neverBuiltRequest (Seam.servedAt files hr)
    (proversAtFiles files hr (P.provers files)) ⟨offlineError, linkError, onlineError⟩ hParts
  have hZ : ∀ reading, HonestVerifierZeroKnowledge
      (flashLayout files (settingsOfRead pp) neverBuiltRequest reading).work
      (proversAtFiles files hr (P.provers files)) simulators rangeAtFiles (Seam.servedAt files hr)
      (budgetAtFiles offlineStops linkStops onlineStops) := fun reading => by
    rw [flashLayout_work]
    exact hSim
  have z := plug_zeroKnowledge P files hr simulators offlineStops linkStops onlineStops
    ⟨offlineError, linkError, onlineError⟩ parserError fits scope live zeroKnowledgeError left hZ
  exact ⟨plugLetters files hr simulators offlineStops linkStops onlineStops
      ⟨offlineError, linkError, onlineError⟩ parserError,
    { complete := hP
      zeroKnowledge := z.zeroKnowledge
      refusesUnserved := z.refusesUnserved
      runValues := z.runValues
      parserUpTo := left.parserUpTo
      settingsFit := fun reading => theSettings_fit files (settingsOfRead pp) neverBuiltRequest _ (writtenLimits files)
        (P.slotSalts files) scope live _ ((fits.lengths files).underRefusal (ServedRequest committerCoinCountLessOne files hr)) reading
        (fits.slots files (settingsOfRead pp) neverBuiltRequest reading)
      copies := z.copies
      sessions := z.sessions
      coinRange := z.coinRange
      range := z.range
      tie := z.tie
      refusedIsUnserved := z.refusedIsUnserved
      completenessBelow := left.completenessBelow _ hSum
      hidingBelow := z.hidingBelow }, fun i x h => Seam.served_inRange_gen files hr committerCoinCountLessOne i x h⟩

set_option maxHeartbeats 2000000 in
/-- **THE ROAD's PREMISES, AT THE HONEST PROVERS.** Every field of RoadPremises
(VerifiableInference/Compilation/FinalRoad.lean), at files in use, for every value of parts: thePartsAt is
the value meant. parserUpTo is in RoadPremises's own form: UndoUpTo at six times 2^-256.
This file shows TermLeft at no value of parts. The settings have one copy;
the error and parts are parameters. -/
theorem roadPremises_at_T1 (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) (left : TermLeft parts files parameters inUse zeroKnowledgeError) :
    ∃ l : RoadLetters files, RoadPremises files (settingsOfRead parameters)
      (honestProversAndSettingsOf parts files (settingsOfRead parameters)) zeroKnowledgeError l ∧ ∀ i x, l.Served i x → l.inRange i := by
  obtain ⟨⟨a, b, c, hC, hZ, hS⟩⟩ := left
  rw [termHonest_eq parts files inUse.read]
  exact plug_roadPremises (termLetters parts) (termLetters_fits parts) files inUse.read inUse.inScope inUse.pass
    (plugLeft_term parts files inUse.read inUse.inScope inUse.pass hC hZ hS)

/-- **THE FORMS BENEATH, AT THE HONEST PROVERS**: Spec.final_of_the_two's theorem at
RoadPremises. Of compile (flashProveAtFiles …), for every value of parts. -/
theorem beneath_at_T1 (zeroKnowledgeError : ℝ≥0∞)
    (left : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      TermLeft parts files parameters inUse zeroKnowledgeError) :
    FinalCompleteAtEveryRequest (honestProversAndSettingsOf parts) ∧ FinalZeroKnowledgeOneBit (honestProversAndSettingsOf parts) zeroKnowledgeError :=
  final_of_the_two_holds (honestProversAndSettingsOf parts) zeroKnowledgeError fun files parameters inUse =>
    (roadPremises_at_T1 parts zeroKnowledgeError files parameters inUse (left files parameters inUse)).imp fun _ h => h.1

/-- **THE REPLIES FIT AT THE HONEST PROVERS**, by the plug's. -/
theorem term_repliesFit : RepliesFit (honestProversAndSettingsOf parts) := by
  intro files parameters inUse
  have h := plug_repliesFit (termLetters parts) (termLetters_fits parts) files parameters inUse
  unfold RepliesFitAtFiles at h ⊢
  rw [finalSystem, termHonest_eq parts files inUse.read]
  rw [finalSystem, thePlug_at (termLetters parts) inUse.read (settingsOfRead parameters)] at h
  exact h

/-- **THE TWO HONEST LINES AT THE HONEST PROVERS**, with the replies fitting, for every value of parts:
thePartsAt is the value meant. This file shows TermLeft at no value of parts.
This is three of FinalStatement's six lines, at one copy; the error and parts are parameters. -/
theorem final_at_T1 (zeroKnowledgeError : ℝ≥0∞)
    (left : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      TermLeft parts files parameters inUse zeroKnowledgeError) :
    (FinalComplete (honestProversAndSettingsOf parts) ∧ FinalZeroKnowledge (honestProversAndSettingsOf parts) zeroKnowledgeError) ∧
      RepliesFit (honestProversAndSettingsOf parts) :=
  ⟨final_lines_of_beneath _ _ (beneath_at_T1 parts zeroKnowledgeError left), term_repliesFit parts⟩

/-- The honest side stays within the budget at the honest provers. -/
theorem term_withinBudget (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters) :
    WithinBudget (compile (flashProveAtFiles files (settingsOfRead parameters) (honestProversAndSettingsOf parts files (settingsOfRead parameters))))
      honestQueryBudget :=
  (term_repliesFit parts files parameters inUse).2.2

/-- **ON THE REQUESTS THAT CAN BE SERVED, AT THE HONEST PROVERS**, of compile (flashProveAtFiles …), by completeOfCompile_holds
and zeroKnowledgeOfCompile_holds, for every value of parts. This file shows TermLeft at no
value of parts. This is no whole line of FinalStatement; it is at one copy; the error and parts
are parameters. -/
theorem served_at_T1 (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) (left : TermLeft parts files parameters inUse zeroKnowledgeError) :
    CompleteOn (compile (flashProveAtFiles files (settingsOfRead parameters) (honestProversAndSettingsOf parts files (settingsOfRead parameters))))
        (CanServe (settingsOfRead parameters)) finalCompletenessError ∧
      ∃ error : ℕ → ℕ → ℝ≥0∞, (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
          error asked replies ≤ zeroKnowledgeError) ∧
        ZeroKnowledgeOn (compile (flashProveAtFiles files (settingsOfRead parameters)
          (honestProversAndSettingsOf parts files (settingsOfRead parameters)))) (CanServe (settingsOfRead parameters)) error := by
  obtain ⟨l, road, hIn⟩ := roadPremises_at_T1 parts zeroKnowledgeError files parameters inUse left
  obtain ⟨weights, -, -⟩ := someRequestIsServedInUse files parameters inUse
  have budget := term_withinBudget parts files parameters inUse
  exact ⟨complete_by_compile files (settingsOfRead parameters) _ inUse.inScope road hIn budget,
    zeroKnowledge_by_compile files (settingsOfRead parameters) _ inUse.inScope road hIn budget
      (backThe files (settingsOfRead parameters) weights)⟩

/-
WHAT IS LEFT AS A PREMISE of final_at_T1 and served_at_T1: the three clauses of TermLeft.
  stops, first line   CompleteOnServedRequests at the provers: completeness as an interactive oracle proof.
  stops, second line  ZeroKnowledgeOnServedRequests at the provers: honest-verifier zero knowledge as such.
  stops, third line   the written error at that statement's three numbers: one inequality on their values.
Theorems here or beneath: the run values (sendsItsRunValues_term); the parser (undoOn_at_theSettings, with
zeroRun_mass_arm_refuse: six times 2^-256); the strategies' law (termPrints, by offlineAt_stratLaw and
onlineAt_stratLaw); the completeness number (numbers_hold), the budget (compile_withinBudget), the arm (returnIsTheDescription).
-/

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.termHonest_eq
#print axioms VerifiableInference.Compilation.plugLeft_term
#print axioms VerifiableInference.Compilation.plug_roadPremises
#print axioms VerifiableInference.Compilation.roadPremises_at_T1
#print axioms VerifiableInference.Compilation.beneath_at_T1
#print axioms VerifiableInference.Compilation.term_repliesFit
#print axioms VerifiableInference.Compilation.final_at_T1
#print axioms VerifiableInference.Compilation.served_at_T1
