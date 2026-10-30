-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/FinalRoadProof.lean: the statement of VerifiableInference/Compilation/FinalRoad.lean, proved: from its premises to the final statement's lines on completeness and zero knowledge.

1.  compile at flashProveAtFiles is flashSlotF; what holds at flashSlot carries to it, since committer and
    prover keep their law at every hash function.
2.  Each of the two reaches every request: FinalCompleteAtEveryRequest and FinalZeroKnowledgeOneBit, as
    stated; Checks.lean carries them to the final statement's two lines. That a refused request gets no proof is no premise: at each set of files in use
    it follows from the premises' own fields, and zeroKnowledgeFollowsFromOn does the rest.
3.  Joined: Spec.final_of_the_two, and the same from exactly the fields that each of the two proofs uses.
4.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the protocol.
    With soundness these are three of FinalStatement's six lines. The premises allow at most 710,324 copies.
-/
import Johnson.CompletenessAndZeroKnowledge.RoadComplete
import Johnson.CompletenessAndZeroKnowledge.RoadRefusal
import VerifiableInference.Final.CompilerAtVerifyProofs
import VerifiableInference.AtEveryRequestFollows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover VerifiableInference.OnPublicFiles
open IntegerTransformer (Settings)

/-- **compile at flashProveAtFiles is flashSlotF.** -/
theorem compile_flashProve_eq (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings) :
    compile (flashProveAtFiles files settings honest) = flashSlotF files settings honest :=
  compile_eq_slotSystemF flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq honest.fallbackInstance
    honest.provers honest.compiledSettings (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files)

/-- servedResult says a request's output exactly where it can be served and is the model's. -/
theorem servedResult_agree {s : Settings} (valid : settingsAreValid s = true) (w : ModelWeights s)
    (p o : List Token) :
    (True ∧ AtEveryRequest.servedResult s w (p, o) = some o) ↔
      (CanServe s w p o ∧ ∀ position (inOutput : position < o.length),
        modelNextToken s w (p ++ o.take position) = some o[position]) := by
  constructor
  · rintro ⟨-, h⟩
    have label : AtEveryRequest.requestLabel s w (p, o) = .served := by
      by_contra hn
      unfold AtEveryRequest.servedResult at h
      rw [if_neg hn] at h
      cases h
    exact (AtEveryRequest.served_iff_canServe valid w (p, o)).1
      ((AtEveryRequest.requestLabel_eq_served_iff s w (p, o)).1 label)
  · intro h
    refine ⟨trivial, ?_⟩
    unfold AtEveryRequest.servedResult
    exact if_pos ((AtEveryRequest.requestLabel_eq_served_iff s w (p, o)).2
      ((AtEveryRequest.served_iff_canServe valid w (p, o)).2 h))

/-- **Completeness at every request**, from the fields that its proof uses. -/
theorem finalCompleteAtEveryRequest_of_spent (honest : HonestProversAndSettings)
    (road : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
      ∃ (l : RoadLetters files) (α γ : ℝ≥0∞),
        RoadCompletePremises files (settingsOfRead parameters)
          (honest files (settingsOfRead parameters)) l α γ) :
    FinalCompleteAtEveryRequest honest := by
  intro files parameters inUse
  obtain ⟨l, α, γ, hRoad⟩ := road files parameters inUse
  have h := completeOn_slotSystemF (familyLaws_the files).noCoin
    (flash_firstBlockFits files (honestPartSide files (settingsOfRead parameters)
      (honest files (settingsOfRead parameters))))
    (road_complete_atSlot files (settingsOfRead parameters)
      (honest files (settingsOfRead parameters)) l α γ inUse.inScope hRoad)
  have onCanServe : CompleteOn (finalSystem honest files (settingsOfRead parameters))
      (CanServe (settingsOfRead parameters)) finalCompletenessError :=
    fun w p o hd hm => le_trans
      (completeOn_of_eq (compile_flashProve_eq files (settingsOfRead parameters)
        (honest files (settingsOfRead parameters))) rfl rfl
        (CanServe (settingsOfRead parameters)) _ h w p o hd hm) hRoad.errorsBelow
  exact (AtEveryRequest.proofAcceptedWhere_iff_completeOn
    (finalSystem honest files (settingsOfRead parameters)) (fun _ => True)
    (AtEveryRequest.servedResult (settingsOfRead parameters)) (CanServe (settingsOfRead parameters))
    (fun w p o => servedResult_agree (valid_of_read inUse.read) w p o) _).2 onCanServe

/-- Handing out no proof passes along an equation between argument systems. -/
theorem handsOutNoProof_of_eq {W P : Type} {A B : ArgumentSystem} (e : A = B) (hA : A.Weights = W)
    (hB : B.Weights = W) (pA : A.Proof = P) (pB : B.Proof = P)
    (unserved : W → AtEveryRequest.Request → Prop) (isNoProof : P → Prop)
    (h : AtEveryRequest.HandsOutNoProof B (fun w => unserved (cast hB w))
      (fun π => isNoProof (cast pB π))) :
    AtEveryRequest.HandsOutNoProof A (fun w => unserved (cast hA w))
      (fun π => isNoProof (cast pA π)) := by
  subst e
  exact h

section AtADescription

variable (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.C Z).I) (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (pair : Digest → D.More → T.D) (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X)
  (provers : HonestProvers ((D.F Z).withProvers (D.P Z)))
  (settings : (reading : T.D) →
    CompiledSettings ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers)
  (firstBlockTest : (reading : T.D) → Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256
    (D.input Z c₀ m₀).queryLayout.K (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier (D.input Z c₀ m₀).protocol
                (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

set_option quotPrecheck false

local notation "𝕀" =>
  atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
local notation "ℍ" =>
  fun reading => AtRecs.side (honestSide
    ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers (settings reading))

/-- From slotSystemF to compile, at a description. -/
theorem handsOut_atCompile (outcome : ModelWeights s → AtEveryRequest.Request → AtEveryRequest.Outcome)
    (noProof : Form)
    (h : AtEveryRequest.HandsOutNoProof
      (slotSystemF D Z c₀ m₀ T ℍ firstBlockTest s idx x₀ Form parse write coinBound)
      (fun weights request => outcome weights request = .refused) (· = noProof)) :
    AtEveryRequest.HandsOutNoProof (compile 𝕀)
      (fun weights request => outcome weights request = .refused) (· = noProof) :=
  handsOutNoProof_of_eq
    (compile_eq_slotSystemF D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound
      Form parse write) rfl rfl rfl rfl (fun weights request => outcome weights request = .refused)
    (· = noProof) h

end AtADescription

/-- Zero knowledge on a domain gives it on any smaller one, as far as model outputs go. -/
theorem zeroKnowledgeOn_of_domain {system : ArgumentSystem}
    {domain domain' : system.Weights → List Token → List Token → Prop} {ζ : ℕ → ℕ → ℝ≥0∞}
    (smaller : ∀ w p o, domain' w p o → system.IsModelOutput w p o → domain w p o)
    (h : ZeroKnowledgeOn system domain ζ) : ZeroKnowledgeOn system domain' ζ :=
  let ⟨simulator, hs⟩ := h
  ⟨simulator, fun weights chooser hc => hs weights chooser fun view p o e =>
    ⟨smaller _ _ _ (hc view p o e).1 (hc view p o e).2, (hc view p o e).2⟩⟩

/-- **At a refused request the final system's prover hands out no proof**, at public files in use. -/
theorem final_handsOut (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (zeroKnowledgeError : ℝ≥0∞) (l : RoadLetters files)
    (road : RoadZeroKnowledgePremises files (settingsOfRead parameters)
      (honest files (settingsOfRead parameters)) zeroKnowledgeError l) :
    AtEveryRequest.HandsOutNoProof (finalSystem honest files (settingsOfRead parameters))
      (fun weights request =>
        AtEveryRequest.requestOutcome (settingsOfRead parameters) weights request = .refused)
      (· = noProofForm) :=
  handsOut_atCompile flashProveDescription files (settingsOfRead parameters) (backThe files (settingsOfRead parameters))
    allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq
    (honest files (settingsOfRead parameters)).fallbackInstance
    (honest files (settingsOfRead parameters)).provers
    (honest files (settingsOfRead parameters)).compiledSettings (flashFirstBlockTest files)
    (honest files (settingsOfRead parameters)).coinBound flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files)
    (AtEveryRequest.requestOutcome (settingsOfRead parameters)) noProofForm
    (road_handsOut_atSlot files (settingsOfRead parameters)
      (honest files (settingsOfRead parameters)) l.Served road.refusesUnserved
      road.refusedIsUnserved)

/-- **Zero knowledge, the simulator told one bit**, from the fields that its proof uses. -/
theorem finalZeroKnowledgeOneBit_of_spent (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (road : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
      ∃ l : RoadLetters files,
        RoadZeroKnowledgePremises files (settingsOfRead parameters)
          (honest files (settingsOfRead parameters)) zeroKnowledgeError l) :
    FinalZeroKnowledgeOneBit honest zeroKnowledgeError := by
  intro files parameters inUse
  obtain ⟨l, hRoad⟩ := road files parameters inUse
  obtain ⟨weights, -, -⟩ := someRequestIsServedInUse files parameters inUse
  refine ⟨fun t n => roadError (honest files (settingsOfRead parameters)) l (t + 1) n, ?_, ?_⟩
  · exact fun asked replies ha hr =>
      iSup_le fun reading => hRoad.hidingBelow reading asked replies ha hr
  · have onCanServe : ZeroKnowledgeOn (finalSystem honest files (settingsOfRead parameters))
        (CanServe (settingsOfRead parameters))
        (fun t n => roadError (honest files (settingsOfRead parameters)) l (t + 1) n) :=
      zeroKnowledgeOn_of_eq (compile_flashProve_eq files (settingsOfRead parameters)
          (honest files (settingsOfRead parameters))) rfl rfl
        (CanServe (settingsOfRead parameters)) _
        (zeroKnowledgeOn_slotSystemF (familyLaws_the files).noCoin
          (flash_firstBlockFits files (honestPartSide files (settingsOfRead parameters)
            (honest files (settingsOfRead parameters))))
          (road_zeroKnowledge_atSlot files (settingsOfRead parameters)
            (honest files (settingsOfRead parameters)) zeroKnowledgeError l inUse.inScope
            (backThe files (settingsOfRead parameters) weights) hRoad))
    exact AtEveryRequest.zeroKnowledgeFollowsFromOn _ _ noProofForm
      (finalServedIsModelOutput honest files parameters inUse.toFilesTaken)
      (final_handsOut honest files parameters zeroKnowledgeError l hRoad) _
      (zeroKnowledgeOn_of_domain (fun w p o served _ =>
        ((AtEveryRequest.served_iff_canServe (valid_of_read inUse.read) w (p, o)).1 served).1)
        onCanServe)

/-- **The statement of FinalRoad.lean, proved.** -/
theorem final_of_the_two_holds : Spec.final_of_the_two :=
  fun honest zeroKnowledgeError road =>
    ⟨finalCompleteAtEveryRequest_of_spent honest fun files parameters inUse =>
        (road files parameters inUse).imp fun _ h => ⟨_, _, h.toComplete⟩,
      finalZeroKnowledgeOneBit_of_spent honest zeroKnowledgeError fun files parameters inUse =>
        (road files parameters inUse).imp fun _ h => h.toZeroKnowledge⟩

/-- The same statement from the fields that each proof uses, on one set of parameters. -/
def Spec.final_of_the_two_upTo : Prop :=
  ∀ (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞),
    (∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
      ∃ (l : RoadLetters files) (α γ : ℝ≥0∞),
        RoadZeroKnowledgePremises files (settingsOfRead parameters)
            (honest files (settingsOfRead parameters)) zeroKnowledgeError l ∧
          RoadCompletePremises files (settingsOfRead parameters)
            (honest files (settingsOfRead parameters)) l α γ) →
    FinalCompleteAtEveryRequest honest ∧ FinalZeroKnowledgeOneBit honest zeroKnowledgeError

/-- **That statement, proved.** -/
theorem final_of_the_two_upTo_holds : Spec.final_of_the_two_upTo :=
  fun honest zeroKnowledgeError road =>
    ⟨finalCompleteAtEveryRequest_of_spent honest fun files parameters inUse =>
        (road files parameters inUse).imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.2,
      finalZeroKnowledgeOneBit_of_spent honest zeroKnowledgeError fun files parameters inUse =>
        (road files parameters inUse).imp fun _ ⟨_, _, h⟩ => h.1⟩

/-- **The two forms at every request give the final statement's two lines.** -/
theorem final_lines_of_beneath (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (beneath : FinalCompleteAtEveryRequest honest ∧ FinalZeroKnowledgeOneBit honest zeroKnowledgeError) :
    FinalComplete honest ∧ FinalZeroKnowledge honest zeroKnowledgeError :=
  ⟨finalComplete_of_atEveryRequest honest beneath.1,
    finalZeroKnowledge_of_atEveryRequest honest zeroKnowledgeError
      (finalZeroKnowledgeAtEveryRequest_of_oneBit honest zeroKnowledgeError beneath.2)⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.compile_flashProve_eq
#print axioms VerifiableInference.Compilation.handsOutNoProof_of_eq
#print axioms VerifiableInference.Compilation.zeroKnowledgeOn_of_domain
#print axioms VerifiableInference.Compilation.final_handsOut
#print axioms VerifiableInference.Compilation.servedResult_agree
#print axioms VerifiableInference.Compilation.finalCompleteAtEveryRequest_of_spent
#print axioms VerifiableInference.Compilation.finalZeroKnowledgeOneBit_of_spent
#print axioms VerifiableInference.Compilation.final_lines_of_beneath
#print axioms VerifiableInference.Compilation.final_of_the_two_holds
#print axioms VerifiableInference.Compilation.final_of_the_two_upTo_holds
