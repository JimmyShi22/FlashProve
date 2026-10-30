-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/Describe.lean: a description of the ladder made of the told record of
Johnson/PV/ToldMember.lean, at letters that do not read the public files.
`describeFull V`: the value; its further public reading asks the seven strings in order (`askList`);
its T reads (c, m) in four fields alone. `toldAt_describe`: it meets `ToldAt` under `core`,
`meaning`, `carries`. `G7_describe`, `G8_describe`: the goals there.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Ladder
import Johnson.PV.Fit
import Ladder.Ties
import Johnson.PV.ToldMember
import Johnson.Top.Seam.ReaderWith

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  {T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P}

/-- The letters at the public files Z. -/
def atZ (U : ToldLetters T₀) (Z : PublicFiles) : ToldLetters T₀ :=
  { U with pol := Z.pol, KL := Z.KL, lay := Z.lay }

/-- Ask the strings of a list, in order. -/
def askList : List BitString → DeterministicAlgorithm (List Digest)
  | [] => .done []
  | s :: l => .query s fun a => (askList l).andThen fun r => .done (a :: r)

/-- What stays a letter of a description beside T₀: the told record's letters; a map from indices to
weights at every settings; the honest side. -/
structure DescribeLetters
    (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P) where
  U : ToldLetters T₀
  /-- asked at VALID settings alone: at others `ModelWeights s` may be empty, and the record would
  have no member -/
  φ : (s : IntegerTransformer.Settings) → settingsAreValid s = true → A.Mat → ModelWeights s
  Shown : Type
  shown : (s : IntegerTransformer.Settings) → ModelWeights s → Shown
  Rand : Type
  sample : RandomizedAlgorithm Rand
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  Form : Type
  parse : PublicFiles → List Token → List Token → Form → DeterministicAlgorithm
    (TypedProof (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt) P)
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm Form

variable (V : DescribeLetters T₀)

/-- **THE VALUE.** C, F, P do not read Z at these letters; T reads Z through the public reading's
strings alone, and (c, m) in four fields alone. -/
def describeFull : Description where
  C := fun _ => DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)
  F := fun _ => threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt
  P := fun _ => P
  More := List (Dig 256)
  readMore := fun Z c => askList (ssOf (par7 recordGround Z.pol Z.KL Z.lay) c)
  T := fun Z c m =>
    { T₀.letters with
      Sd := (toldOf (atZ V.U Z)).Sd (c, m)
      cA := (toldOf (atZ V.U Z)).cA (c, m)
      m := (toldOf (atZ V.U Z)).m (c, m)
      enc := fun k => encTOf T₀ (c, k) }
  extractor := fun Z s commitment queryLog =>
    if h : settingsAreValid s = true then
      ((toldOf (atZ V.U Z)).extractor commitment queryLog).map (V.φ s h)
    else none
  Shown := V.Shown
  shown := V.shown
  Rand := V.Rand
  sample := V.sample
  commit := V.commit
  Form := V.Form
  parse := V.parse
  prove := V.prove

/-- The pair at which the fit's R is taken: any would do. -/
def c₀ : Digest := fun _ => false

/-- The told record, laid over the description's own input at (c₀, []): field by field:
`LayoutsByPublicReading R` names R, and the description's input is another term than `innerCompilerInputWithFixedLinkAtFullSize T₀`. -/
def toldAtZ (Z : PublicFiles) : LayoutsByPublicReading ((describeFull V).input Z c₀ []) where
  D := (toldOf (atZ V.U Z)).D
  Pub := (toldOf (atZ V.U Z)).Pub
  Pt := (toldOf (atZ V.U Z)).Pt
  part := (toldOf (atZ V.U Z)).part
  Sd := (toldOf (atZ V.U Z)).Sd
  cA := (toldOf (atZ V.U Z)).cA
  m := (toldOf (atZ V.U Z)).m
  encT := (toldOf (atZ V.U Z)).encT
  ISK := (toldOf (atZ V.U Z)).ISK
  commit := (toldOf (atZ V.U Z)).commit
  prove := (toldOf (atZ V.U Z)).prove
  π₀ := (toldOf (atZ V.U Z)).π₀

/-- (1) **fits.** -/
theorem fits_describe (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) (commitment : Commitment)
    (prompt output : List Token)
    (proof : TypedProof ((describeFull V).F Z) ((describeFull V).P Z)) :
    innerCompiledVerifier ((describeFull V).input Z c m) commitment prompt output proof =
      innerCompiledVerifier ((toldAtZ V Z).at (c, m)) commitment prompt output proof := rfl

/-- What `askList` returns: the hash function's values, in order. -/
theorem evaluate_askList (hash : VerifiableInference.Hash) :
    ∀ l : List BitString, (askList l).evaluate hash = l.map hash
  | [] => rfl
  | s :: l => by
      show ((askList l).andThen fun r => .done (hash s :: r)).evaluate hash = hash s :: l.map hash
      rw [DeterministicAlgorithm.evaluate_andThen, evaluate_askList hash l]
      rfl

/-- It asks as often as the list is long. -/
theorem queryBound_askList : ∀ l : List BitString, (askList l).toRandomized.QueryBound l.length
  | [] => trivial
  | s :: l => fun a => by
      have h := queryBound_andThen (askList l)
        (fun r => (DeterministicAlgorithm.done (a :: r) : DeterministicAlgorithm (List Digest)))
        l.length 0 (queryBound_askList l) fun _ => trivial
      simpa using h

/-- (2) **reads**, at pair := Prod.mk. -/
theorem reads_describe (Z : PublicFiles) (hash : VerifiableInference.Hash) :
    (readBoth (describeFull V) Z c₀ [] (toldAtZ V Z) Prod.mk).evaluate hash =
      (toldAtZ V Z).Pub.det fun _ => hash := by
  show _ = (pub8 recordGround Z.pol Z.KL Z.lay).det fun _ => hash
  rw [pub8_det]
  unfold readBoth
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
  show (_, (askList _).evaluate hash) = _
  rw [evaluate_askList]
  rfl

/-- (3) **hq₀**: the two readings ask at most eight times. -/
theorem hq₀_describe (Z : PublicFiles) :
    (readBoth (describeFull V) Z c₀ [] (toldAtZ V Z) Prod.mk).toRandomized.QueryBound 8 := by
  unfold readBoth
  refine queryBound_andThen (readConfig Z) _ 1 7 (fun _ => trivial) fun c => ?_
  have hl : (ssOf (par7 recordGround Z.pol Z.KL Z.lay) c).length ≤ 7 := by
    unfold ssOf par7
    rw [List.length_map]
    split <;> simp
  have h := queryBound_andThen (askList (ssOf (par7 recordGround Z.pol Z.KL Z.lay) c))
    (fun m => (DeterministicAlgorithm.done (c, m) : DeterministicAlgorithm (toldAtZ V Z).D))
    7 0 (queryBound_mono_det _ _ _ hl (queryBound_askList _)) fun _ => trivial
  simpa using h

/-- (4) **ToldAt**, from what is truly owed: the fifteen hypotheses that name no claim at every d,
the meaning, and that φ carries the claim. -/
def toldAt_describe (Z : PublicFiles) (s : IntegerTransformer.Settings) (hv : settingsAreValid s = true)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (claim : A.Mat → List Token → List Token → Prop) (Wn : Type) (Rno : A.Mat → X → Wn → Prop)
    (x₀ : X) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions ((toldAtZ V Z).beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, T₀.build x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ i prompt output, claim i prompt output → newClaim (V.φ s hv i) prompt output) :
    ToldAt (describeFull V) Z s newClaim where
  c₀ := c₀
  m₀ := []
  T := toldAtZ V Z
  pair := Prod.mk
  claim := claim
  Wn := Wn
  Rno := Rno
  x₀ := x₀
  εs := εs
  q₀ := 8
  φ := V.φ s hv
  fits := fits_describe V Z
  core := core
  meaning := meaning
  noCoin := told_noCoin (atZ V.U Z)
  asks := told_asks (atZ V.U Z)
  once := told_once (atZ V.U Z)
  spare := told_spare (atZ V.U Z)
  word := told_word (atZ V.U Z)
  code := told_code (atZ V.U Z)
  reads := reads_describe V Z
  hq₀ := hq₀_describe V Z
  carries := carries

/-- (5) **hext.** -/
theorem hext_describe (Z : PublicFiles) (s : IntegerTransformer.Settings) (hv : settingsAreValid s = true)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (claim : A.Mat → List Token → List Token → Prop) (Wn : Type) (Rno : A.Mat → X → Wn → Prop)
    (x₀ : X) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions ((toldAtZ V Z).beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, T₀.build x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ i prompt output, claim i prompt output → newClaim (V.φ s hv i) prompt output) :
    (describeFull V).extractor Z s =
      (toldAt_describe V Z s hv newClaim claim Wn Rno x₀ εs core meaning carries).extractor := by
  funext commitment queryLog
  show (if h : settingsAreValid s = true then
      ((toldOf (atZ V.U Z)).extractor commitment queryLog).map (V.φ s h) else none) = _
  rw [dif_pos hv]
  rfl

/-- The error at this description: one term for all Z: the wiring is T₀'s. -/
def errDescribe (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)
    (εs : ℝ≥0∞) (t n : ℕ) : ℝ≥0∞ :=
  soundnessBoundOverTypedOracles T₀.W εs (t + (8 + n)) 0 + epsCode (t + (8 + n))

/-- **THE LADDER's G7 AT THIS DESCRIPTION, FROM FIVE DEBTS BY NAME**: core (the fifteen hypotheses
that name no claim, at every Z in scope and every d), meaning, carries (against the ladder's own
`ModelOutput`), ownParser (the goal's own first conjunct), ceil (numbers). A conditional: no letter
is filled. -/
theorem G7_describe (claim : A.Mat → List Token → List Token → Prop) (Wn : Type)
    (Rno : A.Mat → X → Wn → Prop) (x₀ : X) (εs : ℝ≥0∞)
    (core : ∀ Z, InScope Z = true → ∀ d, CompilerSoundnessConditions ((toldAtZ V Z).beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, T₀.build x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      pp.pol = Inst.Model.AcceptancePolicy.exact → ∀ i prompt output, claim i prompt output →
        ModelOutput (settingsOfRead pp) (V.φ (settingsOfRead pp) (valid_of_read hr) i) prompt
            output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact → Parser.Within ((describeFull V).parse Z) honestBudget)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → errDescribe T₀ εs t n ≤ ceiling) :
    G7 fun _ => describeFull V :=
  G7_of_told (fun _ => describeFull V) (errDescribe T₀ εs) ceil
    (fun Z pp h₁ h₂ h₃ => toldAt_describe V Z (settingsOfRead pp) (valid_of_read h₂) _ claim Wn Rno
        x₀ εs
      (core Z h₁) meaning (carries Z pp h₁ h₂ h₃))
    ownParser fun _ _ _ _ _ _ _ => le_rfl

/-- **THE LADDER's G8 AT THIS DESCRIPTION**, likewise, with carries against the files' policy. -/
theorem G8_describe (claim : A.Mat → List Token → List Token → Prop) (Wn : Type)
    (Rno : A.Mat → X → Wn → Prop) (x₀ : X) (εs : ℝ≥0∞)
    (core : ∀ Z, InScope Z = true → ∀ d, CompilerSoundnessConditions ((toldAtZ V Z).beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, T₀.build x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim i prompt output →
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol (V.φ (settingsOfRead pp) (valid_of_read hr) i)
          prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeFull V).parse Z) honestBudget)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → errDescribe T₀ εs t n ≤ ceiling) :
    G8 fun _ => describeFull V :=
  G8_of_told (fun _ => describeFull V) (errDescribe T₀ εs) ceil
    (fun Z pp h₁ h₂ => toldAt_describe V Z (settingsOfRead pp) (valid_of_read h₂) _ claim Wn Rno x₀
        εs
      (core Z h₁) meaning (carries Z pp h₁ h₂))
    ownParser (fun Z pp h₁ h₂ => hext_describe V Z (settingsOfRead pp) (valid_of_read h₂) _ claim
        Wn Rno x₀ εs
      (core Z h₁) meaning (carries Z pp h₁ h₂)) fun _ _ _ _ _ _ => le_rfl

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.G7_describe
#print axioms VerifierAndGoals.Fit.G8_describe
#print axioms VerifierAndGoals.Fit.fits_describe
#print axioms VerifierAndGoals.Fit.reads_describe
#print axioms VerifierAndGoals.Fit.hq₀_describe
#print axioms VerifierAndGoals.Fit.toldAt_describe
#print axioms VerifierAndGoals.Fit.hext_describe
