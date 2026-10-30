-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/ProofAtName.lean: statements on the blocks of a description of the proof file,
in the form in which `proofSound_at_descB` (Johnson/Desc/Plain/BothAtDesc.lean) takes them, give
`ProofFileAt Z` (Johnson/Goal/Skeleton/ProofFile.lean) for the description `VerifierAndGoals.theDescription`.
`ProofFileAt Z` at every Z in scope at which `protocolDataWellFormed` says yes gives `ProofSound`
(`proofSound_of_proofFileAt`, ProofFile.lean).

"The thirteen hypotheses" are hO, hf, fit, e₁, e₂, e₃, G, pubEarly, oneKey, tie, b₁, b₂ and b₃ of
`proofSound_at_descB`. The three equations on shapes h₁, h₂, h₃ are parameters, there and here.
  `rows_at_fullD`: `rows_at_descB` (Johnson/Goal/Skeleton/ProofRowsAtDesc.lean), restated from
    `filesOf` for `threeProtocolsAtFullSize`. The thirteen hypotheses give a choice of the free
    variables and the seven fields of `RowsOfProofFile`, for every decision runP that equals the
    description's run (er) and every Tl : `InnerCompilerInputAndAnalysisFieldsAtFullSize` whose bound is εs (hε).
  `proofSound_at_fullD`: under the same hypotheses `proofSound_at_descB` gives
    `CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl)`. Nothing uses it: it is here to check that the list
    of hypotheses is that theorem's.
  `proofFileAt_of_descB`: the thirteen hypotheses at the data of `dataAtFiles flashProveData Z` (b₁ to b₃ at
    1 / 2^128), F = FP.pull instP, a yes of `protocolDataWellFormed` and the equation
    `theProofRun (asDescriptionFiles Z) = F.run` give `ProofFileAt Z`.
  `reads_the_names_table`: if `readFiles Z` succeeds, it returns `ppAtFiles Z.pol Z.KL`.
  `early_of_live`: where `protocolDataWellFormed` says yes, `(dataAtFiles flashProveData Z).G.early` is `reqWithoutReply`.
  `proofFileAt_of_some`: `proofFileAt_of_descB` at M := `meansSome`, with `TieOwesSome`
    (Johnson/Goal/Meaning/TieAtSome.lean) in the place of the hypothesis tie. It also asks that Z
    is in scope and that `readFiles` and `publicOf` succeed at Z.

Limits. This file only combines statements. None of the hypotheses is proved for the protocol's own
description, so nothing here shows that the proof file's protocol is sound. No example is given in
which the hypotheses hold together. That the equation
`theProofRun (asDescriptionFiles Z) = F.run` holds is not shown here.

(Where this and lean/THEOREM.md differ, the page holds.)
`early_of_live` rests on `g_built_live`
(Johnson/Goal/Conditions/LiveAtThe.lean).

-/
import Johnson.Goal.Skeleton.ProofRowsAtSome
import Johnson.Goal.Meaning.EarlyAtThe
import Johnson.Goal.Conditions.LiveAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run (ckP)
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open OnBytes.Road OnBytes.Road.L5
open LPFD.Full (XF)

/-! ## Short names -/

/-- The depth of the stored table in the full-size parameters `frS`. -/
abbrev aF : ℕ := frS.P.T.a

/-- The configuration `lettersAt A (relationsAndEncodingOfClaims A E)` at claims A and a coding E. -/
abbrev confAt {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) :
    ConfLetters aF := lettersAt A (relationsAndEncodingOfClaims A E)

/-- The proof file's three chains at the data DP and the record rP. -/
abbrev chainsAt (DP : WholeD) (rP : RecFull) : Chains :=
  chainsOf (ckP .two) (DP.at aF) (front₀ rP) (join₀ rP) ByteArray.empty

/-- The type of the stored table's strings at the data DP. -/
abbrev StrAt (DP : WholeD) : Type := (oneExternalString (2 ^ (DP.at aF).a) SgX).Str

/-! ## From `filesOf` to `threeProtocolsAtFullSize` -/

section Frame
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}
  (F : FileDescription (X × RecFull)) (all : List LeftT) {X₁ X₂ W κ : Type}
  (T : ThreeAt (ckP .two) (DP.at aF) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at aF) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at aF).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at aF).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at aF).ds₃)
  (M : (X × RecFull) × StrAt DP → (F.XiPub × F.S₁) × (EAll (DP.at aF) all).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at aF) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at aF) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at aF) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at aF) all).Str → κ)
  (w₀ : (confAt A E).conf.Cells) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
  (fit : RowFit (DP.at aF) all all)
  (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
  (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ (2 ^ depthReq) 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
  (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
  (G : Glues (atDesc F T) Pl M L₁ L₂)
  (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
  (F₁ : RecFull → StrAt DP → κ)
  (oneKey : ∀ x rec y τ b,
    (plainP (confAt A E) DP (front₀ rP) (join₀ rP) ByteArray.empty F all T Pl h₁ h₂ h₃ M L₁ L₂
      d).out₁ ((x, rec), y) τ = some b → key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
  (tie : ∀ x rec (y : StrAt DP) (τ : Tr (chainsAt DP rP).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
    (z : (EAll (DP.at aF) all).Str),
    F.okStart (x, rec) = true →
    silP (x, rec) ((chainsAt DP rP).msgF τ).2 ((chainsAt DP rP).msgJ τ).2
      ((chainsAt DP rP).msg3 τ).2 = true →
    F.fin (x, rec) s₁ s₂ s₃ = true →
    (Pl.on₁ 0 ((atDesc F T).in₁ (early x, rec), (y, fun _ => [])) →
      M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
    (confAt A E).conf.D y rec = none ∨
      ∃ i, (confAt A E).conf.D y rec = some i ∧ (confAt A E).conf.Rno i x w₀)
  (εs : ℝ≥0∞)
  (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at aF).ds₁ h₁) εs)
  (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at aF).ds₂ h₂) εs)
  (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at aF).ds₃ h₃) εs)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (er : runP = F.run)
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
    salt).Provers}
  (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P)
  (hε : Tl.εs = εs)

include hO hf fit e₁ e₂ e₃ G pubEarly oneKey tie b₁ b₂ b₃ er hε

/-- **The thirteen hypotheses give a choice of the free variables and the seven fields.** -/
theorem rows_at_fullD :
    ∃ L : ProofLetters (innerCompilerInputAtFullSize Tl) (soundnessAnalysisDataAtFullSize Tl) (chainsAt DP rP),
      RowsOfProofFile
        (wholeDesc (ckP .two) (DP.at aF) (front₀ rP) (join₀ rP) ByteArray.empty silP F.run) L
        εs := by
  subst er
  subst hε
  exact ⟨lettersAtDescB (confAt A E) DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
      (join₀ rP) ByteArray.empty silK runK silP (linkProtocolAtFullSize dsFull frD.xs dec salt) (2 ^ depthReq)
      early F all T Pl h₁ h₂ h₃ M L₁ L₂ d key P Tl.letters Tl.names w₀ F₁,
    rows_at_descB (confAt A E) DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP)
      ByteArray.empty silK runK silP (linkProtocolAtFullSize dsFull frD.xs dec salt) (2 ^ depthReq) early F
      all T Pl h₁ h₂ h₃ M L₁ L₂ d key P Tl.letters Tl.names w₀ hO hf fit e₁ e₂ e₃ G pubEarly F₁
      oneKey tie b₁ b₂ b₃⟩

/-- The same hypotheses give `CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl)` by `proofSound_at_descB`.
Nothing uses this theorem: it checks that the list of hypotheses is that theorem's. -/
theorem proofSound_at_fullD : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl) := by
  subst er
  subst hε
  exact proofSound_at_descB (confAt A E) DK DP (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP)
    (join₀ rP) ByteArray.empty silK runK silP (linkProtocolAtFullSize dsFull frD.xs dec salt) (2 ^ depthReq)
    early F all T Pl h₁ h₂ h₃ M L₁ L₂ d key P Tl.letters Tl.names w₀ hO hf fit e₁ e₂ e₃ G pubEarly
    F₁ oneKey tie b₁ b₂ b₃

end Frame

/-! ## At `VerifierAndGoals.theDescription` -/

/-- The proof file's data in `dataAtFiles flashProveData Z`. -/
abbrev dpZ (Z : PublicFiles) : WholeD := (dataAtFiles flashProveData Z).DP

/-- The second part of the fixed instance `z₀` in `dataAtFiles flashProveData Z`. Below, `front₀` and `join₀`
are taken at it. -/
abbrev recZ (Z : PublicFiles) : RecFull := (dataAtFiles flashProveData Z).G.z₀.2

/-- The map `early` on instances in `dataAtFiles flashProveData Z`. -/
abbrev earlyZ (Z : PublicFiles) : XF → XF := (dataAtFiles flashProveData Z).G.early

/-- The depth of the tree of requests in `dataAtFiles flashProveData Z`. -/
abbrev depthZ (Z : PublicFiles) : ℕ := (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves

/-- The configuration at the claims and the coding of `dataAtFiles flashProveData Z`. -/
abbrev confZ (Z : PublicFiles) : ConfLetters aF := confAt (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E

/-- **The thirteen hypotheses at the data of `dataAtFiles flashProveData Z` give `ProofFileAt Z`.** F is the
description FP with its instances pulled back along instP. -/
theorem proofFileAt_of_descB (Z : PublicFiles) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {XiP : Type}
    (FP : FileDescription XiP) (instP : XF × RecFull → XiP) (F : FileDescription (XF × RecFull))
    (hF : F = FP.pull instP) (seat_proof_file : theProofRun (asDescriptionFiles Z) = F.run)
    (all : List LeftT) {X₁ X₂ W κ : Type} (T : ThreeAt (ckP .two) ((dpZ Z).at aF) all F X₁ X₂ W)
    (Pl : PPlaces ((dpZ Z).at aF) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) ((dpZ Z).at aF).ds₁)
    (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) ((dpZ Z).at aF).ds₂)
    (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) ((dpZ Z).at aF).ds₃)
    (M : (XF × RecFull) × StrAt (dpZ Z) →
      (F.XiPub × F.S₁) × (EAll ((dpZ Z).at aF) all).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll ((dpZ Z).at aF) all).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll ((dpZ Z).at aF) all).Str → Prop)
    (d : (F.XiPub × F.S₁) × (EAll ((dpZ Z).at aF) all).Str)
    (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll ((dpZ Z).at aF) all).Str → κ)
    (w₀ : (confZ Z).conf.Cells)
    (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fit : RowFit ((dpZ Z).at aF) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ (2 ^ depthZ Z) 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (earlyZ Z x, rec) = F.pub (x, rec))
    (F₁ : RecFull → StrAt (dpZ Z) → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (confZ Z) (dpZ Z) (front₀ (recZ Z)) (join₀ (recZ Z)) ByteArray.empty F all T Pl h₁ h₂
        h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (tie : ∀ x rec (y : StrAt (dpZ Z)) (τ : Tr (chainsAt (dpZ Z) (recZ Z)).sh) (s₁ : F.S₁)
      (s₂ : F.S₂) (s₃ : F.S₃) (z : (EAll ((dpZ Z).at aF) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsAt (dpZ Z) (recZ Z)).msgF τ).2 ((chainsAt (dpZ Z) (recZ Z)).msgJ τ).2
        ((chainsAt (dpZ Z) (recZ Z)).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (earlyZ Z x, rec), (y, fun _ => [])) →
        M ((earlyZ Z x, rec), y) ((F.pub (x, rec), s₁), z)) →
      (confZ Z).conf.D y rec = none ∨
        ∃ i, (confZ Z).conf.D y rec = some i ∧ (confZ Z).conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ ((dpZ Z).at aF).ds₁ h₁)
      ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ ((dpZ Z).at aF).ds₂ h₂)
      ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ ((dpZ Z).at aF).ds₃ h₃)
      ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    ProofFileAt Z := by
  subst hF
  have e : (dataAtFiles flashProveData Z).runP = (FP.pull instP).run := by
    rw [runP_the_at Z _ seat_proof_file, hl]
    rfl
  obtain ⟨L, R⟩ := rows_at_fullD (FP.pull instP) all T Pl h₁ h₂ h₃ M L₁ L₂ d key w₀ hO hf fit e₁ e₂
    e₃ G pubEarly F₁ oneKey tie _ b₁ b₂ b₃ _ e ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0) (eps_the Z)
  exact ⟨XiP, FP, instP, L, seat_proof_file, R⟩

/-- If `readFiles Z` succeeds, it returns `ppAtFiles Z.pol Z.KL`. -/
theorem reads_the_names_table (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) :
    readFiles Z = .ok (ppAtFiles Z.pol Z.KL) := by
  rw [ppAtFiles_of_read hr]
  exact hr

/-- Where `protocolDataWellFormed` says yes, `earlyZ Z` is `reqWithoutReply`: it sets a request's reply to 0. -/
theorem early_of_live (Z : PublicFiles) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) : earlyZ Z = reqWithoutReply :=
  early_the Z hl

/-- `meansSome` at `numsRef`, `ppAtFiles Z.pol Z.KL`, and the coding and data of
`dataAtFiles flashProveData Z`. -/
abbrev meansZ (Z : PublicFiles) (F : FileDescription (XF × RecFull)) (all : List LeftT)
    (X : OnBytes.Model.Verify.Public) (rep : F.XiPub × F.S₁ → Option (Fin Inst.Model.ppref.V)) :=
  meansSome numsRef (ppAtFiles Z.pol Z.KL) (dataAtFiles flashProveData Z).E (dpZ Z) F all X rep

/-- **`proofFileAt_of_descB` at M := `meansSome`, with `TieOwesSome` in the place of tie.** -/
theorem proofFileAt_of_some (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    {XiP : Type} (FP : FileDescription XiP) (instP : XF × RecFull → XiP) (F : FileDescription (XF × RecFull))
    (hF : F = FP.pull instP) (seat_proof_file : theProofRun (asDescriptionFiles Z) = F.run)
    (all : List LeftT) {X₁ X₂ W κ : Type} (T : ThreeAt (ckP .two) ((dpZ Z).at aF) all F X₁ X₂ W)
    (Pl : PPlaces ((dpZ Z).at aF) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) ((dpZ Z).at aF).ds₁)
    (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) ((dpZ Z).at aF).ds₂)
    (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) ((dpZ Z).at aF).ds₃)
    (L₁ : (F.XiPub × F.S₁) × (EAll ((dpZ Z).at aF) all).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll ((dpZ Z).at aF) all).Str → Prop)
    (d : (F.XiPub × F.S₁) × (EAll ((dpZ Z).at aF) all).Str)
    (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll ((dpZ Z).at aF) all).Str → κ)
    (rep : F.XiPub × F.S₁ → Option (Fin Inst.Model.ppref.V))
    (O : TieOwesSome numsRef (ppAtFiles Z.pol Z.KL) (dataAtFiles flashProveData Z).E (dpZ Z) F all T Pl rep)
    (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fit : RowFit ((dpZ Z).at aF) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ (2 ^ depthZ Z) 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl (meansZ Z F all X rep) L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (F₁ : RecFull → StrAt (dpZ Z) → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (confZ Z) (dpZ Z) (front₀ (recZ Z)) (join₀ (recZ Z)) ByteArray.empty F all T Pl h₁ h₂
        h₃ (meansZ Z F all X rep) L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ ((dpZ Z).at aF).ds₁ h₁)
      ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ ((dpZ Z).at aF).ds₂ h₂)
      ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ ((dpZ Z).at aF).ds₃ h₃)
      ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    ProofFileAt Z := by
  have he := early_of_live Z hl
  refine proofFileAt_of_descB Z hl FP instP F hF seat_proof_file all T Pl h₁ h₂ h₃
    (meansZ Z F all X rep) L₁ L₂ d key () hO hf fit e₁ e₂ e₃ G ?_ F₁ oneKey ?_ b₁ b₂ b₃
  · rw [he]
    exact pubEarly
  · rw [he]
    exact tie_of_some numsRef (ppAtFiles Z.pol Z.KL) (dataAtFiles flashProveData Z).E (dpZ Z) (front₀ (recZ Z))
      (join₀ (recZ Z)) ByteArray.empty silP F all T Pl X rep hs (reads_the_names_table Z hr) h O

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.rows_at_fullD
#print axioms VerifierAndGoals.AtTheName.proofSound_at_fullD
#print axioms VerifierAndGoals.AtTheName.proofFileAt_of_descB
#print axioms VerifierAndGoals.AtTheName.reads_the_names_table
#print axioms VerifierAndGoals.AtTheName.early_of_live
#print axioms VerifierAndGoals.AtTheName.proofFileAt_of_some
