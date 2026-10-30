-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.PV.DescribeO
import Ladder.FitBindsBits
import Johnson.TypedOracleCompiler.Top.IdSeedHasCode
import Johnson.Flat.ThreeFull

/-!
Johnson/PV/DescribeBinds.lean: the goal on opening-form binding, G9 (Ladder.lean), and its form with
a security level, G9bits (Ladder/Bits.lean), at the slot `describeZO` (Johnson/PV/DescribeO.lean),
with what is owed named; and with `G8_describeO`: `SoundAndBinding` and `SoundOpened` of the goals'
verifier, in their nearest forms (Ladder/Package.lean), at that slot. Theorems with proofs.

Main names (namespace `VerifierAndGoals.Fit`).
  `encTOf_total`: every pair (told part, key) has a code (`encId_hasCode` at `room_recordGround`).
  `CommitDebts fr H φO Z s hv`: what is owed at one Z: data (back coins qCoins ri sl b₀ isk tS) and
    six laws (section · behind · coinsWithin · commits · decodes · within).
  `bindAt_describeZO`: `BindAt` (Ladder/FitBinds.lean) at the slot. Paid there: the told law's six
    (`told_noCoin` … `told_code`), the first of the wire's laws (`wiresOfFull`, from five tests on
    numbers) and coded (`encTOf_total`).
  **`G9_describeZO`**: G9 at `describeZO fr H φO`. No error is left as a letter:
    3 (t + qMax + 2 tMax + 2)² / 2^256.
  `backO`, `section_backO`: at `phiO` and the reference shape: back w is `Flat.matrixOf` of the
  index
    of w, and `phiO valid (backO valid w) = some w`: section is paid.
  `CommitDebtsO`, **`G9_describeO`**, **`G9bits_describeO`**,
  **`nearestSoundAndBinding_describeO`**,
  `nearestSoundOpened_describeO`: at the slot of `G8_describeO`.

What G9_describeO owes, all of it. 2 tMax + qMax ≤ 2^65 (for G9bits: 2 tMax + qMax + 2 ≤ 2^50). At
every Z in scope: hk wK dK wP dP (the five tests on numbers of `G8_describeO`) · the data coins
qCoins
ri sl b₀ isk tS · behind (U.commit is the public reading, then `committerOverTypedOracles` at (Sd d, m d), the told
part laid beside the key: an equation that fixes a free field: whoever writes U can meet it) ·
coinsWithin (coins asks at most qCoins ≤ qMax queries) · commits (H.commit has, at every hash
function, that committer's value under the key's code, at the number that coins makes of H's
randomness there; coins may ask the hash function: a committer whose pads and salts come from a key
that holds answers of the hash function can meet it only so) · decodes (the decoder gives back the
matrix of every set of weights from its honest encoding and record: it owes a written encoder: E is
a letter here) · within (that committer asks at most tS ≤ tMax queries) · commitWithin (the goal's
own
first conjunct, restated).
Not among them: keySound, proofSound, the theorem on codes, meaning, carries: binding reads no
hypothesis on soundness.

Limits. A slot, no member: conditionals: no goal of Ladder.lean is met. The verifier is idle in G9.
No program's committer is tied to `committerOverTypedOracles`.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model.Layout (kRef hRef)
open Inst.Model (ScalesAndPolicy Lawful)
open scoped ENNReal

section Code
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)

/-- **Every pair (told part, key) has a code.** -/
theorem encTOf_total (key : Dig 256 × KeyRoot 256 (innerCompilerInputWithFixedLinkAtFullSize T₀).protocol) : encTOf T₀ key ≠ none :=
by
  obtain ⟨code, h⟩ := encId_hasCode recordGround
    (restOfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P) room_recordGround key
  unfold encTOf
  rw [h]
  exact Option.some_ne_none _

end Code

section General
variable (fr : PublicFiles → FrameAt) (H : SideZ fr)
  (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
    (fr Z).A.Mat → Option (ModelWeights s))

/-- **What opening-form binding (`BindsWith`) owes at one Z, at the slot**: data, then six laws. -/
structure CommitDebts (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (hv : settingsAreValid s = true) where
  back : ModelWeights s → (fr Z).A.Mat
  coins : H.Rand → DeterministicAlgorithm (Fin (((describeZO fr H φO).input Z c₀ []).coinBound + 1))
  qCoins : ℕ
  ri : _root_.Iop.Enum ((describeZO fr H φO).input Z c₀ []).protocol.EncodingRandomness
  sl : _root_.Iop.Enum (ℕ → Rom.Bits)
  b₀ : ((describeZO fr H φO).input Z c₀ []).LeafBody
  isk : (toldAtZ (lettersAt fr H Z) Z).D →
    (fr Z).A.Mat × ((describeZO fr H φO).input Z c₀ []).protocol.EncodingRandomness × (ℕ → Rom.Bits) →
      (toldAtZ (lettersAt fr H Z) Z).ISK
  tS : ℕ
  section_ : ∀ w, φO Z s hv (back w) = some w
  behind : CommitsBehind (toldAtZ (lettersAt fr H Z) Z) ri sl b₀ isk
  coinsWithin : ∀ ρ, (coins ρ).toRandomized.QueryBound qCoins
  commits : ∀ w ρ hash, (H.commit Z s w ρ).evaluate hash =
    (((toldAtZ (lettersAt fr H Z) Z).systemOn back (modelNextToken s)).commit w
      ((coins ρ).evaluate hash)).evaluate hash
  decodes : ∀ w r sd, ((describeZO fr H φO).input Z c₀ []).protocol.decodeIndex
    (((describeZO fr H φO).input Z c₀ []).protocol.encodeIndex (back w) r)
    (((describeZO fr H φO).input Z c₀ []).protocol.recOf (back w) r sd) = some (back w)
  within : ∀ w, ((toldAtZ (lettersAt fr H Z) Z).commit (back w)).QueryBound tS

variable {fr H φO}

/-- **BindAt at the slot**: the told law's six, the wire's first law and «coded» are paid. -/
def bindAt_describeZO (Z : PublicFiles) (s : IntegerTransformer.Settings) (hv : settingsAreValid s = true)
    (hk : kThree .two (fr Z).DK frRds (fr Z).DP ≤ (fr Z).K) (wK : (fr Z).DK.workFit = true)
    (dK : (fr Z).DK.depthFit = true) (wP : (fr Z).DP.workFit = true)
    (dP : (fr Z).DP.depthFit = true) (Q : CommitDebts fr H φO Z s hv) :
    BindAt (describeZO fr H φO) Z s where
  c₀ := c₀
  m₀ := []
  T := toldAtZ (lettersAt fr H Z) Z
  φ := φO Z s hv
  back := Q.back
  coins := Q.coins
  qCoins := Q.qCoins
  ri := Q.ri
  sl := Q.sl
  b₀ := Q.b₀
  isk := Q.isk
  tS := Q.tS
  noCoin := told_noCoin (atZ (fr Z).U Z)
  asks := told_asks (atZ (fr Z).U Z)
  once := told_once (atZ (fr Z).U Z)
  spare := told_spare (atZ (fr Z).U Z)
  word := told_word (atZ (fr Z).U Z)
  code := told_code (atZ (fr Z).U Z)
  wire := (wiresOfFull (fr Z).A (relationsAndEncodingOfClaims (fr Z).A (fr Z).E) (fr Z).DK (fr Z).DP (fr Z).runK (fr
                        Z).runP
    (fr Z).rK (fr Z).rP (fr Z).depthReq (fr Z).early (fr Z).salt (fr Z).P (fr Z).K
    (fr Z).T₀.depthReqT hk wK dK wP dP).1
  section_ := Q.section_
  behind := Q.behind
  coinsWithin := Q.coinsWithin
  commits := Q.commits
  decodes := Q.decodes
  coded := (ZKCP.SpecialAny.oneOf _).keysHaveCodes_of_total (encTOf_total (fr Z).T₀)
  within := Q.within

variable (fr H φO)

/-- **G9 AT describeZO.** -/
theorem G9_describeZO (tMax qMax : ℕ) (hMax : 2 * tMax + qMax ≤ 2 ^ 65)
    (hk : ∀ Z, InScope Z = true → kThree .two (fr Z).DK frRds (fr Z).DP ≤ (fr Z).K)
    (wK : ∀ Z, InScope Z = true → (fr Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (fr Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (fr Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (fr Z).DP.depthFit = true)
    (Q : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      CommitDebts fr H φO Z (settingsOfRead pp) (valid_of_read hr))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, (H.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (count : ∀ Z pp h₁ h₂, (Q Z pp h₁ h₂).tS ≤ tMax ∧ (Q Z pp h₁ h₂).qCoins ≤ qMax) :
    G9 fun _ => describeZO fr H φO :=
  G9_of_bindAt (fun _ => describeZO fr H φO) tMax qMax hMax
    (fun Z pp h₁ h₂ => bindAt_describeZO Z (settingsOfRead pp) (valid_of_read h₂) (hk Z h₁) (wK Z
    h₁)
      (dK Z h₁) (wP Z h₁) (dP Z h₁) (Q Z pp h₁ h₂))
    commitWithin
    (fun Z pp _ h₂ => by
      funext commitment queryLog
      show (if h : settingsAreValid (settingsOfRead pp) = true then
          ((toldOf (atZ (fr Z).U Z)).extractor commitment queryLog).bind
            (φO Z (settingsOfRead pp) h) else none) = _
      rw [dif_pos (valid_of_read h₂)]
      rfl)
    count

end General

/-! ## At the files' own policy, the reference shape and phiO -/

/-- The matrix of given weights: `Flat.matrixOf` of their index. -/
def backO {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    (w : ModelWeights settings) : Fin hRef → Fin (2 ^ kRef) → Flat.GE :=
  Flat.matrixOf (indexOfWeights valid w)

/-- **«section» IS PAID**: phiO gives back the weights from their matrix. -/
theorem section_backO {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (w : ModelWeights settings) :
    phiO valid (backO valid w) = some w := by
  unfold phiO backO
  rw [Flat.indexOf_eq (le_refl _) (le_refl _) (Flat.holds_matrixOf _)]
  exact congrArg some (weightsOfIndex_indexOfWeights valid w)

section AtPolicy
variable (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
  (H : SideZ fun Z => (g Z).toFrame)

/-- The slot of `G8_describeO`. -/
abbrev slotO : Description :=
  describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid)

/-- **WHAT OPENING-FORM BINDING OWES AT ONE Z, AT G8_describeO's SLOT**: «back» is written and
«section» is paid: data, then five laws. -/
structure CommitDebtsO (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (hv : settingsAreValid s = true) where
  coins : H.Rand → DeterministicAlgorithm (Fin (((slotO g H).input Z c₀ []).coinBound + 1))
  qCoins : ℕ
  ri : _root_.Iop.Enum ((slotO g H).input Z c₀ []).protocol.EncodingRandomness
  sl : _root_.Iop.Enum (ℕ → Rom.Bits)
  b₀ : ((slotO g H).input Z c₀ []).LeafBody
  isk : (toldAtZ (lettersAt (fun Z => (g Z).toFrame) H Z) Z).D →
    (g Z).toFrame.A.Mat × ((slotO g H).input Z c₀ []).protocol.EncodingRandomness × (ℕ → Rom.Bits) →
      (toldAtZ (lettersAt (fun Z => (g Z).toFrame) H Z) Z).ISK
  tS : ℕ
  behind : CommitsBehind (toldAtZ (lettersAt (fun Z => (g Z).toFrame) H Z) Z) ri sl b₀ isk
  coinsWithin : ∀ ρ, (coins ρ).toRandomized.QueryBound qCoins
  commits : ∀ w ρ hash, (H.commit Z s w ρ).evaluate hash =
    (((toldAtZ (lettersAt (fun Z => (g Z).toFrame) H Z) Z).systemOn (backO hv)
      (modelNextToken s)).commit w ((coins ρ).evaluate hash)).evaluate hash
  decodes : ∀ w r sd, ((slotO g H).input Z c₀ []).protocol.decodeIndex
    (((slotO g H).input Z c₀ []).protocol.encodeIndex (backO hv w) r)
    (((slotO g H).input Z c₀ []).protocol.recOf (backO hv w) r sd) = some (backO hv w)
  within : ∀ w, ((toldAtZ (lettersAt (fun Z => (g Z).toFrame) H Z) Z).commit
    (backO hv w)).QueryBound tS

variable {g H}

/-- As the general record: «back» written, «section» paid. -/
def CommitDebtsO.toDebts {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {hv : settingsAreValid s = true} (Q : CommitDebtsO g H Z s hv) :
    CommitDebts (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid) Z s hv where
  back := backO hv
  coins := Q.coins
  qCoins := Q.qCoins
  ri := Q.ri
  sl := Q.sl
  b₀ := Q.b₀
  isk := Q.isk
  tS := Q.tS
  section_ := section_backO hv
  behind := Q.behind
  coinsWithin := Q.coinsWithin
  commits := Q.commits
  decodes := Q.decodes
  within := Q.within

variable (g H)

/-- **G9 AT G8_describeO's SLOT.** -/
theorem G9_describeO (tMax qMax : ℕ) (hMax : 2 * tMax + qMax ≤ 2 ^ 65)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (Q : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      CommitDebtsO g H Z (settingsOfRead pp) (valid_of_read hr))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, (H.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (count : ∀ Z pp h₁ h₂, (Q Z pp h₁ h₂).tS ≤ tMax ∧ (Q Z pp h₁ h₂).qCoins ≤ qMax) :
    G9 fun _ => slotO g H :=
  G9_describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid) tMax qMax hMax hk wK dK wP
    dP
    (fun Z pp h₁ h₂ => (Q Z pp h₁ h₂).toDebts) commitWithin count

/-- **G9bits (lean/Ladder/Bits.lean) AT G8_describeO's SLOT: THE GOAL ON BINDING WITH A SECURITY
LEVEL, FROM THE SAME DEBTS**, where
2 tMax + qMax + 2 ≤ 2^50. -/
theorem G9bits_describeO (tMax qMax : ℕ) (hMax : 2 * tMax + qMax + 2 ≤ 2 ^ 50)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (Q : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      CommitDebtsO g H Z (settingsOfRead pp) (valid_of_read hr))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, (H.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (count : ∀ Z pp h₁ h₂, (Q Z pp h₁ h₂).tS ≤ tMax ∧ (Q Z pp h₁ h₂).qCoins ≤ qMax) :
    G9bits fun _ => slotO g H :=
  G9bits_of_bindAt (fun _ => slotO g H) tMax qMax hMax
    (fun Z pp h₁ h₂ => bindAt_describeZO Z (settingsOfRead pp) (valid_of_read h₂) (hk Z h₁) (wK Z
    h₁)
      (dK Z h₁) (wP Z h₁) (dP Z h₁) (Q Z pp h₁ h₂).toDebts)
    commitWithin
    (fun Z pp _ h₂ => by
      funext commitment queryLog
      show (if h : settingsAreValid (settingsOfRead pp) = true then
          ((toldOf (atZ (g Z).toFrame.U Z)).extractor commitment queryLog).bind (phiO h)
          else none) = _
      rw [dif_pos (valid_of_read h₂)]
      rfl)
    count

/-- **`SoundAndBinding` OF verify()'s SYSTEM, IN ITS NEAREST FORM, AT THE SLOT**: from
G8_describeO's
named debts and G9_describeO's, AT ONE DESCRIPTION AND SO AT ONE EXTRACTOR. The error is at most the
ceiling (1/4) up to the budget of queries. On the theorem on codes: G8_describeO's docstring. -/
theorem nearestSoundAndBinding_describeO
    (c : ℝ≥0∞) (a s v : ℕ) (has : a + s = 128) (hs : s ≤ 55) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hv : v ≤ 2 ^ 63)
    (he : ∀ Z, InScope Z = true → (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (hcnt : ∀ Z, InScope Z = true →
      cntFrameFull (g Z).DK (g Z).DP (g Z).depthReq (g Z).T₀.depthReqT ≤ v)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (hb : ∀ Z, InScope Z = true → ∀ x' a, (g Z).T₀.build x' a = Flat.buildReq x' a)
    (asks15 : ∀ Z, InScope Z = true → ∀ prompt output form,
      (H.parse Z prompt output form).toRandomized.QueryBound 15)
    (tMax qMax : ℕ) (hMax : 2 * tMax + qMax ≤ 2 ^ 65)
    (Q : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      CommitDebtsO g H Z (settingsOfRead pp) (valid_of_read hr))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, (H.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (count : ∀ Z pp h₁ h₂, (Q Z pp h₁ h₂).tS ≤ tMax ∧ (Q Z pp h₁ h₂).qCoins ≤ qMax) :
    ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ ceiling) ∧
      NearestSoundAndBinding (fun _ => slotO g H) eps :=
  nearestSoundAndBinding_of_g8_g9 _
    (G8_describeO g H c a s v has hs hc hv he hcnt hk wK dK wP dP kS pS hb asks15)
    (G9_describeO g H tMax qMax hMax hk wK dK wP dP Q commitWithin count)

/-- **`SoundOpened` likewise**, at most 1/2. -/
theorem nearestSoundOpened_describeO
    (c : ℝ≥0∞) (a s v : ℕ) (has : a + s = 128) (hs : s ≤ 55) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hv : v ≤ 2 ^ 63)
    (he : ∀ Z, InScope Z = true → (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (hcnt : ∀ Z, InScope Z = true →
      cntFrameFull (g Z).DK (g Z).DP (g Z).depthReq (g Z).T₀.depthReqT ≤ v)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (hb : ∀ Z, InScope Z = true → ∀ x' a, (g Z).T₀.build x' a = Flat.buildReq x' a)
    (asks15 : ∀ Z, InScope Z = true → ∀ prompt output form,
      (H.parse Z prompt output form).toRandomized.QueryBound 15)
    (tMax qMax : ℕ) (hMax : 2 * tMax + qMax ≤ 2 ^ 65)
    (Q : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      CommitDebtsO g H Z (settingsOfRead pp) (valid_of_read hr))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, (H.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (count : ∀ Z pp h₁ h₂, (Q Z pp h₁ h₂).tS ≤ tMax ∧ (Q Z pp h₁ h₂).qCoins ≤ qMax) :
    ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ 2⁻¹) ∧
      NearestSoundOpened (fun _ => slotO g H) eps :=
  nearestSoundOpened_of_g8_g9 _
    (G8_describeO g H c a s v has hs hc hv he hcnt hk wK dK wP dP kS pS hb asks15)
    (G9_describeO g H tMax qMax hMax hk wK dK wP dP Q commitWithin count)

end AtPolicy

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.encTOf_total
#print axioms VerifierAndGoals.Fit.G9_describeZO
#print axioms VerifierAndGoals.Fit.section_backO
#print axioms VerifierAndGoals.Fit.G9_describeO
#print axioms VerifierAndGoals.Fit.G9bits_describeO
#print axioms VerifierAndGoals.Fit.nearestSoundAndBinding_describeO
#print axioms VerifierAndGoals.Fit.nearestSoundOpened_describeO
