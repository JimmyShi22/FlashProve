-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgePremWLink.lean: `premW_link` proves `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean: all hypotheses of the statement of index privacy) at three public
files Z, under the hypotheses that are listed below, with the link's prover filled in. It is
`premW_key_own` (E2E/BridgePremWKey.lean) at one value of that theorem's parameter hL: the second of
the three honest provers is the explicit honest prover of the link,
`OnBytes.LinkSim.AtHome.explicitLinkProver` (Johnson/LinkSim/AtHome/SpecHome.lean), and its simulator is that
file's `homeSim`. The four clauses of `PremW` on the link's prover and simulator are proved here
(`linkFields_atZ`). The first prover is `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean), a prover structure built
by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes
(below: the shell `offlineProverWithEncodedTable`). The third is the session's family `famG` (E2E/BridgeJoinAtFiles.lean),
each prover of which is such a structure too. All is stated at the wiring, the OOD-seed wire, the
code of the answers and the parameters of `lettersZ Z c₀ m₀`, at every digest c₀ and every list m₀
of further digests (below: the pair). E2E/BridgePremWRoom.lean has the form in which the error of
the session's simulator is a parameter too.

  `premW_link`: `PremW` at these four, at `atRecsAll`, at the simulators sT, `homeSim Z` and simOne
    (read through `instanceAsPlainRecord`), the range ok, Gs := all OOD seeds, the relation Yes, the coins' numbers
    c, and the numbers `indexPrivacyNumbers s1 zT 0 0 hT' 0 hO'`: the link's two error terms and the error of the
    session's simulator are 0
  `linkFields_atZ`: the four clauses on the link (`OnBytes.LinkSim.LinkFields`,
    Johnson/LinkSim/Spec.lean) at `atRecsAll`, `homeSim Z` and the wiring of every pair, at every
    range ok and set Gs of OOD seeds, with both error terms 0, and with no hypothesis
  `wiring_any`: the wiring `(lettersZ Z c₀ m₀).W` does not depend on the pair
  `linkProverAtFiles b Z`: an abbreviation: `explicitLinkProver b Z`, with the type of an honest prover of the link's
    protocol in the library's object `protocolAtFiles Z`; the two types agree by unfolding. b is a free parameter
    that only `explicitLinkProver` and `linkFieldsHome` take: the type of `linkProverAtFiles b Z` does not name it, and
    every statement here holds at every b
  `atRecsAll …`: an abbreviation: the parameters of the scheme's honest side
    (`OnBytes.WholeKey.AtRecs`) at `proversOf (offlineProverWithEncodedTable …) (linkProverAtFiles b Z) (famG …)`. The link's run value
    is set to one constant v₀, both as read off the coins and as read off the plain parts. Of the
    parameter R₀ only these fields are read there: dcT, dcL, b₀, capT, capL, capB, M, nm, rtail,
    fill. `restKey` and `canon` overwrite all others, its enumerations of coins and salts among them

By what. `wiring_any`: the wiring (`InnerCompilerInputAndAnalysisFieldsAtFullSize.W`, Johnson/Flat/Dec/TwoSizesAt.lean) reads of
`lettersZ Z c₀ m₀` only the field `depthReqT`, the depth of the key file's request tree. By
`FlashProve.depthReqT_tOf` (Johnson/Goal/Conditions/DepthsAtDescriptionDataAtFiles.lean) that depth is a number read
off `dataAtFiles flashProveData Z`, the same at every pair. `linkFields_atZ` is one call of `linkFieldsHome`
(Johnson/LinkSim/AtHome/Home.lean). That theorem is stated at the wiring of `homeR b Z`, which by
unfolding is the wiring of the pair (`allZeroDigest`, []), and `wiring_any` carries it to every pair:
`LinkFields` reads the wiring and no OOD-seed wire. Its three hypotheses (the link's prover is
`explicitLinkProver b Z`; the run value is v₀ off every coin, and off all plain parts) hold by unfolding.
`premW_link` is one call of `premW_key_own`. The four fields of `linkFields_atZ` give that theorem's
hypotheses on the link: its external strings, its run values, and its clauses of `StopsSmall` and
`Sims.Good`. The session's clause of `StopsSmall` comes from hz' by `stopsB_of_small`, with
`validIn` (E2E/BridgeJoinAtFiles.lean) and `hidZero_link` (E2E/BridgeJoin.lean). Its clause of
`Sims.Good`, at error 0, comes from hx by `goodB_of_exact`, with `ExactAt.re`
(E2E/BridgeAlong.lean), `validIn` and `extIsEnc_famG` (E2E/BridgeJoinAtFiles.lean). Both lemmas:
E2E/BridgePrivacy.lean. Definitions: `lettersZ`, `protocolAtFiles`, `descZ`, `provG`, `TiedIn`
(E2E/BridgeJoinAtFiles.lean); `restKey` (E2E/BridgePremWKey.lean); `atRecsZ` (E2E/BridgePremW.lean);
`canon` (E2E/BridgeCoins.lean); `RestOf` (E2E/BridgeAtRecs.lean); `proversOf`, `HidSmall`
(E2E/BridgePrivacy.lean); `ExactAt`, `honestProversByCopyNumber` (E2E/BridgeAlong.lean); `indexPrivacyNumbers`
(E2E/PremisesAtFiles.lean); `RyesZ` (E2E/TiedAtFiles.lean); `Sims.Good`, `StopsSmall`, `CoinsFit`,
`CoinNums` (Johnson/WholeKey/Premises.lean); `homeR`, `homeT`
(Johnson/Goal/Conditions/HomeAtWider.lean).

Hypotheses of `premW_link`. None of them is proved here. scope: Z is in scope
(`VerifierAndGoals.InScope Z = true`). hY: Yes implies the object's relation `RyesZ Z`. hit:
`AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)` (E2E/ItemsZero.lean): every stored table that a round of the
description declares is under the item 0. That is where `provG`, the prover structure of `famG`, has
the committer's columns (`Committer.proverAt` at 0, Johnson/Desc/ProofFile/Honest/CommitterAt.lean);
`itemsZero_of_data` proves hit wherever the description's `data` returns. hs1, hM, two bounds on
numbers: at most 688127 sessions a copy, at most 710324 copies. On the shell `offlineProverWithEncodedTable`, each as the
structure has it, written out, with Gs := all OOD seeds: gT, the field `T` of `Sims.Good`, at the
simulator sT and the error zT; pT, the field `T` of `StopsSmall`, at hT': the measure of the abort
set `Hid`, which may depend on the private input. On the session's prover: hx, `ExactAt` of the
family at the description's own instances (`honestProversByCopyNumber`), at the simulator simOne; hz', one measure:
`HidSmall` of `famG` at hO'. Both are asked at the relation `TiedIn` at Yes, ok and all OOD seeds
(hz' at what `instanceAsPlainRecord` writes). Seven on lengths and run values, p being the parameters of
`lettersZ Z c₀ m₀`. hlen: the length of `c.pre₀` and `c.ℓ` add up to `p.sMT`. okT, okL, okB: okV
holds of every pair (val₂ q2, val₃ q3), of v₀, and of every pair (run₂ r2, run₃ r3). lenT, lenL,
lenB, on a leaf's salt: at a run value of which okV holds and a string of length `p.sFS`, the length
of what startT (startL, startB) returns and `c.ℓ` add up to `p.sMT`. These three are asked at every
round's number, where `CoinsFit` asks them within the window.

Limits.
- The pair (c₀, m₀) is fixed before the hash function is drawn. The verifier of the release calls
  the compiled verifier at values of the hash function at public strings: the step from "at every
  fixed pair" to that scheme is not stated in Lean here. (E2E/BridgeDebtsTold.lean carries the
  conclusion, from the hypotheses at the pair (`allZeroDigest`, []), to the OOD-seed wire and the code of
  the answers of `homeT b Z` at every value of the public reading: `premW_link_told`. Its Limits say
  what that is worth.)
- Of the link's four clauses one has content: that its simulator has the honest output's
  distribution. The clause on its external strings holds by unfolding; its abort set `Hid` is empty
  at that term; its run values agree because this file sets one constant for both. The simulator is
  handed both OOD samples and the columns that the link's verifier reads of both tables (at most 62
  and 62).
- Of the three provers only the link's is a closed term. `offlineProverWithEncodedTable` and `famG` are shells over free
  parameters (a description, a book of coins, a prover structure, rows), tied to Z by nothing here.
  Of the description `descZ Zp Np cF` by itself only hit is asked, and hit does not read Z.
- zT (the error of the key file's simulator), hT' and hO' (the measures of the abort set `Hid` of
  the key file's prover and of the session's) are free parameters: at a number ≥ 1 the hypothesis
  with that number is vacuous.
- The public abort sets (`Bad`) have no number in `PremW` (Limits of E2E/BridgePrivacy.lean).
- The simulators sT and simOne are bound with Yes and ok, not before them: at an ok that holds at
  one index only they may lean on that index, and simOne also at such a Yes (Limits of
  E2E/BridgeJoinAtFiles.lean).
- What a caller puts into a field of R₀ that `restKey` or `canon` overwrites is dropped without
  notice.
- The limits of E2E/BridgePremWKey.lean and of the head of Johnson/LinkSim/AtHome/Home.lean (an
  honest verifier; the interactive protocol; one link) hold here too.
- `premW_link` shows that the types fit, on hypotheses not shown here; no property follows. No
  value is shown here to meet its hypotheses together. The field `good` of `linkFields_atZ` is the
  statement of `linkFieldsHome` on the link's interactive protocol (the second limit above), carried
  to every pair; it does not say that the index is hidden (the first limit of Home.lean's head).
  Beyond that, nothing on completeness, soundness or hiding follows from this file alone.
-/
import E2E.BridgePremWKey
import Johnson.LinkSim.AtHome.Home
import Johnson.Goal.Conditions.DepthsAtDescriptionDataAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Premises
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀ relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open _root_.Run (ckP)
open _root_.Compile (Params)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open OnBytes.WholeKey (PremW StopsSmall Sims CoinNums NumsW)
open OnBytes.LinkSim (LinkFields)
open OnBytes.LinkSim.AtHome (explicitLinkProver homeSim linkFieldsHome)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- The wiring at Z does not depend on the digest and the list of further digests: of
`lettersZ Z c₀ m₀` it reads only the depth of the key file's request tree, which is a number read
off `dataAtFiles flashProveData Z`. -/
theorem wiring_any (Z : PublicFiles) (c₁ : VerifiableInference.Digest) (m₁ : List (Iop.Dig 256))
    (c₂ : VerifiableInference.Digest) (m₂ : List (Iop.Dig 256)) :
    (lettersZ Z c₁ m₁).W = (lettersZ Z c₂ m₂).W := by
  unfold VerifiableInference.OnPublicFiles.InnerCompilerInputAndAnalysisFieldsAtFullSize.W
  rw [FlashProve.depthReqT_tOf, FlashProve.depthReqT_tOf]

/-- The explicit honest prover of the link, `explicitLinkProver b Z`, with its type stated at the library's
object `protocolAtFiles Z`. -/
abbrev linkProverAtFiles : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)) :=
  explicitLinkProver b Z

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
  (c : CoinNums (List Bool))
  (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
  (okV : ByteArray × ByteArray → Prop) (v₀ : ByteArray × ByteArray)
  (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)

/-- The parameters of the scheme's honest side (`AtRecs`) at the three provers; the link's run value
is the constant v₀. Of R₀ only these fields are read: dcT, dcL, b₀, capT, capL, capB, M, nm, rtail,
fill. `restKey` and `canon` overwrite the others: what a caller puts there is dropped without
notice. -/
abbrev atRecsAll :=
  atRecsZ Z Zp Np cF run₂ run₃ B G H (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
    (canon (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).p c
      (restKey Z Fx BT HT val₂ val₃ shT (linkProverAtFiles b Z) R₀ okV (fun _ => v₀) startT startL
        (fun _ => v₀))) id startB

/-- **The four clauses on the link hold at `atRecsAll`, with both error terms 0**, at the wiring of
every pair (c₀, m₀). -/
theorem linkFields_atZ (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    LinkFields (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀
      startT
      startL startB) (homeSim Z)
      (lettersZ Z c₀ m₀).W ok Gs 0 0 :=
  have h : LinkFields (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV
      v₀ startT startL startB) (homeSim Z) (lettersZ Z FlashProve.allZeroDigest []).W ok Gs 0 0 :=
    linkFieldsHome b Z _ v₀ rfl (fun _ => rfl) (fun _ => rfl) ok Gs
  wiring_any Z FlashProve.allZeroDigest [] c₀ m₀ ▸ h

/-- **All hypotheses of the statement of index privacy, with the link's prover filled in**: `PremW`
at the parameters of `lettersZ Z c₀ m₀`. This file's head says what is proved here and what stays a
hypothesis. -/
theorem premW_link (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (s1 : ℕ) (hs1 : s1 ≤ 688127) (zT hT' hO' : ℝ≥0∞)
    {ok : FullSizeMatrix → Prop} {simOne} {sT} (hM : R₀.M + 1 ≤ 710324)
    (gT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ ∉
            (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e) ∧
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).output (i, r, e) ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ) ≠
          sT ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ)
            ((protocolAtFiles Z).offline.extAns ((protocolAtFiles Z).recOf i r e)
              (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
                (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ) ((protocolAtFiles Z).encodeIndex i r))} ≤
                  zT)
    (pT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
            (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ hT')
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w (instanceAsPlainRecord a)) hO')
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True)))
    (hlen : c.pre₀.length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : okV v₀)
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startT v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startL v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startB v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT) :
    PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
      := 1)) (lettersZ Z c₀ m₀).p
      (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
        startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  have LF := linkFields_atZ c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀
    startT
    startL startB ok
    (fun _ => True)
  premW_key_own Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT (linkProverAtFiles b Z) scope hY hit c₀ m₀
    c s1 hs1 zT 0 hT' 0 hO' R₀ hM okV (fun _ => v₀) startT startL startB (fun _ => v₀) LF.ext
    LF.runVals
    (Fm₂ := famG Z Zp Np cF run₂ run₃ B G H) (Fm₃ := famG Z Zp Np cF run₂ run₃ B G H)
    ⟨pT, LF.stops, stopsB_of_small _ _ (famG Z Zp Np cF run₂ run₃ B G H) (lettersZ Z c₀ m₀).W hz'
      (validIn Z Zp Np cF run₂ run₃ B G H hY hit ok (fun _ => True))
      (hidZero_link (lettersZ Z c₀ m₀) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
        ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃)
          (shAt Zp Np cF) (extZ Z))⟩
    hz'
    ⟨gT, LF.good, goodB_of_exact _ _ (famG Z Zp Np cF run₂ run₃ B G H) (lettersZ Z c₀ m₀).W (hx.re
      instanceAsPlainRecord _
      id)
      (validIn Z Zp Np cF run₂ run₃ B G H hY hit ok (fun _ => True))
        (extIsEnc_famG Z Zp Np cF run₂ run₃
        B G H)⟩
    hx hlen okT (fun _ => okL) okB lenT lenL lenB

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.wiring_any
#print axioms AtPublicFiles.AtFiles.linkFields_atZ
#print axioms AtPublicFiles.AtFiles.premW_link
#print axioms AtPublicFiles.AtFiles.linkProverAtFiles
#print axioms AtPublicFiles.AtFiles.atRecsAll
