-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeDebtsTold.lean: `premW_link` (E2E/BridgePremWLink.lean), `premW_of_owed`
(E2E/BridgeOwedLink.lean) and `premW_of_debts` (E2E/BridgeDebts.lean) once more, with the conclusion
stated at the compiler's input `homeR b Z` (an `InnerCompilerInput`) and at the structure `homeT b Z` (a
`LayoutsByPublicReading`: what of an input depends on the public reading, as functions of its value). Both are
defined in Johnson/Goal/Conditions/HomeAtWider.lean. The conclusion is `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean): all hypotheses of the statement of index privacy. It has two forms
here. Form (1): at the four fields `queryLayout`, `seedQueries`, `answerCode` and `compilerParameters` of `homeR b Z`. Form (2): with
`(homeT b Z).Sd dg` and `(homeT b Z).cA dg` in the place of `seedQueries` (the OOD phase's compilation data;
in other heads of this folder: the OOD-seed wire) and `answerCode` (the code of the answers), at every value
dg of the public reading (`D8`: a digest and a list of digests), at one value of provers, simulators
and numbers for all dg. These are the terms in which E2E/LinkLaidPrivacy.lean and
E2E/LinkLaidTold.lean state `PremW`. The three theorems are taken at one pair: the digest `allZeroDigest`
(all bits false, Johnson/Goal/Conditions/BindsAtThe.lean) and the empty further reading []. Each of
their other parameters is a parameter here.

  `premW_link_home`, `premW_home_of_owed`, `premW_home_of_debts`: the three theorems at the pair
    (allZeroDigest, []), with the conclusion in form (1); the hypotheses are theirs, word for word
  `premW_link_told`, `premW_told_of_debts`: `premW_link` and `premW_of_debts` at that pair, with the
    conclusion in form (2), at every dg; the hypotheses are theirs, word for word. `premW_of_owed`
    is not stated in form (2)
  `premW_home_of_letters`: the first step: `PremW` at the wiring, the OOD-seed wire and the
    parameters of `lettersZ Z allZeroDigest []` (E2E/BridgeJoinAtFiles.lean) and at the code of the answers
    `OnBytes.Flat.codeA`, for whatever provers, simulators, ranges, relation and numbers, is `PremW`
    in form (1)
  `premW_told_of_letters`: both steps: the same hypothesis gives `PremW` in form (2), at every dg

By what. `premW_home_of_letters`: the proof is the hypothesis itself: its four arguments are the
four fields of `homeR b Z` by unfolding. `premW_told_of_letters`: after it, one call of
`premW_told_of_home` (E2E/LinkLaidToldAsks.lean). That theorem is one direction of the equivalence
`premW_of_cfg` (same file): `(homeT b Z).Sd dg` is `(homeR b Z).seedQueries` with the field `cfg` set to
[dg.1] (`seed_is`, same file), `(homeT b Z).cA dg` is `(homeR b Z).answerCode` (`code_told`,
E2E/LinkLaidTold.lean), and `PremW` does not read `cfg` (`premW_cfg`: see Limits). Each of the five
others: one call of its theorem at (allZeroDigest, []), then one of the two steps.

Hypotheses. The heads of the three theorems' files say at length what each one is. Of
`premW_link_home` and `premW_link_told`. scope: Z is in scope (`VerifierAndGoals.InScope`). hY: Yes holds only
where the object's relation `RyesZ Z` (E2E/TiedAtFiles.lean) does. hit: every stored table that a
round of the description `descZ Zp Np cF` declares is under the item 0 (`ItemsZero`,
E2E/ItemsZero.lean). hs1, hM: s1 ≤ 688127 and `R₀.M + 1` ≤ 710324. gT, pT: the fields `T` of
`Sims.Good` and of `StopsSmall` (Johnson/WholeKey/Premises.lean), written out, at all OOD seeds.
They are the clauses on the key file's prover `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean), a prover structure
built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here
fixes: the first with its simulator sT at the error zT; the second: the measure of its abort set
`Hid`, which may depend on the private input, is at most hT'. hz': `HidSmall`
(E2E/BridgePrivacy.lean): the measure of the abort set `Hid` of the session's family `famG`
(E2E/BridgeJoinAtFiles.lean; built by `honestBatchProverOfFile` likewise), which may depend on the private input,
is at most hO', at the inputs of `TiedIn` (same file) at Yes, ok and all OOD seeds. hx: `ExactAt`
(E2E/BridgeAlong.lean) of the family at the description's own instances (`honestProversByCopyNumber`), at the simulator
simOne and the same `TiedIn`: outside `Hid` the honest output is the simulator's. hlen, okT, okL,
okB, lenT, lenL, lenB: seven statements on lengths and run values. Of `premW_home_of_owed`: these
without hit and hx, and four more. live: the IOP's own test on the public files accepts
(`protocolDataWellFormed (asDescriptionFiles Z) = true`). L: `LaidAt` (Johnson/P5J/LaidOpens.lean) ties the description to Z;
`premW_of_owed` has `ItemsZero` from its field `data`. hO: `Owed`
(Johnson/Desc/ProofFile/Honest/Owed.lean) at the description, the book of coins B (`ProverCoinCounts`), the
muted rows `G.mute` (G: `Sides`: for each sub-protocol the prover's part and its simulator), the
relation `relAt` of `RyesZ Z`, and the prover structure
`(cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H`: H with the committer's columns as its stored table
at the item 0 only, and with the committer's key (`Committer.proverAt`,
Johnson/Desc/ProofFile/Honest/CommitterAt.lean). hE: the test `G.owns` returns true. Of
`premW_home_of_debts` and `premW_told_of_debts`. d: `PremWDebts` at the pair (allZeroDigest, []): the
hypotheses of `premW_of_owed` as the fields of one structure.

Limits. `PremW` does not read the field through which dg enters: it is unchanged when the field
`cfg` of the OOD phase's compilation data is replaced by any list (`premW_cfg`,
E2E/LinkLaidToldAsks.lean). The second step needs no hypothesis for that reason: form (2) says no
more than form (1), and it says nothing on what the scheme does with dg. The hypotheses are stated
at the one pair (allZeroDigest, []): no hypothesis reads dg. In form (2) dg is a variable of the theorem:
the step to a scheme that takes it from the hash function's values at public strings is not stated
here (the Limits of E2E/BridgePremWLink.lean say it of the pair (c₀, m₀)). All limits of
E2E/BridgePremWLink.lean, E2E/BridgeOwedLink.lean, E2E/BridgeDebts.lean and
E2E/LinkLaidToldAsks.lean hold here. The theorems show that the types fit and list what is left to
show; no property follows. No value is shown to meet the hypotheses together. What the conclusion
says of the link's prover `linkProverAtFiles b Z` is proved in E2E/BridgePremWLink.lean, whose head says what it
is and what it is not. Beyond that, nothing on completeness, soundness or hiding follows from this
file alone.
-/
import E2E.BridgeDebts
import E2E.LinkLaidToldAsks

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
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open _root_.Compile (Params)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse Owed relAt)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed homeR homeT allZeroDigest)
open OnBytes.K.Arm.Pub (D8)
open OnBytes.WholeKey (PremW StopsSmall Sims CoinNums NumsW AtRecs)
open OnBytes.LinkSim.AtHome (explicitLinkProver homeSim)
open AtPublicFiles.LinkLaid.Told (premW_told_of_home)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **The first step**: the wiring, the OOD-seed wire and the parameters of `lettersZ Z allZeroDigest []`,
and the code of the answers `OnBytes.Flat.codeA`, are the fields `queryLayout`, `seedQueries`, `compilerParameters` and `answerCode` of
`homeR b Z`, by unfolding. So `PremW` at the former is `PremW` at the latter. -/
theorem premW_home_of_letters
    {a : AtRecs 256 (protocolAtFiles Z) (List Bool) (filesAt Z).annT (filesAt Z).annL} {Sm : Sims (protocolAtFiles Z)}
    {ok : FullSizeMatrix → Prop} {Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop} {Ryes : FullSizeMatrix → XF → Prop}
    {c : CoinNums (List Bool)} {N : NumsW}
    (h : PremW (lettersZ Z allZeroDigest []).W (lettersZ Z allZeroDigest []).letters.Sd
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (lettersZ Z allZeroDigest []).p a Sm ok Gs Ryes c N) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a Sm ok Gs Ryes c N := h

/-- **Both steps**: the same hypothesis gives `PremW` at `(homeT b Z).Sd dg` and
`(homeT b Z).cA dg`, at every value dg of the public reading. -/
theorem premW_told_of_letters (dg : D8)
    {a : AtRecs 256 (protocolAtFiles Z) (List Bool) (filesAt Z).annT (filesAt Z).annL} {Sm : Sims (protocolAtFiles Z)}
    {ok : FullSizeMatrix → Prop} {Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop} {Ryes : FullSizeMatrix → XF → Prop}
    {c : CoinNums (List Bool)} {N : NumsW}
    (h : PremW (lettersZ Z allZeroDigest []).W (lettersZ Z allZeroDigest []).letters.Sd
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (lettersZ Z allZeroDigest []).p a Sm ok Gs Ryes c N) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd dg) ((homeT b Z).cA dg) (homeR b Z).compilerParameters a Sm ok Gs Ryes c N :=
  premW_told_of_home b Z dg (premW_home_of_letters b Z h)

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

/-- **`premW_link` with its conclusion at the four fields of `homeR b Z`**: its hypotheses at the
pair (allZeroDigest, []). -/
theorem premW_link_home (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (s1 : ℕ) (hs1 : s1 ≤ 688127) (zT hT' hO' : ℝ≥0∞)
    {ok : FullSizeMatrix → Prop} {simOne} {sT} (hM : R₀.M + 1 ≤ 710324)
    (gT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ ∉
            (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e) ∧
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).output (i, r, e) ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ) ≠
          sT ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ)
            ((protocolAtFiles Z).offline.extAns ((protocolAtFiles Z).recOf i r e)
              (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
                (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ)
              ((protocolAtFiles Z).encodeIndex i r))} ≤ zT)
    (pT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
            (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ hT')
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w (instanceAsPlainRecord a)) hO')
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True)))
    (hlen : c.pre₀.length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : okV v₀)
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startT v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startL v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startB v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters
      (atRecsAll allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
        startL startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  premW_home_of_letters b Z
    (premW_link allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB scope hY hit s1 hs1 zT hT' hO' hM gT pT hz' hx hlen okT okL okB lenT lenL lenB)

/-- **`premW_of_owed` with its conclusion at the four fields of `homeR b Z`**: its hypotheses at the
pair (allZeroDigest, []). -/
theorem premW_home_of_owed (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x) (s1 : ℕ) (hs1 : s1 ≤ 688127) (zT hT' hO' : ℝ≥0∞)
    {ok : FullSizeMatrix → Prop} {sT} (hM : R₀.M + 1 ≤ 710324)
    (gT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ ∉
            (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e) ∧
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).output (i, r, e) ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ) ≠
          sT ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ)
            ((protocolAtFiles Z).offline.extAns ((protocolAtFiles Z).recOf i r e)
              (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
                (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ)
              ((protocolAtFiles Z).encodeIndex i r))} ≤ zT)
    (pT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
            (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ hT')
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w (instanceAsPlainRecord a)) hO')
    (hO : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) instanceAsPlainRecord))
    (hE : G.owns = true)
    (hlen : c.pre₀.length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : okV v₀)
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startT v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startL v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startB v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters
      (atRecsAll allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
        startL startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  premW_home_of_letters b Z
    (premW_of_owed allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB scope live L hY s1 hs1 zT hT' hO' hM gT pT hz' hO hE hlen okT okL okB lenT lenL
      lenB)

/-- **`premW_of_debts` with its conclusion at the four fields of `homeR b Z`**: from `PremWDebts` at
the pair (allZeroDigest, []). -/
theorem premW_home_of_debts {Yes : FullSizeMatrix → XF → Prop} {ok : FullSizeMatrix → Prop}
    {sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)} {s1 : ℕ} {zT hT' hO' : ℝ≥0∞}
    (d : PremWDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT' hO') :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters
      (atRecsAll allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
        startL startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  premW_home_of_letters b Z
    (premW_of_debts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB d)

/-- **`premW_link` with its conclusion at `(homeT b Z).Sd dg` and `(homeT b Z).cA dg`**: its
hypotheses at the pair (allZeroDigest, []); its conclusion at every value dg of the public reading. -/
theorem premW_link_told (dg : D8) (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (s1 : ℕ) (hs1 : s1 ≤ 688127) (zT hT' hO' : ℝ≥0∞)
    {ok : FullSizeMatrix → Prop} {simOne} {sT} (hM : R₀.M + 1 ≤ 710324)
    (gT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ ∉
            (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e) ∧
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).output (i, r, e) ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ) ≠
          sT ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ)
            ((protocolAtFiles Z).offline.extAns ((protocolAtFiles Z).recOf i r e)
              (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
                (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ)
              ((protocolAtFiles Z).encodeIndex i r))} ≤ zT)
    (pT : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
            (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z allZeroDigest []).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ hT')
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w (instanceAsPlainRecord a)) hO')
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True)))
    (hlen : c.pre₀.length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : okV v₀)
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startT v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startL v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = (lettersZ Z allZeroDigest []).p.sFS →
      (startB v i b s).length + c.ℓ = (lettersZ Z allZeroDigest []).p.sMT) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd dg) ((homeT b Z).cA dg) (homeR b Z).compilerParameters
      (atRecsAll allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
        startL startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  premW_told_of_letters b Z dg
    (premW_link allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB scope hY hit s1 hs1 zT hT' hO' hM gT pT hz' hx hlen okT okL okB lenT lenL lenB)

/-- **`premW_of_debts` with its conclusion at `(homeT b Z).Sd dg` and `(homeT b Z).cA dg`**: from
`PremWDebts` at the pair (allZeroDigest, []); its conclusion at every value dg of the public reading. -/
theorem premW_told_of_debts (dg : D8) {Yes : FullSizeMatrix → XF → Prop} {ok : FullSizeMatrix → Prop}
    {sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)} {s1 : ℕ} {zT hT' hO' : ℝ≥0∞}
    (d : PremWDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT' hO') :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd dg) ((homeT b Z).cA dg) (homeR b Z).compilerParameters
      (atRecsAll allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
        startL startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  premW_told_of_letters b Z dg
    (premW_of_debts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB d)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.premW_home_of_letters
#print axioms AtPublicFiles.AtFiles.premW_told_of_letters
#print axioms AtPublicFiles.AtFiles.premW_link_home
#print axioms AtPublicFiles.AtFiles.premW_home_of_owed
#print axioms AtPublicFiles.AtFiles.premW_home_of_debts
#print axioms AtPublicFiles.AtFiles.premW_link_told
#print axioms AtPublicFiles.AtFiles.premW_told_of_debts
