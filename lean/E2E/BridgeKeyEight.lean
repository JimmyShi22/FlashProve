-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeKeyEight.lean: at three public files Z, `AtPublicFiles.KeyBridge.Sentences` (E2E/KeyBridge.lean: one
structure of all the hypotheses that that file defines by name for the key file's honest prover) is
proved from eight hypotheses, at the prover `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean) and at all OOD seeds.
`offlineProverWithEncodedTable` is a prover structure built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from
parameters that nothing here fixes (below: the shell `offlineProverWithEncodedTable`). These fields of `Sentences` need no
hypothesis of their own there: `ext`, `badZero`, `hidZero` and `runVals` are theorems at that shell
(E2E/KeyBridgeFilled.lean), and `tiedAll` is the same proposition as `tied`. The field `runForm`
follows from okT, the hypothesis on the form of the key file's run values from which the clause
`okT` of `CoinsFit` (the field `coins` of `PremW`) is proved too: it is one statement, and it is
asked once. With that value of `Sentences`, and under the further hypotheses that are listed below,
the acceptance side and the privacy side follow at one value of all three honest provers. The
acceptance side is `OnBytes.Prover.HonFit`: what the prover of a whole request asks of three honest
provers and three families of falls. The privacy side is `OnBytes.WholeKey.PremW`: all hypotheses of
the statement of index privacy. The file is for whoever has to show the hypotheses on the key file's
prover. `sentences_keyZ` is general in Z; both theorems are general in the parameters of the shell
`offlineProverWithEncodedTable`, and in the digest c₀ and the list m₀ of further digests of `lettersZ Z c₀ m₀`.

A fall (`FallT`, E2E/KeyBridge.lean) is a set of verifier randomness, at a private input, an
instance and a coin of the prover's, that is set aside on the acceptance side. An OOD seed that is
set aside is one at which `HonFit` asks no acceptance.

  `sentences_keyZ`: `Sentences` at the shell `offlineProverWithEncodedTable`, at the wiring `(lettersZ Z c₀ m₀).W`, at all
    OOD seeds (Gs is all seeds, and one relation TiedK is both Tied and TiedM), at the two maps
    `pvKey` and `rvKey` (E2E/KeyBridgeFilled.lean) for the run values, from eight hypotheses:
    `OneExact`, `ValidTied`, `FallZero`, `HidSmall`, `BadSmall`, `FallSmall`, `AccAtTied` and okT
  `both_of_eight`: `both_of_one_bundle` (E2E/BridgeOneBundle.lean) at that value: `HonFit` and
    `PremW`, both at `proversOf` of the shell `offlineProverWithEncodedTable`, the explicit honest prover `linkProverAtFiles b Z` of the
    link, and the session's family `famG`. All that either side asks of the key file's prover comes
    from these eight. `HonFit` is concluded at the falls themselves (FT, no fall at the link,
    `fallG`), with no OOD seed set aside, at the bounds 0 (the seeds set aside), zBK + zK + pFK (the
    key file's prover), 0 (the link's) and zB + z + pF (the session's). `PremW` is concluded at the
    simulators sT, `homeSim Z` and sB, at the range ok, at all OOD seeds and at the numbers
    `indexPrivacyNumbers s1 0 0 zO zK 0 hO'`

By what. `sentences_keyZ` fills the structure field by field. `extIsEnc_obj`, `badZero_obj`,
`hidZero_obj` and `runValsAt_obj` (E2E/KeyBridgeFilled.lean) are `ext`, `badZero`, `hidZero` and
`runVals`. kTied is both `tied` and `tiedAll`. okT, at the two components of the coin that `rvKey`
reads, is `runForm`. The other six hypotheses are the fields. `both_of_eight` is one call of
`both_of_one_bundle`, which concludes `HonFit` at the falls under `guardT` and `guardFall` and at
`asideOf` of all seeds, and one call of `honFit_noneAside` (E2E/BridgeNoneAside.lean), which
rewrites these to the falls themselves and to the empty set. Definitions: `OneExact`, `ValidTied`,
`FallZero`, `AccAtTied`, `SimT`, `TiedT`, `FallT`, and `HidSmall`, `BadSmall`, `FallSmall` for one
prover (E2E/KeyBridge.lean; written here with `AtPublicFiles.KeyBridge.` before them); `BadSmall`, `FallSmall`
for a family, `fallsOf` (E2E/BridgeAccept.lean); `HidSmall` for a family, `proversOf`
(E2E/BridgePrivacy.lean); `asideOf` (E2E/BridgeSeeds.lean); `linkProverAtFiles`, `atRecsAll`
(E2E/BridgePremWLink.lean); `protocolAtFiles`, `lettersZ`, `descZ`, `provG`, `famG`, `fallG`, `TiedYes`,
`TiedOut`, `PlainAt`, `ServesAt`, `ThreadsAt` (E2E/BridgeJoinAtFiles.lean); `RestOf`
(E2E/BridgeAtRecs.lean); `indexPrivacyNumbers` (E2E/PremisesAtFiles.lean); `RyesZ` (E2E/TiedAtFiles.lean);
`homeSim` (Johnson/LinkSim/AtHome/SpecHome.lean); `HonFit` (Johnson/Prover/All/OfHonest.lean);
`PremW`, `CoinsFit`, `CoinNums`, `Sims.Good`, `StopsSmall` (Johnson/WholeKey/Premises.lean).

Hypotheses. The eight, on the shell `offlineProverWithEncodedTable`, in both theorems. TiedK, a free parameter, is a relation
between a private input (index, committer's randomness, OOD seed) and an OOD sample; below, an input
is tied where TiedK holds. kExact: `OneExact`: at tied inputs, at every verifier randomness outside
the abort set `Hid`, which may depend on the private input, the honest output is that of the
simulator sT. kTied: `ValidTied`: every index in the range ok, with every committer's randomness and
every OOD seed, is tied to its own OOD sample. kFallZero: `FallZero`: if verifier randomness with
its proof-of-work test bits set to 0 lies in a fall of FT, then the verifier randomness itself lies
in that fall or in the abort set. kHid, kBad, kFall, three measures: of `Hid` at tied inputs, at
most zK; of the public abort set `Bad`, at most zBK; of a fall of FT at tied inputs, at each fixed
coin, at most pFK. kAcc: `AccAtTied`: at tied inputs and at every coin, `AccLaw`
(Johnson/Prover/Law/Defs.lean: the interactive verifier accepts the strategy's own run, whatever the
nonces, where all proof-of-work tests are passed) outside the abort set and the fall at that coin.
okT: okV holds of `(val₂ q2, val₃ q3)` at all q2 and q3.

Further hypotheses of `both_of_eight`: those of `both_of_one_bundle` other than okT and its value of
`Sentences`. On the public files. scope: Z is in scope (`VerifierAndGoals.InScope Z = true`). live: the IOP's
own test on the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`). L: `LaidAt`
(Johnson/P5J/LaidOpens.lean), which ties the description `descZ Zp Np cF` to Z. On the relation. hY:
Yes implies the object's relation `RyesZ Z`. hyK: every index that has a request of Yes is in ok. On
the session's prover. gB and pB: the field `B` of `Sims.Good`, at the simulators sB and the error
zO, and the field `B` of `StopsSmall`, at hO', each written out. okB: okV holds of
`(run₂ r2, run₃ r3)` at all r2 and r3. halved, rooted, ready₁: the fields of `PlainAt` that read
that prover. Sv: `ServesAt`. hthr: `ThreadsAt` at `TiedOut`. hb, hz, hf, three measures: `BadSmall`
at zB, `HidSmall` at `TiedYes` and z, `FallSmall` at `TiedOut` and pF. On its description. h₀: the
first test `okStart` accepts one written instance. plainSeal, width: two more fields of `PlainAt`
(its sixth, `nonZero`, is proved within `both_of_one_bundle`: `plainAt_of_five`,
E2E/BridgeNonZero.lean). On numbers. hs1, hM: at most 688127 sessions a copy, at most 710324 copies.
On lengths and run values. hlen: the length of `c.pre₀` and `c.ℓ` add up to `p.sMT`, where p is
`(lettersZ Z c₀ m₀).p`. okL: okV holds of v₀, the link's constant run value. lenT, lenL, lenB: at
run values of which okV holds and at a string of `p.sFS` bits, the length of what startT, startL and
startB return and `c.ℓ` add up to `p.sMT`. The heads of E2E/BridgeJoinAtFiles.lean and
E2E/BridgeBothAtLink.lean say more on what these ask.

Limits.
- Both theorems show that the types fit; no property follows (on the link's prover see the last
  limit). None of the eight is shown here at any parameters of the shell `offlineProverWithEncodedTable`. `OneExact` and
  `AccAtTied` are the two heavy ones: the statement on the simulator and the statement on
  acceptance.
- All is asked at every OOD seed, seed by seed, with no mean over the seeds: one seed at which the
  honest run cannot go on forces zK or pFK up, and here nothing can take that seed out. The way out
  is stated in Lean elsewhere: a set Gs of seeds, with `NoProverSide.restrict`
  (E2E/PremisesAtFiles.lean) into `premW_key` (E2E/BridgePremWKey.lean).
- The same holds of the session's prover here: `ThreadsAt` and its `FallSmall` are asked at every
  OOD seed (`TiedOut` at `asideOf` of all seeds, which sets no seed aside). All that Hypotheses
  lists on that prover and on its description is asked; none of it is proved here.
- The error 0 of the key file's simulator (the first 0 in `indexPrivacyNumbers s1 0 0 zO zK 0 hO'`; the field `T`
  of `Sims.Good`) is no result by itself: `OneExact` is a hypothesis, and the measure of the public
  abort set `Bad` has no number in that clause (Limits of E2E/BridgeOneBundle.lean and
  E2E/KeyBridge.lean).
- lenT, lenL and lenB are asked at every round's number; `CoinsFit` asks them only of a round within
  the window. The hypotheses are stronger than the clauses.
- All limits of E2E/KeyBridgeFilled.lean and E2E/KeyBridge.lean hold here too, and so do those of
  E2E/BridgeOneBundle.lean except two: here okT is asked once, and the conclusion has no guard and
  sets no OOD seed aside.
- The clauses on the link's prover in the conclusion of `both_of_eight` are statements on the link's
  interactive protocol. They are taken over from `both_atLink` (E2E/BridgeBothAtLink.lean), whose
  head says what they say and what they do not. Beyond that, nothing on completeness, soundness or
  hiding follows from this file alone.
-/
import E2E.BridgeOneBundle
import E2E.BridgeNoneAside

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
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse halvedAll sealPlain rootedAll ready)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open OnBytes.Prover (HonFit)
open OnBytes.WholeKey (PremW CoinNums sessionAt)
open OnBytes.LinkSim.AtHome (homeSim)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
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

/-- **`Sentences` at the shell `offlineProverWithEncodedTable`, at all OOD seeds, from eight hypotheses.** -/
theorem sentences_keyZ {sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)} {ok : FullSizeMatrix → Prop}
    {TiedK : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)} (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    {zK zBK pFK : ℝ≥0∞}
    (kExact : AtPublicFiles.KeyBridge.OneExact (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) sT TiedK)
    (kTied : AtPublicFiles.KeyBridge.ValidTied TiedK ok fun _ => True)
    (kFallZero : AtPublicFiles.KeyBridge.FallZero (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT)
    (kHid : AtPublicFiles.KeyBridge.HidSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) TiedK zK)
    (kBad : AtPublicFiles.KeyBridge.BadSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) zBK)
    (kFall : AtPublicFiles.KeyBridge.FallSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) FT TiedK pFK)
    (kAcc : AtPublicFiles.KeyBridge.AccAtTied (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT TiedK)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) :
    AtPublicFiles.KeyBridge.Sentences (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W sT TiedK TiedK FT
      ok (fun _ => True)
      (pvKey (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).G.rec₀) (rvKey BT val₂ val₃) okV zK zBK pFK
        where
  exact := kExact
  tied := kTied
  tiedAll := kTied
  ext := extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT
  badZero := badZero_obj Z Fx BT (dataAtFiles flashProveData Z).P _ _ HT _ shT _
  hidZero := hidZero_obj Z Fx BT (dataAtFiles flashProveData Z).P _ _ HT _ shT _
  fallZero := kFallZero
  hidSmall := kHid
  badSmall := kBad
  fallSmall := kFall
  runVals := runValsAt_obj Z Fx BT (dataAtFiles flashProveData Z).P HT val₂ val₃ shT _ ok
  runForm := fun κ => okT κ.1.2 κ.2.2
  acc := kAcc

/-- **`HonFit` and `PremW` at one value of the three provers, with all that either asks of the key
file's prover from the eight hypotheses of `sentences_keyZ`.** The head of this file says what each
hypothesis asks, and which of them are on the key file's prover and on the session's. -/
theorem both_of_eight (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop} (s1 : ℕ)
    (hs1 : s1 ≤ 688127) (zO hO' : ℝ≥0∞) {ok : FullSizeMatrix → Prop} {sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)} {sB}
    (hM : R₀.M + 1 ≤ 710324)
    (gB : ∀ n i r e x, ok i → True → Yes i x →
      pr (unif (Rho (protocolAtFiles Z).onlineBatch.loc.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
              (TypedOracleCompiler.Compile.Batch.Cms.wBC (lettersZ Z c₀ m₀).W).sh ρ ∉
            ((famG Z Zp Np cF run₂ run₃ B G H).at n).Hid (i, r, e) (x, (protocolAtFiles Z).recOf i r e) ∧
          ((famG Z Zp Np cF run₂ run₃ B G H).at n).output (i, r, e) (x, (protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
              (TypedOracleCompiler.Compile.Batch.Cms.wBC (lettersZ Z c₀ m₀).W).sh ρ) ≠
          sB n (x, (protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
              (TypedOracleCompiler.Compile.Batch.Cms.wBC (lettersZ Z c₀ m₀).W).sh ρ)
            ((protocolAtFiles Z).onlineBatch.loc.extAns (x, (protocolAtFiles Z).recOf i r e)
              (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
              (TypedOracleCompiler.Compile.Batch.Cms.wBC (lettersZ Z c₀ m₀).W).sh ρ) ((protocolAtFiles Z).encodeIndex i r))} ≤
                zO)
    (pB : ∀ n i r e x, ok i → True → Yes i x →
      pr (unif (Rho (protocolAtFiles Z).onlineBatch.loc.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann
              (TypedOracleCompiler.Compile.Batch.Cms.wBC (lettersZ Z c₀ m₀).W).sh ρ ∈
          ((famG Z Zp Np cF run₂ run₃ B G H).at n).Hid (i, r, e) (x, (protocolAtFiles Z).recOf i r e)} ≤ hO')
    (hlen : c.pre₀.length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : okV v₀)
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startT v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startL v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startB v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hY : ∀ i x, Yes i x → RyesZ Z i x)
    {TiedK : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)}
    (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    {zK zBK pFK zB z pF : ℝ≥0∞}
    (kExact : AtPublicFiles.KeyBridge.OneExact (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) sT TiedK)
    (kTied : AtPublicFiles.KeyBridge.ValidTied TiedK ok fun _ => True)
    (kFallZero : AtPublicFiles.KeyBridge.FallZero (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT)
    (kHid : AtPublicFiles.KeyBridge.HidSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) TiedK zK)
    (kBad : AtPublicFiles.KeyBridge.BadSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) zBK)
    (kFall : AtPublicFiles.KeyBridge.FallSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) FT TiedK pFK)
    (kAcc : AtPublicFiles.KeyBridge.AccAtTied (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT TiedK)
    (hyK : ∀ i x, Yes i x → ok i)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (plainSeal : sealPlain (descZ Zp Np cF) = true)
    (halved : halvedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true)
    (rooted : rootedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true)
    (width : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, t.sh.W = 2 ^ frS.P.v)
    (ready₁ : ∃ w₀ rc x k R, ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R)
    (Sv : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      (asideOf (L := protocolAtFiles Z) fun _ => True)))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes (asideOf (L := protocolAtFiles Z) fun _ => True) n w
        (instanceAsPlainRecord a)) pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
        (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _ FT (fun _ _ _ => ∅)
          (fallG Z Zp Np cF run₂ run₃ B G H))
        (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes (fun _ _ => ∅) 0 (zBK + zK + pFK) 0
        (zB + z + pF) ∧
      PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
        := 1)) (lettersZ Z c₀ m₀).p (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃
        shT c R₀ okV v₀ startT startL startB) ⟨sT, homeSim Z, sB⟩ ok (fun _ => True) Yes c (indexPrivacyNumbers
        s1 0 0 zO zK 0 hO') :=
  have h := both_of_one_bundle c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀
    startT startL startB
    scope s1 hs1 zO hO' hM gB pB hlen okT okL okB lenT lenL lenB live L hY FT
    (sentences_keyZ c₀ m₀ Z Fx BT HT val₂ val₃ shT okV FT kExact kTied kFallZero kHid kBad kFall
      kAcc
      okT)
    hyK h₀ plainSeal halved rooted width ready₁ Sv hthr hb hz hf
  ⟨honFit_noneAside h.1, h.2⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.sentences_keyZ
#print axioms AtPublicFiles.AtFiles.both_of_eight
