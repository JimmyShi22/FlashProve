-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeOwedLink.lean: two theorems of this folder joined into one: `exactAt_of_owed`
(E2E/BridgeExact.lean) proves the hypothesis `ExactAt` of `premW_link` (E2E/BridgePremWLink.lean).
The conclusion is `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean): all hypotheses of the
statement of index privacy, at three public files Z, at the parameters of `lettersZ Z c₀ m₀`, at
every digest c₀ and further reading m₀, under the hypotheses that are listed below. One statement;
its proof only calls other theorems. E2E/BridgeDebts.lean, which imports this file, has the same
theorem with the hypotheses as the fields of one structure.

The provers and simulators in the conclusion. The link's prover `linkProverAtFiles b Z` and its simulator
`homeSim Z` (Johnson/LinkSim/AtHome/SpecHome.lean) are closed terms: written out, with no parameter
but b and Z. The session's simulator is a term over the rows G (`Sides`: for each sub-protocol the
prover's part and its simulator). The key file's prover `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean) is a prover
structure built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that
nothing here fixes (below: the shell `offlineProverWithEncodedTable`): a description Fx, a book of coins BT (`ProverCoinCounts`), a
prover structure HT (`ProofFile.Honest.Prover`), and val₂, val₃, shT. So is each prover of the session's
family `famG` (E2E/BridgeJoinAtFiles.lean), from a description `descZ Zp Np cF`, a book of coins B,
a prover structure H, the rows G, and run₂, run₃; of these the hypothesis `LaidAt` ties the
description to Z. The key file's simulator sT is a free parameter.

  `premW_of_owed`: `PremW` at the wiring, the OOD-seed wire and the parameters of
    `lettersZ Z c₀ m₀`, at the three provers `offlineProverWithEncodedTable`, `linkProverAtFiles b Z` and `famG` (`atRecsAll`,
    E2E/BridgePremWLink.lean), at the range ok, the relation Yes, Gs := all OOD seeds and the
    numbers `indexPrivacyNumbers s1 zT 0 0 hT' 0 hO'` (E2E/PremisesAtFiles.lean). The session's simulator is no
    longer a parameter: it is `simZ` (E2E/BridgeExact.lean), made of the description, the book of
    coins, the data, the rows' simulators, the key's map, the public seam and the honest prover's
    public abort set `Bad`; it is read at the instance that `instanceAsPlainRecord` writes

Compared with `premW_link`. No longer there: the hypotheses `ExactAt` and `ItemsZero`, and the
parameter for the session's simulator. New: `Owed` (Johnson/Desc/ProofFile/Honest/Owed.lean) at the
muted rows `G.mute` (Johnson/Desc/ProofFile/Honest/Law/Rule/Mute.lean) and at the object's whole
relation `RyesZ Z`; the test `G.owns`; the IOP's own test on the public files; `LaidAt`.

By what. One call of `premW_link`. Its hypothesis `ExactAt` is `exactAt_of_owed`, at Gs := all OOD
seeds. That theorem's hypothesis that no declared round asks for more non-zero elements than
elements is proved here, by `nonZero_atFiles` (E2E/BridgeNonZero.lean). The hypothesis `ItemsZero`
of `premW_link` (E2E/ItemsZero.lean: every stored table that a round of the description declares is
under the item 0) is proved by `itemsZero_of_data` (same file) from the field `data` of `LaidAt`.

Hypotheses. On the public files. scope: Z is in scope (`VerifierAndGoals.InScope`). live: the IOP's own test
on the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`). L: `LaidAt` (Johnson/P5J/LaidOpens.lean)
ties the description `descZ Zp Np cF` to Z. On the relation. hY: Yes holds only where the object's
relation `RyesZ Z` (E2E/TiedAtFiles.lean) does. On numbers. hs1, hM: at most 688127 sessions a copy
and 710324 copies. On the key file's prover. gT, pT: the fields `T` of `Sims.Good` and of
`StopsSmall`, written out word for word: the clauses on the shell `offlineProverWithEncodedTable`, the first with its
simulator sT at the error zT, the second at the measure hT'. On the session's prover. hO: `Owed` at
the description, the book of coins B and the rows `G.mute`, at the prover structure
`(cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H` and at the relation `relAt`
(Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) of `RyesZ Z`. That structure is H with the
committer's columns as its stored table at the item 0 only, and with the committer's key
(`Committer.proverAt`, Johnson/Desc/ProofFile/Honest/CommitterAt.lean). The relation holds of what
`instanceAsPlainRecord` writes for a request of `RyesZ Z` at the index, with the OOD sample of the committer's
randomness at some OOD seed. hE: `G.owns = true`, a Bool-valued test: the owner of every entry of
`B.ahead` is a part of a row (Johnson/Desc/ProofFile/Honest/Law/Rule/Session.lean). hz': `HidSmall`
(E2E/BridgePrivacy.lean): the measure of the abort set `Hid` of `famG`, which may depend on the
private input, is at most hO', at the inputs of `TiedIn` (E2E/BridgeJoinAtFiles.lean) at Yes, ok and
all OOD seeds. On lengths and run values, seven statements; p stands for the parameters of
`lettersZ Z c₀ m₀`. hlen: the length of `c.pre₀` and `c.ℓ` add up to `p.sMT`. okT, okL, okB: okV
holds of every run value `(val₂ q2, val₃ q3)` of the key file's prover, of the constant v₀ that
`atRecsAll` sets as the link's run value, and of every run value `(run₂ r2, run₃ r3)` of the
session's prover. lenT, lenL, lenB: at a run value of okV, every round number and a first salt of
the length `p.sFS`, the length of the start and `c.ℓ` add up to `p.sMT`.

Limits.
- The theorem shows that the types fit and lists what is left to show; no property follows. No value
  is shown to meet the hypotheses on the key file's prover and on the session's: whether all
  hypotheses can hold together is not shown here, so the theorem may be vacuous.
- A way to meet the hypotheses that makes the statement vacuous and shows in no number: the public
  abort set `Bad`. `PremW` has no number for the honest provers' public abort sets. Not stated in
  Lean, and followed through the definitions in part only: provers whose public abort set holds
  every verifier randomness, and which so never answer, may meet all hypotheses at
  zT = hT' = hO' = 0: nothing among the hypotheses is seen to exclude that (the Limits of
  E2E/BridgePrivacy.lean say it of `OneExact` and `HidSmall`). What gives the public abort set a
  number is on the acceptance side (`BadSmall`, E2E/BridgeAccept.lean): E2E/BridgeBothOfDebts.lean
  has the acceptance side (`HonFit`) and the privacy side (`PremW`) at one value of the three
  provers.
- A second such way: provers that never abort and are never accepted: a prover structure that has no
  part for any sub-protocol (`Placed`), rows that lack the prover's part for a sub-protocol, or
  parts whose messages the first step rejects: fixed substitutes are shown, none of that lies in an
  abort set, and `PremW` has no number for the share of rejected runs (the Limits of
  E2E/BridgeDebts.lean and of E2E/BridgeNoStop.lean). Not stated in Lean.
- The range ok is a free parameter, and the key file's simulator sT is a free parameter next to it.
  The key file's clauses of `Sims.Good` and `StopsSmall` are asked at the indices of ok only: at a
  range with one index sT may hold that index, and `PremW` then says nothing on hiding it. What
  E2E/BridgeExact.lean excludes (as far as `RyesZ Z` holds at more than one index, which is not
  shown there) it excludes for the session's simulator only. Whoever uses this theorem says which
  range it is, and that it holds two indices or more (the head of Johnson/WholeKey/Statement.lean).
- All OOD seeds: the hypotheses on the key file's prover and on the session's are asked at every OOD
  seed, seed by seed.
- All limits of E2E/BridgeExact.lean and of E2E/BridgePremWLink.lean hold here, and those of the
  file of the lemma on one slot that `exactAt_of_owed` rests on (`ProofFile.Honest.one_exact_atItem_mute`,
  Johnson/Desc/ProofFile/Honest/Law/Rule/TiedAtItem.lean; its head takes over the limits of
  Tied.lean, OneAt.lean and Mute.lean in the same folder). Among them: (c₀, m₀) are fixed before the
  hash function is drawn; `offlineProverWithEncodedTable` and `famG` are shells over free parameters; zT, hT' and hO' are
  free parameters, and at a number ≥ 1 the hypothesis with that number is vacuous; at a muted row
  two fields of `Good` (Johnson/Desc/ProofFile/Honest/Side.lean), `plays` and `acc`, ask nothing, on
  purpose.
- What the conclusion says of the link's prover `linkProverAtFiles b Z` is proved in E2E/BridgePremWLink.lean,
  whose head says what it is and what it is not. Beyond that, nothing on completeness, soundness or
  hiding follows from this file alone.
-/
import E2E.BridgeExact
import E2E.BridgePremWLink
import E2E.BridgeNonZero

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
open FlashProve (flashProveData protocolDataWellFormed)
open OnBytes.WholeKey (PremW StopsSmall Sims CoinNums NumsW)
open OnBytes.LinkSim.AtHome (explicitLinkProver homeSim)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

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

/-- **`PremW` at `lettersZ Z c₀ m₀`, with `ExactAt` proved from `Owed` at the muted rows.** `PremW`:
all hypotheses of the statement of index privacy. From `ExactAt`, `premW_link` has the session's
clause of `Sims.Good`. The head of this file says what is proved here, what is left to show, and the
limits. -/
theorem premW_of_owed (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x) (s1 : ℕ) (hs1 : s1 ≤ 688127) (zT hT' hO' : ℝ≥0∞)
    {ok : FullSizeMatrix → Prop} {sT} (hM : R₀.M + 1 ≤ 710324)
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
    (hO : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) instanceAsPlainRecord))
    (hE : G.owns = true)
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
        (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') :=
  premW_link c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
    startB scope hY (AtPublicFiles.AtZero.itemsZero_of_data L.data) s1 hs1 zT hT' hO' hM gT pT hz'
    (exactAt_of_owed Z Zp Np cF run₂ run₃ B G H scope live L hY ok (fun _ => True) hO hE
      (nonZero_atFiles Z Zp Np cF scope L))
    hlen okT okL okB lenT lenL lenB

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.premW_of_owed
