-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeBothOfSentences.lean: `both_of_sentences` is `both_atLink` (E2E/BridgeBothAtLink.lean)
with its hypothesis `KeyFive` (E2E/BridgeNineCut.lean) proved from `AtPublicFiles.KeyBridge.Sentences`
(E2E/KeyBridge.lean), the structure that has the hypotheses on the key file's prover as named
fields. The conclusion is that of `both_atLink`, a conjunction at three public files Z and at one
value of all three honest provers: the acceptance side, `OnBytes.Prover.HonFit`
(Johnson/Prover/All/OfHonest.lean), and the privacy side, `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean): all hypotheses of the statement of index privacy. `Sentences` is
asked at the key file's prover of that value, `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean): a prover structure
built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here
fixes (below: the shell `offlineProverWithEncodedTable`). General in the parameters of `Sentences` other than its prover and
its wiring, and in those of `both_atLink` other than its FT, Zs, ζ and pT, which are set as follows.

  `both_of_sentences`: the conclusion of `both_atLink`, with four parameters set. The OOD seeds that
    are set aside on the acceptance side are forced: Zs := `asideOf GsK` (E2E/BridgeSeeds.lean), all
    seeds outside GsK, the set of OOD seeds of `Sentences`. The key file's fall (`Falls`: a set of
    verifier randomness that is set aside on the acceptance side) is `guardT` (E2E/KeyBridge.lean)
    of the fall FT of `Sentences`: FT, made empty at the seeds outside GsK. ζ := δ, a bound on the
    chance of a seed outside GsK. pT := zBK + zK + pFK

By what. Two calls: `both_atLink`, with `keyFive_of_out` (E2E/BridgeSeedsOut.lean) for its
hypothesis k. `keyFive_of_out` is `keyFive_of` (E2E/BridgeKeyFive.lean) with the name `SeedsOut`
for the hypothesis on the seeds' measure.

Hypotheses. Those of `both_atLink` but for k, with `asideOf GsK` for Zs in hthr and hf: the head of
E2E/BridgeBothAtLink.lean has a clause on each. In the place of k there are three. hK: `Sentences`
at the shell `offlineProverWithEncodedTable`, at the wiring `(lettersZ Z c₀ m₀).W`, the fall FT, the range okK of indices,
the set GsK of OOD seeds, and the bounds zK, zBK and pFK on the measures of the abort set `Hid`,
which may depend on the private input, of the public abort set `Bad`, and of a fall at each fixed
coin. hyK: every index that has a request of Yes is in okK. hδ: `SeedsOut`
(E2E/BridgeSeedsOut.lean): the chance that the OOD-seed wire `(lettersZ Z c₀ m₀).letters.Sd` gives a
seed outside GsK is at most δ.

Limits.
- The step from `both_atLink` shows that the types fit; no property follows. `Sentences` is shown
  here at no value of the parameters of the shell `offlineProverWithEncodedTable`: the one value that is stated in Lean to
  meet it with no hypothesis (`sentences_idle`, E2E/KeyBridge.lean) is at another prover, `idleT`.
- Three fields of `Sentences` are not used on the acceptance side (`exact`, `runVals`, `runForm`).
  The two clauses of the privacy side on the key file's prover stay hypotheses of their own (gT and
  pT'). `Sentences.good` and `Sentences.stops` (E2E/KeyBridge.lean) prove these two clauses from
  `Sentences`, at its own simulator simK, range okK and set GsK of OOD seeds; they are not called
  here.
- The two sides speak of different sets of OOD seeds: acceptance is stated outside `asideOf GsK`;
  the privacy side is stated at all seeds. Nothing ties the two ranges of indices, okK (of
  `Sentences`) and ok (of `PremW`), to each other.
- All limits of E2E/BridgeBothAtLink.lean, E2E/BridgeKeyFive.lean and E2E/BridgeSeeds.lean hold here
  too.
- What the conclusion says of the link's prover `linkProverAtFiles b Z` is proved by `both_atLink`; the head of
  E2E/BridgeBothAtLink.lean says it, with its limits. Beyond that, nothing on completeness,
  soundness or hiding follows from this file alone.
-/
import E2E.BridgeBothAtLink
import E2E.BridgeSeedsOut

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
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse)
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

/-- **`HonFit` and `PremW` at one value of the three provers, with `KeyFive` proved from
`Sentences`.** This file's head says what is proved and what is left to show. -/
theorem both_of_sentences (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop} (s1 : ℕ)
    (hs1 : s1 ≤ 688127) (zT zO hT' hO' : ℝ≥0∞) {ok : FullSizeMatrix → Prop} {sT} {sB}
    (hM : R₀.M + 1 ≤ 710324)
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
    (pT' : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ hT')
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
    {simK : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)} {TiedK TiedMK : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)}
    (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)) {okK : FullSizeMatrix → Prop}
    (GsK : (protocolAtFiles Z).OutOfDomainSeed → Prop) {RVK : Type} {pvK : Plains (protocolAtFiles Z).offline.shape → RVK}
    {rvK : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Coin → RVK} {okVK : RVK → Prop}
    {zK zBK pFK δ zB z pF : ℝ≥0∞}
    (hK : AtPublicFiles.KeyBridge.Sentences (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W simK TiedK
      TiedMK FT okK GsK pvK rvK okVK zK zBK pFK)
    (hyK : ∀ i x, Yes i x → okK i)
    (hδ : AtPublicFiles.KeyBridge.SeedsOut (lettersZ Z c₀ m₀).letters.Sd GsK δ)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G H) (Sv : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      (asideOf GsK)))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes (asideOf GsK) n w (instanceAsPlainRecord a)) pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
        (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _
          (AtPublicFiles.KeyBridge.guardT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (asideOf GsK) FT) (fun _ _ _ => ∅)
          (guardFall (asideOf GsK) (fallG Z Zp Np cF run₂ run₃ B G H)))
        (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes (asideOf GsK) δ (zBK + zK + pFK) 0
        (zB + z + pF) ∧
      PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
        := 1)) (lettersZ Z c₀ m₀).p (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃
        shT c R₀ okV v₀ startT startL startB) ⟨sT, homeSim Z, sB⟩ ok (fun _ => True) Yes c (indexPrivacyNumbers
        s1 zT 0 zO hT' 0 hO') :=
  both_atLink c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
    startB scope s1 hs1 zT zO
    hT' hO' hM gT gB pT' pB hlen okT okL okB lenT lenL lenB live L hY
    (AtPublicFiles.KeyBridge.guardT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (asideOf GsK) FT) (asideOf GsK)
    (AtPublicFiles.KeyBridge.keyFive_of_out hK (lettersZ Z c₀ m₀).letters.Sd hyK hδ) h₀ Q Sv hthr hb hz hf

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.both_of_sentences
