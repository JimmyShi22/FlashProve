-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeOneBundle.lean: `both_of_one_bundle` proves, at three public files Z, the conjunction that
`both_of_sentences` (E2E/BridgeBothOfSentences.lean) proves. Its first part is the acceptance side:
`OnBytes.Prover.HonFit` (Johnson/Prover/All/OfHonest.lean), which is what the prover of a whole
request asks of three honest provers and three families of falls (`Falls`: sets of verifier
randomness that are set aside on the acceptance side). Its second part is the privacy side:
`OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean), all hypotheses of the statement of index
privacy. Both are stated at one value of the three provers,
`proversOf (offlineProverWithEncodedTable ...) (linkProverAtFiles b Z) (famG ...)`. The key file's prover `offlineProverWithEncodedTable`
(E2E/BridgePremWKey.lean) is a prover structure built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes (below: the
shell `offlineProverWithEncodedTable`). Here every hypothesis of `both_of_sentences` on it follows from one value hK of
`AtPublicFiles.KeyBridge.Sentences` (E2E/KeyBridge.lean: a structure whose fields are hypotheses on the key
file's prover; below: the bundle), but for one, okT (see Limits). In `both_of_sentences` the bundle
serves the acceptance side only. The hypothesis `PlainAt` (E2E/BridgeJoinAtFiles.lean) is replaced
by its clauses other than `nonZero`. General in the parameters of `both_of_sentences` that are not
set below.

  `both_of_one_bundle`: `HonFit` at that value; the falls are FT for the key file's prover, none for
    the link's and `fallG …` for the session's, the first under `guardT` and the third under
    `guardFall`, at `asideOf` of all OOD seeds; at Yes, with that `asideOf` for the OOD seeds that
    are set aside, and at the bounds 0, zBK + zK + pFK, 0 and zB + z + pF (for the seeds that are
    set aside, the key file's prover, the link's and the session's). And `PremW` at `atRecsAll …`,
    at the simulators sT, `homeSim Z` and sB, the range ok, all OOD seeds, the same Yes, the coins'
    numbers c and the numbers `indexPrivacyNumbers s1 0 0 zO zK 0 hO'`: the key file's clause of `Sims.Good` is
    at error 0, its clause of `StopsSmall` at zK

What is set so that one bundle serves both sides. `Sentences` is taken at all OOD seeds (its
parameter Gs holds of every seed), at the range ok of `PremW` and at the simulator sT of `PremW`. So
both sides now speak of the same OOD seeds (all: nothing is set aside on the acceptance side:
`asideOf` of all seeds is empty, and ζ is 0) and of one range: every index with a request of Yes
lies in ok (hyK).

By what. One call of `both_of_sentences`, with all OOD seeds for its set GsK, ok for its range okK
and sT for its simulator simK. These hypotheses of it are proved. gT, the key file's clause of
`Sims.Good` (the field `T`), at error 0: `goodT_of_exact` (E2E/KeyBridge.lean), from the fields
`exact`, `tied` and `ext` of hK. pT', the key file's clause of `StopsSmall` (the field `T`), at zK:
`stopsT_of_small` (same file), from `hidSmall`, `tiedAll` and `hidZero`. `SeedsOut`, the bound on
the chance of an OOD seed outside the set, at 0: `seedsOut_all` (E2E/BridgeSeedsOut.lean).
`PlainAt`: `plainAt_of_five` (E2E/BridgeNonZero.lean), which has the clause `nonZero` from scope and
L. `both_of_sentences` takes the key file's clauses of `HonFit` from hK by `keyFive_of_out`
(E2E/BridgeSeedsOut.lean). Definitions: `guardT`, `SimT`, `TiedT`, `FallT` (E2E/KeyBridge.lean);
`asideOf` (E2E/BridgeSeeds.lean); `guardFall` (E2E/BridgeAccept.lean); `Sims.Good`, `StopsSmall`,
`CoinsFit` (Johnson/WholeKey/Premises.lean); for the others see the head of
E2E/BridgeBothAtLink.lean.

Hypotheses. On the public files. scope: Z is in scope (`VerifierAndGoals.InScope Z = true`). live: the IOP's
own test on the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`). L: `LaidAt`
(Johnson/P5J/LaidOpens.lean), which ties the description `descZ Zp Np cF` to Z. On the relation. hY:
Yes implies the object's relation `RyesZ Z`. hyK: every index with a request of Yes is in ok. On the
shell `offlineProverWithEncodedTable`. hK: the bundle, at the wiring `(lettersZ Z c₀ m₀).W`, the simulator sT, the relations
TiedK and TiedMK, the falls FT, the range ok and all OOD seeds; its bounds are zK for the measure of
the abort set `Hid`, which may depend on the private input, zBK for that of the public abort set
`Bad`, and pFK for that of a fall at each fixed coin. okT: see Limits. On the session's prover and
its description, for acceptance, as in `honFit_atFiles` (E2E/BridgeJoinAtFiles.lean, whose head says
what each asks). h₀: the description's first test accepts one written instance. plainSeal, halved,
rooted, width, ready₁: the clauses of `PlainAt` other than `nonZero`. Sv: `ServesAt`. hthr:
`ThreadsAt` at `TiedOut`. hb, hz, hf, three measures: `BadSmall` at zB, `HidSmall` at `TiedYes` and
z, `FallSmall` at `TiedOut` and pF. On the session's prover, for privacy. gB and pB: the field `B`
of `Sims.Good`, at the simulators sB and the error zO, and the field `B` of `StopsSmall`, at hO',
each written out. On numbers. hs1, hM: at most 688127 sessions a copy, at most 710324 copies. On
lengths and run values, as in `premW_room` (E2E/BridgePremWRoom.lean): hlen, okL, okB, lenT, lenL,
lenB.

Limits.
- The theorem shows that the types fit; no property follows (on the link's prover see the last
  limit). No value of the parameters of the shell `offlineProverWithEncodedTable` is shown here to meet `Sentences`. At all
  OOD seeds `Sentences` has its hardest form: the clause on acceptance (`acc`), the clause on the
  simulator (`exact`) and the measures are asked at every seed, seed by seed, with no mean over
  seeds and no seed set aside: one seed at which the honest run cannot go on forces zK or pFK up,
  and here nothing can take it out. The way out is stated in Lean elsewhere: a set Gs of seeds with
  `NoProverSide.restrict` (E2E/PremisesAtFiles.lean) into `premW_key` (E2E/BridgePremWKey.lean).
- Not all comes from the bundle. okT stays a hypothesis of its own: at all values of the two codes
  val₂ and val₃ of the shell `offlineProverWithEncodedTable`, the pair of run values is of the right form (`okV`). The
  clauses of `PremW` on coins ask this of the run values that the shell's coins give (the field
  `okT` of `CoinsFit`). It is the bundle's field `runForm` at other parameters (rvK and okVK): one
  statement is asked twice, and neither proves the other here. Two fields of the bundle are not used
  (`runVals`, `runForm`), so its parameters RVK, pvK, rvK and okVK, which only these two read, play
  no part. The bundle asks more than has to be shown: E2E/BridgeKeyEight.lean, which imports this
  file, proves it at the shell `offlineProverWithEncodedTable` from fewer hypotheses (`sentences_keyZ`), among them okT, from
  which it has `runForm`.
- "Error 0" at the key file's clause of `Sims.Good` is no result by itself: `OneExact` is a field of
  the bundle (`exact`), and that clause has no number for the measure of the public abort set `Bad`
  (the head of E2E/KeyBridge.lean).
- Of the session's prover everything stays a hypothesis, and two hypotheses are harder than in
  `both_of_sentences` at a smaller set of seeds: `ThreadsAt` and the `FallSmall` that goes with it
  (hthr, hf) are now asked at every OOD seed (`TiedOut` at `asideOf` of all seeds). The list: its
  clauses of `Sims.Good` and `StopsSmall` (gB, pB); okB; `ServesAt`, `ThreadsAt`, three measures
  (hb, hz, hf); the clauses of `PlainAt` that read it (halved, rooted, ready₁). Of its description:
  one accept of the first test (h₀), and the clauses plainSeal and width of `PlainAt`.
- That `asideOf` of all seeds is empty is not stated in this file: the conclusion keeps `guardT`,
  `guardFall` and `asideOf`. E2E/BridgeNoneAside.lean has the equations.
- All limits of E2E/BridgeBothOfSentences.lean, E2E/BridgeNonZero.lean and E2E/KeyBridge.lean hold
  here too, but for what the first says of two sets of OOD seeds, of two ranges that nothing ties,
  and of the key file's two clauses of the privacy side as hypotheses of their own.
- The clauses of the conclusion on the link's prover are those of `both_atLink`: statements on the
  link's interactive protocol; the head of E2E/BridgeBothAtLink.lean says what they are and what
  they do not say. Beyond that, nothing on completeness, soundness or hiding follows from this file
  alone.
-/
import E2E.BridgeBothOfSentences
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

/-- **`HonFit` and `PremW` at one value of all three provers, with one value of `Sentences` for the
key file's prover.** This file's head says what is proved and what stays a hypothesis. -/
theorem both_of_one_bundle (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop} (s1 : ℕ)
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
    {TiedK TiedMK : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)}
    (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    {RVK : Type} {pvK : Plains (protocolAtFiles Z).offline.shape → RVK}
    {rvK : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Coin → RVK} {okVK : RVK → Prop}
    {zK zBK pFK zB z pF : ℝ≥0∞}
    (hK : AtPublicFiles.KeyBridge.Sentences (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W sT TiedK
      TiedMK FT ok (fun _ => True) pvK rvK okVK zK zBK pFK)
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
        (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _
          (AtPublicFiles.KeyBridge.guardT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (asideOf (L := protocolAtFiles Z) fun _ => True)
            FT) (fun _ _ _ => ∅)
          (guardFall (asideOf (L := protocolAtFiles Z) fun _ => True) (fallG Z Zp Np cF run₂ run₃ B G H)))
        (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes (asideOf (L := protocolAtFiles Z) fun _ => True) 0
        (zBK + zK + pFK) 0
        (zB + z + pF) ∧
      PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
        := 1)) (lettersZ Z c₀ m₀).p (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃
        shT c R₀ okV v₀ startT startL startB) ⟨sT, homeSim Z, sB⟩ ok (fun _ => True) Yes c (indexPrivacyNumbers
        s1 0 0 zO zK 0 hO') :=
  both_of_sentences c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
    startL startB scope s1
    hs1 0 zO zK hO' hM
    (AtPublicFiles.KeyBridge.goodT_of_exact (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂
                                                     run₃ B G H) (lettersZ Z c₀ m₀).W hK.exact
      hK.tied hK.ext)
    gB
    (AtPublicFiles.KeyBridge.stopsT_of_small (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂
                                                     run₃ B G H) (lettersZ Z c₀ m₀).W
      hK.hidSmall hK.tiedAll hK.hidZero)
    pB hlen okT okL okB lenT lenL lenB live L hY FT (fun _ => True) hK hyK
    (AtPublicFiles.KeyBridge.seedsOut_all _) h₀
    (plainAt_of_five Z Zp Np cF B G H scope L plainSeal halved rooted width ready₁) Sv hthr hb hz hf

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.both_of_one_bundle
