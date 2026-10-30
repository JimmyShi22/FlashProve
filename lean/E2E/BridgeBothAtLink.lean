-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeBothAtLink.lean: `both_atLink` proves one conjunction at three public files Z, under the
hypotheses that are listed below. Its first part is `OnBytes.Prover.HonFit`
(Johnson/Prover/All/OfHonest.lean), which is what the prover of a whole request asks of three honest
provers and three families of falls (`Falls`: sets of verifier randomness that are set aside on the
acceptance side). Its second part is `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean): all
hypotheses of the statement of index privacy. Both are stated at one value of the three honest
provers, `proversOf (offlineProverWithEncodedTable …) (linkProverAtFiles b Z) (famG …)`, and at one relation Yes. The second of the three
is written out: `linkProverAtFiles b Z` (E2E/BridgePremWLink.lean) is the explicit honest prover of the link.
The first is `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean), a prover structure built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes (below: the
shell `offlineProverWithEncodedTable`). The third is the session's family `famG` (E2E/BridgeJoinAtFiles.lean), each prover of
which is such a structure too. All is stated at the wiring, the OOD-seed wire, the code of the
answers and the parameters of `lettersZ Z c₀ m₀`, at every digest c₀ and every list m₀ of further
digests (below: the pair).

  `both_atLink`: `HonFit` at that value, with FT, no fall at the link and `guardFall Zs (fallG …)`
    for the three families of falls, at Yes, at the OOD seeds Zs that are set aside, and at the
    bounds ζ, pT, 0 and zB + z + pF; and `PremW` at `atRecsAll …`, at the simulators sT, `homeSim Z`
    and sB, the range ok, Gs := all OOD seeds, the same Yes, the coins' numbers c and the numbers
    `indexPrivacyNumbers s1 zT 0 zO hT' 0 hO'`
  `provers_atRecsAll`: the field `Hs` of `atRecsAll …` (E2E/BridgePremWLink.lean: the parameters of
    the scheme's honest side, `OnBytes.WholeKey.AtRecs`) is that value of the three provers: by
    unfolding. So `PremW` is stated at the provers at which `HonFit` is

What is proved of the link's prover on both sides, with no hypothesis on it. On the acceptance side:
its four clauses of `HonFit` (one has content: the clause on acceptance, `accL`, at every coin; the
abort set is empty at that term). On the privacy side: its clauses of `Sims.Good` and `StopsSmall`,
at 0 and 0, the clause on its external strings, and the clause on its run values (one constant v₀ is
set for both sides of that clause: it asks nothing). So of one term both are theorems, in scope,
where the IOP's own test on the public files accepts: that the link's verifier of the interactive
protocol accepts it in every run in which all proof-of-work tests are passed; and that the output of
a named simulator, which is handed both OOD samples and the columns that the link's verifier reads
of both tables, has the distribution of that prover's output, at verifier randomness whose
proof-of-work test bits are 0. In the conclusion of `both_atLink` the first is stated at the indices
that have a request of Yes and at OOD seeds outside Zs, the second at the indices of ok.

By what. Two calls. `HonFit`: `honFit_atFiles` (E2E/BridgeJoinAtFiles.lean), at the compiled
verifier's own structure of the OOD-seed wire (`num_letters`, same file). Its hypothesis `NineFit`
(E2E/BridgeAccept.lean) comes from `nineFit_link` (E2E/BridgeNineLink.lean), which takes `KeyFive`
and has the link's four clauses from `homeSide_accepted` (Johnson/LinkSim/AtHome/HomeAccepted.lean).
`PremW`: `premW_room` (E2E/BridgePremWRoom.lean), which has the link's four clauses from
`linkFields_atZ` (E2E/BridgePremWLink.lean). Definitions: `protocolAtFiles`, `lettersZ`, `descZ`, `fallG`,
`TiedYes`, `TiedOut`, `PlainAt`, `ServesAt`, `ThreadsAt` (E2E/BridgeJoinAtFiles.lean); `proversOf`,
`HidSmall` (E2E/BridgePrivacy.lean); `fallsOf`, `guardFall`, `BadSmall`, `FallSmall`
(E2E/BridgeAccept.lean); `KeyFive` (E2E/BridgeNineCut.lean); `RestOf` (E2E/BridgeAtRecs.lean);
`indexPrivacyNumbers` (E2E/PremisesAtFiles.lean); `RyesZ` (E2E/TiedAtFiles.lean); `homeSim`
(Johnson/LinkSim/AtHome/SpecHome.lean); `Sims.Good`, `StopsSmall`, `CoinNums`
(Johnson/WholeKey/Premises.lean).

Hypotheses of `both_atLink`. They are those of the two calls together. On the public files. scope: Z
is in scope (`VerifierAndGoals.InScope Z = true`). live: the IOP's own test on the public files accepts
(`protocolDataWellFormed (asDescriptionFiles Z) = true`). L: `LaidAt` (Johnson/P5J/LaidOpens.lean), which ties the description
`descZ Zp Np cF` to Z. On the relation. hY: Yes implies the object's relation `RyesZ Z`. On the
shell `offlineProverWithEncodedTable`. k, for acceptance: `KeyFive`: the four clauses of `HonFit` on the key file's prover,
at the falls FT and the bound pT, and the bound ζ on the measure of the OOD seeds that are set
aside. gT and pT', for privacy: the field `T` of `Sims.Good`, at the simulator sT and the error zT,
and the field `T` of `StopsSmall`, at hT' (the measure of the abort set `Hid`, which may depend on
the private input), each written out. On the session's prover, for acceptance, as in
`honFit_atFiles`, whose file's head says what each asks. h₀: the description's first test accepts
one written instance. Q: `PlainAt`. Sv: `ServesAt`. hthr: `ThreadsAt` at `TiedOut`. hb, hz, hf,
three measures: `BadSmall` at zB, `HidSmall` at `TiedYes` and z, `FallSmall` at `TiedOut` and pF. On
the session's prover, for privacy. gB and pB: the field `B` of `Sims.Good`, at the simulators sB and
the error zO, and the field `B` of `StopsSmall`, at hO', each written out, with `(famG …).at n` for
the session's prover at the number n. On numbers. hs1, hM: at most 688127 sessions a copy, at most
710324 copies. Seven on lengths and run values, as in `premW_room`: hlen, okT, okL, okB, lenT, lenL,
lenB.

Limits.
- Of the three provers only the link's is a closed term: `offlineProverWithEncodedTable` and `famG` are shells over free
  parameters (of these only the description `descZ Zp Np cF` is tied to Z, by L). No value is shown
  to meet the hypotheses on these two, on either side.
- ok, the range of indices of the privacy side, is a wholly free parameter, and nothing ties it to
  Yes: at a range ok that holds at no index the clauses of `PremW` on simulators, abort sets and run
  values (`good`, `stops`, `runVals`) are vacuous, while `HonFit` keeps its whole content. The two
  sides speak of different sets of OOD seeds: Zs, what is set aside on the acceptance side, is a
  free parameter; the privacy side is stated at all seeds.
- The session's clause of `StopsSmall` (pB) is asked, though at hO' := z it follows from hz, with hY
  and L (by `stopsB_of_small`, E2E/BridgePrivacy.lean, as in `premW_link`): one hypothesis more than
  is needed.
- The conclusion is a conjunction of two structures of hypotheses of two conditional theorems.
  Neither theorem is called here: neither completeness nor index privacy of anything is concluded.
- Acceptance of the link is at the interactive protocol; nothing is said of a compiled link's file.
- The pair (c₀, m₀) is fixed before the hash function is drawn.
- All limits of the three files that are called (E2E/BridgeJoinAtFiles.lean,
  E2E/BridgeNineLink.lean, E2E/BridgePremWRoom.lean) hold here too.
- The clauses on the link's prover are statements on the link's interactive protocol, as said above;
  the one on its simulator does not say that the index is hidden (the first limit of the head of
  Johnson/LinkSim/AtHome/Home.lean). Beyond that, nothing on completeness, soundness or hiding
  follows from this file alone.
-/
import E2E.BridgePremWRoom
import E2E.BridgeNineLink

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

/-- The field `Hs` of `atRecsAll …`, the three provers among the parameters of the scheme's honest
side, is `proversOf (offlineProverWithEncodedTable …) (linkProverAtFiles b Z) (famG …)`: by unfolding. -/
theorem provers_atRecsAll :
    (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
      startB).Hs =
      proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H) := rfl

/-- **`HonFit` and `PremW` at one value of all three provers.** This file's head says what is proved
and what stays a hypothesis. -/
theorem both_atLink (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop} (s1 : ℕ)
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
    (FT) (Zs) {ζ pT zB z pF : ℝ≥0∞}
    (k : KeyFive (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT Zs
      (lettersZ Z c₀ m₀).letters.Sd Yes ζ pT)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G H) (Sv : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      Zs))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
        (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _ FT (fun _ _ _ => ∅)
          (guardFall Zs (fallG Z Zp Np cF run₂ run₃ B G H)))
        (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes Zs ζ pT 0 (zB + z + pF) ∧
      PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
        := 1)) (lettersZ Z c₀ m₀).p (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃
        shT c R₀ okV v₀ startT startL startB) ⟨sT, homeSim Z, sB⟩ ok (fun _ => True) Yes c (indexPrivacyNumbers
        s1 zT 0 zO hT' 0 hO') :=
  ⟨honFit_atFiles Z Zp Np cF run₂ run₃ B G H scope live L c₀ m₀ (lettersZ Z c₀ m₀).letters.Sd
    (num_letters Z c₀ m₀) hY
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) FT (fun _ _ _ => ∅) Zs
      (nineFit_link c₀ m₀ b Z scope live (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (famG Z Zp Np cF run₂ run₃
                                 B G H) (fallG Z Zp Np cF run₂ run₃ B G H) FT Zs
        k) h₀ Q Sv hthr hb hz hf,
    premW_room c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
      startB scope s1 hs1 zT zO
      hT' hO' hM gT gB pT' pB hlen okT okL okB lenT lenL lenB⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.provers_atRecsAll
#print axioms AtPublicFiles.AtFiles.both_atLink
