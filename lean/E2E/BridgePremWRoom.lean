-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgePremWRoom.lean: `premW_room` proves `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean: all hypotheses of the statement of index privacy) at three public
files Z, under the hypotheses that are listed below, at the wiring, the OOD-seed wire, the code of
the answers and the parameters of `lettersZ Z c₀ m₀`, at every digest c₀ and every list m₀ of
further digests (below: the pair). In it the errors and measures of the key file's prover and of the
session's (zT, zO, hT', hO') are free parameters: a prover that stops, or whose output differs from
a simulator's at a share of the verifier randomness, can meet the hypotheses with these numbers. The
three honest provers are those of `premW_link` (E2E/BridgePremWLink.lean). The first is `offlineProverWithEncodedTable`
(E2E/BridgePremWKey.lean), a prover structure built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes (below: the
shell `offlineProverWithEncodedTable`). The second is `linkProverAtFiles b Z`, the explicit honest prover of the link. The third is the
session's family `famG` (E2E/BridgeJoinAtFiles.lean), each prover of which is such a structure too.
General in Z within scope, in the pair and in the parameters of the two shells. Two theorems that
have 0 for some of the four numbers are of the same kind, and are not proved from this one:
`premW_link` (zO := 0, from `ExactAt`; hO' from a measure at the family, `HidSmall`) and
`premW_plain` (E2E/BridgeNoStop.lean: every measure of an abort set at 0). Both also ask that Yes
implies the object's relation `RyesZ Z`, and `ItemsZero` (E2E/ItemsZero.lean) of the description
`descZ Zp Np cF`; `premW_room` asks neither.

  `premW_room`: `PremW` at the wiring, OOD-seed wire, code of the answers and parameters named
    above, at `atRecsAll` (the parameters of the scheme's honest side at
    `proversOf (offlineProverWithEncodedTable …) (linkProverAtFiles b Z) (famG …)`), at the simulators sT, `homeSim Z` and sB, the range
    ok, Gs := all OOD seeds, the relation Yes, the coins' numbers c, and the numbers
    `indexPrivacyNumbers s1 zT 0 zO hT' 0 hO'`: the link's two error terms are 0. Proved: the fields that read no
    prover; the clauses on the external strings; the clauses on the run values; the link's clauses
    of `Sims.Good` and `StopsSmall`; the fields of `CoinsFit`, except what the seven hypotheses on
    lengths and run values say. Handed through from hypotheses: the key file's clause and the
    session's clause of `Sims.Good` and of `StopsSmall`

By what. `premW_iff` (E2E/PremisesAtFiles.lean) splits `PremW` into `NoProverSide`, the fields that
read no prover, and five more. `NoProverSide`: `noProverSide_atFiles` (same file), from scope, hM
and hs1. `ExtEnc`: `extEnc_join` (E2E/BridgeJoinAtFiles.lean), with `extIsEnc_obj`
(E2E/KeyBridgeFilled.lean) for the shell `offlineProverWithEncodedTable`. `RunVals`: `runVals_of` (E2E/BridgeAtRecs.lean),
with `runValsAt_obj` (E2E/KeyBridgeFilled.lean) for the shell `offlineProverWithEncodedTable` and `runVals_tied`
(E2E/BridgeTied.lean) for the session's prover. `Sims.Good` and `StopsSmall`: gT, gB, pT and pB, as
they are. The link's clause of each of these four structures is a field of `linkFields_atZ`
(E2E/BridgePremWLink.lean). `CoinsFit`: `coinsFit_canon` (E2E/BridgeCoins.lean), from the seven
hypotheses on lengths and run values. Definitions: `atRecsAll` (E2E/BridgePremWLink.lean); `restKey`
(E2E/BridgePremWKey.lean); `lettersZ`, `protocolAtFiles`, `descZ` (E2E/BridgeJoinAtFiles.lean); `canon`
(E2E/BridgeCoins.lean); `RestOf` (E2E/BridgeAtRecs.lean); `proversOf` (E2E/BridgePrivacy.lean);
`indexPrivacyNumbers` (E2E/PremisesAtFiles.lean); `homeSim` (Johnson/LinkSim/AtHome/SpecHome.lean); `Sims.Good`,
`StopsSmall`, `CoinsFit`, `CoinNums` (Johnson/WholeKey/Premises.lean).

Hypotheses of `premW_room`. None of them is proved here. scope: Z is in scope
(`VerifierAndGoals.InScope Z = true`). hs1, hM, two bounds on numbers: at most 688127 sessions a copy, at most
710324 copies. Four on provers, each as the structure has it, written out, with Gs := all OOD seeds.
gT: the field `T` of `Sims.Good`, on the shell `offlineProverWithEncodedTable` and the simulator sT, at the error zT. gB: its
field `B`, on the session's prover and the simulator sB, at the error zO. pT, pB: the fields `T` and
`B` of `StopsSmall`, at hT' and hO': the measures of these two provers' abort sets `Hid`, which may
depend on the private input. In gB and pB the session's prover at the number n is written
`(famG …).at n`; by unfolding that is the structures' `sessionAt` at the three provers
(`sessionAt_proversOf`, E2E/BridgePrivacy.lean). Seven on lengths and run values, p being the
parameters of `lettersZ Z c₀ m₀`. hlen: the length of `c.pre₀` and `c.ℓ` add up to `p.sMT`. okT,
okL, okB: okV holds of every pair (val₂ q2, val₃ q3), of v₀, and of every pair (run₂ r2, run₃ r3).
lenT, lenL, lenB, on a leaf's salt: at a run value of which okV holds and a string of length
`p.sFS`, the length of what startT (startL, startB) returns and `c.ℓ` add up to `p.sMT`. These three
are asked at every round's number, where `CoinsFit` asks them within the window.

Limits.
- The room that the four numbers give is room in the verifier randomness only. Each of the four
  clauses measures a set of verifier randomness: the set at which the prover stops (`Hid`), or the
  set on which the distribution of the honest output over the prover's coins and the simulator's
  distribution differ at all: there is no distance between distributions. Each is asked at every
  committer's randomness and every OOD seed. A stop or a fault at a small share of the verifier
  randomness costs that share. A fault whose chance over the coins depends on the private input at
  many verifier messages still drives the number to 1.
- The public abort sets (`Bad`) have no number: `PremW` measures only the abort sets `Hid`, which
  may depend on the private input (Limits of E2E/BridgePrivacy.lean). So for the public stops of a
  prover nothing has to be shown here, whatever their measure.
- The pair (c₀, m₀) is fixed before the hash function is drawn. The verifier of the release calls
  the compiled verifier at values of the hash function at public strings: the step from "at every
  fixed pair" to that scheme is not stated in Lean here. (E2E/BridgeDebtsTold.lean carries the
  conclusion of `premW_link`, from the hypotheses at the pair (`allZeroDigest`, []), to the OOD-seed wire
  and the code of the answers of `homeT b Z` at every value of the public reading:
  `premW_link_told`. Its Limits say what that is worth.)
- Yes and ok are free parameters with no hypothesis on them: none says that Yes implies the object's
  relation. At a range ok that holds of no index all four clauses, and the link's clauses of the
  same two structures, are vacuous; at a relation Yes that holds of nothing the session's two are.
  The simulators sT and sB are bound with Yes and ok, not before them: at an ok that holds at one
  index only they may lean on that index, and sB also at such a Yes (Limits of
  E2E/BridgeJoinAtFiles.lean).
- The four clauses are handed through: this file proves nothing of them. They are asked at every OOD
  seed (Gs := all OOD seeds), the session's two at the requests of Yes, and all four at verifier
  randomness with the test bits 0.
- Of the three provers only the link's is a closed term. `offlineProverWithEncodedTable` and `famG` are shells over free
  parameters (a description, a book of coins (`ProverCoinCounts`), a prover structure (`ProofFile.Honest.Prover`) and,
  for `famG`, the rows G (`Sides`)), tied to Z by nothing here. Of the description `descZ Zp Np cF`
  by itself nothing is asked.
- Of the link's four clauses one has content: that its simulator has the honest output's
  distribution. The clause on its external strings holds by unfolding; its abort set `Hid` is empty
  at that term; its run values agree because `atRecsAll` sets one constant for both. Its simulator
  is handed both OOD samples and the columns that the link's verifier reads of both tables.
- At a number ≥ 1 the clause with that number is vacuous.
- The limits of E2E/BridgePremWLink.lean, E2E/BridgePremWKey.lean and E2E/BridgeCoins.lean hold
  here.
- `premW_room` shows that the types fit and lists what is left to show; no property follows. No
  value is shown here to meet its hypotheses together. What the conclusion says of the link's prover
  `linkProverAtFiles b Z` is proved in E2E/BridgePremWLink.lean, whose head says what it is and what it is not.
  Beyond that, nothing on completeness, soundness or hiding follows from this file alone.
-/
import E2E.BridgePremWLink

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
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
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

/-- **All hypotheses of the statement of index privacy (`PremW`), with the errors and measures of
the key file's prover and of the session's as parameters**: at the parameters of `lettersZ Z c₀ m₀`.
This file's head says what is proved here, what is handed through and what stays a hypothesis. -/
theorem premW_room (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop} (s1 : ℕ)
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
    (pT : ∀ i r e, ok i → True →
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
      (startB v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT) :
    PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (lettersZ Z c₀ m₀).p
      (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
        startB)
      ⟨sT, homeSim Z, sB⟩ ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 zO hT' 0 hO') :=
  have LF := linkFields_atZ c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀
    startT startL startB ok
    (fun _ => True)
  (premW_iff _ _ _ _ _ _ _ _ _ _ _).2
    ⟨noProverSide_atFiles Z scope c₀ m₀ R₀.M s1 hM hs1 zT 0 zO hT' 0 hO' R₀.capT R₀.capL R₀.capB,
      extEnc_join Z Zp Np cF run₂ run₃ B G H (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT) LF.ext,
      runVals_of (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H)
        (canon (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).p c
          (restKey Z Fx BT HT val₂ val₃ shT (linkProverAtFiles b Z) R₀ okV (fun _ => v₀) startT startL
            (fun _ => v₀))) _ _ startB ok
        (runValsAt_obj Z Fx BT (dataAtFiles flashProveData Z).P HT val₂ val₃ shT _ ok) LF.runVals
        (fun i r e n x κ ρ =>
          runVals_tied Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P (G.prover H)
            (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) i r e n x κ ρ),
      ⟨gT, LF.good, gB⟩, ⟨pT, LF.stops, pB⟩,
      coinsFit_canon (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).p c (famG Z Zp Np cF run₂ run₃ B G H)
        (restKey Z Fx BT HT val₂ val₃ shT (linkProverAtFiles b Z) R₀ okV (fun _ => v₀) startT startL
          (fun _ => v₀)) _ _ startB hlen (fun κ => okT κ.1.2 κ.2.2) (fun _ => okL)
        (fun κ => okB κ.1.2 κ.2.2) lenT lenL lenB⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.premW_room
