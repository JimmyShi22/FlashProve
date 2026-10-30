-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgePremW.lean: a term of `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean: all
hypotheses of the statement of index privacy, Johnson/WholeKey/Statement.lean) at three public files
Z, under the hypotheses that are listed below. Its three honest provers are
`proversOf hT hL (famG …)`. The third, the session's prover, is the family `famG` of
E2E/BridgeJoinAtFiles.lean, which is built by `ProofFile.Honest.honestBatchProverOfFile` from a description (the IOP of
the proof file as written in Lean: `descZ Zp Np cF`), a book of coins B (`ProverCoinCounts`), rows G (`Sides`:
for each sub-protocol the prover's part and its simulator) and a prover structure H
(`ProofFile.Honest.Prover`). hT and hL, the key file's prover and the link's, are free parameters. The
term is there so that Lean checks that the pieces fit: the fields of `PremW` that read no prover
(`NoProverSide`, E2E/PremisesAtFiles.lean), those on provers and simulators
(E2E/BridgeJoinAtFiles.lean, E2E/BridgeAtRecs.lean), and the field on coins (`CoinsFit`). General in
Z and in the parameters of `famG`. The description is not tied to Z here: `LaidAt`
(Johnson/P5J/LaidOpens.lean) is not asked, and of (Zp, Np, cF) only hit is (see Hypotheses). The
five fields of `PremW` outside `NoProverSide` do not read the object's decision (`isLocal`, in
`NoProverSide`, does).

  `premW_atFiles`: `PremW (lettersZ Z c₀ m₀).W S cA p (atRecsZ …) ⟨sT, sL, …⟩ ok Gs Yes c N`, where
    the third simulator, the session's, is simOne read through `instanceAsPlainRecord`. It holds at the wiring of
    every pair of a digest c₀ and a further reading m₀, at every relation Yes that implies the
    object's own relation `RyesZ Z`, at every range ok of indices and at every set Gs of OOD seeds.
    As far as the fields of `PremW` read the session's prover: `ext` and `runVals` are proved.
    Stated in other words, not proved: `good` (from `ExactAt`, at error 0) and `stops` (from the
    measure in hz'). Of `coins` nothing is proved here (E2E/BridgeAtRecs.lean has two of its
    clauses, `kB_of` and `okB_of`; neither is called)
  `atRecsZ …`: an abbreviation: the value of `AtRecs` (the three honest provers and the other
    parameters of the scheme's honest side) at `proversOf hT hL (famG …)`: `atRecsOf`
    (E2E/BridgeAtRecs.lean), with the session's run values read off the coins and off the plain
    parts through any map enc from pairs of byte strings into `R.RV`, the type of run values of R

By what. `premW_iff` (E2E/PremisesAtFiles.lean): `PremW` holds if `NoProverSide` and the five fields
`ext`, `runVals`, `good`, `stops` and `coins` do. `NoProverSide` is h0 and `coins` is hc. `ext`:
`extEnc_join`. `good`: `good_join`, with hN to write `N.zO` for the error 0. `stops`: `stops_join`
(all three E2E/BridgeJoinAtFiles.lean). `runVals`: `runVals_of` (E2E/BridgeAtRecs.lean), whose
hypothesis on the family is `runVals_tied` (E2E/BridgeTied.lean) with enc applied to both sides;
that theorem has the equation at every verifier randomness. Definitions: `RestOf`
(E2E/BridgeAtRecs.lean); `proversOf`, `HidSmall` (E2E/BridgePrivacy.lean); `ExactAt`, `honestProversByCopyNumber`
(E2E/BridgeAlong.lean); `viewRe` (E2E/OneAlong.lean); `lettersZ`, `protocolAtFiles`, `descZ`, `CoinG`, `provG`,
`TiedIn` (E2E/BridgeJoinAtFiles.lean); `SdOf` (E2E/BridgeJoin.lean); `pvZ` (E2E/BridgeTied.lean);
`RyesZ` (E2E/TiedAtFiles.lean); `StopsSmall`, `Sims.Good`, `CoinsFit`, `CoinNums`, `NumsW`
(Johnson/WholeKey/Premises.lean).

Hypotheses of `premW_atFiles`. hY: Yes implies `RyesZ Z`. hit:
`AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)` (E2E/ItemsZero.lean): every stored table that a round of the
description declares is under the item 0, which is where `provG` has the committer's columns
(`Committer.proverAt` at 0, Johnson/Desc/ProofFile/Honest/CommitterAt.lean); `itemsZero_of_data`
proves it wherever the description's `data` returns. h0: `NoProverSide` at the same wiring, S, cA,
Gs and N, and at the fields M, capT, capL and capB of R. A value that meets it is shown for Z in
scope (`VerifierAndGoals.InScope Z = true`), at Gs := all OOD seeds, at the compiled verifier's own S and code
of the answers, at the numbers `indexPrivacyNumbers`, at most 710,324 copies and at most 688,127 sessions a copy:
`noProverSide_atFiles`; `NoProverSide.restrict` carries it to a smaller Gs. On the key file's prover
and the link's: eT, eL: their external strings are the encoded index (for hL: the index as encoded
at each of the two values of the committer's randomness in its private input). hTv, hLv: at the
indices of ok, outside the abort set, `R.pvT` (`R.pvL`) of the plain parts of the run is `R.rvT`
(`R.rvL`) of the coin. s, gd: values of `StopsSmall` and `Sims.Good` at any families Fm₂, Fm₃ in the
place of `famG`: their clauses on these two provers are handed through. On the session's prover:
hz': `HidSmall`: the measure of the family's abort set `Hid`, which may depend on the private input,
is at most `N.hO`. hx: `ExactAt` of the family at the description's own instances (`honestProversByCopyNumber`), at the
simulator simOne: outside `Hid` the honest output is the simulator's. Both are asked at `TiedIn` at
Yes, ok and Gs only. hN: `N.zO`, the error of the session's simulator, is 0. hc: `CoinsFit`, whole.

Limits.
- The theorem shows that the types fit, and its hypotheses list what is left to show; no property
  follows. The statement of index privacy is not called here, and `ExactAt`, `CoinsFit`, the
  measures and all clauses on the two other provers are shown of nothing.
- The parameters p, the code of the answers cA, the coins' numbers c, the structure S of the
  OOD-seed wire (`SdOf`), and R, enc and startB are free parameters: `PremW` speaks of the compiled
  verifier only at that verifier's own p, cA and S (fields of its input). Among the fields of
  `PremW`, p and c occur in `CoinsFit` only; the error of the statement of index privacy (`zetaW`,
  Johnson/WholeKey/Zeta.lean) reads them too (of c: the number ℓ of free bits of a leaf's salt: at ℓ
  := 0 its term on the hash function is at least 1).
- The value that is shown to meet `NoProverSide` is for Z in scope, at the compiled verifier's own S
  and code of the answers. No value is shown here to meet all hypotheses together. The ways to meet
  them that have been argued make the statement vacuous: Yes or ok set to a predicate that never
  holds; provers whose public abort set `Bad` holds every verifier randomness; a prover structure
  that does nothing, for instance one that has no part for any sub-protocol (`Placed`) (Limits of
  E2E/BridgeDebts.lean).
- Where the prover structure H has no trace, the abort set `Hid`, which may depend on the private
  input, is an empty set (`hidB`, Johnson/Desc/ProofFile/Honest/Record.lean), and the bound on its
  measure in hz' holds there because no verifier randomness is in the set. Nothing here asks a
  trace; the field `rows` of `PremWDebts` (E2E/BridgeDebts.lean) does.
- The simulators sT, sL and simOne are bound with Yes and ok, not before them: at an ok that holds
  at one index only they may lean on that index, and simOne also at such a Yes (Limits of
  E2E/BridgeJoinAtFiles.lean).
- The limits of E2E/BridgeJoinAtFiles.lean, E2E/BridgePrivacy.lean ("error 0 is no result by
  itself") and E2E/PremisesAtFiles.lean hold here too.
- Nothing on completeness, soundness or hiding follows from this file alone.
-/
import E2E.BridgeJoinAtFiles
import E2E.BridgeAtRecs
import E2E.PremisesAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Premises
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open OnBytes.Slice (frS)
open _root_.Run (ckP)
open _root_.Compile (Params)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open OnBytes.WholeKey (PremW StopsSmall Sims CoinsFit CoinNums NumsW RunVals)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
  (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
  (R : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL hT hL)
  (enc : ByteArray × ByteArray → R.RV) (startB : R.RV → ℕ → Bool → Rom.Bits → Rom.Bits)

/-- The value of `AtRecs` (the three honest provers and the other parameters of the scheme's honest
side) at Z: `atRecsOf` at `proversOf hT hL (famG …)`. -/
abbrev atRecsZ :=
  atRecsOf hT hL (famG Z Zp Np cF run₂ run₃ B G H) R (fun κ : CoinG B R₂ R₃ => enc (run₂ κ.1.2, run₃
    κ.2.2))
    (fun π => enc (pvZ Z (dataAtFiles flashProveData Z).P π)) startB

/-- **All hypotheses of the statement of index privacy (`PremW`), at Z, with the session's family
`famG` filled in.** The head of this file says what is proved and what is a hypothesis. -/
theorem premW_atFiles {Yes : FullSizeMatrix → XF → Prop} (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF))
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (S : SdOf (lettersZ Z c₀ m₀))
    (cA) (p : Params) (c : CoinNums (List Bool)) (N : NumsW) {ok : FullSizeMatrix → Prop} {Gs} {simOne}
    {sT sL} {Fm₂ Fm₃} {hpO zO : ℝ≥0∞}
    (h0 : NoProverSide (lettersZ Z c₀ m₀).W S cA Gs N R.M R.capT R.capL R.capB)
    (eT : ∀ i r e, hT.ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = ((protocolAtFiles Z).encodeIndex i r, (protocolAtFiles Z).encodeIndex i r'))
    (hTv : ∀ i r e κ ρ, ok i → ρ ∉ hT.withheld (i, r, e) ((protocolAtFiles Z).recOf i r e) →
      R.pvT ((hT.strat (i, r, e) ((protocolAtFiles Z).recOf i r e) κ).run ρ).1.plains = R.rvT κ)
    (hLv : ∀ i u u' κ ρ, ok i →
      ρ ∉ hL.withheld (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) →
      R.pvL ((hL.strat (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) κ).run
        ρ).1.plains = R.rvL κ)
    (s : StopsSmall (proversOf hT hL Fm₂) (lettersZ Z c₀ m₀).W ok Gs Yes N.hT N.hL hpO)
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G
      H Yes ok Gs n w (instanceAsPlainRecord a)) N.hO)
    (gd : Sims.Good
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      (proversOf hT hL Fm₃) (lettersZ Z c₀ m₀).W ok Gs Yes N.zT N.zL zO)
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs))
    (hN : N.zO = 0)
    (hc : CoinsFit (lettersZ Z c₀ m₀).W p (atRecsZ Z Zp Np cF run₂ run₃ B G H hT hL R enc startB) c)
      :
    PremW (lettersZ Z c₀ m₀).W S cA p (atRecsZ Z Zp Np cF run₂ run₃ B G H hT hL R enc startB)
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok Gs Yes c N :=
  (premW_iff _ _ _ _ _ _ _ _ _ _ _).2
    ⟨h0, extEnc_join Z Zp Np cF run₂ run₃ B G H hT hL eT eL,
      runVals_of hT hL (famG Z Zp Np cF run₂ run₃ B G H) R _ _ startB ok hTv hLv
        (fun i r e n x κ ρ => congrArg enc
          (runVals_tied Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P (G.prover H) hT hL i r e
            n
            x κ ρ)),
      hN ▸ good_join Z Zp Np cF run₂ run₃ B G H hY hit c₀ m₀ hT hL gd hx, stops_join Z Zp Np cF run₂
        run₃ B G H hY hit c₀ m₀ hT hL s hz', hc⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.premW_atFiles
#print axioms AtPublicFiles.AtFiles.atRecsZ
