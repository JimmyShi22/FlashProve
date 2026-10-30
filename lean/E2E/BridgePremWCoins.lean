-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgePremWCoins.lean: the term of `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean: all
hypotheses of the statement of index privacy) that E2E/BridgePremW.lean has at three public files Z,
without that theorem's hypothesis `CoinsFit` (the field `coins` of `PremW`: the statements on all
coins). `CoinsFit` is proved at the enumerations and the window that `canon` (E2E/BridgeCoins.lean)
chooses, from seven hypotheses on lengths and run values. As general as E2E/BridgePremW.lean: in Z,
in the parameters of the session's family `famG`, and in the two other provers hT and hL.

  `premW_canon`: `PremW (lettersZ Z c₀ m₀).W S cA p (atRecsZ …) ⟨sT, sL, …⟩ ok Gs Yes c N`, where
    `atRecsZ` is at `canon (lettersZ Z c₀ m₀).W p c R₀`, enc and startB, and the third simulator,
    the session's, is simOne read through `instanceAsPlainRecord`

By what. One call of `premW_atFiles` (E2E/BridgePremW.lean) at `canon (lettersZ Z c₀ m₀).W p c R₀`
in the place of its parameter R. Its hypothesis on `CoinsFit` is `coinsFit_canon`
(E2E/BridgeCoins.lean) at the family `famG` (E2E/BridgeJoinAtFiles.lean). `canon` sets anew only the
enumerations and the window of R₀, so the fields that the hypotheses below read are those of R₀.

Hypotheses. All but the last seven are those of `premW_atFiles`, with R₀ for R; the head of
E2E/BridgePremW.lean says more on each. hY: Yes implies the object's own relation `RyesZ Z`. hit:
`AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)` (E2E/ItemsZero.lean): every stored table that a round of the
description declares is under the item 0; `itemsZero_of_data` proves it wherever the description's
`data` returns. h0: `NoProverSide` (E2E/PremisesAtFiles.lean): the fields of `PremW` that read no
prover. eT, eL: the external strings of hT and hL are the encoded index (for hL: the index as
encoded at each of the two values of the encoding's randomness in its private input). hTv, hLv: at
the indices of ok, outside the abort set, `R₀.pvT` (`R₀.pvL`) of the plain parts of the run is
`R₀.rvT` (`R₀.rvL`) of the coin. s, gd: values of `StopsSmall` and `Sims.Good` at any families Fm₂,
Fm₃ in the place of `famG`: their clauses on hT and hL are handed through. hz': `HidSmall`: the
measure of the family's abort set `Hid`, which may depend on the private input, is at most `N.hO`.
hx: `ExactAt` of the family at the description's own instances (`honestProversByCopyNumber`), at the simulator simOne:
outside `Hid` the honest output is the simulator's. Both are asked at `TiedIn` at Yes, ok and Gs
only. hN: `N.zO`, the error of the session's simulator, is 0.
In the place of `CoinsFit`: hlen: the length of `c.pre₀`, the public start of a table's leaf salt,
and `c.ℓ` add up to `p.sMT`, the length that the strict format asks of a leaf's salt. okT, okL: the
run values that the coins of hT and hL give (`R₀.rvT κ`, `R₀.rvL κ`) are of the right form
(`R₀.okV`). okB: so is `enc (run₂ r2, run₃ r3)`, at all r2 and r3. lenT, lenL, lenB: at a run value
of the right form, at every round's number and at a first salt of `p.sFS` bits, the length of the
public start of a leaf's salt (`R₀.startT`, `R₀.startL`, startB) and `c.ℓ` add up to `p.sMT`.

Limits.
- The limits of E2E/BridgePremW.lean and E2E/BridgeCoins.lean hold here. The theorem shows that the
  types fit, and its hypotheses list what is left to show; no property follows. The choice of
  enumerations is that of E2E/BridgeCoins.lean, and it is classical (`Fintype.equivFin`).
- The seven hypotheses that are left carry no weight in `PremW`: `okV`, the starts and `pre₀` are
  the caller's parameters: with every run value counted as of the right form and constant starts of
  the right length all seven can be met wherever `c.ℓ` is at most `p.sMT`, the strict format's
  length of a leaf's salt. In Lean this is in two files that import this one, for run values that
  are pairs of byte strings: `lensAt_plain` (E2E/BridgeDebts.lean) meets the seven, in the form
  `LensAt`, and sets `pre₀` anew; `premW_plain` (E2E/BridgeNoStop.lean) makes the same choice and
  keeps the statement on `pre₀` as a hypothesis. The true starts are the format's: `PremW` never
  asks that.
- c is a free parameter, and the error of the statement of index privacy (`zetaW`,
  Johnson/WholeKey/Zeta.lean) reads `c.ℓ`, the number of free bits of a leaf's salt: at ℓ := 0 the
  clauses of `CoinsFit` hold under the same seven hypotheses (the salts are constant), and that
  error's term on the hash function is at least 1: the statement of index privacy is then vacuous.
- lenT, lenL and lenB are asked at every round's number, where `CoinsFit` asks them within the
  window only (head of E2E/BridgeCoins.lean): more is asked than `CoinsFit` needs.
- Nothing on completeness, soundness or hiding follows from this file alone.
-/
import E2E.BridgePremW
import E2E.BridgeCoins

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
open OnBytes.WholeKey (PremW StopsSmall Sims CoinNums NumsW)
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
  (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL hT hL)
  (enc : ByteArray × ByteArray → R₀.RV) (startB : R₀.RV → ℕ → Bool → Rom.Bits → Rom.Bits)

/-- **All hypotheses of the statement of index privacy (`PremW`), at Z, with the session's family
`famG` filled in and `CoinsFit` proved at the enumerations and the window of `canon`.** The heads of
this file and of E2E/BridgePremW.lean say what is proved and what is a hypothesis. -/
theorem premW_canon {Yes : FullSizeMatrix → XF → Prop} (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF))
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (S : SdOf (lettersZ Z c₀ m₀))
    (cA) (p : Params) (c : CoinNums (List Bool)) (N : NumsW) {ok : FullSizeMatrix → Prop} {Gs} {simOne}
    {sT sL} {Fm₂ Fm₃} {hpO zO : ℝ≥0∞}
    (h0 : NoProverSide (lettersZ Z c₀ m₀).W S cA Gs N R₀.M R₀.capT R₀.capL R₀.capB)
    (eT : ∀ i r e, hT.ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = ((protocolAtFiles Z).encodeIndex i r, (protocolAtFiles Z).encodeIndex i r'))
    (hTv : ∀ i r e κ ρ, ok i → ρ ∉ hT.withheld (i, r, e) ((protocolAtFiles Z).recOf i r e) →
      R₀.pvT ((hT.strat (i, r, e) ((protocolAtFiles Z).recOf i r e) κ).run ρ).1.plains = R₀.rvT κ)
    (hLv : ∀ i u u' κ ρ, ok i →
      ρ ∉ hL.withheld (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) →
      R₀.pvL ((hL.strat (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) κ).run
        ρ).1.plains = R₀.rvL κ)
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
    (hN : N.zO = 0) (hlen : c.pre₀.length + c.ℓ = p.sMT)
    (okT : ∀ κ, R₀.okV (R₀.rvT κ)) (okL : ∀ κ, R₀.okV (R₀.rvL κ))
    (okB : ∀ r2 r3, R₀.okV (enc (run₂ r2, run₃ r3)))
    (lenT : ∀ v i b s, R₀.okV v → s.length = p.sFS → (R₀.startT v i b s).length + c.ℓ = p.sMT)
    (lenL : ∀ v i b s, R₀.okV v → s.length = p.sFS → (R₀.startL v i b s).length + c.ℓ = p.sMT)
    (lenB : ∀ v i b s, R₀.okV v → s.length = p.sFS → (startB v i b s).length + c.ℓ = p.sMT) :
    PremW (lettersZ Z c₀ m₀).W S cA p
      (atRecsZ Z Zp Np cF run₂ run₃ B G H hT hL (canon (lettersZ Z c₀ m₀).W p c R₀) enc startB)
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok Gs Yes c N :=
  premW_atFiles Z Zp Np cF run₂ run₃ B G H hT hL
    (canon (lettersZ Z c₀ m₀).W p c R₀) enc startB hY hit
    c₀ m₀ S cA p c N h0 eT
    eL hTv hLv s hz' gd hx hN
    (coinsFit_canon (lettersZ Z c₀ m₀).W p c (famG Z Zp Np cF run₂ run₃ B G H) R₀ _ _ startB hlen
      okT okL
      (fun κ => okB κ.1.2 κ.2.2) lenT lenL lenB)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.premW_canon
