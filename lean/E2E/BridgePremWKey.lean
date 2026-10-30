-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgePremWKey.lean: `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean: all hypotheses of
the statement of index privacy) at three public files Z, as `premW_canon`
(E2E/BridgePremWCoins.lean) concludes it, with the key file's prover filled in. The first of the
three honest provers is `offlineProverWithEncodedTable`: `offlineProverInThreeProtocols` (E2E/KeyHonest.lean), with `keySeam` for what the
three rounds without a challenge send and the encoder's table `tableOf` for the committed table. It
is a prover structure built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from
parameters that nothing here fixes (below: the shell `offlineProverWithEncodedTable`). The second, the link's prover hL, is a
free parameter. The third is the session's family `famG` (E2E/BridgeJoinAtFiles.lean). The run
values are pairs of byte strings. At the shell `offlineProverWithEncodedTable` two hypotheses of `premW_canon` are proved;
the others stay hypotheses. `premW_key` is general in Z, in the parameters of `offlineProverWithEncodedTable` and of `famG`,
and in the digest c₀ and the further reading m₀ of the wiring `(lettersZ Z c₀ m₀).W`; of the proof
file's description `descZ Zp Np cF` only hit is asked (see Hypotheses).

  `premW_key`: `PremW` at the three provers `proversOf (offlineProverWithEncodedTable …) hL (famG …)` and the simulators sT,
    sL and, for the session, simOne read through `instanceAsPlainRecord`; at any S, cA, p, c, N, ok, Gs and Yes
    that meet the hypotheses. Proved beyond `premW_canon`, by E2E/KeyBridgeFilled.lean: the external
    string of the shell `offlineProverWithEncodedTable` is the encoded index (`extIsEnc_obj`); its run values are in the
    plain parts of its run (`runValsAt_obj`). Stated in other words, not proved: that the run values
    which its coins give are of the right form is asked of all values of its two codes val₂ and val₃
    (okT)
  `premW_key_own`: the same at the compiled verifier's own parameters: its own OOD-seed wire, code
    of the answers and parameters (the fields `letters.Sd` and `p` of `lettersZ Z c₀ m₀`, and
    `codeA`), with Gs := all OOD seeds and N := `indexPrivacyNumbers s1 zT zL 0 hT' hL' hO'`. There the fields of
    `PremW` that read no prover (`NoProverSide`) are proved: `noProverSide_atFiles`
    (E2E/PremisesAtFiles.lean), for Z in scope, at most 710,324 copies and at most 688,127 sessions
    a copy
  `offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT`: an abbreviation: that prover at Z, at any description Fx of the
    key file, book of coins BT (`ProverCoinCounts`) and prover structure HT (`ProofFile.Honest.Prover`)
  `restKey … R₀ okV rvL startT startL pvL`: a definition: a value of `RestOf`
    (E2E/BridgeAtRecs.lean: the fields of `AtRecs` that do not read the session's prover): R₀ with
    pairs of byte strings for run values and with the key file's two maps `pvKey` and `rvKey`
    (E2E/KeyBridgeFilled.lean) as pvT and rvT. `premW_key` applies `canon` (E2E/BridgeCoins.lean) to
    it. After `canon` there are left of R₀: the decisions of two abort sets (dcT, dcL), the body of
    a table's leaf beyond the word's length (b₀), the caps (capT, capL, capB), how many copies there
    are and each copy's number (M, nm), rtail and fill. `restKey` by itself also keeps the window's
    numbers (nR, nK, nJ) and the enumerations of encoding randomness, salts and coins (ri, sl, kT,
    kL, coT, coL, coB)

By what. `premW_key` is one call of `premW_canon`, at `offlineProverWithEncodedTable` for the key file's prover, `restKey`
for R₀ and the identity for the map enc from pairs of byte strings to run values. `extIsEnc_obj` and
`runValsAt_obj` prove its hypotheses eT and hTv; its okT follows from okT here, at the two
components of the coin that `rvKey` reads. `premW_key_own` is one call of `premW_key`, with
`noProverSide_atFiles` for h0. Definitions: `atRecsZ` (E2E/BridgePremW.lean); `proversOf`,
`HidSmall` (E2E/BridgePrivacy.lean); `ExactAt`, `honestProversByCopyNumber` (E2E/BridgeAlong.lean); `lettersZ`, `protocolAtFiles`,
`descZ`, `provG`, `TiedIn` (E2E/BridgeJoinAtFiles.lean); `SdOf` (E2E/BridgeJoin.lean); `RyesZ`
(E2E/TiedAtFiles.lean); `NoProverSide`, `indexPrivacyNumbers` (E2E/PremisesAtFiles.lean); `StopsSmall`,
`Sims.Good`, `CoinsFit`, `CoinNums`, `NumsW` (Johnson/WholeKey/Premises.lean).

Hypotheses of `premW_key`. hY: Yes implies the object's relation `RyesZ Z`. hit:
`AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)` (E2E/ItemsZero.lean): every stored table that a round of the
description declares is under the item 0, which is where `provG` has the committer's columns
(`Committer.proverAt` at 0, Johnson/Desc/ProofFile/Honest/CommitterAt.lean); `itemsZero_of_data`
proves it wherever the description's `data` returns. h0: `NoProverSide` at the wiring, S, cA, Gs, N
and the fields M, capT, capL, capB of R₀. s, gd: values of `StopsSmall` and `Sims.Good` at any
families Fm₂, Fm₃ in the place of `famG`: their clauses on the shell `offlineProverWithEncodedTable` and on the link's prover
are handed through. On the shell `offlineProverWithEncodedTable` these two clauses are hypotheses. On the link's prover all
its clauses are left: those in s and gd, okL and lenL below, and two more. eL: its external strings
are the two encoded indices. hLv: at the indices of ok, outside its abort set, pvL of the plain
parts of its run is rvL of its coin. hz': `HidSmall`: the measure of the family's abort set `Hid`,
which may depend on the private input, is at most `N.hO`, at `TiedIn` at Yes, ok and Gs. hx:
`ExactAt` of the family at the description's own instances (`honestProversByCopyNumber`), at the simulator simOne and
the same `TiedIn`: outside `Hid` the honest output is the simulator's. hN: `N.zO` is 0. Last, the
seven hypotheses of `premW_canon` on lengths and run values. hlen: the length of `c.pre₀`, the
public start of a table's leaf salt, and `c.ℓ` add up to `p.sMT`. okT, okL, okB:
`(val₂ q2, val₃ q3)`, `rvL κ` and `(run₂ r2, run₃ r3)` are of the right form (`okV`), at all q2, q3,
κ, r2 and r3. lenT, lenL, lenB: at run values of the right form and a first salt of `p.sFS` bits,
the length of the public start of a leaf's salt and `c.ℓ` add up to `p.sMT`; these three are asked
at every round's number, where `CoinsFit` asks them within the window. In `premW_key_own`, scope
(`VerifierAndGoals.InScope Z = true`), hs1 and hM (the two bounds above) are in the place of h0, there is no
hN, and the others are asked at Gs := all OOD seeds and at the verifier's own p.

Limits.
- The limits of E2E/BridgePremWCoins.lean and E2E/KeyBridgeFilled.lean hold here. What is proved
  here holds of the shell `offlineProverWithEncodedTable` whatever is put into it, also at a prover structure HT that has no
  part for any sub-protocol (`Placed`).
- The two theorems show that the types fit, on hypotheses not shown here; no property follows.
- "The compiled verifier's own parameters" are the fields of `lettersZ Z c₀ m₀`. That they are the
  fields of the compiler's input holds by unfolding. It is stated in Lean for the wiring, the
  OOD-seed wire and the code of the answers (`noProverSide_built`, E2E/PremisesAtFiles.lean), and
  with the parameters p at the pair (allZeroDigest, []) (`premW_home_of_letters`, E2E/BridgeDebtsTold.lean).
  To the input of the description as the goals spell it, `(atSecondHashFunction theDescription).input Z c m`, a
  proved equation leads (`theDescription_eq`, Johnson/Goal/Description/Description.lean). The
  conclusions of this file are not carried along it: their three provers have their types at the
  object at Z (`protocolAtFiles Z`).
- In `premW_key_own` Gs is all OOD seeds: the chance of a seed outside Gs is 0. The price: the
  clauses of `Sims.Good` and `StopsSmall`, the measure in hz' and `ExactAt` are each asked at every
  OOD seed: one seed at which the honest run cannot go on forces the numbers to that seed's own
  measure. The way out is stated in Lean: `NoProverSide.restrict` (E2E/PremisesAtFiles.lean) into h0
  of `premW_key`.
- c is a free parameter, and the error of the statement of index privacy (`zetaW`,
  Johnson/WholeKey/Zeta.lean) reads `c.ℓ`, the number of free bits of a leaf's salt: at ℓ := 0 the
  clauses of `CoinsFit` hold under the same seven hypotheses (the salts are constant), and that
  error's term on the hash function is at least 1: the statement of index privacy is then vacuous.
- `PremW` has no number for the public abort sets `Bad` (Limits of E2E/BridgePrivacy.lean).
- The simulators sT, sL and simOne are bound with Yes and ok, not before them: at an ok that holds
  at one index only they may lean on that index, and simOne also at such a Yes (Limits of
  E2E/BridgeJoinAtFiles.lean).
- Nothing on completeness, soundness or hiding follows from this file alone.
-/
import E2E.BridgePremWCoins
import E2E.KeyBridgeFilled

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
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- The shell `offlineProverWithEncodedTable`: `offlineProverInThreeProtocols` at Z, with `keySeam` at the two codes val₂ and val₃, and with
the encoder's table `tableOf`. -/
abbrev offlineProverWithEncodedTable :=
  offlineProverInThreeProtocols Z Fx BT HT (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) shT
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (dataAtFiles flashProveData Z).P

variable (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))

/-- The fields of `AtRecs` that do not read the session's prover (`RestOf`), with pairs of byte
strings for run values and with the key file's two maps `rvKey` and `pvKey`. The type RV of run
values of R₀ and its seven fields over that type are overwritten. -/
def restKey (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL) (okV : ByteArray × ByteArray → Prop)
    (rvL : hL.Coin → ByteArray × ByteArray)
    (startT startL : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
    (pvL : Plains (protocolAtFiles Z).link.shape → ByteArray × ByteArray) :
    RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL :=
  { R₀ with
    RV := ByteArray × ByteArray
    okV := okV
    rvT := rvKey BT val₂ val₃
    rvL := rvL
    startT := startT
    startL := startL
    pvT := pvKey (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).G.rec₀
    pvL := pvL }

/-- **All hypotheses of the statement of index privacy (`PremW`), at Z, with the key file's prover
`offlineProverWithEncodedTable` and the session's family `famG` filled in.** Conditional: the head lists the hypotheses. -/
theorem premW_key {Yes : FullSizeMatrix → XF → Prop} (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF))
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (S : SdOf (lettersZ Z c₀ m₀))
    (cA) (p : Params) (c : CoinNums (List Bool)) (N : NumsW) {ok : FullSizeMatrix → Prop} {Gs} {simOne}
    {sT sL} {Fm₂ Fm₃} {hpO zO : ℝ≥0∞}
    (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL) (okV : ByteArray × ByteArray → Prop)
    (rvL : hL.Coin → ByteArray × ByteArray)
    (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
    (pvL : Plains (protocolAtFiles Z).link.shape → ByteArray × ByteArray)
    (h0 : NoProverSide (lettersZ Z c₀ m₀).W S cA Gs N R₀.M R₀.capT R₀.capL R₀.capB)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = ((protocolAtFiles Z).encodeIndex i r, (protocolAtFiles Z).encodeIndex i r'))
    (hLv : ∀ i u u' κ ρ, ok i →
      ρ ∉ hL.withheld (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) →
      pvL ((hL.strat (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) κ).run
        ρ).1.plains = rvL κ)
    (s : StopsSmall (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL Fm₂) (lettersZ Z c₀ m₀).W ok Gs
      Yes N.hT N.hL hpO)
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G
      H Yes ok Gs n w (instanceAsPlainRecord a)) N.hO)
    (gd : Sims.Good
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL Fm₃) (lettersZ Z c₀ m₀).W ok Gs Yes N.zT N.zL
      zO)
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs))
    (hN : N.zO = 0) (hlen : c.pre₀.length + c.ℓ = p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : ∀ κ, okV (rvL κ))
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = p.sFS → (startT v i b s).length + c.ℓ = p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = p.sFS → (startL v i b s).length + c.ℓ = p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = p.sFS → (startB v i b s).length + c.ℓ = p.sMT) :
    PremW (lettersZ Z c₀ m₀).W S cA p
      (atRecsZ Z Zp Np cF run₂ run₃ B G H (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL
        (canon (lettersZ Z c₀ m₀).W p c
          (restKey Z Fx BT HT val₂ val₃ shT hL R₀ okV rvL startT startL pvL)) id startB)
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok Gs Yes c N :=
  premW_canon Z Zp Np cF run₂ run₃ B G H (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL
    (restKey Z Fx BT HT val₂ val₃ shT hL R₀ okV rvL startT startL pvL)
      id startB hY hit c₀ m₀ S cA p c N
    h0 (extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT) eL
    (runValsAt_obj Z Fx BT (dataAtFiles flashProveData Z).P HT val₂ val₃ shT _ ok) hLv s hz' gd hx hN hlen
    (fun κ => okT κ.1.2 κ.2.2) okL okB lenT lenL lenB

/-- **The same at the compiled verifier's own parameters**: its own OOD-seed wire, code of the
answers and parameters; no OOD seed is outside Gs (Gs := all OOD seeds); at most 710,324 copies and
688,127 sessions a copy. The fields that read no prover are proved (`noProverSide_atFiles`, for Z in
scope). -/
theorem premW_key_own (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (c₀ : VerifiableInference.Digest)
    (m₀ : List (Iop.Dig 256)) (c : CoinNums (List Bool)) (s1 : ℕ) (hs1 : s1 ≤ 688127)
    (zT zL hT' hL' hO' : ℝ≥0∞) {ok : FullSizeMatrix → Prop} {simOne} {sT sL} {Fm₂ Fm₃} {hpO zO : ℝ≥0∞}
    (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL) (hM : R₀.M + 1 ≤ 710324)
    (okV : ByteArray × ByteArray → Prop) (rvL : hL.Coin → ByteArray × ByteArray)
    (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
    (pvL : Plains (protocolAtFiles Z).link.shape → ByteArray × ByteArray)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = ((protocolAtFiles Z).encodeIndex i r, (protocolAtFiles Z).encodeIndex i r'))
    (hLv : ∀ i u u' κ ρ, ok i →
      ρ ∉ hL.withheld (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) →
      pvL ((hL.strat (i, u, u') ((protocolAtFiles Z).recOf i u.1 u.2, (protocolAtFiles Z).recOf i u'.1 u'.2) κ).run
        ρ).1.plains = rvL κ)
    (s : StopsSmall (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL Fm₂) (lettersZ Z c₀ m₀).W ok
      (fun _ => True) Yes hT' hL' hpO)
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w (instanceAsPlainRecord a)) hO')
    (gd : Sims.Good
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL Fm₃) (lettersZ Z c₀ m₀).W ok (fun _ => True)
      Yes zT zL zO)
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True)))
    (hlen : c.pre₀.length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (okT : ∀ q2 q3, okV (val₂ q2, val₃ q3)) (okL : ∀ κ, okV (rvL κ))
    (okB : ∀ r2 r3, okV (run₂ r2, run₃ r3))
    (lenT : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startT v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (lenL : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startL v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (lenB : ∀ v i b s, okV v → s.length = (lettersZ Z c₀ m₀).p.sFS →
      (startB v i b s).length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT) :
    PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (lettersZ Z c₀ m₀).p
      (atRecsZ Z Zp Np cF run₂ run₃ B G H (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) hL
        (canon (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).p c
          (restKey Z Fx BT HT val₂ val₃ shT hL R₀ okV rvL startT startL pvL)) id startB)
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT zL 0 hT' hL' hO') :=
  premW_key Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT hL hY hit c₀ m₀ _ _ _ c _ R₀ okV rvL
    startT startL startB pvL
    (noProverSide_atFiles Z scope c₀ m₀ R₀.M s1 hM hs1 zT zL 0 hT' hL' hO' R₀.capT R₀.capL R₀.capB)
    eL hLv s hz' gd hx rfl hlen okT okL okB lenT lenL lenB

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.premW_key
#print axioms AtPublicFiles.AtFiles.premW_key_own
#print axioms AtPublicFiles.AtFiles.offlineProverWithEncodedTable
#print axioms AtPublicFiles.AtFiles.restKey
