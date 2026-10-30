-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeNoStop.lean: where no `Part` of a prover structure (`ProofFile.Honest.Prover`) ever stops
(`NoStopAll`, E2E/NoStop.lean: the fields `bad` and `hid` of every `Part` are `none` at all
arguments), the abort sets of the honest prover built from that structure are empty, so their
measures are 0. This is proved at three public files Z: for the session's family `famG`
(E2E/BridgeJoinAtFiles.lean), of both parts of its abort set, and for the key file's prover `offlineProverWithEncodedTable`
(E2E/BridgePremWKey.lean), of the part `Hid`. `offlineProverWithEncodedTable` is a prover structure built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes (below: the
shell `offlineProverWithEncodedTable`), and so is each prover of `famG`. From the hypotheses listed under Hypotheses below,
`premW_plain` then proves `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean: all hypotheses
of the statement of index privacy) by `premW_link` (E2E/BridgePremWLink.lean), with these measures
at 0 and with that theorem's hypotheses on lengths and run values proved by a plain choice, except
the length of `c.pre₀`, which stays one of these hypotheses. General in the parameters of the two
shells. E2E/BridgePremWRoom.lean has the form in which the errors and measures of these two provers
are parameters: `premW_plain` is the narrow case of that kind, and is not proved from it.

  `premW_plain`: `PremW` at the parameters of `lettersZ Z c₀ m₀`, at every digest c₀ and list of
    digests m₀, at the three provers `offlineProverWithEncodedTable`, `linkProverAtFiles b Z` and `famG` (`atRecsAll`), with Gs := all
    OOD seeds and the numbers `indexPrivacyNumbers s1 zT 0 0 0 0 0`. The plain choice: every run value counts as
    of the right form, and the three starts are `plainStart`. What is left to show: see Hypotheses
  `hid_famG`, `bad_famG`: under `NoStopAll` of `provG`, the two parts of the family's abort set are
    empty: `Hid`, which may depend on the private input, at every number, private input and
    instance; and the public abort set `Bad`
  `hidSmall_famG`, `badSmall_famG`: so `HidSmall` holds at 0, at every relation, and `BadSmall` at 0
  `hid_keyZ`: under `NoStopAll HT`, the abort set `Hid` of the shell `offlineProverWithEncodedTable` is empty
  `stopsT_keyZ`: so the field `T` of `StopsSmall` holds at 0: written out, at every range ok, with
    Gs := all OOD seeds
  `plainStart p c`: a definition: a constant string of `p.sMT - c.ℓ` bits, whatever its arguments
  `plainStart_len`: where `c.ℓ ≤ p.sMT`, its length and `c.ℓ` add up to `p.sMT`

By what. `hid_empty` and `bad_empty` (E2E/NoStop.lean), which are general in the parameters of
`honestBatchProverOfFile`: by unfolding, the sets of `famG` and of `offlineProverWithEncodedTable` are those of the one-slot structure `one`
of such a structure, with instances read through `instanceAsPlainRecord` and `keyInstanceOfOutOfDomainSample`. A set without elements has
measure 0: `prRho_empty` (Iop/ViewKit.lean), `pr_eq_zero_of_forall_not_mem` (Prob/Count.lean).
`premW_plain` is one call of `premW_link`, with `stopsT_keyZ` and `hidSmall_famG` for its two
hypotheses on measures and `plainStart_len` for its three on the starts. Definitions: `provG`,
`TiedIn`, `lettersZ`, `descZ`, `protocolAtFiles` (E2E/BridgeJoinAtFiles.lean); `linkProverAtFiles`, `atRecsAll`
(E2E/BridgePremWLink.lean); `HidSmall` (E2E/BridgePrivacy.lean); `BadSmall` (E2E/BridgeAccept.lean);
`ExactAt`, `honestProversByCopyNumber` (E2E/BridgeAlong.lean); `StopsSmall`, `Sims.Good`, `CoinsFit`, `CoinNums`
(Johnson/WholeKey/Premises.lean); `indexPrivacyNumbers` (E2E/PremisesAtFiles.lean); `RyesZ`
(E2E/TiedAtFiles.lean).

Hypotheses of `premW_plain`. scope: Z is in scope (`VerifierAndGoals.InScope`). hY: Yes holds only where the
object's relation `RyesZ Z` does. hit: `ItemsZero` (E2E/ItemsZero.lean) of the description
`descZ Zp Np cF`: every stored table that one of its rounds declares is under the item 0. `provG`
has the committer's stored table at the item 0 only (`Committer.proverAt`,
Johnson/Desc/ProofFile/Honest/CommitterAt.lean); `itemsZero_of_data` proves hit wherever the
description's `data` returns. hs1, hM: at most 688127 sessions a copy and 710324 copies. hlen: the
length of `c.pre₀` and `c.ℓ` add up to `p.sMT`, p the parameters of `lettersZ Z c₀ m₀`. hℓ:
`c.ℓ ≤ p.sMT`, which follows from hlen. nT, nB: `NoStopAll` of HT and of `provG`. gT: the field `T`
of `Sims.Good`, written out: the clause on the shell `offlineProverWithEncodedTable` and its simulator sT, at the error zT.
hx: `ExactAt` of the session's family at the description's own instances (`honestProversByCopyNumber`), at the simulator
simOne and the relation `TiedIn` at Yes, ok and all OOD seeds.

Limits.
- Of the six errors and measures in `indexPrivacyNumbers`, the statement itself sets all but zT to 0. "All abort
  sets have measure 0" is not "the prover always sends its own messages": the honest prover's
  strategy cannot refuse to speak: where its run cannot be made ready, at a fault of a `Part`, at a
  column that is not at hand, and after a rejection by the verifier's own step it sends fixed
  substitutes (Johnson/Desc/ProofFile/Honest/StratC.lean: its head and, for the first case, `requestStrategyTrackingVerifier`
  and `sharedChainStart`): none of these cases lies in an abort set. So under `NoStopAll`, `ExactAt` is asked
  at every verifier randomness, OOD seed and committer's randomness, with no room: the weight of the
  abort sets has moved into `ExactAt` and gT. It is the hardest form for a real prover: one fault
  that depends on the private input, and `premW_plain` is vacuous at that prover.
- A prover that withholds its proof where no verifier would accept it has a stop, and the format's
  own page (`docs/format/FORMAT.md`, 13.9, "Sampled values at which a verifier gives no acceptance")
  lists events of sampled values at which no verifier accepts an honest proof: at such a prover
  `NoStopAll` fails and the hypotheses of `premW_plain` cannot be proved: the theorem is a corner
  case. (The honest prover as written in Lean does not withhold there: it sends substitutes.)
- `NoStopAll` reads no OOD seed and no coin. It fails at every prover structure of which one `Part`
  names a stop (its `bad` or `hid` is not `none` at some arguments), even if that stop never occurs
  at a valid input. It is vacuous at a prover structure that has no part for any sub-protocol
  (`Placed`). What excludes that is on the acceptance side (`HonFit`) only: the field `halved` of
  `PlainAt` (E2E/BridgeJoinAtFiles.lean), a test that each sub-protocol one of whose rounds states
  an item other than a root has its part of the prover's. With the public abort set `Bad` empty, "a
  public abort set that holds everything" (the Limits of E2E/BridgePrivacy.lean) is excluded.
- The seven hypotheses of `premW_link` on lengths and run values carry no weight in `PremW`: `okV`,
  the three starts and `pre₀` are the caller's parameters: with every run value counted as of the
  right form and constant starts of the right length all seven can be met (`lensAt_plain`,
  E2E/BridgeDebts.lean, which sets `pre₀` anew). The true starts are the format's (made of the run
  values and the first salt, which the plain choice drops): `PremW` never asks that.
- c is a free parameter, and the error of the statement of index privacy (`zetaW`,
  Johnson/WholeKey/Zeta.lean) reads `c.ℓ`, the number of free bits of a leaf's salt: at ℓ := 0,
  under hlen, all fields of `CoinsFit` hold (the salts are constant) and that error's term on the
  hash function is at least 1: the statement of index privacy is then vacuous.
- zT is a free parameter: at zT ≥ 1 gT is vacuous. ok and Yes are free parameters (Yes below the
  object's relation): at a range ok that holds of no index gT and `ExactAt` ask nothing; at a Yes
  that holds of nothing `ExactAt` asks nothing.
- Gs := all OOD seeds: the chance of a seed outside Gs is 0. The price: gT and `ExactAt` are asked
  at every OOD seed. The way out is stated in Lean elsewhere: `NoProverSide.restrict`
  (E2E/PremisesAtFiles.lean) into `premW_key` (E2E/BridgePremWKey.lean).
- Of the three provers only the link's is a closed term. `offlineProverWithEncodedTable` and `famG` are shells over free
  parameters; of the description (Zp, Np, cF) only hit is asked.
- The limits of E2E/BridgePremWLink.lean hold here.
- `premW_plain` shows that the types fit and lists what is left to show; no property follows. No
  value is shown to meet its hypotheses together.
- What the conclusion says of the link's prover `linkProverAtFiles b Z` is proved in E2E/BridgePremWLink.lean,
  whose head says what it is and what it is not. Beyond that, nothing on completeness, soundness or
  hiding follows from this file alone.
-/
import E2E.BridgePremWLink
import E2E.NoStop

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Premises AtPublicFiles.Stops
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
open OnBytes.WholeKey (PremW CoinNums)
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

/-- The family's abort set `Hid`, which may depend on the private input, is empty. -/
theorem hid_famG (h : NoStopAll (provG Z Zp Np cF B G H)) (n : ℕ) (w) (x) :
    ((famG Z Zp Np cF run₂ run₃ B G H).at n).Hid w x = ∅ :=
  hid_empty (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty (descZ Zp Np cF) silInst B (seamZ Z run₂ run₃ n) (shAt Zp Np cF) (extZ Z) h w
    (instanceAsPlainRecord x)

/-- So is its public abort set `Bad`. -/
theorem bad_famG (h : NoStopAll (provG Z Zp Np cF B G H)) : (famG Z Zp Np cF run₂ run₃ B G H).Bad =
  ∅ :=
  bad_empty (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty (descZ Zp Np cF) silInst B (seamZ Z run₂ run₃ 0) (shAt Zp Np cF) (extZ Z) h

/-- **`HidSmall` at 0, at every relation.** -/
theorem hidSmall_famG (h : NoStopAll (provG Z Zp Np cF B G H)) (Td) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H) Td 0 :=
  fun n w x _ => prRho_empty _ fun ρ a =>
    (Set.eq_empty_iff_forall_notMem.1 (hid_famG Z Zp Np cF run₂ run₃ B G H h n w x)) ρ a

/-- `BadSmall` at 0. -/
theorem badSmall_famG (h : NoStopAll (provG Z Zp Np cF B G H)) : BadSmall (famG Z Zp Np cF run₂ run₃
  B G H) 0 :=
  prRho_empty _ fun ρ a => (Set.eq_empty_iff_forall_notMem.1 (bad_famG Z Zp Np cF run₂ run₃ B G H
    h)) ρ a

variable (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- The abort set `Hid` of the shell `offlineProverWithEncodedTable`, which may depend on the private input, is empty. -/
theorem hid_keyZ (h : NoStopAll HT) (w) (x) : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid w x = ∅ :=
  hid_empty (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
    (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty Fx silKey BT
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) shT
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK) h w
    (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample x)

/-- The field `T` of `StopsSmall`, written out, at 0. -/
theorem stopsT_keyZ (h : NoStopAll HT) (ok : FullSizeMatrix → Prop) :
    ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
            (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ 0 :=
  fun i r e _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ a =>
    (Set.eq_empty_iff_forall_notMem.1 (hid_keyZ Z Fx BT HT val₂ val₃ shT h (i, r, e) _)) _ a)

/-- A constant start of a leaf's salt: as many bits as, with the `c.ℓ` free bits, make up the length
`p.sMT` that the strict format asks (where `c.ℓ ≤ p.sMT`: `plainStart_len`). -/
def plainStart (p : Params) (c : CoinNums (List Bool)) :
    ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits :=
  fun _ _ _ _ => List.replicate (p.sMT - c.ℓ) false

theorem plainStart_len (p : Params) (c : CoinNums (List Bool)) (h : c.ℓ ≤ p.sMT) (v i b s) :
    (plainStart p c v i b s).length + c.ℓ = p.sMT := by
  unfold plainStart
  rw [List.length_replicate]
  omega

variable (c : CoinNums (List Bool))
  (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
  (v₀ : ByteArray × ByteArray)

/-- **All hypotheses of the statement of index privacy (`PremW`), with every measure of an abort set
at 0**: at the parameters of `lettersZ Z c₀ m₀`, with the fields of `CoinsFit` proved by a plain
choice, except the length of `c.pre₀`. This file's head says what is left to show, and at what
price. -/
theorem premW_plain (scope : VerifierAndGoals.InScope Z = true) {Yes : FullSizeMatrix → XF → Prop}
    (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (s1 : ℕ) (hs1 : s1 ≤ 688127) (zT : ℝ≥0∞)
    {ok : FullSizeMatrix → Prop} {simOne} {sT} (hM : R₀.M + 1 ≤ 710324)
    (hℓ : c.ℓ ≤ (lettersZ Z c₀ m₀).p.sMT) (hlen : c.pre₀.length + c.ℓ = (lettersZ Z c₀ m₀).p.sMT)
    (nT : NoStopAll HT) (nB : NoStopAll (provG Z Zp Np cF B G H))
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
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True))) :
    PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
      := 1)) (lettersZ Z c₀ m₀).p
      (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ (fun _ => True) v₀
        (plainStart (lettersZ Z c₀ m₀).p c) (plainStart (lettersZ Z c₀ m₀).p c) (plainStart
          (lettersZ Z c₀ m₀).p c))
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 0 0 0) :=
  premW_link c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ (fun _ => True) v₀ _ _ _
    scope
    hY hit s1 hs1 zT 0 0 hM gT
    (stopsT_keyZ c₀ m₀ Z Fx BT HT val₂ val₃ shT nT ok) (hidSmall_famG Z Zp Np cF run₂ run₃ B G H nB
      _) hx
      hlen
    (fun _ _ => trivial) trivial (fun _ _ => trivial)
    (fun v i b s _ _ => plainStart_len _ c hℓ v i b s)
    (fun v i b s _ _ => plainStart_len _ c hℓ v i b s)
    (fun v i b s _ _ => plainStart_len _ c hℓ v i b s)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.hid_famG
#print axioms AtPublicFiles.AtFiles.bad_famG
#print axioms AtPublicFiles.AtFiles.hidSmall_famG
#print axioms AtPublicFiles.AtFiles.badSmall_famG
#print axioms AtPublicFiles.AtFiles.hid_keyZ
#print axioms AtPublicFiles.AtFiles.stopsT_keyZ
#print axioms AtPublicFiles.AtFiles.plainStart_len
#print axioms AtPublicFiles.AtFiles.premW_plain
#print axioms AtPublicFiles.AtFiles.plainStart
