-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBridgeFilled.lean: some of the hypotheses that E2E/KeyBridge.lean defines by name for the key
file's honest prover are proved of `keyHonestAny` (E2E/KeyHonest.lean), a prover structure built by
`honestBatchProverOfFile` from parameters that nothing here fixes, at the library's own wiring (`wireOfFullD`,
Johnson/Flat/Dec/WiresAtSizes.lean); at three public files Z, of `offlineProverInThreeProtocols`. With no hypothesis:
`BadZero` and `HidZero`; `ExtIsEnc`, at the table `tableOf`; `RunValsAt`, where what the three
rounds without a challenge send (the parameter J) is `keySeam val₂ val₃`. At the empty fall only:
`FallZero`. Reworded, not shown: `RunForm`, under a hypothesis that is the clause in other words.
E2E/KeyBridge.lean gives, from its hypotheses, clauses that the acceptance side
(`OnBytes.Prover.HonFit`) and the privacy side (`OnBytes.WholeKey.PremW`) have on the key file's
prover. The book of coins B (`ProverCoinCounts`), the prover structure H (`ProofFile.Honest.Prover`) and the
description Fx of the key file stay free parameters: nothing is claimed of any prover structure H.

A fall (`FallT`, E2E/KeyBridge.lean) is a set of verifier randomness, at a private input, an
instance and a coin of the prover's, that is set aside on the acceptance side. The empty fall sets
nothing aside.

At any parameters of the library's three protocols of the full size (`threeProtocolsAtFullSize`,
Johnson/Flat/Dec/WiresAtSizes.lean).
  `badZero_key`, `hidZero_key`: the two parts of the abort set do not depend on the proof-of-work
    test bits, in the one direction that `BadZero` and `HidZero` state: if verifier randomness with
    its test bits set to 0 lies in the public part (`Bad`), or in the part that may depend on the
    private input (`Hid`), then so does the verifier randomness itself
  `whT_key`: so the clause `whT` of `HonFit` (Johnson/Prover/All/OfHonest.lean), at the empty fall:
    word for word up to unfolding (`zeroT` for the test bits set to 0, `∪ ∅` for the fall)
  `extIsEnc_key`: where the external string is the table of the configuration's encoder (`tableOf`),
    it is the object's encoded index (`ExtIsEnc`; the clause `extT` of `HonFit`, and the clause T of
    `OnBytes.WholeKey.ExtEnc`)
  `runValsAt_key`: at J := `keySeam val₂ val₃` (so the key type of H is `OnBytes.TableKey`) and at
    every predicate ok on indices: `pvKey` at the plain parts of a run of the shell `keyHonestAny`
    is `rvKey` at the run's coin (`RunValsAt`; the clause T of `OnBytes.WholeKey.RunVals`,
    Johnson/WholeKey/Premises.lean). `RunValsAt` asks this outside the abort set; the proof gives it
    at all verifier randomness
  `runForm_key`: each coin's run values have a form that all values of the two maps have: if okV
    holds of (`val₂ r2`, `val₃ r3`) at all r2 and r3 (the hypothesis h), it holds of `rvKey` at
    every coin (`RunForm`; the clause `okT` of `OnBytes.WholeKey.CoinsFit`, same file)
  `pvKey`, `rvKey`: definitions: the two run values. `pvKey` reads them off a transcript's plain
    parts: the field `run` of the joining round's plain part, and the seam's plain part, which is a
    byte string. `rvKey` reads them off the coin: `val₂` and `val₃` at the coin's two components for
    the run values
  `fallZero_none`: the empty fall meets `FallZero`, vacuously. General in the object, in the honest
    prover (`Honest`) and in the wiring
At three public files Z.
  `wireAtZ`: an abbreviation: `wireOfFullD` at the parameters of Z; K and depthReqT stay free
  `badZero_obj`, `hidZero_obj`, `whT_obj`, `extIsEnc_obj`, `runValsAt_obj`: the same as the theorems
    above that end in `_key`, at `offlineProverInThreeProtocols` and, where a wiring is named, at `wireAtZ`: by
    unfolding

By what. `badZero_key` and `hidZero_key` are one direction of `keyHonest_bad_zero` and
`keyHonest_hid_zero`, and `whT_key` is `keyHonest_wh_zero` at the empty fall (all three
E2E/KeyHonestBlind.lean, which also defines `zeroT` and `zeroTAt`). `runValsAt_key` joins
`keySeam_plain` (E2E/KeyHonestPlain.lean, which also defines `keyChains`) with `plJ_plains` and
`pl3_plains` (E2E/BridgeRunVals.lean). `extIsEnc_key` and `extIsEnc_obj` hold by `rfl`. The other
four at Z call the general theorems: `offlineProverInThreeProtocols` is `keyHonestAny` at the parameters of Z
(`keyHonestObj_eq`, E2E/KeyHonest.lean).

Limits.
- These are the clauses that hold of the shell `keyHonestAny` whatever is put into it: no proof here
  uses anything about a part of the prover's for a sub-protocol (`Placed`). They hold too at a
  prover structure H that does nothing, for instance at one that has no such part.
- `BadZero` and `HidZero` say nothing on how large the abort set is. The limits of
  E2E/KeyHonestBlind.lean hold of `badZero_key`, `hidZero_key` and `whT_key` too.
- `whT_key` and `whT_obj` are at the empty fall. At any other fall, whoever proves `whT` has to show
  `FallZero` of that fall.
- The clauses `accT` (acceptance outside the abort set and the fall: `AccLaw`) and `prT` (the
  measure of the abort set and the fall together) of `HonFit` are not proved here.
- K, the number of blocks for a round's verifier message, and depthReqT, the depth of the key file's
  request tree, are free parameters of the wiring.
- `pvKey` and `rvKey` are defined in this file: that they are the maps of a scheme's honest side is
  not shown. E2E/BridgePremWKey.lean sets them as the fields pvT and rvT of `restKey`: by
  definition.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBridge
import E2E.KeyHonestBlind
import E2E.KeyHonestPlain
import E2E.BridgeRunVals

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyBridge
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The empty fall meets `FallZero`, vacuously: nothing lies in it. -/
theorem fallZero_none {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}
    (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)) {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) :
    FallZero hT W (fun _ _ _ => ∅) := fun _ _ _ _ h => h.elim

end AtPublicFiles.KeyBridge

namespace AtPublicFiles.AtFiles
open Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyBridge
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)

section General
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fx : FileDescription KeyInst)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (runK : RecFull → View → View → View → Bool)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

/-- **The public part of the abort set (`Bad`) does not depend on the test bits**, in the one
direction that `BadZero` states. -/
theorem badZero_key :
    BadZero
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P)
      (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) :=
  fun ρ h => (keyHonest_bad_zero A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext
    runK P K depthReqT ρ).1 h

/-- **Nor does the part that may depend on the private input (`Hid`)**, in the one direction that
`HidZero` states. -/
theorem hidZero_key :
    HidZero
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P)
      (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) :=
  fun w x ρ h => (keyHonest_hid_zero A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh
    ext runK P K depthReqT w x ρ).1 h

/-- **The clause `whT` of `HonFit`, word for word up to unfolding, at the empty fall.** -/
theorem whT_key :
    ∀ w x
      (_ : (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
        P).Coin) ρ,
      zeroT A R DK DP runP ds xs dec rK rP depthReq early salt runK P K depthReqT ρ ∈
          (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
            P).withheld w x ∪ ∅ →
        ρ ∈ (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
            P).withheld w x ∪ ∅ :=
  keyHonest_wh_zero A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P K
    depthReqT (fun _ _ _ => ∅) fun _ _ _ _ h => h.elim

/-- **At the encoder's table (`tableOf`) the external string is the object's encoded index.** -/
theorem extIsEnc_key :
    ExtIsEnc
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh
        (tableOf A R DK) runK P) :=
  fun _ _ _ => rfl

end General

section Filled
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fx : FileDescription KeyInst)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  {Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst
    OnBytes.TableKey Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray) (sh : OnBytes.TableKey → Fx.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (runK : RecFull → View → View → View → Bool)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- The two run values, read off a transcript's plain parts: the field `run` of the joining round's
plain part, and the seam's plain part. -/
def pvKey (DK : WholeD) (rK : RecFull) (π : Plains (keyChains DK rK).sh) : ByteArray × ByteArray :=
  (((keyChains DK rK).plJ π).run, (keyChains DK rK).pl3 π)

/-- The two run values, read off the coin: `val₂` and `val₃` at its two components for the run
values. -/
def rvKey (κ : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) :
    ByteArray × ByteArray := (val₂ κ.1.2, val₃ κ.2.2)

/-- **At `keySeam` the run values in the plain parts are the coin's.** `RunValsAt` asks this outside
the abort set; the proof gives it at all verifier randomness. -/
theorem runValsAt_key (ok : (DecR.configurationOfStoredTable A R).I → Prop) :
    RunValsAt
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H
        (keySeam A R val₂ val₃) sh ext runK P) ok (pvKey DK rK) (rvKey B val₂ val₃) := by
  intro i r e κ ρ _ _
  obtain ⟨-, h2, h3⟩ := keySeam_plain A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H val₂
    val₃ sh ext runK P i r e _ κ ρ
  exact Prod.ext
    ((congrArg Compile.Joined.JoinMsg.run (AtPublicFiles.Bridge.plJ_plains (keyChains DK rK) _)).trans
      (congrArg (fun z => z.2.run) h2))
    ((AtPublicFiles.Bridge.pl3_plains (keyChains DK rK) _).trans (congrArg Prod.snd h3))

/-- Each coin's run values have a form that all values of the two maps `val₂` and `val₃` have. The
hypothesis h is the clause in other words. -/
theorem runForm_key (okV : ByteArray × ByteArray → Prop) (h : ∀ r2 r3, okV (val₂ r2, val₃ r3)) :
    RunForm
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H
        (keySeam A R val₂ val₃) sh ext runK P) okV (rvKey B val₂ val₃) :=
  fun κ => h κ.1.2 κ.2.2

end Filled

/-! ## At three public files Z -/

section AtZ
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (P : (filesAt Z).Provers)
  (K depthReqT : ℕ)

/-- The library's wiring at Z, with K blocks for a round's verifier message and the depth depthReqT
of the key file's request tree. -/
abbrev wireAtZ :=
  wireOfFullD (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF
    PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) P K depthReqT

section Any
variable (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Ky Tr X₀ X')
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed KeyInst Ky
    (OnBytes.Maker.FrontMsg (List OnBytes.E)) (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

theorem badZero_obj : BadZero (offlineProverInThreeProtocols Z Fx B H J sh ext P) (wireAtZ Z P K depthReqT) :=
  badZero_key _ _ _ _ Fx _ _ _ _ _ _ _ _ _ B H J sh ext _ P K depthReqT

theorem hidZero_obj : HidZero (offlineProverInThreeProtocols Z Fx B H J sh ext P) (wireAtZ Z P K depthReqT) :=
  hidZero_key _ _ _ _ Fx _ _ _ _ _ _ _ _ _ B H J sh ext _ P K depthReqT

theorem whT_obj :
    ∀ w x (_ : (offlineProverInThreeProtocols Z Fx B H J sh ext P).Coin) ρ,
      zeroTAt Z P K depthReqT ρ ∈ (offlineProverInThreeProtocols Z Fx B H J sh ext P).withheld w x ∪ ∅ →
        ρ ∈ (offlineProverInThreeProtocols Z Fx B H J sh ext P).withheld w x ∪ ∅ :=
  whT_key _ _ _ _ Fx _ _ _ _ _ _ _ _ _ B H J sh ext _ P K depthReqT

theorem extIsEnc_obj :
    ExtIsEnc (offlineProverInThreeProtocols Z Fx B H J sh
      (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK) P) :=
  fun _ _ _ => rfl

end Any

theorem runValsAt_obj
    (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Tr X₀ X')
    (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray) (sh : OnBytes.TableKey → Fx.S₂)
    (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
      (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
    (ok : (Cz Z).I → Prop) :
    RunValsAt
      (offlineProverInThreeProtocols Z Fx B H
        (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) sh ext P) ok
      (pvKey (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).G.rec₀) (rvKey B val₂ val₃) :=
  runValsAt_key _ _ _ _ Fx _ _ _ _ _ _ _ _ _ B H val₂ val₃ sh ext _ P ok

end AtZ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.KeyBridge.fallZero_none
#print axioms AtPublicFiles.AtFiles.badZero_key
#print axioms AtPublicFiles.AtFiles.hidZero_key
#print axioms AtPublicFiles.AtFiles.whT_key
#print axioms AtPublicFiles.AtFiles.extIsEnc_key
#print axioms AtPublicFiles.AtFiles.runValsAt_key
#print axioms AtPublicFiles.AtFiles.runForm_key
#print axioms AtPublicFiles.AtFiles.badZero_obj
#print axioms AtPublicFiles.AtFiles.hidZero_obj
#print axioms AtPublicFiles.AtFiles.whT_obj
#print axioms AtPublicFiles.AtFiles.extIsEnc_obj
#print axioms AtPublicFiles.AtFiles.runValsAt_obj
#print axioms AtPublicFiles.AtFiles.pvKey
#print axioms AtPublicFiles.AtFiles.rvKey
#print axioms AtPublicFiles.AtFiles.wireAtZ
