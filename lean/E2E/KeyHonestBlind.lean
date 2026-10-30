-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyHonestBlind.lean: the abort set of `keyHonestAny` does not depend on the proof-of-work test
bits of the verifier's messages. `keyHonestAny` (E2E/KeyHonest.lean) is a prover structure
(`Honest`, Iop/InteractiveOracleProof.lean) for the key file's protocol, built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes. Which bits are
test bits is read off the key file's part of the library's own wiring of the full size's three
protocols (`wireOfFullD`, Johnson/Flat/Dec/WiresAtSizes.lean). `RoundsQueryLayout.zero s A W ρ`
(OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) is the verifier randomness ρ with all test bits set to 0. The
statements are on the abort set only. E2E/KeyBridgeFilled.lean calls `keyHonest_hid_zero`,
`keyHonest_bad_zero` and `keyHonest_wh_zero`. General in every parameter of `keyHonestAny` and of
`wireOfFullD`, among them the description Fx of the key file (its IOP as written in Lean), the book
of coins B (`ProverCoinCounts`), the prover structure H (`ProofFile.Honest.Prover`), J (what the three rounds without
a challenge send), the key file's decision runK, the number K of hash outputs for a verifier's
message, and the depth depthReqT of the key file's request tree.

  `keyHonest_hid_zero`: ρ with the test bits set to 0 lies in the part of the abort set that may
    depend on the private input (`Hid`) just when ρ does
  `keyHonest_bad_zero`: the same for the public part (`Bad`)
  `keyHonest_withheld_zero`: so the same for the abort set (`withheld`: the union of the two parts)
  `keyHonest_wh_zero`: call a set closed if ρ lies in it whenever ρ with the test bits set to 0
    does. For any family FT of further sets, by private input, instance and coin, whose sets are
    closed (the hypothesis hF), the abort set and FT together are closed. Where every set of FT is
    empty, hF holds vacuously. The conclusion has the form of the clause `whT` of `HonFit`
    (Johnson/Prover/All/OfHonest.lean)
  `keyHonestCut_hid_zero`, `keyHonestCut_bad_zero`: at three public files Z: the first two for
    `keyHonestCut`, the prover structure at the object whose index type is cut to the matrices in
    range (`objAt Z P`, E2E/ObjectAtFiles.lean), under the same map on verifier randomness: that of
    the wiring of the object at Z that is not cut (`zeroTAt`)
  `zeroT`: an abbreviation: `RoundsQueryLayout.zero` at the key file's part of `wireOfFullD`
  `zeroTAt`: an abbreviation: `zeroT` at the parameters of Z

By what. `keyHonest_hid_zero` and `keyHonest_bad_zero` are `hid_zero` and `bad_zero`
(E2E/DrawsBlind.lean), which state the same of the single-run prover of `honestBatchProverOfFile` under the wiring
data `wiresOf` (OnBytes/Maker/Wire.lean). They are called at the arguments of `offlineBatchProver`
(E2E/KeyHonest.lean), the first at the written key `keyInstanceOfOutOfDomainSample x` of the instance x. By unfolding, the
two parts of the abort set of `keyHonestAny` are that prover's (stated in `keyHonestAny_fields`,
E2E/KeyHonest.lean), and the rounds' data in the key file's part of `wireOfFullD` are those of
`wiresOf`. `keyHonest_withheld_zero` joins the two, and `keyHonest_wh_zero` joins it with hF. The
two theorems at Z call the first two at the parameters of Z. `keyHonestCut` is `reW` at
`onFst Subtype.val` (E2E/CutIndex.lean) of `offlineProverAtFilesDecision`, which is `keyHonestAny` at these
parameters (`keyHonestObj_eq`, E2E/KeyHonest.lean); `reW` keeps `Bad` and reads the private input of
`Hid` through the inclusion.

Limits. The statements are on the abort set only: nothing on what is sent, nothing on acceptance (a
verifier that tests proof of work does read the test bits), no probability. They hold at every
prover structure H, also at one that has no part for any sub-protocol (`Placed`). They say nothing
on how large the abort set is: what they state holds of the empty set and of the set of all verifier
randomness alike. The wiring is the one that the library writes out, `wireOfFullD`. runK is a free
parameter: the abort set does not read it. At rounds' data without proof of work, setting the test
bits to 0 changes nothing, and the statements hold trivially. At the cut object the map on verifier
randomness is that of the wiring over the object that is not cut. That a wiring over the cut object
has the same map is not stated here. No property of a protocol is stated: nothing on completeness,
soundness or hiding.
-/
import E2E.KeyHonest
import E2E.DrawsBlind
import Johnson.Flat.Dec.WiresAtSizes

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Prob Hiop AtPublicFiles.Cut
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

/-- ρ with all test bits set to 0, under the key file's part of the wiring `wireOfFullD`. -/
abbrev zeroT
    (ρ : Rho ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
      P).offline.shape) :
    Rho ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).offline.shape :=
  RoundsQueryLayout.zero ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
                 P).offline.shape
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT
    (wTC (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)).sh ρ

/-- **The part of the abort set that may depend on the private input (`Hid`) does not depend on the
test bits**: ρ with the test bits set to 0 lies in it just when ρ does. -/
theorem keyHonest_hid_zero
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull)
    (ρ : Rho ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
      P).offline.shape) :
    zeroT A R DK DP runP ds xs dec rK rP depthReq early salt runK P K depthReqT ρ ∈
        (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
          P).Hid w x ↔
      ρ ∈ (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
          P).Hid w x :=
  AtPublicFiles.Reads.hid_zero (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty K (chalP .two K) Fx silKey B H J sh ext w (keyInstanceOfOutOfDomainSample x) ρ

/-- **The same for the public part (`Bad`).** -/
theorem keyHonest_bad_zero
    (ρ : Rho ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
      P).offline.shape) :
    zeroT A R DK DP runP ds xs dec rK rP depthReq early salt runK P K depthReqT ρ ∈
        (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
          P).Bad ↔
      ρ ∈ (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
          P).Bad :=
  AtPublicFiles.Reads.bad_zero (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty K (chalP .two K) Fx silKey B H J sh ext ρ

/-- So the same for the abort set (`withheld`), the union of the two parts. -/
theorem keyHonest_withheld_zero
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull)
    (ρ : Rho ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
      P).offline.shape) :
    zeroT A R DK DP runP ds xs dec rK rP depthReq early salt runK P K depthReqT ρ ∈
        (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
          P).withheld w x ↔
      ρ ∈ (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
          P).withheld w x :=
  or_congr
    (keyHonest_bad_zero A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P K
      depthReqT ρ)
    (keyHonest_hid_zero A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P K
      depthReqT w x ρ)

/-- **The abort set and a closed family FT of further sets are closed together.** A set is closed if
ρ lies in it whenever ρ with the test bits set to 0 does; hF says so of each set of FT. -/
theorem keyHonest_wh_zero
    (FT : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
      RecFull →
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
        P).Coin →
      Set (Rho ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
        P).offline.shape))
    (hF : ∀ w x c ρ,
      zeroT A R DK DP runP ds xs dec rK rP depthReq early salt runK P K depthReqT ρ ∈ FT w x c →
        ρ ∈ FT w x c) :
    ∀ w x c ρ,
      zeroT A R DK DP runP ds xs dec rK rP depthReq early salt runK P K depthReqT ρ ∈
          (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
            P).withheld w x ∪ FT w x c →
        ρ ∈ (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
            P).withheld w x ∪ FT w x c :=
  fun w x c ρ h => h.elim
    (fun h => Or.inl ((keyHonest_withheld_zero A R DK DP Fx runP ds xs dec rK rP depthReq early salt
      B H J sh ext runK P K depthReqT w x ρ).1 h))
    (fun h => Or.inr (hF w x c ρ h))

end General

/-! ## At three public files Z, at the cut object -/

section AtZ
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed KeyInst Ky
    (OnBytes.Maker.FrontMsg (List OnBytes.E)) (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (P : (filesAt Z).Provers) (K depthReqT : ℕ)

/-- `zeroT` at the parameters of Z: ρ with all test bits set to 0, under the key file's part of
`wireOfFullD` over the object at Z that is not cut. -/
abbrev zeroTAt (ρ : Rho (filesAt Z).key.shape) : Rho (filesAt Z).key.shape :=
  zeroT (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).runK P K depthReqT ρ

/-- **At the cut object: the same for the part of the abort set that may depend on the private input
(`Hid`).** -/
theorem keyHonestCut_hid_zero (w : Ix × (objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed) (x : RecFull)
    (ρ : Rho (filesAt Z).key.shape) :
    zeroTAt Z P K depthReqT ρ ∈ (keyHonestCut Z Fx B H J sh ext P).Hid w x ↔
      ρ ∈ (keyHonestCut Z Fx B H J sh ext P).Hid w x :=
  keyHonest_hid_zero (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP Fx (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B H J sh ext (dataAtFiles flashProveData Z).runK P K depthReqT
    (onFst Subtype.val w) x ρ

/-- **At the cut object: the same for the public part (`Bad`).** -/
theorem keyHonestCut_bad_zero (ρ : Rho (filesAt Z).key.shape) :
    zeroTAt Z P K depthReqT ρ ∈ (keyHonestCut Z Fx B H J sh ext P).Bad ↔
      ρ ∈ (keyHonestCut Z Fx B H J sh ext P).Bad :=
  keyHonest_bad_zero (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP Fx (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B H J sh ext (dataAtFiles flashProveData Z).runK P K depthReqT ρ

end AtZ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keyHonest_hid_zero
#print axioms AtPublicFiles.AtFiles.keyHonest_bad_zero
#print axioms AtPublicFiles.AtFiles.keyHonest_withheld_zero
#print axioms AtPublicFiles.AtFiles.keyHonest_wh_zero
#print axioms AtPublicFiles.AtFiles.keyHonestCut_hid_zero
#print axioms AtPublicFiles.AtFiles.keyHonestCut_bad_zero
#print axioms AtPublicFiles.AtFiles.zeroT
#print axioms AtPublicFiles.AtFiles.zeroTAt
