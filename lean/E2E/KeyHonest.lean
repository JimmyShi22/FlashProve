-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyHonest.lean: `keyHonest` is a value of the type that the library's object (`Files.withProvers`,
OnBytes/Flat/Object.lean) asks of the key file's honest prover. It is built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean), the honest side that is written over the IOP of a file
as written in Lean (below: a description of the file), called at the key file's parameters.
E2E/SessionHonest.lean calls `honestBatchProverOfFile` for the proof file. No part of a prover is written here: the
book of coins B (`ProverCoinCounts`), the prover structure H (`ProofFile.Honest.Prover`) and what the three rounds
without a challenge send (J) are free parameters, and so are the committed table (ext) and the
shared chain's first state (sh). For J, ext and sh one value each is defined (`keySeam`, `tableOf`,
`keyFirst`). Definitions, equations (most hold by unfolding), and three lemmas that carry a
predicate from one prover structure to another. General in the claims, the rounds' data, the
description and the decisions; section 4 is at three public files Z.

The instance type. `honestBatchProverOfFile` is called at the description's own instance type: a stored table's key
as the program writes it (`KeyInst`; below: a written key). The object's instances at the key file
are OOD samples (`RecFull`). `Key.keyInstanceOfOutOfDomainSample` is the library's map from an OOD sample to its written key,
and the library's own `BatchHonestProver.comap` (Hiop/RecKit.lean) reads the honest side's instances through
that map. So nothing of the honest side is stated anew. The other way, `honestBatchProverOfFile` called at OOD
samples over the pulled-back description, is not taken here.

The arguments of `honestBatchProverOfFile` in `offlineBatchProver`.
  instance type       `KeyInst`: the written key of a stored table. There is no request
  description         Fx, a free parameter, at that instance type. The library's maker gives
                      `keyFileDescription X N P`
  challenge types     `ckP .two`: those of the second field
  rounds' data        `DK.at frS.P.T.a`: the key file's data DK, at the table's depth
  fixed plain parts   `front₀ rK`, `join₀ rK`, `ByteArray.empty`: those of the library's key file's
                      protocol
  test                `silKey` (E2E/KeyProtocolOverDescription.lean), on the three plain parts as sent: both
                      copies of the answers are the key's; the copy's number is 0
  private input       index; pads with encoding randomness; OOD seed
  key type            Ky: what the shared chain may read of the instance
  J                   a function of two coins, one for the second and one for the third chain's run
                      value, to a `KeyAndJoiningRoundMessages`: the key, made without an instance, and the three plain
                      parts: what the front round, the joining round and the seam send
  sh                  the shared chain's first state, as a function of the key
  ext                 the committed table, whole, as a function of the private input

  `keyHonest … P`: a definition: the fields of `offlineOneInstanceProver`, with the type
    `Honest (F'.withProvers P).offline (I × (F'.withProvers P).EncodingRandomness × (F'.withProvers P).OutOfDomainSeed)`, for every P. F' is the library's
    three protocols whose key file's decision is the pulled-back description's (`filesWithKey`,
    E2E/KeyProtocolOverDescription.lean). The private input is the object's own, word for word: no map on it, no
    cast. The protocol of `offlineOneInstanceProver` and `(F'.withProvers P).offline` differ in the test on the three plain
    parts only; the two tests are equal by one equation (`silK_fun`), and `atDecision` puts the
    fields from the one protocol to the other: see Limits
  `keyHonest_law`: every predicate on protocol and prover that holds of `offlineOneInstanceProver` holds of
    `keyHonest`
  `keyHonestAny … runK P`: a definition: the same fields at the three protocols with any key file's
    decision runK. `keyHonestAny_self`: at the pulled-back description's own decision it is
    `keyHonest`
  `keyHonestAny_law`: where the pulled-back description's decision is runK, a predicate that names
    the object too passes in the form "for every P": if it holds of `keyHonest` at every P, it holds
    of `keyHonestAny` at runK and every P
  `keyHonest_ext`, `keyHonest_coin`, `keyHonest_strat`, `keyHonest_bad`, `keyHonest_hid`: by
    unfolding: its table is the parameter ext; its coins are the three chains' coins (`Purse`) and
    the two coins for the run values; its strategy and the part of its abort set that may depend on
    the private input (`Hid`) are those of `offlineBatchProver`'s single-run prover at the written key of the
    instance; the public part (`Bad`) is that prover's. `keyHonestAny_fields`: the same five at any
    runK
  `offlineProverAtFilesDecision Z …`: a definition: at three public files Z: the same fields, with the type of an
    honest prover of `(filesAt Z).key` itself, at every Z and description, with no hypothesis: by
    `atDecision`. The type says nothing about the decision
  `keyHonestAt_law`: where the pulled-back description's decision is the key file's at Z, every
    predicate on protocol and prover that holds of `offlineOneInstanceProverAtFiles` holds of `offlineProverAtFilesDecision`
  `offlineProverInThreeProtocols`, `keyHonestObj_eq`: `offlineProverAtFilesDecision` has the type of the first prover of the object at
    Z, `(filesAt Z).withProvers P`, for every P; it is `keyHonestAny` at the parameters of Z, so
    `keyHonestAny_fields` and `keyHonestAny_law` speak of it
  `keyHonestCut Z …`: a definition: the same at the object whose index type is cut to the matrices
    in range (`objAt Z P`, E2E/ObjectAtFiles.lean), for every P: the index is read through the
    inclusion
  `offlineBatchProver`: a definition: `honestBatchProverOfFile` at the arguments above
  `offlineOneInstanceProver`: a definition: `offlineBatchProver` with its instances read through `Key.keyInstanceOfOutOfDomainSample`, and of that the
    single-run prover (`BatchHonestProver.one`, Iop/Batch.lean): a batch of one, in which the strategies of
    the shared part and of the one run are zipped. `offlineOneInstanceProverAtFiles`: it at the parameters of Z
  `withKey P h`, `withKey_hT`: provers of three protocols with the first replaced by h; the object's
    own first prover is then h
  `tableOf`, `tableOf_enc`: a value for ext, by the configuration's encoder: the table at (i, r, e)
    is the object's encoded index at (i, r): by unfolding
  `sampleOf`, `recOf_eq`: the honest OOD sample, in the configuration's fields; it is the object's
    `recOf`
  `keySeam val₂ val₃`: a definition: one value for J. The key is the field `key` of the written key
    of the honest OOD sample; the front round sends its answers and the number 0; the joining round
    its answers and the second chain's run value; the seam the third chain's
  `keySeam_key`, `keySeam_join`: the key depends on neither run value, and what the joining round
    sends does not depend on the third chain's. The head of
    Johnson/Desc/ProofFile/Honest/Record.lean asks of whoever calls the honest side that these two
    do not depend on the third chain's run value
  `keySeam_public`: where the instance is the written key of the honest OOD sample, the key and all
    three plain parts are functions of the instance and the two run values
  `keySeam_silent`, `keySeam_silentK`: there the test on the three plain parts accepts them, in both
    forms (`silKey` at the written key, `silK` at the OOD sample)
  `keyFirst X N P`, `keyFirst_is`: at a key file's description `keyFileDescription X N P`, the shared chain's
    first state is a function of the instance's key only: by unfolding. StratC.lean's head leaves to
    whoever sets sh the hypothesis that sh at the instance's key is the description's own first
    state. It is met at sh := `keyFirst X N P` and a prover structure whose field `key` returns the
    instance's field `key`

By what. `honestBatchProverOfFile` (StratC.lean), `BatchHonestProver.comap` (Hiop/RecKit.lean) and `BatchHonestProver.one`
(Iop/Batch.lean) make `offlineOneInstanceProver`. `atDecision` (E2E/KeyProtocolOverDescription.lean) makes `keyHonest`,
`keyHonestAny` and `offlineProverAtFilesDecision` of it, and `reW` at `onFst` (E2E/CutIndex.lean) makes
`keyHonestCut`. `keyHonest_law` is `atTest_law`, and `keyHonestAt_law` is `atDecision_law`, both at
`silK_fun` (all three E2E/KeyProtocolOverDescription.lean). `keyHonestAny_law` and `keySeam_public` substitute
their equation. `keySeam_silent` unfolds `silKey`, `silentOf` (OnBytes/Maker/SilentParts.lean) and
`keySeam`; `keySeam_silentK` rewrites by `silK_fun`. `keyFirst` is `Desc.K14.first`
(Johnson/Desc/K14/Blocks.lean). Every other proof is by `rfl`.

Hypotheses. h, in `keyHonestAny_law` and `keyHonestAt_law`: the pulled-back description's decision,
`(Fx.pull keyInstanceOfOutOfDomainSample).run`, is runK; in the second, runK is the key file's decision at Z,
`(dataAtFiles flashProveData Z).runK`, and at Fx := `keyFileDescription X N P` h is the field `KeyNamed.run`
(E2E/KeyProtocolOverDescription.lean). hp, in the three lemmas on predicates: p holds of the prover structure
from which it passes. hx, in `keySeam_public`: the instance x is the written key of the honest OOD
sample.

Limits.
- Nothing is shown of any prover: no completeness, nothing on what a view shows. All of this holds
  at every book of coins B, prover structure H and J, also at a prover structure H that has no part
  for any sub-protocol (`Placed`), and at a description that rejects everything: `keyHonest` and the
  others are prover structures (`Honest`) built by `honestBatchProverOfFile` from parameters that nothing here
  fixes, and none is a prover that is written out.
- The type of an honest prover reads only the shape of its protocol's rounds, and `atDecision` is
  defined at every two tests and every two decisions. So that a term has the type "honest prover of
  this protocol" says nothing about the protocol's decision. `keyHonest` calls `atDecision` at one
  decision and at two tests that are equal (`silK_fun`); `keyHonestAny`, `offlineProverAtFilesDecision`,
  `offlineProverInThreeProtocols` and `keyHonestCut` are defined at every runK, or at every Z, and at every
  description.
- `keySeam_silent` is no statement of completeness: it speaks of one test of the verifier's, at one
  value of J. That test is on three rounds that no part of the prover's plays, and it reads neither
  run value.
- `keySeam`'s front round does not read its instance argument: it makes the answers from the index,
  the pads and the OOD seed. At a valid pair of private input and instance, the instance is the
  written key of that sample, so there these are the instance's own answers (`keySeam_public`).
  Where the instance's answers are others, the test rejects them (by the definition of `silentOf`;
  no theorem here).
- No statement here asks that ext holds what the prover structure H reads as its stored table
  (`H.stored`).
- That the key which `keySeam` makes is the key which H reads from the instance (`H.key`) holds at
  the written key of the honest OOD sample if `H.key` returns the instance's field `key`: a
  hypothesis on H that no statement here has.
- The rounds' data DK are a free parameter; that the data at Z are the description's own is
  `KeyNamed.data_at` (E2E/KeyProtocolOverDescription.lean). Where the IOP's own test on the public files
  (`protocolDataWellFormed`) rejects, the data at Z are three empty lists (`emptyRoundsData`,
  Johnson/Goal/Tie/DescriptionOfData.lean; `builtS_dead`, Johnson/Goal/Conditions/NumbersAtThe.lean; no
  theorem here): `offlineProverAtFilesDecision` is then a prover of a protocol that has only the three rounds without
  a challenge.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyProtocolOverDescription
import Johnson.Desc.ProofFile.Honest.StratC

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD reductionOfWholeFile)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)

/-! ## 1. The prover structure, at any parameters -/

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

/-- `honestBatchProverOfFile` over the key file's description Fx, at the description's own instance type. -/
abbrev offlineBatchProver :
    BatchHonestProver (keyOverOwn DK Fx rK)
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :=
  honestBatchProverOfFile (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty Fx silKey B H J sh ext

/-- `offlineBatchProver` with its instances read through `keyInstanceOfOutOfDomainSample`, the map that writes the key; of that, the
single-run prover (`BatchHonestProver.one`). Its protocol is the one over the pulled-back description, with
the test read through the map. -/
def offlineOneInstanceProver :
    Honest (reductionOfWholeFile (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
        ByteArray.empty (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) (Fx.pull keyInstanceOfOutOfDomainSample).run).toInteractiveOracleProof
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :=
  ((offlineBatchProver A R DK Fx rK B H J sh ext).comap keyInstanceOfOutOfDomainSample id).one

/-- **The fields of `offlineOneInstanceProver`, with the type of the key file's honest prover in the object at the
library's three protocols.** The book of coins B, the prover structure H, J (the key and the three
plain parts), sh and ext are arguments: no part of a prover is written. For every P; the private
input's type is written in the object's own fields `EncodingRandomness` and `OutOfDomainSeed`. -/
def keyHonest
    (P : (filesWithKey A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early
      salt).Provers) :
    Honest ((filesWithKey A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early salt).withProvers
        P).offline
      ((DecR.configurationOfStoredTable A R).I ×
        ((filesWithKey A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early salt).withProvers
          P).EncodingRandomness ×
        ((filesWithKey A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early salt).withProvers
          P).OutOfDomainSeed) :=
  atDecision (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) OnBytes.Flat.silK (Fx.pull keyInstanceOfOutOfDomainSample).run
    (Fx.pull keyInstanceOfOutOfDomainSample).run (offlineOneInstanceProver A R DK Fx rK B H J sh ext)

/-- **The same fields at the library's three protocols with any key file's decision runK.** The type
reads only the shape of the rounds, and says nothing about runK. -/
def keyHonestAny (runK : RecFull → View → View → View → Bool)
    (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers) :
    Honest ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).offline
      ((DecR.configurationOfStoredTable A R).I ×
        ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).EncodingRandomness ×
        ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).OutOfDomainSeed) :=
  atDecision (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) OnBytes.Flat.silK (Fx.pull keyInstanceOfOutOfDomainSample).run
    runK (offlineOneInstanceProver A R DK Fx rK B H J sh ext)

variable
  (P : (filesWithKey A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early salt).Provers)

/-- At the pulled-back description's own decision it is `keyHonest`. -/
theorem keyHonestAny_self :
    keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext
      (Fx.pull keyInstanceOfOutOfDomainSample).run P =
      keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P := rfl

omit P in
/-- **For a predicate that names the object too** (or a wiring over it). Such a predicate reads the
provers P, whose type depends on the decision. Where the pulled-back description's decision is runK,
it passes in the form "for every P". -/
theorem keyHonestAny_law {runK : RecFull → View → View → View → Bool}
    (h : (Fx.pull keyInstanceOfOutOfDomainSample).run = runK)
    (p : (r : RecFull → View → View → View → Bool) →
      (P : (threeProtocolsAtFullSize A R DK DP r runP ds xs dec rK rP depthReq early salt).Provers) →
      Honest ((threeProtocolsAtFullSize A R DK DP r runP ds xs dec rK rP depthReq early salt).withProvers P).offline
        ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) →
      Prop)
    (hp : ∀ P, p (Fx.pull keyInstanceOfOutOfDomainSample).run P
      (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P)) :
    ∀ P, p runK P
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P) := by
  subst h
  exact hp

/-- **Every predicate on protocol and prover that holds of `offlineOneInstanceProver` holds of `keyHonest`.** p: any
such predicate, at any test on the three plain parts. -/
theorem keyHonest_law
    (p : (s : RecFull → OnBytes.Maker.FrontMsg (List OnBytes.E) →
        Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool) →
      Honest (reductionOfWholeFile (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
        (OnBytes.Flat.join₀ rK) ByteArray.empty s (Fx.pull keyInstanceOfOutOfDomainSample).run).toInteractiveOracleProof
        ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) →
      Prop)
    (hp : p (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) (offlineOneInstanceProver A R DK Fx rK B H J sh ext)) :
    p OnBytes.Flat.silK
      (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P) :=
  atTest_law (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty silK_fun.symm (Fx.pull keyInstanceOfOutOfDomainSample).run p _ hp

/-- Its table is the parameter ext. -/
theorem keyHonest_ext :
    (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P).ext = ext :=
  rfl

/-- Its coins: the shared chain's coins and the coin for the second chain's run value; the two other
chains' coins and the coin for the third chain's run value. -/
theorem keyHonest_coin :
    (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P).Coin =
      ((Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) := rfl

/-- Its strategy at an OOD sample is that of `offlineBatchProver`'s single-run prover at the written key of
that sample. -/
theorem keyHonest_strat
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull) (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) :
    (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P).strat w x c =
      (offlineBatchProver A R DK Fx rK B H J sh ext).one.strat w (keyInstanceOfOutOfDomainSample x) c := rfl

/-- The public part of its abort set (`Bad`) is that of `offlineBatchProver`'s single-run prover. -/
theorem keyHonest_bad :
    (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P).Bad =
      (offlineBatchProver A R DK Fx rK B H J sh ext).one.Bad := rfl

/-- The rest of its abort set (`Hid`) at an OOD sample is that of `offlineBatchProver`'s single-run prover at
the written key of that sample. -/
theorem keyHonest_hid
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull) :
    (keyHonest A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext P).Hid w x =
      (offlineBatchProver A R DK Fx rK B H J sh ext).one.Hid w (keyInstanceOfOutOfDomainSample x) := rfl

omit P in
/-- **The same five at any key file's decision runK**: table, coins, strategy and the abort set's
two parts do not read it: by unfolding. -/
theorem keyHonestAny_fields (runK : RecFull → View → View → View → Bool)
    (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers) :
    (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P).ext =
      ext ∧
    (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P).Coin =
      ((Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) ∧
    (∀ w x c,
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
        P).strat w x c = (offlineBatchProver A R DK Fx rK B H J sh ext).one.strat w (keyInstanceOfOutOfDomainSample x) c) ∧
    (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P).Bad =
      (offlineBatchProver A R DK Fx rK B H J sh ext).one.Bad ∧
    ∀ w x,
      (keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
        P).Hid w x = (offlineBatchProver A R DK Fx rK B H J sh ext).one.Hid w (keyInstanceOfOutOfDomainSample x) :=
  ⟨rfl, rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl⟩

end General

/-- Provers of three protocols, with the key file's prover replaced by h. -/
def withKey {C : ConfigurationWithOutOfDomainSample} {F : Files C} (P : F.Provers)
    (h : Honest F.key (C.I × (C.Pad × C.Rnd) × C.Seed)) : F.Provers := ⟨h, P.hL, P.hB⟩

/-- The object's own first prover (its field `honestOfflineProver`) is then h. -/
theorem withKey_hT {C : ConfigurationWithOutOfDomainSample} {F : Files C} (P : F.Provers)
    (h : Honest F.key (C.I × (C.Pad × C.Rnd) × C.Seed)) : (F.withProvers (withKey P h)).honestOfflineProver = h := rfl

/-! ## 2. The table, the OOD sample, and one value for the three rounds without a challenge -/

section Seam
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A)

/-- The committed table of a private input, by the configuration's encoder. DK: any rounds' data;
only the type reads it. -/
def tableOf (DK : WholeD)
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str :=
  (DecR.configurationOfStoredTable A R).enc ((DecR.configurationOfStoredTable A R).hold w.1 w.2.1.1) w.2.1.2

/-- The honest OOD sample at an index, pads with encoding randomness, and an OOD seed. -/
def sampleOf (i : (DecR.configurationOfStoredTable A R).I) (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (e : (DecR.configurationOfStoredTable A R).Seed) : RecFull :=
  (e, (DecR.configurationOfStoredTable A R).smp e ((DecR.configurationOfStoredTable A R).hold i r.1))

/-- It is the object's `recOf`, for any three protocols and provers. -/
theorem recOf_eq (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) :
    (F.withProvers P).recOf i r e = sampleOf A R i r e := rfl

/-- The table is the object's encoded index (its field `encodeIndex`). -/
theorem tableOf_enc (DK : WholeD) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
    (i : (DecR.configurationOfStoredTable A R).I) (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (e : (DecR.configurationOfStoredTable A R).Seed) : tableOf A R DK (i, r, e) = (F.withProvers P).encodeIndex i r := rfl

variable {R₂ R₃ : Type} (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray)

/-- **One value for the parameter J.** val₂, val₃: the second and the third chain's run values as
bytes, as functions of two coins. -/
def keySeam (r2 : R₂) (r3 : R₃) :
    KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (DecR.configurationOfStoredTable A R).Seed
      KeyInst OnBytes.TableKey (OnBytes.Maker.FrontMsg (List OnBytes.E))
      (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray where
  keyOf := fun i r e => (keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key
  front := fun i r e _ => ⟨(keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key.record.toList, 0⟩
  join := fun i r e => ⟨(keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key.record.toList, val₂ r2⟩
  seam := fun _ _ _ _ => val₃ r3

/-- The key does not depend on the two run values. -/
theorem keySeam_key (r2 r2' : R₂) (r3 r3' : R₃) :
    (keySeam A R val₂ val₃ r2 r3).keyOf = (keySeam A R val₂ val₃ r2' r3').keyOf := rfl

/-- What the joining round sends does not depend on the third chain's run value. -/
theorem keySeam_join (r2 : R₂) (r3 r3' : R₃) :
    (keySeam A R val₂ val₃ r2 r3).join = (keySeam A R val₂ val₃ r2 r3').join := rfl

/-- **Where the instance is the written key of the honest OOD sample, the key and the three plain
parts are functions of the instance and the two run values.** -/
theorem keySeam_public (r2 : R₂) (r3 : R₃) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed)
    (x : KeyInst) (hx : x = keyInstanceOfOutOfDomainSample (sampleOf A R i r e)) :
    (keySeam A R val₂ val₃ r2 r3).keyOf i r e = x.key ∧
    (keySeam A R val₂ val₃ r2 r3).front i r e x = ⟨x.key.record.toList, 0⟩ ∧
    (keySeam A R val₂ val₃ r2 r3).join i r e = ⟨x.key.record.toList, val₂ r2⟩ ∧
    (keySeam A R val₂ val₃ r2 r3).seam i r e x = val₃ r3 := by
  subst hx
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **There the test on the three plain parts accepts them.** It is one test of the verifier's. -/
theorem keySeam_silent (r2 : R₂) (r3 : R₃) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) :
    silKey (keyInstanceOfOutOfDomainSample (sampleOf A R i r e))
      ((keySeam A R val₂ val₃ r2 r3).front i r e (keyInstanceOfOutOfDomainSample (sampleOf A R i r e)))
      ((keySeam A R val₂ val₃ r2 r3).join i r e)
      ((keySeam A R val₂ val₃ r2 r3).seam i r e (keyInstanceOfOutOfDomainSample (sampleOf A R i r e))) = true := by
  simp [silKey, OnBytes.Maker.silentOf, keySeam]

/-- The same in the library's form of the test (`silK`), at the OOD sample itself. -/
theorem keySeam_silentK (r2 : R₂) (r3 : R₃) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) :
    OnBytes.Flat.silK (sampleOf A R i r e)
      ((keySeam A R val₂ val₃ r2 r3).front i r e (keyInstanceOfOutOfDomainSample (sampleOf A R i r e)))
      ((keySeam A R val₂ val₃ r2 r3).join i r e)
      ((keySeam A R val₂ val₃ r2 r3).seam i r e (keyInstanceOfOutOfDomainSample (sampleOf A R i r e))) = true := by
  rw [silK_fun]
  exact keySeam_silent A R val₂ val₃ r2 r3 i r e

end Seam

/-! ## 3. At a key file's description -/

section Desc
variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- The shared chain's first state, as a function of the table's key. -/
def keyFirst (ky : OnBytes.TableKey) : (keyFileDescription X N P).S₂ :=
  _root_.Desc.K14.first X.chains.made.sized.key.codes ky

/-- **The description's own first state of the shared chain is `keyFirst` at the instance's key**:
by unfolding. -/
theorem keyFirst_is (x : KeyInst) :
    (keyFileDescription X N P).start₂ ((keyFileDescription X N P).pub x) = keyFirst X N P x.key := rfl

end Desc

/-! ## 4. At three public files Z -/

section AtZ
variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed KeyInst Ky
    (OnBytes.Maker.FrontMsg (List OnBytes.E)) (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- `offlineOneInstanceProver` at the parameters of Z, over a description Fx. -/
abbrev offlineOneInstanceProverAtFiles :=
  offlineOneInstanceProver (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK Fx
    (dataAtFiles flashProveData Z).G.rec₀ B H J sh ext

/-- **The fields of `offlineOneInstanceProverAtFiles`, with the type of an honest prover of the key
file's protocol at Z itself.** At every Z and every description, with no hypothesis: the type reads
only the shape of the rounds, and says nothing about the decision. -/
def offlineProverAtFilesDecision : Honest (filesAt Z).key ((Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) :=
  atDecision (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀)
    ByteArray.empty (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) OnBytes.Flat.silK (Fx.pull keyInstanceOfOutOfDomainSample).run
    (dataAtFiles flashProveData Z).runK (offlineOneInstanceProverAtFiles Z Fx B H J sh ext)

/-- **Where the pulled-back description's decision is the key file's at Z, every predicate on
protocol and prover that holds of `offlineOneInstanceProverAtFiles` holds of `offlineProverAtFilesDecision`.** -/
theorem keyHonestAt_law (h : (Fx.pull keyInstanceOfOutOfDomainSample).run = (dataAtFiles flashProveData Z).runK)
    (p : (s : RecFull → OnBytes.Maker.FrontMsg (List OnBytes.E) →
        Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool) →
      (r : RecFull → View → View → View → Bool) →
      Honest (reductionOfWholeFile (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
        (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀)
        (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty s r).toInteractiveOracleProof
        ((Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → Prop)
    (hp : p (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) (Fx.pull keyInstanceOfOutOfDomainSample).run
      (offlineOneInstanceProverAtFiles Z Fx B H J sh ext)) :
    p OnBytes.Flat.silK (dataAtFiles flashProveData Z).runK (offlineProverAtFilesDecision Z Fx B H J sh ext) :=
  atDecision_law (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀)
    ByteArray.empty silK_fun.symm h p _ hp

/-- `offlineProverAtFilesDecision` has the type of the first prover of the object at Z, for every P. The type says
nothing about the decision: the definition is at every Z and every description. -/
def offlineProverInThreeProtocols (P : (filesAt Z).Provers) :
    Honest ((filesAt Z).withProvers P).offline
      ((Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) :=
  offlineProverAtFilesDecision Z Fx B H J sh ext

/-- It is `keyHonestAny` at the parameters of Z. -/
theorem keyHonestObj_eq (P : (filesAt Z).Provers) :
    offlineProverInThreeProtocols Z Fx B H J sh ext P =
      keyHonestAny (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
        (dataAtFiles flashProveData Z).DP Fx (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
        (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
        (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
        (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B H J sh ext (dataAtFiles flashProveData Z).runK P := rfl

/-- **The same at the object whose index type is cut to the matrices in range**: the index is read
through the inclusion. The type says nothing about the decision: the definition is at every Z and
every description. -/
def keyHonestCut (P : (filesAt Z).Provers) :
    Honest (objAt Z P).offline (Ix × (objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed) :=
  reW (offlineProverAtFilesDecision Z Fx B H J sh ext) (onFst Subtype.val)

end AtZ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.offlineOneInstanceProver
#print axioms AtPublicFiles.AtFiles.keyHonest
#print axioms AtPublicFiles.AtFiles.keyHonestAny
#print axioms AtPublicFiles.AtFiles.keyHonestAny_self
#print axioms AtPublicFiles.AtFiles.keyHonestAny_law
#print axioms AtPublicFiles.AtFiles.keyHonest_law
#print axioms AtPublicFiles.AtFiles.keyHonest_ext
#print axioms AtPublicFiles.AtFiles.keyHonest_coin
#print axioms AtPublicFiles.AtFiles.keyHonest_strat
#print axioms AtPublicFiles.AtFiles.keyHonest_bad
#print axioms AtPublicFiles.AtFiles.keyHonest_hid
#print axioms AtPublicFiles.AtFiles.keyHonestAny_fields
#print axioms AtPublicFiles.AtFiles.withKey_hT
#print axioms AtPublicFiles.AtFiles.recOf_eq
#print axioms AtPublicFiles.AtFiles.tableOf_enc
#print axioms AtPublicFiles.AtFiles.keySeam_key
#print axioms AtPublicFiles.AtFiles.keySeam_join
#print axioms AtPublicFiles.AtFiles.keySeam_public
#print axioms AtPublicFiles.AtFiles.keySeam_silent
#print axioms AtPublicFiles.AtFiles.keySeam_silentK
#print axioms AtPublicFiles.AtFiles.keyFirst_is
#print axioms AtPublicFiles.AtFiles.offlineProverAtFilesDecision
#print axioms AtPublicFiles.AtFiles.keyHonestAt_law
#print axioms AtPublicFiles.AtFiles.offlineProverInThreeProtocols
#print axioms AtPublicFiles.AtFiles.keyHonestObj_eq
#print axioms AtPublicFiles.AtFiles.keyHonestCut
#print axioms AtPublicFiles.AtFiles.offlineBatchProver
#print axioms AtPublicFiles.AtFiles.withKey
#print axioms AtPublicFiles.AtFiles.tableOf
#print axioms AtPublicFiles.AtFiles.sampleOf
#print axioms AtPublicFiles.AtFiles.keySeam
#print axioms AtPublicFiles.AtFiles.keyFirst
#print axioms AtPublicFiles.AtFiles.offlineOneInstanceProverAtFiles
