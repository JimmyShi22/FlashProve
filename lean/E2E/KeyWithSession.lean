-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyWithSession.lean: `proversBoth` is one value of `OnBytes.Prover.ThreeProvers`
(Johnson/Prover/All/OfHonest.lean), the three honest provers as the two statements on the compiled
argument take them (the acceptance side, `HonFit`; the privacy side, `PremW`): the key file's, the
link's and the session's. It is `proversOf` (E2E/BridgePrivacy.lean) with the first field set to
`keyHonest` (E2E/KeyHonest.lean) and the third made of `famC` (E2E/SessionHonest.lean), both at one
object of the library, `(filesWithBoth …).withProvers P`. `keyHonest` is a prover structure, and `famC` a
family of prover structures by the copy's number (`Family`, E2E/HonestFamily.lean), built by
`honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes.
`proversAt` and `proversCut` set the first field in the same way at three public files Z. It serves
files above this one that need the three provers as one value of `ThreeProvers`. General in the claims, the
rounds' data, the two descriptions and the link's decision. Definitions, and equations that hold by
unfolding.

  `proversBoth … P hL`: a definition: `proversOf` at `keyHonest`, at a free parameter hL for the
    link's prover, and at `famC`: a value of `ThreeProvers ((filesWithBoth …).withProvers P)`, for every P. No cast
  `proversBoth_T`, `proversBoth_B`: its first field is `keyHonest`; its third is `famC` made into
    the one prover whose private input ends with the copy's number (`Family.glue`): by unfolding
  `proversBoth_extT`: where the parameter extT of `keyHonest` is the configuration's encoder
    (`tableOf`, E2E/KeyHonest.lean), the first field's table at (i, r, e) is the object's encoded
    index at (i, r): by unfolding. Both statements ask this equation of the first field:
    `HonFit.extT` (Johnson/Prover/All/OfHonest.lean), and `ExtEnc.T` in the field `ext` of `PremW`
    (Johnson/WholeKey/Premises.lean)
  `proversAt Z … P hL Fm`: a definition: at three public files Z, at the object of `filesAt Z`
    itself (E2E/ObjectAtFiles.lean) and any P, hL and family Fm: `proversOf` at `offlineProverInThreeProtocols`
    (E2E/KeyHonest.lean), hL and Fm. `proversAt_T`: its first field is `offlineProverInThreeProtocols`
  `proversCut`, `proversCut_T`: the same at the object whose index type is cut to the matrices in
    range (`objAt Z P`, E2E/ObjectAtFiles.lean), with `keyHonestCut` (E2E/KeyHonest.lean)
  `filesWithBoth`: short for the library's three protocols of the full size (`threeProtocolsAtFullSize`,
    Johnson/Flat/Dec/WiresAtSizes.lean) whose key file's decision is that of a description Fx of the
    key file (`FileDescription`, Johnson/Desc/Block.lean: the file's IOP as written in Lean), pulled back
    along `Key.keyInstanceOfOutOfDomainSample`, and whose proof file's decision is that of a description Fd of the proof file
  `filesWithBoth_key`: `filesWithBoth` is written with `filesWith` (E2E/ProtocolOverDescription.lean), the form
    in the type of `famC`; it is equal to `filesWithKey` (E2E/KeyProtocolOverDescription.lean), the form in the
    type of `keyHonest`: by unfolding

By what. Every proof is `rfl`. `filesWith` and `filesWithKey` both unfold to `threeProtocolsAtFullSize`, so
`keyHonest` and `famC` fit one object with no cast. `proversOf` puts its first two arguments into
the fields `T` and `Lk`, and `Family.glue` of the third into `B`. `proversBoth_extT` unfolds what
`keyHonest_ext` and `tableOf_enc` (E2E/KeyHonest.lean) state.

Limits. Nothing is shown of any prover. In `proversBoth` all parameters of the shell `keyHonest` and
of `famC` stay free: the books of coins BT and B (`ProverCoinCounts`), the prover structures HT and H
(`ProofFile.Honest.Prover`), JT and J, shT and sh, extT and ext, and the descriptions Fx and Fd. So do B,
H, J, sh, ext and Fx at Z. The link's prover hL is a free parameter. At Z the session's family Fm is
a free parameter too: `famC` has its type at three protocols whose proof file's decision is a
description's own (`filesWith`), and at the parameters of Z these are `filesAt Z` under a hypothesis
on that decision (`filesWith_eq`, E2E/ProtocolOverDescription.lean). `proversAt` and `proversCut` are defined at
every Z and every description Fx, by `atDecision` (E2E/KeyProtocolOverDescription.lean): that they have their
types says nothing about the key file's decision. Of what the two statements ask of the first field,
only the equation of `proversBoth_extT` is treated here, and for `proversBoth` only. No property of
a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyHonest
import E2E.SessionHonest
import E2E.BridgePrivacy

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)
open OnBytes.Prover (ThreeProvers)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

section General
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fx : FileDescription KeyInst)
  (Fd : FileDescription (X × RecFull))
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)

/-- The library's three protocols with both descriptions' decisions: the key file's is
`(Fx.pull keyInstanceOfOutOfDomainSample).run`, the proof file's is `Fd.run`. -/
abbrev filesWithBoth : Files (DecR.configurationOfStoredTable A R) :=
  filesWith A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample).run Fd ds xs dec rK rP depthReq early salt

/-- They are `filesWithKey` at the pulled-back description `Fx.pull keyInstanceOfOutOfDomainSample` and the decision
`Fd.run`, the form in the type of `keyHonest`: by unfolding. -/
theorem filesWithBoth_key :
    filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt =
      filesWithKey A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample) Fd.run ds xs dec rK rP depthReq early salt := rfl

variable {KyT TrT X₀T XT R₂T R₃T : Type} (BT : ProverCoinCounts)
  (HT : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst KyT TrT X₀T
    XT)
  [Fintype R₂T] [Nonempty R₂T] [Fintype R₃T] [Inhabited R₃T]
  (JT : R₂T → R₃T → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed KeyInst KyT (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (shT : KyT → Fx.S₂)
  (extT : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (X × RecFull) Ky Tr X₀
    X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed (X × RecFull) Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → Fd.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (P : (filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).Provers)
  (hL : Honest ((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P).link
    ((DecR.configurationOfStoredTable A R).I ×
      (((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P).EncodingRandomness ×
        ((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P).OutOfDomainSeed) ×
      (((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P).EncodingRandomness ×
        ((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P).OutOfDomainSeed)))

/-- **The three honest provers at one object**: the key file's is `keyHonest`, a prover structure
built by `honestBatchProverOfFile` from parameters that nothing here fixes (its book of coins BT, its prover
structure HT and its description Fx are free parameters); the link's is the free parameter hL; the
session's is made of the family `famC`. -/
def proversBoth :
    ThreeProvers ((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P) :=
  proversOf
    (keyHonest A R DK DP Fx Fd.run ds xs dec rK rP depthReq early salt BT HT JT shT extT P) hL
    (famC A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample).run Fd ds xs dec rK rP depthReq early salt B H J sh ext P)

/-- Its first field is the shell `keyHonest`. -/
theorem proversBoth_T :
    (proversBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt BT HT JT shT extT B H J sh ext
      P hL).T =
      keyHonest A R DK DP Fx Fd.run ds xs dec rK rP depthReq early salt BT HT JT shT extT P := rfl

/-- Its third field is the family `famC`, made into one prover by `Family.glue`. -/
theorem proversBoth_B :
    (proversBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt BT HT JT shT extT B H J sh ext
      P hL).B =
      (famC A R DK DP (Fx.pull keyInstanceOfOutOfDomainSample).run Fd ds xs dec rK rP depthReq early salt B H J sh ext
        P).glue := rfl

/-- **At the configuration's encoder (`tableOf`), the first field's table is the object's encoded
index.** -/
theorem proversBoth_extT (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) :
    (proversBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt BT HT JT shT (tableOf A R DK) B
      H J sh ext P hL).T.ext (i, r, e) =
      ((filesWithBoth A R DK DP Fx Fd ds xs dec rK rP depthReq early salt).withProvers P).encodeIndex i r := rfl

end General

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
  (P : (filesAt Z).Provers)

/-- The three honest provers at `(filesAt Z).withProvers P`, the object of the three protocols at Z itself.
The type says nothing about the key file's decision: this is defined at every Z and every
description Fx. -/
def proversAt
    (hL : Honest ((filesAt Z).withProvers P).link ((Cz Z).I ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed)))
    (Fm : Family ((filesAt Z).withProvers P).onlineBatch.loc
      ((Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed)) :
    ThreeProvers ((filesAt Z).withProvers P) :=
  proversOf (offlineProverInThreeProtocols Z Fx B H J sh ext P) hL Fm

theorem proversAt_T
    (hL : Honest ((filesAt Z).withProvers P).link ((Cz Z).I ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed)))
    (Fm : Family ((filesAt Z).withProvers P).onlineBatch.loc
      ((Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed)) :
    (proversAt Z Fx B H J sh ext P hL Fm).T = offlineProverInThreeProtocols Z Fx B H J sh ext P := rfl

/-- The same at `objAt Z P`, the object whose index type is cut to the matrices in range. The type
says nothing about the key file's decision. -/
def proversCut
    (hL : Honest (objAt Z P).link (Ix × ((objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed) ×
      ((objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed)))
    (Fm : Family (objAt Z P).onlineBatch.loc (Ix × (objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed)) :
    ThreeProvers (objAt Z P) :=
  proversOf (keyHonestCut Z Fx B H J sh ext P) hL Fm

theorem proversCut_T
    (hL : Honest (objAt Z P).link (Ix × ((objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed) ×
      ((objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed)))
    (Fm : Family (objAt Z P).onlineBatch.loc (Ix × (objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed)) :
    (proversCut Z Fx B H J sh ext P hL Fm).T = keyHonestCut Z Fx B H J sh ext P := rfl

end AtZ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.filesWithBoth_key
#print axioms AtPublicFiles.AtFiles.proversBoth
#print axioms AtPublicFiles.AtFiles.proversBoth_T
#print axioms AtPublicFiles.AtFiles.proversBoth_B
#print axioms AtPublicFiles.AtFiles.proversBoth_extT
#print axioms AtPublicFiles.AtFiles.proversAt
#print axioms AtPublicFiles.AtFiles.proversAt_T
#print axioms AtPublicFiles.AtFiles.proversCut
#print axioms AtPublicFiles.AtFiles.proversCut_T
#print axioms AtPublicFiles.AtFiles.filesWithBoth
