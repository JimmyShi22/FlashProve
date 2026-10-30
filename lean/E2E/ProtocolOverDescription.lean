-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/ProtocolOverDescription.lean: where the proof file's decision is the `run` of a description Fd of the proof
file (`FileDescription`, Johnson/Desc/Block.lean: the file's IOP as written in Lean), the batch protocol of
the library's three protocols (`Files.batch`, OnBytes/Flat/Object.lean: the proof file's protocol
with its annotation of the rounds) is `batchOf` over Fd (Johnson/Desc/ProofFile/Honest/Record.lean).
`batchOf` is the protocol in the type of `ProofFile.Honest.honestB` (same file), the prover structure for
the proof file's protocol that is written over a description. So such a structure has the type of
the third field of the library's provers of three protocols (`Files.Provers.hB`). It is for files
that import this one and build such a structure for the proof file. Stated first at any parameters
of the library's full size, then at three public files Z. E2E/KeyProtocolOverDescription.lean does the same for
the key file. Definitions, equations between protocols, and facts about types; nothing is shown of
any prover.

  `batch_eq_batchOf`: by unfolding, at any claims, rounds' data and decisions, and any description
    Fd at the instance type (request, OOD sample), `X × RecFull`: the batch protocol of `filesWith`
    is `batchOf` at these parameters: the choice of challenge types at the second field, `ckP .two`;
    the proof file's rounds' data with the depth set to the table's, `DP.at frS.P.T.a`; the three
    fixed plain parts `front₀ rP`, `join₀ rP` and `ByteArray.empty`; the description Fd; the
    library's test on the three plain parts at the proof file (`silP`, OnBytes/Flat/FilesAt.lean)
  `seatB`: a definition: so a prover structure (`BatchHonestProver`, Iop/Batch.lean) over that `batchOf` is,
    unchanged, one of the type that `Files.Provers.hB` asks at `filesWith`. The type of private
    inputs is the same expression: (index, (pads, encoding randomness), OOD seed). No re-indexing
  `seatHonestB`: a definition: `seatB` at `honestB` itself. Every argument of `honestB` is passed on
    as it is; of its type parameters, W₀ is the index type, Rc the pads with the encoding
    randomness, Sd the OOD seeds
  `filesWith_eq`: if `Fd.run` is the proof file's decision at Z (`(dataAtFiles flashProveData Z).runP`), then
    `filesWithAt Z Fd` is `filesAt Z` (E2E/ObjectAtFiles.lean)
  `run_eq_of_laid`: where the IOP's own test on the public files accepts
    (`protocolDataWellFormed (asDescriptionFiles Z) = true`) and `FlashProve.theProofLaid` returns a pair p of rounds' data
    and a decision, the proof file's decision at Z is p.2: the hypothesis of `filesWith_eq`, for an
    Fd whose `run` is p.2
  `filesWith`: short for the library's three protocols of the full size (`threeProtocolsAtFullSize`,
    Johnson/Flat/Dec/WiresAtSizes.lean) with `Fd.run` as the proof file's decision
  `filesWithAt Z Fd`: a definition: `filesWith` at the parameters of `filesAt Z`

By what. `batch_eq_batchOf` holds by unfolding `threeProtocolsAtFullSize`, `Files.batch` and `batchOf`.
`filesWith_eq` rewrites by its hypothesis; the rest is unfolding (`filesAt`; `FsAtR`,
Johnson/Top/Fire/Code/TieAtValues.lean). `run_eq_of_laid` is by `theProofGate_live`
(Johnson/Goal/Description/Gates.lean) and `theProofRun_ok`
(Johnson/Goal/Description/ProofFold.lean). The step from a description's `run` to the proof file's
decision at Z is a proved equation, not an unfolding. That decision is "the test on the public files
accepts, and `theProofRun` accepts" (`theProofGate`, by `gatedFileDecision`, Johnson/Flat/Dec/ClosedAll.lean),
and `theProofRun` is a match on whether `theProofLaid` returns: on whether the description could be
made, passed its tests and gave its rounds' data. So a prover structure that is stated at a
description's own `run` is stated at protocols that are `filesAt Z` only by a theorem, under
`protocolDataWellFormed (asDescriptionFiles Z) = true`.

Limits.
- The decision that `theProofLaid` returns is the `run` of the description pulled back along the map
  from the verifier's instance to the description's own instance type (`proofDecisionOfDescription`, `instanceAsPlainRecord`,
  Johnson/Desc/Laid/ProofFull.lean). So the Fd that meets the hypothesis of `filesWith_eq` by
  `run_eq_of_laid` is that pulled-back description. A prover structure that is stated at the
  description's own instance type needs that map carried through as well: not done here.
- The rounds' data D are a free parameter of `batchOf` and of `honestB`. Here D is set to
  `DP.at frS.P.T.a`: at Z, the term that occurs in `filesAt Z`, unfolded. That it is the
  description's own data is another equation, with hypotheses of its own (`data_atFiles`,
  E2E/BridgePaidAtFiles.lean).
- ext is a free parameter of `honestB`: that it is the encoder's table has to be shown by whoever
  uses `seatHonestB`.
- No statement here says that a prover structure has any property.
- `seatB`, `seatHonestB` and `batch_eq_batchOf` are for a description that is stated at the object's
  own instances, or pulled back to them. E2E/BridgeAlong.lean, which reads a prover structure along
  a writing map instead, calls none of the three. For acceptance along that map,
  E2E/BridgeLinkAtFiles.lean calls `run_eq_of_laid`. `protocol_atFiles` (E2E/TiedAtFiles.lean) calls
  `run_eq_of_laid` and `filesWith_eq`.
- `run_eq_of_laid` holds vacuously where the test on the public files rejects or `theProofLaid`
  returns an error.
- The key file's and the link's provers (`hT`, `hL`) are not touched.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.ObjectAtFiles
import Johnson.Desc.ProofFile.Honest.Record

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
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (batchOf honestB Prover KeyAndJoiningRoundMessages ProverCoinCounts)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)

/-! ## 1. At any parameters -/

section General
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool) (Fd : FileDescription (X × RecFull))
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)

/-- The library's three protocols of the full size (`threeProtocolsAtFullSize`), with `Fd.run` as the proof
file's decision. -/
abbrev filesWith : Files (DecR.configurationOfStoredTable A R) :=
  threeProtocolsAtFullSize A R DK DP runK Fd.run ds xs dec rK rP depthReq early salt

/-- **Their batch protocol is `batchOf` over Fd**, the protocol in the type of `honestB`: by
unfolding. -/
theorem batch_eq_batchOf :
    (filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).batch =
      batchOf (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP)
        ByteArray.empty Fd OnBytes.Flat.silP := rfl

/-- **A prover structure over that `batchOf` has the type that `Files.Provers.hB` asks**: the same
term; the type of private inputs is the same expression. -/
def seatB
    (hB : BatchHonestProver
      (batchOf (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP)
        ByteArray.empty Fd OnBytes.Flat.silP)
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)) :
    BatchHonestProver (filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).batch
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :=
  hB

/-- `seatB` at `honestB` itself; every argument of `honestB` is passed on as it is. -/
def seatHonestB {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
    (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (X × RecFull) Ky Tr
      X₀ X')
    [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
      (DecR.configurationOfStoredTable A R).Seed (X × RecFull) Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
      (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
    (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
      (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str) :
    BatchHonestProver (filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).batch
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :=
  seatB A R DK DP runK Fd ds xs dec rK rP depthReq early salt
    (honestB (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP)
      ByteArray.empty Fd OnBytes.Flat.silP B H J ext)

end General

/-! ## 2. At three public files Z -/

/-- `filesWith` at the parameters of `filesAt Z`: the three protocols at Z with the proof file's
decision replaced by `Fd.run`. -/
def filesWithAt (Z : PublicFiles) (Fd : FileDescription (XF × RecFull)) : Files (Cz Z) :=
  filesWith (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK Fd PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G)

/-- **If `Fd.run` is the proof file's decision at Z, `filesWithAt Z Fd` is `filesAt Z`.** -/
theorem filesWith_eq (Z : PublicFiles) (Fd : FileDescription (XF × RecFull))
    (h : Fd.run = (dataAtFiles flashProveData Z).runP) : filesWithAt Z Fd = filesAt Z := by
  unfold filesWithAt filesWith
  rw [h]
  rfl

/-- **Where `protocolDataWellFormed` accepts and `theProofLaid` returns p, the proof file's decision at Z is p.2**:
the hypothesis of `filesWith_eq`, for an Fd whose `run` is p.2. -/
theorem run_eq_of_laid (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (p : WholeD × (XF × RecFull → View → View → View → Bool))
    (h : FlashProve.theProofLaid (asDescriptionFiles Z) = .ok p) : (dataAtFiles flashProveData Z).runP = p.2 :=
  (FlashProve.theProofGate_live (asDescriptionFiles Z) live).trans (FlashProve.theProofRun_ok h)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.batch_eq_batchOf
#print axioms AtPublicFiles.AtFiles.filesWith_eq
#print axioms AtPublicFiles.AtFiles.run_eq_of_laid
#print axioms AtPublicFiles.AtFiles.filesWith
#print axioms AtPublicFiles.AtFiles.seatB
#print axioms AtPublicFiles.AtFiles.seatHonestB
#print axioms AtPublicFiles.AtFiles.filesWithAt
