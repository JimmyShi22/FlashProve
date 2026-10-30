-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/TiedAlong.lean: the proof file's batch protocol (`batchOf`,
Johnson/Desc/ProofFile/Honest/Record.lean) at the IOP as written in Lean (below: the description),
pulled back as a protocol along the library's writing map `LPFD.Full.instanceAsPlainRecord`
(Johnson/Desc/Laid/ProofFull.lean), is the batch protocol at the pulled-back description:
`batch_along`, for every description at `ProofFile.Inst`. So, where the IOP's own test on the public files
Z accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`), at a description of which `LaidAt`
(Johnson/P5J/LaidOpens.lean) holds at Z's files, it is the batch protocol of the library's object at
Z, `(filesAt Z).withProvers P` (E2E/ObjectAtFiles.lean): `protocol_along`. At the provers that send fixed
messages (`Files.fixedMessageProvers`) that is the object in the input at which `VerifierAndGoals.verify` calls the
compiled verifier (`object_description`, E2E/DescriptionTie.lean). `tied_live` has three things at
one description: `LaidAt` holds of it; the object's batch protocol is its protocol, pulled back;
every pair that is valid for the object meets the condition `Tied`
(Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean; below: is tied). Statements and proofs.

For what. An honest prover (a `BatchHonestProver`) can be stated at the description's own instance type
(`ProofFile.Inst`) and pulled back to the object's instances (request, out-of-domain (OOD) sample) as a
whole (`BatchHonestProver.comap`, Hiop/RecKit.lean): then nothing of it has to be stated anew. What has to be
shown once for that way of stating it is the equation of the two protocols.

  `tied_live`: where that test accepts: ∃ Zp Np cF: `LaidAt` at Z's files, the rounds' data
    `theProofData (asDescriptionFiles Z)` and the decision `theProofRun (asDescriptionFiles Z)` ∧ the equation of
    `protocol_along` ∧ for all provers P of the object, all n, all types of the two coins (the
    second inhabited) with their maps run₂ and run₃, all prover structures H (`ProofFile.Honest.Prover`)
    and all w, a: `((filesAt Z).withProvers P).validB (RyesZ Z) w a → Tied … w (instanceAsPlainRecord a)`. The prover
    structure in `Tied` is `(cmAlong …).proverAt 0 H`
    (Johnson/Desc/ProofFile/Honest/CommitterAt.lean): H with the committer's columns as its stored
    table at the item 0, no column at another item, and the committer's key
  `protocol_along`: where that test accepts, for every (Zp, Np, cF) of which `LaidAt` holds at Z's
    files: the object's batch protocol `(filesAt Z).batch` is
    `(batchOf … (F0T OnBytes.secondHashFunction Zp Np cF) silInst).comap instanceAsPlainRecord`, at the object's rounds' data
  `batch_along`: for every choice of challenge types (`CK`, Run/PlanQTypes.lean), all rounds' data
    (`WholeD`), any three fixed plain parts (a plain part: what one of the three rounds without a
    challenge sends: the front round, the joining round, the seam) and every description F at
    `ProofFile.Inst`: `batchOf … (F.pull instanceAsPlainRecord) silP = (batchOf … F silInst).comap instanceAsPlainRecord`
  `silP_fun`: the library's test on the three plain parts (`silP`, OnBytes/Flat/FilesAt.lean), as a
    function, is `silInst` (E2E/TiedAtFiles.lean) at what `instanceAsPlainRecord` writes for the instance
  `pub_passes`, `pub_passes_along`: at every n, r2, r3 and every instance: the three values of
    `pubAt`, which are read off the instance, pass `silP` (at the object's instance) and `silInst`
    (at the description's). For what an honest prover sends (`frontAt`, `joinAt`, `seamAt`) that
    follows only with the clause seam of `Tied`

By what. `silP_fun` is `silP_along` as an equation of functions. `batch_along` rewrites by
`silP_fun`; the rest is by unfolding `batchOf`, `FileDescription.pull` (Johnson/Desc/Block.lean) and
`BatchInteractiveOracleProof.comap` (Hiop/RecKit.lean). `protocol_along` is `protocol_atFiles`, then `batch_along`.
`tied_live` joins `laid_of_live`, `protocol_along` and `tied_atFiles_along`. The last has the
hypothesis hit, `AtPublicFiles.AtZero.ItemsZero` of the description: every stored table that a round of the
description declares is under the item 0. `itemsZero_of_data` (E2E/ItemsZero.lean) proves it from
the field `data` of `LaidAt`. `silP_along`, `protocol_atFiles`, `laid_of_live` and
`tied_atFiles_along` are in E2E/TiedAtFiles.lean. `pub_passes` and `pub_passes_along` unfold `silP`,
`silInst` and `pubAt`.

Hypotheses of `protocol_along`. live: `protocolDataWellFormed (asDescriptionFiles Z) = true`. L: `LaidAt` at Z's three files,
some rounds' data D and decision r, and (Zp, Np, cF); its field `value` says that the library makes
the description `F0T OnBytes.secondHashFunction Zp Np cF` (Johnson/P5J/AtTerm.lean) of these files. `tied_live`
has live only.

Limits.
- The statements are on protocols and on a condition on inputs. No honest prover is built or pulled
  back here. `batch_along` is an equation that is proved by a rewriting, not by unfolding only: a
  prover that is pulled back reaches the object's type of provers by a rewriting along it.
- In `tied_live` the ∃ binds `LaidAt` and the equation of the protocols. The clause on `Tied` holds
  at every (Zp, Np, cF) whose description meets `ItemsZero`, not only at the one that the ∃ gives
  (`tied_atFiles_along`).
- `pub_passes` says that the verifier's test on the three plain parts accepts them. That test reads
  the two copies of the answers only, not the copy's number n and not the two run values: by its
  definition (`silP`, OnBytes/Flat/FilesAt.lean). Elsewhere n is read: the OOD-seed wire among the
  compiled verifier's parameters at Z has a test on the number, which reads the front round's number
  (`num_letters`, E2E/BridgeJoinAtFiles.lean). The run values are read for the starts of a compiled
  run's leaf salts (`RunVals`, Johnson/WholeKey/Premises.lean).
- That `protocolDataWellFormed` accepts is a theorem of the side library at the written files `storedPublicFiles` and `zGap`
  (`AtFullSide.Top.theLive_zFull`, `theLive_zGap`); this file, in the main library, cannot call it.
  Where it rejects, `protocol_along` and `tied_live` say nothing.
- All limits of E2E/TiedAtFiles.lean hold here too. Nothing on what a view shows follows from this
  file.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.TiedAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Committed
open Iop Hiop
open OnBytes.Flat (RecFull silP ansL front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD FrontMsg)
open Compile.Joined (JoinMsg)
open VerifiableInference.Desc (FileDescription Chain)
open ProofFile.Honest (batchOf Prover Tied relAt)
open OnBytes (TableKey)
open LPFD.Full (XF)
open _root_.Run (ckP)

/-- The library's test on the three plain parts (`silP`) is `silInst` at what the writing map
`instanceAsPlainRecord` writes for the instance. -/
theorem silP_fun : (silP : XF × RecFull → _) = fun z => silInst (LPFD.Full.instanceAsPlainRecord z) :=
  funext fun z => funext fun f => funext fun j => funext fun t => silP_along z f j t

/-- **The batch protocol at the pulled-back description is the batch protocol at the description,
pulled back as a protocol.** -/
theorem batch_along (C : _root_.Run.PQ.CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
    (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) (F : FileDescription ProofFile.Inst) :
    batchOf C D tF tJ t3 (F.pull LPFD.Full.instanceAsPlainRecord) silP =
      (batchOf C D tF tJ t3 F silInst).comap LPFD.Full.instanceAsPlainRecord := by
  rw [silP_fun]
  rfl

section AtZ
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open P5J

local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181


/-- **Where the IOP's own test on the public files accepts, the object's batch protocol is the
description's, pulled back along the writing map.** -/
theorem protocol_along (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (filesAt Z).batch =
      (batchOf (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (F0T OnBytes.secondHashFunction Zp Np cF)
        silInst).comap LPFD.Full.instanceAsPlainRecord :=
  (protocol_atFiles Z live L).trans (batch_along _ _ _ _ _ _)

/-- **Three things at one description.** Where the IOP's own test on the public files accepts there
is a description (Zp, Np, cF) of which `LaidAt` holds at Z's files, such that the object's batch
protocol is that description's, pulled back along the writing map, and every pair that is valid for
the object, at the relation `RyesZ Z`, is tied (meets `Tied`) at that description, at what the map
writes for the instance: for all provers P of the object, every n, all types of the two coins with
their maps, and every prover structure H. The last of the three holds at every (Zp, Np, cF) whose
description meets `ItemsZero` (`tied_atFiles_along`); here `itemsZero_of_data` proves `ItemsZero`
from the field `data` of `LaidAt`. So the ∃ binds the first two, and the last through `ItemsZero`
only. -/
theorem tied_live (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ Zp Np cF,
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FlashProve.theProofData (asDescriptionFiles Z))
        (FlashProve.theProofRun (asDescriptionFiles Z)) Zp Np cF ∧
      (filesAt Z).batch =
        (batchOf (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
          (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (F0T OnBytes.secondHashFunction Zp Np cF)
          silInst).comap LPFD.Full.instanceAsPlainRecord ∧
      ∀ (P : (filesAt Z).Provers) (R₂ R₃ : Type) [Inhabited R₃] (run₂ : R₂ → ByteArray)
        (run₃ : R₃ → ByteArray) (n : ℕ) (Tr X₀ Xh : Type)
        (H : Prover FullSizeMatrix ((filesAt Z).withProvers P).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
        (w : FullSizeMatrix × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) (a : XF × RecFull),
        ((filesAt Z).withProvers P).validB (RyesZ Z) w a →
        Tied ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (F0T OnBytes.secondHashFunction Zp Np cF)
          ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
          (fun r2 r3 => (cmAlong (AZ Z) PadZ (holdZ Z)).seam
            (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3) (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2)
            (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3))
          ((cmAlong (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a)
          (pubAt run₂ run₃ ansInst n) (shAt Zp Np cF)
          (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) LPFD.Full.instanceAsPlainRecord) w
          (LPFD.Full.instanceAsPlainRecord a) := by
  obtain ⟨Zp, Np, cF, L⟩ := laid_of_live Z live
  exact ⟨Zp, Np, cF, L, protocol_along Z live L,
    fun P _ _ _ run₂ run₃ n _ _ _ H w a h => tied_atFiles_along Z P Zp Np cF run₂ run₃ n H w a
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) h⟩

end AtZ

section Passes
variable {R₂ R₃ : Type} (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray)

/-- The three values as they are read off the instance (`pubAt`) pass the verifier's test on the
three plain parts (`silP`). -/
theorem pub_passes (n : ℕ) (r2 : R₂) (r3 : R₃) (x : XF × RecFull) :
    silP x (pubAt run₂ run₃ (fun y : XF × RecFull => ansL y.2) n r2 r3 x).1
      (pubAt run₂ run₃ (fun y : XF × RecFull => ansL y.2) n r2 r3 x).2.1
      (pubAt run₂ run₃ (fun y : XF × RecFull => ansL y.2) n r2 r3 x).2.2 = true := by
  unfold silP pubAt
  simp

/-- The same at the description's own instances, for `silInst`. -/
theorem pub_passes_along (n : ℕ) (r2 : R₂) (r3 : R₃) (x : ProofFile.Inst) :
    silInst x (pubAt run₂ run₃ ansInst n r2 r3 x).1 (pubAt run₂ run₃ ansInst n r2 r3 x).2.1
      (pubAt run₂ run₃ ansInst n r2 r3 x).2.2 = true := by
  unfold silInst pubAt
  simp

end Passes

end AtPublicFiles.Committed

#print axioms AtPublicFiles.Committed.silP_fun
#print axioms AtPublicFiles.Committed.batch_along
#print axioms AtPublicFiles.Committed.protocol_along
#print axioms AtPublicFiles.Committed.tied_live
#print axioms AtPublicFiles.Committed.pub_passes
#print axioms AtPublicFiles.Committed.pub_passes_along
