-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
The verifier's fast form at the full size, with its arguments filled in.

`fastD` and `fastF` are functions with code that are meant to return, faster, the `Bool` that the
verifier `verifyV` gives when it is evaluated at a hash function. `FastDIs` states that `fastD`
equals `verifyVDet` at `DvE …` and `proofE …`; `fastD_is` (Johnson/Top/Fire/Code/FastDProbe.lean) is
a theorem of that statement. This file is where a run of the fast form gets its arguments.

`fastD`, `fastF` and `DvE` (Johnson/Top/Fire/Code/VerifyVFastD.lean) take about thirty arguments.
This file fills in those that follow from the makers' data `G` and the configuration's digest `c`,
and leaves the rest as arguments. DvFull.lean does the same for the plain form `DvOf`. Against that
form, the fast form takes the entry file's `ds`, `xs`, `dec` in the places of five parts, and the
shapes of two binding trees in the places of two depths. FastSmall.lean is this text at the small
size.

The definitions:
  * `dvEAt`: the input of which the statement on the fast form, `FastDIs`, speaks.
  * `fastAt`: the fast form at the family that `m` reads out of a hash function.
  * `fastFAt`: what a run calls. The fast form at a family that is made directly of a function `O`
    from bytes to bytes, and at the hash function `hashOf O` made of the same `O`.
  * `stepsFAt`: the same as twelve steps by name, at `fastFAt`'s arguments.
  * `armTAt`, `armLAt`, `armBAt`: the key file's, the entry file's and the proof file's arm of the
    check alone, so that a run can print each as it ends.

Each stands in up to four forms:
  * `…At G c DK DP runK runP ds xs dec`: general in these nine arguments.
  * `…FullAt Z DK DP`: at the three public files `Z`, with `G := GF Z`, `c := cB Z`, the entry
    file's `dsF`, `xsF`, `decF` (Vals/EntryFive.lean) and, for `runK` and `runP`, `runKFull` and
    `runPFull` (Johnson/Flat/WireAt.lean). These two are made of the decisions of the Lean text
    `verify-on-bytes`. They are not the description's own decisions.
  * `…FullRun Z DK DP runK runP`: the same with the two decisions as arguments. This is the form for
    the description's own decisions.
  * `…FullPlan Z DK DP`: the same with `runKPlanF` and `runPPlanF`; see the last section.

Also filled in:
  * `sTG G` and `sBG G`, the shapes of the key file's and of the proof file's binding tree. The
    plain form's depth for the key file is `(sTG G).logLeaves`; at a planned `G` its other depth,
    `G.depthReq`, is `(sBG G).logLeaves` (OnBytes/Flat/BigAt.lean).
  * `KF DK DP`, the number of blocks but one; see its comment.
  * the tag, `cfg`, `shape`, the two plain parts and `m`, from Johnson/PV/MFull.lean. They are
    general in the plain form's arguments and are used here at the fast form's.
  * `num := PV.Front.numCopy` (Johnson/Top/Fire/Code/PvFrontNum.lean): the number in the plain part
    of the proof file's front round must be the number of the stored copy.
  * `seed := recSeedK …` (OnBytes/Flat/RecordSeed.lean) and `r₀ := PV.Front.r0Full`, the record of
    zeros. That this is the right seed is a reading of how the library uses it elsewhere;
    that choice is not shown here.
  * the salt's length, `pAt`, the code of a key (of which the commitment ID is the hash) and the
    builder of the instance, as in DvFull.lean.
Still arguments: `h₀`, `sp`, `okS`, `sR`, `linkF`, `dK`, `dP`, which go to `m` in `dvEAt` and
`fastAt` and to the prepared value `pr` in the five that a run calls; `O` or `hash`; and a run's own
`commitment`, `prompt`, `output`, `aux`, `cm`, `rcd`, `copy`, `fT`, `e`, `fB`.

Why it is written so:
  * The general forms take `G` and `c` as arguments because the statements are to use the hash
    function as a random oracle throughout. At `GF Z` and `cB Z` the plan's digest inside the
    verifier's own values is made by the fixed hash function, while the reading of the files asks
    the oracle for it. In the general forms the reading's own query can fill `G` and `c`, which
    keeps the hash function in one role.
  * `hashOf O` is bound inside `fastFAt` so that `fastF_reads_is_verifyV`
    (Johnson/Top/Fire/Code/FastFamProbe.lean) applies. That theorem speaks of `fastF` at the same
    arguments: at a family that answers what `m` reads out of `O`, it is the evaluation of `verifyV`
    at `DvE …`. `famFQ_reads` (Johnson/PV/MFullQ.lean) says that `famFQ` at `prepF` is such a
    family, whatever `bk` is; `fastFT_eq` lies between `fastF` and what `fastFAt` calls.
    Johnson/PV/FastIsVerifyF.lean puts these together: `fast_is_verify` and `steps_is_verify`,
    without a premise.
  * `fastFAt`, `stepsFAt`, `armTAt` and `armBAt` call `fastFT`, `fastStepsT`, `armTET` and `armBET`
    (Johnson/PV/KitWholeF.lean, KitArmsF.lean). These use a kit that reads a round's draws off the
    blocks' bytes: with the plain kit `ckP .two` the proof file's largest round did not end in one
    measured run (its size is not recorded here). Each has a theorem `…_eq`, without a premise, that
    it equals the plain one. `armLAt`, `dvEAt` and `fastAt` stay at the plain kit, so the
    statement's input does too.
  * `pr`, `bk` and the family `F` are bound once at the head of each of the five definitions that
    call the family. Made anew at every query they cost far more. Two measurements: with `pr`
    prepared and bound once, the key file's arm on the small stored example took 5.5 GiB against 36
    GiB; with `F` bound once, 300 made-up queries took 0.9 ms each against 48 to 50 ms
    (interpreted). `famBound_eq` says that `F` is `famFQ`. Nothing here shows whether compiled code
    keeps them bound once.
  * `bk` is wrapped in `W4M.shoutAt`, which returns it unchanged and writes a line when it is
    called, so that a run shows whether that code is ever reached.

Limits:
  * `runK`, `runP`, `ds`, `xs`, `dec`, `DK`, `DP` are arguments: what is passed there decides what
    the value is.
  * The general forms take `G` and `c` apart. Nothing in them ties `c` to the files of which `G` was
    made, and no `planOk` is asked of `G`: whoever fills them owes both. The forms at `Z` tie the
    two by how they are made, and `planOk Z` is still a run's first question: where it is false,
    `GF Z` is a stand-in and nothing ties the two shapes to the plain form's depths.
  * No definition in this file asks `planOk` or `dataPlanOk` (DvFull.lean). A caller must ask both,
    or its print must show them as rows that can say no.
  * `KF DK DP` is made at `dsF`'s rounds whatever `ds` is passed. At another `ds`, that every
    round's blocks fit it is not asked here.
  * The data are read at the frame's depth, `DK.at frS.P.T.a` and `DP.at frS.P.T.a`. `WholeD.at`
    overwrites the depth and tests nothing.
  * At `linkF := fun _ => none` the entry file's arm says no. A value with code is `linkFF`
    (Johnson/PV/LinkFull.lean); it and its twin at the small size have been evaluated, each at its
    size; that it gives the queries of the entry file's chain rests on a reading, not on a theorem.
  * `okS` is the caller's to choose.
  * Not stated here: that `dvEFullAt` is `dvFullAt`. It would need the entry file's five parts to
    agree, and `(sBG G).logLeaves = G.depthReq` under `planOk`.
  * What `fast_is_verify` does not say: that `dvEAt …` is the input of which a soundness theorem
    speaks, or that the typed proof `proofE …` is what a parser of the files returns. The `m` that
    is filled in is the writing side of a coding; no theorem named here says that it is one to one.
  * No soundness is claimed. What is known of a run of these definitions is known by evaluation, not
    by proof.
  * `numCopy`'s control is the honest proof with `copy` changed by one, which must be refused.
    Neither `numCopy` on a real proof nor that control is recorded here as run.
  * This file uses none of the theorems `…_eq` on the kit (Johnson/PV/KitWholeF.lean,
    KitArmsF.lean).
  * The text compiles. Its small twin (FastSmall.lean of this folder) is reported evaluated, in runs
    not recorded in this library; of this text no run is recorded here.

Terms: lean/GLOSSARY.md.


-/
import Johnson.Top.Fire.Code.VerifyVFastD
import Johnson.Top.Fire.Code.Vals.DvFull
import Johnson.PV.MFull
import Johnson.PV.MFullQ
import Johnson.PV.KitWholeF
import Johnson.Flat.WordsBytes
import Johnson.Top.Fire.Code.PvFrontK
import Johnson.Top.Fire.Code.PvFrontNum
import OnBytes.Flat.RecordSeed
import Johnson.Top.Fire.Code.FastFamProbe
import Johnson.Top.Fire.Code.VerifyVFastStepsD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)
open PV.EntryFive
open OnBytes.Maker.Page (Pd3)

/-- The configuration's digest of the three public files, as bytes. -/
def cB (Z : OnBytes.K.Pub) : ByteArray := OnBytes.Params.configurationDigest [Z.pol, Z.lay, Z.KL]

/-- The shape of the key file's binding tree, off the plan. -/
def sTG (G : FilesParameters XF RecFull) : OnBytes.Params.LinBindingShape := G.k.oneTime.binding

/-- The shape of the proof file's binding tree, off the plan. -/
def sBG (G : FilesParameters XF RecFull) : OnBytes.Params.LinBindingShape := G.c.first.binding

/-- The salt's length in bytes, off the plan. -/
def saltG (G : FilesParameters XF RecFull) : ℕ := G.k.oneTime.given.plan.salt

/-- The number of blocks but one: `PV.Front.KFull` (a function of the data alone), and at least 139.
  The `max` is there so that the seed's 140 blocks fit `K + 1` by a proof at every `DK`, `DP`, as
  `KSmallAt` does by a `max` of its own (Johnson/Flat/WireAt.lean). -/
def KF (DK DP : WholeD) : ℕ := max (PV.Front.KFull DK DP) 139

/-- The seed's blocks fit. -/
theorem hKF (DK DP : WholeD) : (seedBS recLg recS).b ≤ KF DK DP + 1 := by
  rw [seedBS_b_full]
  exact Nat.succ_le_succ (Nat.le_max_right _ _)

/-- A serialiser of a plain part of some round of the written link, at any rounds' data `ds`: the
  text of `PV.MFull.serLF` with `ds` as an argument. -/
def serLAt (ds : List TypedOracleCompiler.Run.PQ.RD) :
    Ser (PlainPart (_root_.Run.Twin.up (SOf (ckP _root_.Fmt.Fld.two) ds))
      (_root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) ds))) :=
  Ser.ofEquiv (OnBytes.K.Arm.pbEq (_root_.Run.Twin.allLo_eq (SOf (ckP _root_.Fmt.Fld.two) ds)))
    (Ser.sum (Ser.sum Ser.unit Ser.unit) (TypedOracleCompiler.Run.PQ.serPBL (ckP _root_.Fmt.Fld.two) ds))

/-- At `dsF` it is `PV.MFull.serLF`. -/
theorem serLAt_dsS : serLAt dsF = PV.MFull.serLF := rfl

section At
variable (G : FilesParameters XF RecFull) (c : ByteArray) (DK DP : WholeD)
  (runK : RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → Bool)
  (runP : XF × RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → _root_.Fmt.View → Bool)

set_option quotPrecheck false in
local notation "Kb" => KF DK DP

set_option quotPrecheck false in
local notation "CKe" => ckP _root_.Fmt.Fld.two
set_option quotPrecheck false in
local notation "LKs" => linkProtocolOfRoundData CKe ds frS.P.T.a xs dec
set_option quotPrecheck false in
local notation "ALs" => _root_.Run.Twin.allLo (SOf CKe ds)
set_option quotPrecheck false in
local notation "LVe" => LvOf DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs
set_option quotPrecheck false in
local notation "ATe" => aTOf DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs
set_option quotPrecheck false in
local notation "CVe" => carrierV LVe (List Bool) ATe ALs
set_option quotPrecheck false in
local notation "PLe" => PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs
set_option quotPrecheck false in
local notation "Me" => PV.MFull.mF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs (saltG G)
set_option quotPrecheck false in
local notation "Pe" => PV.MFull.prepF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs (saltG G)
set_option quotPrecheck false in
local notation "Fq" => PV.MFull.famFQ DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs
set_option quotPrecheck false in
local notation "Bq" => W4M.shoutAt (PV.MFull.bkF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs Kb PV.SerReq.sXF (serLAt ds))

/-- **The input of which the fast form's statement speaks.** -/
def dvEAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    : InputV :=
  DvE DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G)
    G.early ds xs dec Kb (saltG G) PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF PLe PLe
    PV.Front.numCopy (recSeedK recT recLg recS (Kb + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
    (Me Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP Bq)
    (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq)

/-- The fast form at the family that `m` reads out of the hash function. -/
def fastAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
  fastD DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G)
    G.early ds xs dec Kb (saltG G) PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF PLe PLe
    PV.Front.numCopy (recSeedK recT recLg recS (Kb + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
    (Me Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP Bq)
    (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq) hash commitment
        prompt output aux cm rcd copy fT e fB

/-- **The family, as the five definitions below bind it once, is `famFQ`**: by unfolding. -/
theorem famBound_eq (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray) :
    W4M.famPrepQ (Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP) Bq O
        (W4M.hintK (Kb + 1) (DK.at frS.P.T.a)) (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a)) =
      Fq Kb Bq O (Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP) := rfl

/-- **What a run calls**: the fast form at the fast family made of `O`, at the hash function made of
  the same `O`. -/
def fastFAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
  let pr := Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP
  let bk := Bq
  let F := W4M.famPrepQ pr bk O (W4M.hintK (Kb + 1) (DK.at frS.P.T.a))
    (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))
  fastFT DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G)
    G.early ds xs dec Kb (saltG G) PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF PLe PLe
    PV.Front.numCopy (recSeedK recT recLg recS (Kb + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
    F
    (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq) (hashOf O)
        commitment prompt output aux cm rcd copy fT e fB

/-- **The same as twelve steps by name**, at `fastFAt`'s arguments. -/
def stepsFAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : FastSteps :=
  let pr := Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP
  let bk := Bq
  let F := W4M.famPrepQ pr bk O (W4M.hintK (Kb + 1) (DK.at frS.P.T.a))
    (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))
  fastStepsT DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G)
    G.early ds xs dec Kb (saltG G) PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF PLe PLe
    PV.Front.numCopy (recSeedK recT recLg recS (Kb + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
    F
    (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq) (hashOf O)
        commitment prompt output aux cm rcd copy fT e fB

/-- The key file's arm alone. `none` where `piTE` gives no string for the key file. -/
def armTAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (cm : Dig 256) (rcd : RecFull) (fT : FileIn) : Option Bool :=
  let pr := Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP
  let bk := Bq
  let F := W4M.famPrepQ pr bk O (W4M.hintK (Kb + 1) (DK.at frS.P.T.a))
    (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))
  (piTE DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G) G.early ds xs dec fT).map fun πT =>
    armTET DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G) G.early ds xs dec Kb (saltG G) (pAt (saltG
        G))
      F cm rcd fT πT

/-- The entry file's arm alone. `none` where `piLE` gives no string for the entry file. -/
def armLAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (cm : Dig 256) (rcd : RecFull) (e : EntryIn) : Option Bool :=
  let pr := Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP
  let bk := Bq
  let F := W4M.famPrepQ pr bk O (W4M.hintK (Kb + 1) (DK.at frS.P.T.a))
    (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))
  (piLE DK DP runK runP G.rec₀ G.z₀.2 (sBG G) G.early ds xs dec e).map fun πL =>
    armLE DK DP runK runP G.rec₀ G.z₀.2 (sBG G) G.early ds xs dec Kb (saltG G) (pAt (saltG G))
      F cm rcd e πL

/-- The proof file's arm alone. `none` where no instance is built or `piBE` gives no string for the
  proof file. -/
def armBAt (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (prompt output aux : List Token) (e : EntryIn) (fB : FileIn) : Option Bool :=
  let pr := Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP
  let bk := Bq
  let F := W4M.famPrepQ pr bk O (W4M.hintK (Kb + 1) (DK.at frS.P.T.a))
    (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))
  match Flat.buildReq (prompt, output) aux with
  | none => none
  | some x =>
    (piBE DK DP runK runP G.rec₀ G.z₀.2 (sBG G) G.early ds xs dec fB).map fun πB =>
      armBET DK DP runK runP G.rec₀ G.z₀.2 (sBG G) G.early ds xs dec Kb (saltG G) PV.Front.r0Full
          (pAt (saltG G))
        F x e fB πB

/-- **At `dsF`, `xsF`, `decF` the `bk` that is wrapped above is `bkFV`**: by unfolding. -/
theorem bk_decS :
    PV.MFull.bkF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
        (linkProtocolOfRoundData CKe dsF frS.P.T.a xsF decF) (_root_.Run.Twin.allLo (SOf CKe dsF)) Kb PV.SerReq.sXF
        (serLAt dsF) =
      PV.MFull.bkFV DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early Kb := rfl

end At

/-! ## At the three public files -/

/-- `dvEAt` at the makers' data and the configuration's digest of the three public files. -/
def dvEFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  dvEAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF

/-- `fastAt` there. -/
def fastFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  fastAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF

/-- **`fastFAt` there**, with `verify-on-bytes`'s two decisions. -/
def fastFFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  fastFAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF

/-- `stepsFAt` there. -/
def stepsFFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  stepsFAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF

/-- The three arms there. -/
def armTFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  armTAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF
def armLFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  armLAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF
def armBFullAt (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  armBAt (GF Z) (cB Z) DK DP (runKFull (GF Z)) (runPFull (GF Z)) dsF xsF decF

/-! ## The same at any two decisions on the two files' views

`runK` and `runP` are the key file's and the proof file's decision. The names above fill in
`runKFull` and `runPFull`: `verify-on-bytes`'s decisions, each with a dry run of that program inside
(Johnson/Flat/WireAt.lean).

`…FullRun` fill in whatever they are handed. They are meant for the description's own decision, with
`DP` the data made of the same description.

`…FullPlan` fill in `runKPlanF` and `runPPlanF`. These are stand-ins: `verify-on-bytes`'s
`decideKey` and `decideProof`, but without a dry run; the two numbers of trees are `DK`'s and `DP`'s
own. They are not the same `Bool` as `runKFull` and `runPFull`: the conjunct `okAt a (dry…)`, the
makers' tests on the dry run, is dropped. So they do not say no by themselves where those tests
fail: the tests must be asked of `DK` and `DP` where these are made. That `DK.t₁`, `DK.t₂` (and
`DP`'s) are the dry run's numbers is shown nowhere here. -/

/-- The types of the two decisions at the full size. -/
abbrev RunKF : Type := RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → Bool
abbrev RunPF : Type :=
  XF × RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → Bool

def dvEFullRun (Z : OnBytes.K.Pub) (DK DP : WholeD) (runK : RunKF) (runP : RunPF) :=
  dvEAt (GF Z) (cB Z) DK DP runK runP dsF xsF decF
def fastFFullRun (Z : OnBytes.K.Pub) (DK DP : WholeD) (runK : RunKF) (runP : RunPF) :=
  fastFAt (GF Z) (cB Z) DK DP runK runP dsF xsF decF
def stepsFFullRun (Z : OnBytes.K.Pub) (DK DP : WholeD) (runK : RunKF) (runP : RunPF) :=
  stepsFAt (GF Z) (cB Z) DK DP runK runP dsF xsF decF
def armTFullRun (Z : OnBytes.K.Pub) (DK DP : WholeD) (runK : RunKF) (runP : RunPF) :=
  armTAt (GF Z) (cB Z) DK DP runK runP dsF xsF decF
def armLFullRun (Z : OnBytes.K.Pub) (DK DP : WholeD) (runK : RunKF) (runP : RunPF) :=
  armLAt (GF Z) (cB Z) DK DP runK runP dsF xsF decF
def armBFullRun (Z : OnBytes.K.Pub) (DK DP : WholeD) (runK : RunKF) (runP : RunPF) :=
  armBAt (GF Z) (cB Z) DK DP runK runP dsF xsF decF

/-- The key file's decision by `verify-on-bytes`, without a dry run: the numbers of trees are
  `DK`'s. -/
def runKPlanF (G : FilesParameters XF RecFull) (DK : WholeD) : RunKF := fun rec v₁ v₂ v₃ =>
  decideKey G.k (keyOf (fun β : NZ => β.val) rec) DK.t₁ DK.t₂ v₁ v₂ v₃

/-- The proof file's decision by `verify-on-bytes`, without a dry run: the numbers of trees are
  `DP`'s. -/
def runPPlanF (G : FilesParameters XF RecFull) (DP : WholeD) : RunPF := fun z v₁ v₂ v₃ =>
  decideProof G.c (keyOf (fun β : NZ => β.val) z.2) (G.block z.1) DP.t₁ DP.t₂ v₁ v₂ v₃

def dvEFullPlan (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  dvEAt (GF Z) (cB Z) DK DP (runKPlanF (GF Z) DK) (runPPlanF (GF Z) DP) dsF xsF decF
def fastFFullPlan (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  fastFAt (GF Z) (cB Z) DK DP (runKPlanF (GF Z) DK) (runPPlanF (GF Z) DP) dsF xsF decF
def stepsFFullPlan (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  stepsFAt (GF Z) (cB Z) DK DP (runKPlanF (GF Z) DK) (runPPlanF (GF Z) DP) dsF xsF decF
def armTFullPlan (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  armTAt (GF Z) (cB Z) DK DP (runKPlanF (GF Z) DK) (runPPlanF (GF Z) DP) dsF xsF decF
def armLFullPlan (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  armLAt (GF Z) (cB Z) DK DP (runKPlanF (GF Z) DK) (runPPlanF (GF Z) DP) dsF xsF decF
def armBFullPlan (Z : OnBytes.K.Pub) (DK DP : WholeD) :=
  armBAt (GF Z) (cB Z) DK DP (runKPlanF (GF Z) DK) (runPPlanF (GF Z) DP) dsF xsF decF

/-- The instance as the description's plain record wants it: the request file's bytes, the table's
  key out of the entry's record, the reply file's bytes. -/
def instPartsOf (z : XF × RecFull) : ByteArray × OnBytes.TableKey × ByteArray :=
  (requestBytesOf z.1.val, keyOf (fun β : NZ => β.val) z.2, replyBytesOf z.1.val)

end LPFD.Full

#print axioms LPFD.Full.cB
#print axioms LPFD.Full.KF
#print axioms LPFD.Full.hKF
#print axioms LPFD.Full.sTG
#print axioms LPFD.Full.sBG
#print axioms LPFD.Full.saltG
#print axioms LPFD.Full.dvEAt
#print axioms LPFD.Full.fastAt
#print axioms LPFD.Full.fastFAt
#print axioms LPFD.Full.famBound_eq
#print axioms LPFD.Full.bk_decS
#print axioms LPFD.Full.serLAt_dsS
#print axioms LPFD.Full.dvEFullAt
#print axioms LPFD.Full.fastFullAt
#print axioms LPFD.Full.fastFFullAt
#print axioms LPFD.Full.stepsFFullAt
#print axioms LPFD.Full.armTFullAt
#print axioms LPFD.Full.armLFullAt
#print axioms LPFD.Full.armBFullAt
