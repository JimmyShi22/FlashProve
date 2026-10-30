-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ArmPublicTopSmall.lean: at the small example, at the three files' own object and
wiring (`armTopSmall`, Johnson/Top/ArmTopSmall.lean): the family of codings over pairs of public
digests; at the digests of three public files Z it is that input's own coding; and the bound on the
arm where the two digests are answers of the drawn function.

Johnson/Top/Pub/ArmPublicSmall.lean says the like at `armWrittenSmall`, an input with a wire that
serves the entry's arm alone. Here the object is the three files' own (`restSmallAt`), the wire is
the one wiring of the three files (`wireSmallAt`, Johnson/Flat/WireAt.lean, at `KSmallAt G` blocks),
and the record's wire is that of `innerCompilerInputFromDryRunAtSmallSize` (`outOfDomainSampleQueryLayoutOfCode`, Johnson/Flat/SeedTwin.lean).



Of the letters of `armTopSmall`, the record's wire, rest1, pbF, isPL with hpL, and back hang on Z
through `Z.digest` alone. Here each of these is written as a function of a byte string c:
`pubRestTopSmall`, `pubPbTopSmall`, `pubBackTopSmall`: the texts of `topRestSmall`, `topPbSmall`,
`topBackSmall` with c for `Z.digest`. `pubSTopSmall cfg` is `topSSmall` with a letter for the typed
digest. The wire has no Z in it. The fields Served and recOf of `armTopSmall`, which hang on Z's
files and on the program's own seeds, have no member over d here.

Main names.
 `mPubTopSmall`: `mPub` (Johnson/Top/Pub/ArmFamily.lean) at these letters.
 `topSmall_mAt`, `topSmall_m`: `(armTopSmall .. Z sX num).m` is `mAt` at its letters; and it is
     `mPubTopSmall` at the digest of Z's files and the format's digest of the parameter bytes of the
     description at that digest.
 `armPubTopSmall`: the arm made of a pair of public digests.
 `topSmall_arm`: at the digest of Z's files it is the arm with the lax Link at `armTopSmall`'s own
     wire, seeds' data and code of the answers.
 `okla_topSmall`: what the entry's arm asks of the wires holds at the one wiring.
 `topSmall_public`: the bound. Hypotheses: the theorem on codes; the bound on the maker's calls.

To be read with them. `pub2_oBits` (Johnson/Top/Pub/PubStrings.lean): at the oracle made from the
format's hash the public algorithm, at the strings of Z's three files, returns the pair of digests
at which `topSmall_m` and `topSmall_arm` speak. Asked there: both calls' bytes are within the hash's
bound on lengths (2^32 - 144); neither is paid here.

What is not claimed. The bound and the two equations are not joined in one statement here. Soundness
of one arm alone, with the lax Link: `innerCompiledVerifier` has three arms and the strict
format, and no theorem here makes this arm's bound a part of its bound. No yes is shown: the bound
would hold of an arm that refuses everything. The run's value, which the format hashes from the
parameters' digest and bytes that the prover picks, is no public digest and is not treated. No
theorem carries the probability from the drawn function to the fixed hash. The hypothesis on codes
is the theorem on codes, taken as given. The type X and A, E, G, P, sX, num stay, with whatever laws
their types carry; nothing ties G to Z or to the ground. G's six chains each hold parameter bytes
and a digest: a G at the plan of Z's files holds copies of the fixed hash's digest of Z; the object,
the wire and the coding's escape are made of G; the family overwrites nothing in G, and G is fixed
before the function is drawn. That the arm does not read these copies is not shown here. That these
types have a member together is not shown here. The ground holds 32 typed bytes
(`Params.smallRecordCfg`), a digest of three public files, which `entryXD` and `s1Of` overwrite
(`linkAtCfg`). The object's link, and the parts of the wire that are made of the ground's
parameters, stand at these parameters with the typed bytes in place and do not read them:
`decRun_small`, `letters_small`, `sibK_small`, at every digest. No theorem says that the family is
the same at a ground with other typed bytes. All else that the heads of
Johnson/Top/Pub/ArmPublicAt.lean, Johnson/Flat/ArmSibPublic.lean and Johnson/Top/ArmTopSmall.lean do
not claim.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Pub.ArmPublicAt
import Johnson.Top.Pub.ArmSeed
import Johnson.Top.ArmTopSmall

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace OnBytes.K.Arm.Pub
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf)
open TypedOracleCompiler.Run.SeedVals (cfgL shapeBits)
open OnBytes.Tie Hiop Cb Cb.Ood
open OnBytes.K OnBytes.K.Arm OnBytes.Maker
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)
open scoped ENNReal

variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (sX : Ser X)
  (num : ℕ → Plains (restSmallAt A E G P).bat.loc.shape → Bool)

/-- What stands behind the root in a table's name, at the configuration digest c. -/
abbrev pubRestTopSmall (c : ByteArray) : ByteArray :=
  TypedOracleCompiler.Run.FirstName.restOf c smallRecordGround.q.link.table.code.logN
    smallRecordGround.q.link.table.code.ell smallRecordGround.q.link.table.code.r
    smallRecordGround.q.link.table.v
    smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes

/-- The correspondence of the link's plain parts, at the configuration digest c. -/
abbrev pubPbTopSmall (c : ByteArray) :=
  pbSib (entryXD smallRecordGround c) (ckP .two) dsSmall (sibLetters_small c).1
  (sibLetters_small c).2.1

/-- The total code behind the escape, at the configuration digest c. -/
abbrev pubBackTopSmall (c : ByteArray) :=
  backArmSmall A (Flat.relationsAndEncodingOfClaims A E) G P P.hL topALSmall (Bd := List Bool)
  (entryXD smallRecordGround c)
    (earlyTwo (A := List T3 × List T3) topD1Small)
    (seedEntry smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers)
    (pubPbTopSmall c) (Equiv.refl (List Bool)) sX
    (TypedOracleCompiler.Run.PQ.bodyS (entryXD smallRecordGround c).a
      (entryXD smallRecordGround c).base.plan.salt)
    (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)) _root_.Compile.serBits (KSmallAt G + 1)

/-- The shape of the tables, as the first seed query holds it. -/
abbrev pubShapeTopSmall : Bits :=
  shapeBits smallRecordGround.q.link.table.code.logN smallRecordGround.q.link.table.code.ell
    smallRecordGround.q.link.table.code.r smallRecordGround.q.link.table.v
    smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes

/-- The code of a record in the record's wire of `innerCompilerInputFromDryRunAtSmallSize`. -/
abbrev pubCodeTopSmall : (LrG (restSmallAt A E G P)).Rec → List (Dig 256) :=
  fun r => codeP (fun β : NZ => β.val) r

/-- The record's wire of `armTopSmall` with a letter for the typed digest behind the root. -/
abbrev pubSTopSmall (cfg : List (Dig 256)) :=
  sdAtSmall (restSmallAt A E G P) (List Bool) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
    (topWSmall A E G P) .test cfg pubShapeTopSmall (topQSmall A E G P) (topQSmall A E G P)
    (pubCodeTopSmall A E G P) num (topSeedFitsSmall G) seedEqSmall

/-- At the typed digest of Z's files it is `topSSmall`. -/
theorem pubSTopSmall_at (Z : Pub) :
    pubSTopSmall A E G P num (cfgL Z.digest) = topSSmall A E G P Z num := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The family of codings at the three files' own object and wiring, at the small example. -/
def mPubTopSmall :
    Dig 256 × Dig 256 → OracleCoding (typedOracleFamily 256 (topWSmall A E G P).K (topL2Small A E G P)) 256 :=
  mPub (L := LrG (restSmallAt A E G P)) (Bd := List Bool)
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (aL := topALSmall) smallRecordGround topD1Small
    pubRestTopSmall (8 * topSaltSmall) (topWSmall A E G P) (pubSTopSmall A E G P num [])
    codeA pubPbTopSmall (fun _ => Equiv.refl (List Bool)) (topQSmall A E G P) (topQSmall A E G P)
    (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (fun c => isPLAt (entryXD smallRecordGround c) topD1Small (topL2Small A E G P)
      (pubPbTopSmall c))
    (fun c => hpLAt (entryXD smallRecordGround c) topD1Small (topL2Small A E G P) (pubPbTopSmall c))
    OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (pubBackTopSmall A E G P sX)

/-- The coding of `armTopSmall` at Z, as `mAt` at its letters. -/
theorem topSmall_mAt (Z : Pub) :
    (armTopSmall A E G P Z sX num).m =
      mAt smallRecordGround Z.digest topD1Small (topRestSmall Z) (8 * topSaltSmall) (digest_size Z)
        (topWSmall A E G P) (topSSmall A E G P Z num) codeA (topPbSmall Z) (Equiv.refl (List Bool))
        (topQSmall A E G P) (topQSmall A E G P) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
        (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
        (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
        (isPLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z))
        (hpLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z))
        OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
        trAns_sib_inj (topBackSmall A E G P Z sX) := rfl

/-- At the digests of three public files Z the family's member is the coding of `armTopSmall` at Z.
-/
theorem topSmall_m (Z : Pub) :
    (armTopSmall A E G P Z sX num).m =
      mPubTopSmall A E G P sX num
        (bytesToDig Z.digest, EntryRunTop.pdOf (entryXD smallRecordGround Z.digest)) := by
  have h3 := mPub_at (L := LrG (restSmallAt A E G P)) (Bd := List Bool)
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (aL := topALSmall) smallRecordGround topD1Small
    pubRestTopSmall (8 * topSaltSmall) (topWSmall A E G P) (pubSTopSmall A E G P num [])
    codeA pubPbTopSmall (fun _ => Equiv.refl (List Bool)) (topQSmall A E G P) (topQSmall A E G P)
    (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (fun c => isPLAt (entryXD smallRecordGround c) topD1Small (topL2Small A E G P)
      (pubPbTopSmall c))
    (fun c => hpLAt (entryXD smallRecordGround c) topD1Small (topL2Small A E G P) (pubPbTopSmall c))
    OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (pubBackTopSmall A E G P sX) Z.digest (digest_size Z)
  exact (topSmall_mAt A E G P sX num Z).trans ((mAt_seed ..).trans h3.symm)

/-- The arm made of a pair of public digests, at the three files' own object and wiring: the first
digest's bytes stand, as `cfgL`, behind the root in the first seed query. -/
def armPubTopSmall (d : Dig 256 × Dig 256) :
    OutLA 256 (LrG (restSmallAt A E G P)) topALSmall →
      TypedOracleComputation 256 (topWSmall A E G P).K (topL2Small A E G P) Bool :=
  armAtSmallPub (restSmallAt A E G P) (List Bool) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
    (topWSmall A E G P) .test (fun e => cfgL (digToBytes e)) pubShapeTopSmall (topQSmall A E G P)
    (topQSmall A E G P) (pubCodeTopSmall A E G P) num (topSeedFitsSmall G) seedEqSmall d

/-- At the digest of three public files Z, whatever the second digest, it is the arm with the lax
Link at `armTopSmall`'s own wire, seeds' data and code of the answers. -/
theorem topSmall_arm (Z : Pub) (p : Dig 256) :
    armPubTopSmall A E G P num (bytesToDig Z.digest, p) =
      armL (armTopSmall A E G P Z sX num).W (armTopSmall A E G P Z sX num).Sd
        (armTopSmall A E G P Z sX num).cA :=
  armAtSmallPub_at (restSmallAt A E G P) (List Bool) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
    (topWSmall A E G P) .test pubShapeTopSmall (topQSmall A E G P) (topQSmall A E G P)
    (pubCodeTopSmall A E G P) num (topSeedFitsSmall G) seedEqSmall Z.digest (digest_size Z) p

/-- What the entry's arm asks of the wires holds at the one wiring of the three files: under no
hypothesis. -/
theorem okla_topSmall : OKLA (topWSmall A E G P) :=
  have h := wiresSmallAt A E G P topSaltSmall
  ⟨h.2.2.1, h.1.B.ext, h.1.prjE_emb, h.1.prjL_emb, h.1.extDepth.2.1, h.1.extL⟩

set_option maxHeartbeats 2000000 in
/-- The bound at the three files' own object and wiring, at the small example, where the
configuration's digest and the parameters' digest are answers of the drawn function. The maker runs;
then the arm asks the function at the string of the call that hashes the three public files, for c,
and at the string of the call that hashes the parameter bytes of the entry's chain at c, for p, and
runs at them, through the coding with c and p laid in. It accepts, and what it promises fails on the
one-block entries, under that coding, of the maker's log of strings, with probability at most n
2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W), W the one wiring. One hypothesis beside the bound
on the maker's calls: the theorem on codes. -/
theorem topSmall_public (hA : BCHKS46At GF GE) (pol lay KL : ByteArray)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restSmallAt A E G P)) topALSmall))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (expPub (armPubTopSmall A E G P num) (mPubTopSmall A E G P sX num)
        (pub2 (s0Of pol lay KL) (s1Of smallRecordGround)) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds (topWSmall A E G P) (singleTr (mPubTopSmall A E G P sX num x.2.1) x.1.2)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (topWSmall A E G P)) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (topWSmall A E G P)) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atSmall_arm_public (restSmallAt A E G P)
    (restSibSmall_dcd A (Flat.relationsAndEncodingOfClaims A E) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G) P P.hL)
    (restSibSmall_coll A (Flat.relationsAndEncodingOfClaims A E) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G) P P.hL) (List Bool)
    (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT (topWSmall A E G P) .test
    (fun e => cfgL (digToBytes e)) pubShapeTopSmall (topQSmall A E G P) (topQSmall A E G P)
    (pubCodeTopSmall A E G P) num (topSeedFitsSmall G) seedEqSmall smallRecordGround topD1Small
    pubRestTopSmall (8 * topSaltSmall) (pubSTopSmall A E G P num []) pubPbTopSmall
    (fun _ => Equiv.refl (List Bool)) (topQSmall A E G P) (topQSmall A E G P)
    (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (fun c => isPLAt (entryXD smallRecordGround c) topD1Small (topL2Small A E G P)
      (pubPbTopSmall c))
    (fun c => hpLAt (entryXD smallRecordGround c) topD1Small (topL2Small A E G P) (pubPbTopSmall c))
    OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (pubBackTopSmall A E G P sX) hA (okla_topSmall A E G P) pol lay KL Mk tq hq

end OnBytes.K.Arm.Pub
