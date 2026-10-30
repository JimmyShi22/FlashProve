-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ArmPublicTopFull.lean: the check of the entry file as a function of two public
digests; and a bound, under the theorem on codes, on the probability that it accepts while its
promise fails, where the two digests are answers of a hash function drawn at random. The full size.

Soundness of one arm alone, with the lax Link: `innerCompiledVerifier` has three arms and the
strict format, and no theorem here makes this arm's bound a part of its bound.

What this file states, assumes and does not show, its terms and its limits in full: the comment on
`topFull_public`.

-/
import Johnson.Top.Pub.ArmPublicAt
import Johnson.Top.Pub.ArmSeed
import Johnson.Top.ArmTopFull

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

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (sX : Ser X)
  (num : ℕ → Plains (restFullAt A E G P).bat.loc.shape → Bool)

/-- What stands behind the root in a table's name, at the configuration digest c. -/
abbrev pubRestTopFull (c : ByteArray) : ByteArray :=
  TypedOracleCompiler.Run.FirstName.restOf c recordGround.q.link.table.code.logN
    recordGround.q.link.table.code.ell recordGround.q.link.table.code.r recordGround.q.link.table.v
    recordGround.q.link.table.answers recordGround.q.link.table.saltBytes

/-- The correspondence of the link's plain parts, at the configuration digest c. -/
abbrev pubPbTopFull (c : ByteArray) :=
  pbSib (entryXD recordGround c) (ckP .two) dsFull (sibLetters_full c).1 (sibLetters_full c).2.1

/-- The total code behind the escape, at the configuration digest c. -/
abbrev pubBackTopFull (c : ByteArray) :=
  backArmFull A (Flat.relationsAndEncodingOfClaims A E) G P P.hL topALFull (Bd := List Bool) (entryXD recordGround c)
    (earlyTwo (A := List T3 × List T3) topD1Full)
    (seedEntry recordGround.q.link.table.cubeBits recordGround.q.link.table.answers)
    (pubPbTopFull c) (Equiv.refl (List Bool)) sX
    (TypedOracleCompiler.Run.PQ.bodyS (entryXD recordGround c).a (entryXD recordGround c).base.plan.salt)
    (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)) _root_.Compile.serBits (KFullAt G + 1)

/-- The shape of the tables, as the first seed query holds it. -/
abbrev pubShapeTopFull : Bits :=
  shapeBits recordGround.q.link.table.code.logN recordGround.q.link.table.code.ell
    recordGround.q.link.table.code.r recordGround.q.link.table.v
    recordGround.q.link.table.answers recordGround.q.link.table.saltBytes

/-- The code of a record in the record's wire of `innerCompilerInputFromDryRunAtFullSize`. -/
abbrev pubCodeTopFull : (LrG (restFullAt A E G P)).Rec → List (Dig 256) :=
  fun r => codeP (fun β : NZ => β.val) r

/-- The record's wire of `armTopFull` with a letter for the typed digest behind the root. -/
abbrev pubSTopFull (cfg : List (Dig 256)) :=
  sdAtFull (restFullAt A E G P) (List Bool) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
    (topWFull A E G P) .test cfg pubShapeTopFull (topQFull A E G P) (topQFull A E G P)
    (pubCodeTopFull A E G P) num (topSeedFitsFull G) seedEqFull

/-- At the typed digest of Z's files it is `topSFull`. -/
theorem pubSTopFull_at (Z : Pub) :
    pubSTopFull A E G P num (cfgL Z.digest) = topSFull A E G P Z num := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The family of codings at the three files' own object and wiring, at the full size. -/
def mPubTopFull :
    Dig 256 × Dig 256 → OracleCoding (typedOracleFamily 256 (topWFull A E G P).K (topL2Full A E G P)) 256 :=
  mPub (L := LrG (restFullAt A E G P)) (Bd := List Bool)
    (aT := (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (aL := topALFull) recordGround topD1Full
    pubRestTopFull (8 * topSaltFull) (topWFull A E G P) (pubSTopFull A E G P num [])
    codeA pubPbTopFull (fun _ => Equiv.refl (List Bool)) (topQFull A E G P) (topQFull A E G P)
    (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (fun c => isPLAt (entryXD recordGround c) topD1Full (topL2Full A E G P) (pubPbTopFull c))
    (fun c => hpLAt (entryXD recordGround c) topD1Full (topL2Full A E G P) (pubPbTopFull c))
    OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (pubBackTopFull A E G P sX)

/-- The coding of `armTopFull` at Z, as `mAt` at its letters. -/
theorem topFull_mAt (Z : Pub) :
    (armTopFull A E G P Z sX num).m =
      mAt recordGround Z.digest topD1Full (topRestFull Z) (8 * topSaltFull) (digest_size Z)
        (topWFull A E G P) (topSFull A E G P Z num) codeA (topPbFull Z) (Equiv.refl (List Bool))
        (topQFull A E G P) (topQFull A E G P) (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
        (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
        (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
        (isPLAt (DG recordGround Z) topD1Full (topL2Full A E G P) (topPbFull Z))
        (hpLAt (DG recordGround Z) topD1Full (topL2Full A E G P) (topPbFull Z))
        OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
        trAns_sib_inj (topBackFull A E G P Z sX) := rfl

/-- At the digests of three public files Z the family's member is the coding of `armTopFull` at Z.
The limits: the comment on `topFull_public`. -/
theorem topFull_m (Z : Pub) :
    (armTopFull A E G P Z sX num).m =
      mPubTopFull A E G P sX num
        (bytesToDig Z.digest, EntryRunTop.pdOf (entryXD recordGround Z.digest)) := by
  have h3 := mPub_at (L := LrG (restFullAt A E G P)) (Bd := List Bool)
    (aT := (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (aL := topALFull) recordGround topD1Full
    pubRestTopFull (8 * topSaltFull) (topWFull A E G P) (pubSTopFull A E G P num [])
    codeA pubPbTopFull (fun _ => Equiv.refl (List Bool)) (topQFull A E G P) (topQFull A E G P)
    (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (fun c => isPLAt (entryXD recordGround c) topD1Full (topL2Full A E G P) (pubPbTopFull c))
    (fun c => hpLAt (entryXD recordGround c) topD1Full (topL2Full A E G P) (pubPbTopFull c))
    OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (pubBackTopFull A E G P sX) Z.digest (digest_size Z)
  exact (topFull_mAt A E G P sX num Z).trans ((mAt_seed ..).trans h3.symm)

/-- The arm made of a pair of public digests, at the three files' own object and wiring: the first
digest's bytes stand, as `cfgL`, behind the root in the first seed query. -/
def armPubTopFull (d : Dig 256 × Dig 256) :
    OutLA 256 (LrG (restFullAt A E G P)) topALFull →
      TypedOracleComputation 256 (topWFull A E G P).K (topL2Full A E G P) Bool :=
  armAtFullPub (restFullAt A E G P) (List Bool) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
    (topWFull A E G P) .test (fun e => cfgL (digToBytes e)) pubShapeTopFull (topQFull A E G P)
    (topQFull A E G P) (pubCodeTopFull A E G P) num (topSeedFitsFull G) seedEqFull d

/-- At the digest of three public files Z, whatever the second digest, it is the arm with the lax
Link at `armTopFull`'s own wire, seeds' data and code of the answers.
The limits: the comment on `topFull_public`. -/
theorem topFull_arm (Z : Pub) (p : Dig 256) :
    armPubTopFull A E G P num (bytesToDig Z.digest, p) =
      armL (armTopFull A E G P Z sX num).W (armTopFull A E G P Z sX num).Sd
        (armTopFull A E G P Z sX num).cA :=
  armAtFullPub_at (restFullAt A E G P) (List Bool) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
    (topWFull A E G P) .test pubShapeTopFull (topQFull A E G P) (topQFull A E G P)
    (pubCodeTopFull A E G P) num (topSeedFitsFull G) seedEqFull Z.digest (digest_size Z) p

/-- What the entry's arm asks of the wires holds at the one wiring of the three files: under no
hypothesis. -/
theorem okla_topFull : OKLA (topWFull A E G P) :=
  have h := wiresFullAt A E G P topSaltFull
  ⟨h.2.2.1, h.1.B.ext, h.1.prjE_emb, h.1.prjL_emb, h.1.extDepth.2.1, h.1.extL⟩

set_option maxHeartbeats 2000000 in
/-- The bound at the three files' own object and wiring, at the full size, where the configuration's
digest and the parameters' digest are answers of the drawn function. The maker runs; then the arm
asks the function at the string of the call that hashes the three public files, for c, and at the
string of the call that hashes the parameter bytes of the entry's chain at c, for p, and runs at
them, through the coding with c and p laid in. It accepts, and what it promises fails on the
one-block entries, under that coding, of the maker's log of strings, with probability at most
n 2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W), W the one wiring. One hypothesis beside the
bound on the maker's calls: the theorem on codes.

This file states: `armPubTopFull d`: the check of the entry file made of a pair d of public digests,
over the typed description and the wiring of the three files; `mPubTopFull d`: the coding that goes
with it. `topFull_public`: if the theorem on codes holds (`BCHKS46At GF GE`,
Cb/Gen/CodeListRSAt.lean): an adversary with at most tq queries runs; then the check asks the drawn
function for the two digests and runs at them; it accepts while its promise (`LinkHolds`,
Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean) fails with probability at most n 2^-128 + 2 (n + 1)² / 2^256
at n = 5 (tq + `tVL`), where `tVL` (Johnson/TypedOracleCompiler/RecCompile/LinkOnly.lean) is an upper bound on the
number of typed queries of the check after it has the two public digests, and is not evaluated here.
The asking for the two public digests is two queries more: they stand in neither tq nor `tVL`, and
the promise is read off the adversary's log alone. `topFull_m`, `topFull_arm`: at the digests of
three public files Z under the format's own hash, the coding and the check are those of `armTopFull`
(Johnson/Top/ArmTopFull.lean). Proved here from the theorems of the files imported.

It assumes: in `topFull_public` the theorem on codes, taken as given, and the bound on the
adversary's queries; in the other statements no proposition. X, the claims, the coding of claims,
the plan's data, the provers, the request's spelling and num are variables, fixed before the hash
function is drawn, with whatever laws their types carry. Nothing ties the plan's data to the public
files or to the reference parameters.

It does not show: the bound and the two equations joined in one statement. It is the bound of one
check alone, whose link verifier is the one without the strict format: `innerCompiledVerifier`
has three checks and the strict format, and no theorem here makes this bound a part of its bound. No
yes is shown: the bound would hold of a check that refuses everything. No theorem carries the
probability from the drawn function to the fixed hash. The run's value, which the format hashes from
bytes that the prover picks, is not treated. That the variables' types have a member together is not
shown. A plan's data made of Z's files holds copies of the fixed hash's digest of Z, and that the
check does not read them is not shown. The reference parameters hold 32 typed bytes, a digest of
three public files; no theorem says that the check and the coding are the same at other typed bytes.
What the heads of the three files named at the end of this comment do not claim is not claimed here.
The limits in full, for every statement of this file: below.

Terms: lean/GLOSSARY.md. In the comments of this file a "letter" is a variable, an "arm" is the
check of one file taken as a protocol, "the family" is the coding, or the check, as a function of
the pair of digests, a "coding" says how the one hash function stands for the typed oracles
(lean/GLOSSARY.md, coding), the "wire" or "wiring" is the data that the compiler needs beside a
protocol to write the compiled verifier (lean/GLOSSARY.md, wire), "the object" is the typed
description of the link's protocol over which the check runs, "the maker" is the adversary, who puts
out roots, records and a proof string, "the ground" is the reference parameters typed in Lean, the
"lax Link" is the link verifier without the strict format, "the function" is the hash function that
is drawn. Where a comment of this file names the head of a file, read with
it the comment to which that head points.

THE LIMITS.

Johnson/Top/Pub/ArmPublicTopFull.lean: at the full size, at the three files' own object and wiring
(`armTopFull`, Johnson/Top/ArmTopFull.lean): the family of codings over pairs of public digests; at
the digests of three public files Z it is that input's own coding; and the bound on the arm where
the two digests are answers of the drawn function.

The object is the three files' own (`restFullAt`), the wire is the one wiring of the three files
(`wireFullAt`, Johnson/Flat/WireAt.lean, at `KFullAt G` blocks), and the record's wire is that of
`innerCompilerInputFromDryRunAtFullSize` (`outOfDomainSampleQueryLayoutOfCode`, Johnson/Flat/SeedTwin.lean).



Of the letters of `armTopFull`, the record's wire, rest1, pbF, isPL with hpL, and back hang on Z
through `Z.digest` alone. Here each of these is written as a function of a byte string c:
`pubRestTopFull`, `pubPbTopFull`, `pubBackTopFull`: the texts of `topRestFull`, `topPbFull`,
`topBackFull` with c for `Z.digest`. `pubSTopFull cfg` is `topSFull` with a letter for the typed
digest. The wire has no Z in it. The fields Served and recOf of `armTopFull`, which hang on Z's
files and on the program's own seeds, have no member over d here.

Main names.
 `mPubTopFull`: `mPub` (Johnson/Top/Pub/ArmFamily.lean) at these letters.
 `topFull_mAt`, `topFull_m`: `(armTopFull .. Z sX num).m` is `mAt` at its letters; and it is
     `mPubTopFull` at the digest of Z's files and the format's digest of the parameter bytes of the
     description at that digest.
 `armPubTopFull`: the arm made of a pair of public digests.
 `topFull_arm`: at the digest of Z's files it is the arm with the lax Link at `armTopFull`'s own
     wire, seeds' data and code of the answers.
 `okla_topFull`: what the entry's arm asks of the wires holds at the one wiring.
 `topFull_public`: the bound. Hypotheses: the theorem on codes; the bound on the maker's calls.

To be read with them. `pub2_oBits` (Johnson/Top/Pub/PubStrings.lean): at the oracle made from the
format's hash the public algorithm, at the strings of Z's three files, returns the pair of digests
at which `topFull_m` and `topFull_arm` speak. Asked there: both calls' bytes are within the hash's
bound on lengths (2^32 - 144); neither is proved here.

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
(`Params.recordCfg`), a digest of three public files, which `entryXD` and `s1Of` overwrite
(`linkAtCfg`). The object's link, and the parts of the wire that are made of the ground's
parameters, stand at these parameters with the typed bytes in place and do not read them:
`decRun_full`, `letters_full`, `sibK_full`, at every digest. No theorem says that the family is the
same at a ground with other typed bytes. All else that the heads of
Johnson/Top/Pub/ArmPublicAt.lean, Johnson/Flat/ArmSibPublic.lean and Johnson/Top/ArmTopFull.lean do
not claim.
-/
theorem topFull_public (hA : BCHKS46At GF GE) (pol lay KL : ByteArray)
    (Mk : OComp (rom 256) (OutLA 256 (LrG (restFullAt A E G P)) topALFull))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (expPub (armPubTopFull A E G P num) (mPubTopFull A E G P sX num)
        (pub2 (s0Of pol lay KL) (s1Of recordGround)) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds (topWFull A E G P) (singleTr (mPubTopFull A E G P sX num x.2.1) x.1.2)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL (topWFull A E G P)) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL (topWFull A E G P)) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atFull_arm_public (restFullAt A E G P)
    (restSibFull_dcd A (Flat.relationsAndEncodingOfClaims A E) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G) P P.hL)
    (restSibFull_coll A (Flat.relationsAndEncodingOfClaims A E) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G) P P.hL) (List Bool)
    (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT (topWFull A E G P) .test
    (fun e => cfgL (digToBytes e)) pubShapeTopFull (topQFull A E G P) (topQFull A E G P)
    (pubCodeTopFull A E G P) num (topSeedFitsFull G) seedEqFull recordGround topD1Full
    pubRestTopFull (8 * topSaltFull) (pubSTopFull A E G P num []) pubPbTopFull
    (fun _ => Equiv.refl (List Bool)) (topQFull A E G P) (topQFull A E G P)
    (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (isP0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Full A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (fun c => isPLAt (entryXD recordGround c) topD1Full (topL2Full A E G P) (pubPbTopFull c))
    (fun c => hpLAt (entryXD recordGround c) topD1Full (topL2Full A E G P) (pubPbTopFull c))
    OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (pubBackTopFull A E G P sX) hA (okla_topFull A E G P) pol lay KL Mk tq hq

end OnBytes.K.Arm.Pub
