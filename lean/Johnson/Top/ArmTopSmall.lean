-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmTopSmall.lean: the tie's three hypotheses for the entry file (`EntryPart`,
OnBytes/K/Parts.lean) at the input of the entry's arm `armSib` (Johnson/Top/TieArmSib.lean), at the
small size, AT THE THREE FILES' OWN OBJECT AND WIRING.

Johnson/Top/ArmWrittenSmall.lean has the same at a wiring for the arm alone: the entry's own number
of blocks, and stand-ins for the wire records of the two big files. Here the object is
`restSmallAt`, which is the object of the three files by unfolding (`objSmallAt`,
Johnson/Flat/WireAt.lean); the number of blocks is `KSmallAt G + 1`, the one wiring's; and the wire
records of the key file and of the proof file and the four maps between symbols and bodies are those
of `wireSmallAt`. So the wire in the tie's letters IS that wiring (`topWSmall_eq`, `armTopSmall_W`:
by unfolding). The tie at any number of blocks that is at least the description's own is
`entryPart_sibK` (Johnson/Top/TieArmSibK.lean).

The other letters. As in Johnson/Top/ArmWrittenSmall.lean: the ground `smallRecordGround`; the
length of salts the ground's own; nb eight times that; the plain part of the seeds' queries and the
three tests (Johnson/Flat/ArmPlain.lean); the answers' code `codeA`; the total code behind the
escape (`backArmSmall`, Johnson/Flat/SerArmAt.lean), here at `KSmallAt G + 1` blocks; the way of
typed strings `armStringSmall`; the seed d₁ (`topD1Small`). Not as there: the request trees' depths
are those of `wireSmallAt`: the proof file's G.depthReq, the key file's the key's chains' own
(`G.k.oneTime.binding.logLeaves`), the entry file's 0; the record's wire is the top's own `outOfDomainSampleQueryLayoutOfCode`
(Johnson/Flat/SeedTwin.lean), as `InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.letters` (Johnson/Flat/TwoSizes.lean) lays it,
under the tag of Test, at the digest of Z's files and the six words of the tables' shape, with that
record's letter `num` a parameter; the link's honest prover is the provers' own.

Main definitions: `armTopSmall`, `readTopSmall`.
Main theorems.
 `topWSmall_eq`, `armTopSmall_W` the wire is `wireSmallAt A E G P` at the ground's length of salts.
 `armTopSmall_Sd`, `armTopSmall_cA` its seeds' data and its answers' code are the top's own: by
                  unfolding.
 `entryPart_topSmall`     `EntryPart` there. Two hypotheses: Z's parameter file says the ground's
                  lines; `KSmallAt G + 1 < 2 ^ 48`.
 `entryPart_topSmall_at`  the same at every Z whose parameter file begins with the small examples'
                  32 lines (`TestSaysLines.small32`: the first 32 lines of
                  prover/examples/target_small_f2_roomy/policy.txt, which are also those of
                  target_small_f2 and target_small_f2_gap and not those of target_small_file_f2):
                  the second hypothesis alone. What follows the 32 lines, and the two other public
                  files, are free.

What stays a parameter: the claims A with their type X of instances, the coding E of the claims, a
serialiser sX of X, what the makers of the two big files take (G), the honest provers P (data of
which nothing is asked), the record's wire's test `num` on a stored copy's number, and the three
public files Z. THE PARAMETERS' TYPES CARRY LAWS AND INSTANCES, which the counts of hypotheses above
leave out: one law rides in A (`mat_cut`) and two in sX (`get_put`, `put_get`: X must be
serialisable); E's types of randomness and of pads, and each prover's types of coins, are finite and
not empty. That the types of A, E, G, P and sX have a member together is not shown here.

Not claimed. Soundness or hiding. Nothing ties G to Z. Z are the three public files: their digest
stands in the coding and in the seeds' data, and the first hypothesis speaks of their parameter
file. G is what the key file's and the proof file's protocols, their wire records and the number of
blocks are made of. The two are free parameters, so "the three files' own" means "of the description
at G", at any G, also one whose chains are of another plan than Z's (`AtPlan Z G`,
OnBytes/Flat/BigAt.lean, is asked in Johnson/Top/KeyTop.lean and not here). THE WIRE ALONE DOES NOT
MAKE THE ARM'S CODING THE WHOLE VERIFIER'S: the coding of typed queries as strings writes the link's
and the seeds' queries by the format, and the two big files' chain queries behind an escape, by the
total code; the top's own coding is a letter there, and nothing here says that it is this one. The
wiring is of our own choice (Johnson/Flat/WireAt.lean, Limits): that the programs are wired so (this
number of blocks, these three depths, these wire records, these bodies) is not shown. The top's
record's wire has six letters (its tag, two typed pieces, two plain parts and the test `num`): the
arm's is that wire at the values named above for the first five, with `num` a parameter still. The
seeds' two typed queries stand under the tag of Test, so at this object they go to the oracle of the
key file's chain, with the plain part of Johnson/Flat/ArmPlain.lean, which the first round of an
accepted key file sends where its record's answers are the sample record's (see there). The chain of
the compiled verifier of Test asks neither of the two typed forms all the same: that plain part is
one of round 0, and the seeds' queries hold the rounds 1 and 2 (`testChain_ne_seedSmall`,
Johnson/Flat/ArmPlainApart.lean: the chain alone, typed queries alone; nothing on what a prover
asks). That `KSmallAt G + 1 < 2 ^ 48` at any G: the makers' tests on the dry runs bound no round's
draws; at a G that is written out it is a number. That the makers' tests pass at any G: where they
fail, the two big files' data are those of empty lists (Johnson/Flat/WireAt.lean). At the small size
the hypothesis on the proof file's protocol (`CompilerSoundnessConditionStatements.proofSound`) cannot be met by the small
example's protocol at `claimsSmall`, and is not expected to be met at `claimsLedger`, `claimsReq`
(Johnson/Flat/TwoSizes.lean's head: by reading, no theorem). The tie speaks of one fixed function,
Lean's BLAKE2b, in the place of a random function; no bound on a maker of false strings is composed
with it here. The coding and the seeds' data hold two digests that are values of that function: the
digest of Z's three files and the digest of the link's parameters. The arm runs Link's compiled
verifier WITHOUT the strict format. What the arm promises has the way out "the first table decodes
to nothing": the entry file alone closes nothing on an index. What "decodes" means hangs on the
letter A: a table out of A's range decodes to nothing too. The exit code 0 covers the program's
answer "within limits" as well as its yes; a served statement (OnBytes/K/Served.lean) has Z's three
public files, an ID of 64 hex digits, 128 bits, and neither -no-proof-of-work nor -policy, so a call
that ends within limits is not served; no theorem says that the program says yes on any files. Both
theorems are implications: each field of `EntryPart` begins "where the program says yes and the
statement is served at Z". At a Z at which nothing is served (one whose files the planner refuses,
say) they hold for nothing, and `entryPart_topSmall_at` ranges over such Z too. All that the heads
of Johnson/Top/TieArmSibK.lean, Johnson/Top/TieArmSib.lean and Johnson/Top/TieArmAt.lean do not
claim. For proofs only; no program imports this file.


-/
import Johnson.Top.TieArmSibK
import Johnson.Top.ArmStrLaws
import Johnson.Top.ArmOne
import Johnson.Flat.ArmPlain
import Johnson.Flat.ArmSibFiles
import Johnson.Flat.WireAt
import Johnson.Flat.TwoSizes
import OnBytes.K.Left.SibJoin
import OnBytes.K.Left.SaysLinesPrefix

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf)
open TypedOracleCompiler.Run.SeedVals (cfgL shapeBits)
open OnBytes.Tie Hiop Cb Cb.Ood
open OnBytes.K OnBytes.Maker
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (Z : Pub) (sX : Ser X)
  (num : ℕ → Plains (restSmallAt A E G P).bat.loc.shape → Bool)

/-- The length of salts: the ground's own. -/
abbrev topSaltSmall : ℕ := smallRecordGround.q.given.plan.salt

/-- The marks on the link's rounds. -/
abbrev topALSmall := _root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)

/-- The interface of the typed oracles: the three files' own object's. -/
abbrev topL2Small :=
  typedOracleCarrier (LrG (restSmallAt A E G P)) (List Bool) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
  topALSmall

/-- The key file's own wire record. -/
abbrev topWTSmall :=
  wqWhole (ckP .two) (KSmallAt G) (chalP .two (KSmallAt G)) ((dataKSmall G).at srS.P.T.a)
  (front₀ G.rec₀)
    (join₀ G.rec₀) ByteArray.empty silK (runKSmall G)

/-- The proof file's own wire record. -/
abbrev topWBSmall :=
  wqWhole (ckP .two) (KSmallAt G) (chalP .two (KSmallAt G)) ((dataPSmall G).at srS.P.T.a)
  (front₀ G.z₀.2)
    (join₀ G.z₀.2) ByteArray.empty silP (runPSmall G)

/-- The key file's own maps between symbols and bodies. -/
abbrev topEmbTSmall : (p : OPos (restSmallAt A E G P).test.shape) →
    OSym (restSmallAt A E G P).test.shape p → List Bool :=
  SCode.emb _
  (scWhole topSaltSmall (ckP .two) ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀) (join₀ G.rec₀)
      ByteArray.empty)

abbrev topPrjTSmall : (p : OPos (restSmallAt A E G P).test.shape) → List Bool →
    Option (OSym (restSmallAt A E G P).test.shape p) :=
  SCode.prj _
  (scWhole topSaltSmall (ckP .two) ((dataKSmall G).at srS.P.T.a) (front₀ G.rec₀) (join₀ G.rec₀)
      ByteArray.empty)

/-- The proof file's own maps between symbols and bodies. -/
abbrev topEmbBSmall : (p : OPos (restSmallAt A E G P).bat.loc.shape) →
    OSym (restSmallAt A E G P).bat.loc.shape p → List Bool :=
  SCode.emb _
  (scWhole topSaltSmall (ckP .two) ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2) (join₀ G.z₀.2)
      ByteArray.empty)

abbrev topPrjBSmall : (p : OPos (restSmallAt A E G P).bat.loc.shape) → List Bool →
    Option (OSym (restSmallAt A E G P).bat.loc.shape p) :=
  SCode.prj _
  (scWhole topSaltSmall (ckP .two) ((dataPSmall G).at srS.P.T.a) (front₀ G.z₀.2) (join₀ G.z₀.2)
      ByteArray.empty)

/-- The wire, in the tie's letters. -/
abbrev topWSmall :=
  wireSib smallRecordGround (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (restSmallAt A E G P) (KSmallAt G)
    (chalP .two (KSmallAt G))
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (topWTSmall G) (topWBSmall G) G.depthReq
    G.k.oneTime.binding.logLeaves 0
    topSaltSmall (topEmbTSmall A E G P) (topPrjTSmall A E G P) (topEmbBSmall A E G P)
    (topPrjBSmall A E G P)

/-- **The wire is the three files' own wiring**, by unfolding. -/
theorem topWSmall_eq : topWSmall A E G P = wireSmallAt A E G P topSaltSmall := rfl

/-- The wiring has blocks enough for the record's seed. -/
theorem topSeedFitsSmall : (seedBS 19 1).b ≤ KSmallAt G + 1 :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_succ (KSmallAt G))

/-- The plain part of the seeds' two queries. -/
abbrev topQSmall := p0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL topALSmall

/-- The seed that stands where the entry's description has to name one (`earlyTwo`); the tie holds
at every such seed. -/
abbrev topD1Small : Fin 1 → (Fin 19 → GE) × NZ := fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)

/-- The record's wire: the top's own (`outOfDomainSampleQueryLayoutOfCode`, Johnson/Flat/SeedTwin.lean, as
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.letters` of Johnson/Flat/TwoSizes.lean lays it), at the tag of Test, the typed
pieces of a table's name at Z's digest, and the plain part above. -/
abbrev topSSmall :=
  outOfDomainSampleQueryLayoutOfCode (LrG (restSmallAt A E G P)) (List Bool) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT topALSmall
  (v := srS.P.v)
    (lg := 19) (s := 1) .test (cfgL Z.digest)
    (shapeBits smallRecordGround.q.link.table.code.logN smallRecordGround.q.link.table.code.ell
      smallRecordGround.q.link.table.code.r smallRecordGround.q.link.table.v
      smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes)
    (topQSmall A E G P) (topQSmall A E G P) num
    (recSeedK srT 19 1 (KSmallAt G + 1) (topSeedFitsSmall G)) id seedEqSmall

/-- What stands behind the root in a table's name. -/
abbrev topRestSmall : ByteArray :=
  TypedOracleCompiler.Run.FirstName.restOf Z.digest smallRecordGround.q.link.table.code.logN
    smallRecordGround.q.link.table.code.ell smallRecordGround.q.link.table.code.r
    smallRecordGround.q.link.table.v smallRecordGround.q.link.table.answers
    smallRecordGround.q.link.table.saltBytes

/-- The correspondence of the link's plain parts. -/
abbrev topPbSmall :=
  pbSib (DG smallRecordGround Z) (ckP .two) dsSmall (sibLetters_small Z.digest).1
    (sibLetters_small Z.digest).2.1

/-- The total code behind the escape. -/
abbrev topBackSmall :=
  backArmSmall A (Flat.relationsAndEncodingOfClaims A E) G P P.hL topALSmall (Bd := List Bool) (DG smallRecordGround Z)
    (earlyTwo (A := List T3 × List T3) topD1Small)
    (seedEntry smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers)
    (topPbSmall Z) (Equiv.refl (List Bool)) sX
    (TypedOracleCompiler.Run.PQ.bodyS (DG smallRecordGround Z).a (DG smallRecordGround Z).base.plan.salt)
    (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)) _root_.Compile.serBits (KSmallAt G + 1)

/-- **The arm's input at the three files' own object and wiring.** -/
def armTopSmall : ArmIn :=
  armSib smallRecordGround Z (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (restSmallAt A E G P) (KSmallAt G)
    (chalP .two (KSmallAt G))
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (topWTSmall G) (topWBSmall G) G.depthReq
    G.k.oneTime.binding.logLeaves 0
    topSaltSmall (topEmbTSmall A E G P) (topPrjTSmall A E G P) (topEmbBSmall A E G P)
    (topPrjBSmall A E G P)
    (topSSmall A E G P Z num) topD1Small (digest_size Z) (topRestSmall Z) (8 * topSaltSmall)
    (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 (topQSmall A E G P)
    (topQSmall A E G P) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (isPLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z))
    (hpLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z)) codeA codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (topBackSmall A E G P Z sX)

/-- **Its wire is the three files' own wiring**, by unfolding. -/
theorem armTopSmall_W : (armTopSmall A E G P Z sX num).W = wireSmallAt A E G P topSaltSmall := rfl

/-- **Its seeds' data are the top's own record's wire** over that wiring, at the tag of Test, the
typed pieces of a table's name at Z's digest and the ground's shape, and the plain part above: by
unfolding. -/
theorem armTopSmall_Sd : (armTopSmall A E G P Z sX num).Sd =
    outOfDomainSampleQueryLayoutOfCode ((threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
    (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT
      (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annL (v := srS.P.v) (lg := 19) (s := 1) .test
      (cfgL Z.digest)
      (shapeBits smallRecordGround.q.link.table.code.logN smallRecordGround.q.link.table.code.ell
        smallRecordGround.q.link.table.code.r smallRecordGround.q.link.table.v
        smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes)
      (topQSmall A E G P) (topQSmall A E G P) num
      (recSeedK srT 19 1 (wireSmallAt A E G P topSaltSmall).K (seedKSmall A E G P topSaltSmall)) id
      seedEqSmall := rfl

/-- Its answers' code is the top's own. -/
theorem armTopSmall_cA : (armTopSmall A E G P Z sX num).cA = codeA (v := srS.P.v) (s := 1) := rfl

/-- **The reading of the files there.** -/
def readTopSmall : Reading5 (armTopSmall A E G P Z sX num).shape :=
  readSib smallRecordGround Z (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (restSmallAt A E G P) (KSmallAt G)
    (chalP .two (KSmallAt G))
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (topWTSmall G) (topWBSmall G) G.depthReq
    G.k.oneTime.binding.logLeaves 0
    topSaltSmall (topEmbTSmall A E G P) (topPrjTSmall A E G P) (topEmbBSmall A E G P)
    (topPrjBSmall A E G P)
    (topSSmall A E G P Z num) topD1Small (digest_size Z) (topRestSmall Z) (8 * topSaltSmall)
    (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 (topQSmall A E G P)
    (topQSmall A E G P) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (isPLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z))
    (hpLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z)) codeA codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (topBackSmall A E G P Z sX)
    (armStringSmall (restSmallAt A E G P) Z.digest (decAt smallRecordGround Z.digest))

/-- **The tie's three hypotheses for the entry file, at the three files' own object and wiring.**
Two hypotheses: Z's parameter file says the ground's lines; the wiring's number of blocks is below
2 ^ 48. -/
theorem entryPart_topSmall (hZ : smallRecordGround.SaysLines Z.pol) (hK : KSmallAt G + 1 < 2 ^ 48) :
    EntryPart (armTopSmall A E G P Z sX num).shape (readTopSmall A E G P Z sX num) :=
  entryPart_sibK smallRecordGround Z (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (restSmallAt A E G P) (KSmallAt G)
    (chalP .two (KSmallAt G))
    (aT := (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT) (topWTSmall G) (topWBSmall G) G.depthReq
    G.k.oneTime.binding.logLeaves 0
    topSaltSmall (topEmbTSmall A E G P) (topPrjTSmall A E G P) (topEmbBSmall A E G P)
    (topPrjBSmall A E G P)
    (topSSmall A E G P Z num) topD1Small (digest_size Z) (topRestSmall Z) (8 * topSaltSmall)
    (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 (topQSmall A E G P)
    (topQSmall A E G P) (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (isP0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _) (hp0Small A (Flat.relationsAndEncodingOfClaims A E) G P P.hL _)
    (isPLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z))
    (hpLAt (DG smallRecordGround Z) topD1Small (topL2Small A E G P) (topPbSmall Z)) codeA codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (topBackSmall A E G P Z sX)
    (armStringSmall (restSmallAt A E G P) Z.digest (decAt smallRecordGround Z.digest))
    small_record_answers small_record_field hZ armFacts_small (sibLetters_small Z.digest).2.2.1
    (sibLetters_small Z.digest).2.2.2
    (le_of_eq_of_le ((sibK_small Z.digest).symm.trans srD_K.symm) (entryK_le_KSmallAt G))
    (chalP_heq (small_four Z.digest).1.symm rfl) (sibSalt smallRecordGround Z.digest) rfl
    (fun rr => (congrFun (decRun_small Z.digest) (recX rr)).symm) (strLaws_small _ Z)
    (fun x => wire_recSeedK srT 19 1 (KSmallAt G + 1) (topSeedFitsSmall G) x)
    (room_recSeedK (topSeedFitsSmall G)) hK

/-- **The same at every Z whose parameter file begins with the example's 32 lines.** -/
theorem entryPart_topSmall_at (more lay KL : ByteArray) (hK : KSmallAt G + 1 < 2 ^ 48) :
    EntryPart
      (armTopSmall A E G P ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩ sX
        num).shape
      (readTopSmall A E G P ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩ sX
        num) :=
  entryPart_topSmall A E G P _ sX num (small_says_of_prefix more) hK

end

end OnBytes.K.Arm
