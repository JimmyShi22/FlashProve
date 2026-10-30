-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmWrittenSmall.lean: the tie's three hypotheses for the entry file (`EntryPart`,
OnBytes/K/Parts.lean) at the input of the entry's arm `armSib` (Johnson/Top/TieArmSib.lean), at
the small example, with `armSib`'s letters of data written as terms over the parameters A, R, G, P,
hL, sX and Z, and every premise of `entryPart_sib` paid but that Z's parameter file says the
ground's lines.

`entryPart_sib` is general in its letters and asks premises of them. Here each letter of data is a
written term and each premise is paid by a theorem that lies:
 the ground `smallRecordGround`; the object `restSibSmall` at `threeProtocolsFromDryRunAtSmallSize`
 (Johnson/Flat/RestSib.lean);
 99 + 1 blocks, with the written way `chalP .two 99` from blocks to verifier's messages;
 the wire records of the two big files, the four maps, `code`, `num`: the STAND-INS of
 Johnson/Flat/ArmData.lean: by the text of the arm neither its run nor the coding reads them; the
 session's wire of external strings, which is `oneExt`'s (Johnson/Flat/ArmSibMaker.lean), is read
 by what the arm promises alone;
 the test of equality of seeds, which the arm's run reads (every such test gives the same verdict),
 and the seed d₁, which the coding reads (the tie holds at every d₁): written terms of that file;
 the length of salts: the ground's own, on both sides; nb eight times that; depthReqL := 0;
 the record's wire `sdAtSmall` under the tag of Test, at the digest of Z's files and the six words
 of the tables' shape; rest1: what stands behind the root in a table's name (nothing is asked of
 it);
 the plain part of the seeds' queries and the three tests: Johnson/Flat/ArmPlain.lean (the key
 file's first round can send that plain part: see there);
 the answers' code `codeA`; the total code behind the escape: `backArmSmall`
 (Johnson/Flat/SerArmAt.lean); the way of typed strings: `armStringSmall`
 (Johnson/Flat/ArmString.lean).
 The premises: OnBytes/K/Left/SibJoin.lean (the seven letters, the decision),
 OnBytes/K/Arm/ArmFacts.lean (what a yes of the program gives), Johnson/Top/ArmStrLaws.lean,
 OnBytes/K/Left/SeedWire.lean (wire, room), Johnson/Top/ArmOne.lean (the digest's 32 bytes).

Main definitions: `armWrittenSmall`, `readWrittenSmall`.
Main theorems.
 `entryPart_writtenSmall`     `EntryPart` there. One hypothesis: Z's parameter file says the
 ground's
                  lines.
 `entryPart_writtenSmall_at`  the same at every Z whose parameter file begins with the example's 32
                  lines (OnBytes/K/Left/SaysLinesPrefix.lean): no hypothesis.
With `exit_arm` (Johnson/Top/TieArm.lean): from the exit code 0 of the program on a served statement
to the yes of the run of the entry's arm at these terms.

What stays a parameter: the claims A with their type X of instances, a serialiser sX of X, the rest
R, what the makers of the two big files take (G), the honest provers P and hL (data of which nothing
is asked), and the three public files Z. THE PARAMETERS' TYPES CARRY LAWS AND INSTANCES, which the
counts of hypotheses above leave out: one law rides in A (`mat_cut`) and two in sX (`get_put`,
`put_get`: X must be serialisable); R's types of randomness and of pads, and each prover's types of
coins, are finite and not empty. That the six types of A, R, G, P, hL and sX have a member together
is not shown here.

Not claimed. Soundness or hiding. This is a wiring FOR THE ARM ALONE: 99 + 1 blocks are the entry's
count, and the two big files' wire records are stand-ins: no compiled verifier of the key file or
the proof file should be read at it. The object is the three files' own where hL is the provers'
own (Johnson/Flat/RestSib.lean, Johnson/Flat/WireAt.lean); the WIRE is not the one wiring's
(Johnson/Top/ArmTopSmall.lean has that). The coding too serves the arm alone: it writes the
program's strings at the seeds' and the link's queries, leaves and vertices; every other typed
query, the key file's and the proof file's among them, goes behind an escape. The tie speaks of one
fixed function, Lean's BLAKE2b, in the place of a random function; no bound on a
maker of false strings is composed with it here. The coding and the seeds' data hold two digests
that are values of that function: the digest of Z's three files and the digest of the link's
parameters. The arm runs Link's compiled verifier WITHOUT the strict format. What the arm promises
has the way out "the first table decodes to nothing": the entry file alone closes nothing on an
index. What "decodes" means hangs on the letter A: a table out of A's range decodes to nothing too.
The exit code 0 covers the program's answer "within limits" as well as its yes; a served statement
(OnBytes/K/Served.lean) has Z's three public files, an ID of 64 hex digits, 128 bits, and neither
-no-proof-of-work nor -policy, so a call that ends within limits is not served; no theorem says
that the program says yes on any files. All that the heads of Johnson/Top/TieArmSib.lean and
Johnson/Top/TieArmAt.lean do not
claim. For proofs only; no program imports this file.


-/
import Johnson.Top.TieArmSib
import Johnson.Top.ArmStrLaws
import Johnson.Top.ArmOne
import Johnson.Flat.ArmData
import Johnson.Flat.ArmPlain
import Johnson.Flat.ArmSibMaker
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
open OnBytes.K
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A R G).Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))
  (Z : Pub) (sX : Ser X)

/-- The object: the three files' own parts, with `linkSibSmall` for its link. -/
abbrev armTSmall := restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL

/-- The stand-ins for the letters of data. -/
abbrev armDSmall := armDataSmall A R G P hL 99

/-- The wire. -/
abbrev armWSmall :=
  wAtSmall (armTSmall A R G P hL) 99 (armDSmall A R G P hL).wT
    (oneExt (armDSmall A R G P hL).wB (armDSmall A R G P hL).z) (armDSmall A R G P hL).depthReq
    (armDSmall A R G P hL).depthReqT smallRecordGround.q.given.plan.salt (armDSmall A R G P hL).embT
    (armDSmall A R G P hL).prjT (armDSmall A R G P hL).embB (armDSmall A R G P hL).prjB

/-- The interface of the typed oracles. -/
abbrev armL2Small :=
  typedOracleCarrier (LrG (armTSmall A R G P hL)) (List Bool) (threeProtocolsFromDryRunAtSmallSize A R G).annT
    (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))

/-- The plain part of the seeds' two queries. -/
abbrev armQSmall := p0Small A R G P hL (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))

/-- The record's wire. -/
abbrev armSSmall :=
  sdAtSmall (armTSmall A R G P hL) (List Bool) (threeProtocolsFromDryRunAtSmallSize A R G).annT (armWSmall A R G P hL) .test
    (cfgL Z.digest)
    (shapeBits smallRecordGround.q.link.table.code.logN smallRecordGround.q.link.table.code.ell
      smallRecordGround.q.link.table.code.r smallRecordGround.q.link.table.v
      smallRecordGround.q.link.table.answers smallRecordGround.q.link.table.saltBytes)
    (armQSmall A R G P hL) (armQSmall A R G P hL) (armDSmall A R G P hL).code
    (armDSmall A R G P hL).num
    sr_seed_fits (armDSmall A R G P hL).dS

/-- What stands behind the root in a table's name: the digest, then the six words of the tables'
shape. -/
abbrev armRestSmall : ByteArray :=
  TypedOracleCompiler.Run.FirstName.restOf Z.digest smallRecordGround.q.link.table.code.logN
    smallRecordGround.q.link.table.code.ell smallRecordGround.q.link.table.code.r
    smallRecordGround.q.link.table.v smallRecordGround.q.link.table.answers
    smallRecordGround.q.link.table.saltBytes

/-- The correspondence of the link's plain parts. -/
abbrev armPbSmall :=
  pbSib (DG smallRecordGround Z) (ckP .two) dsSmall (sibLetters_small Z.digest).1
    (sibLetters_small Z.digest).2.1

/-- The total code behind the escape. -/
abbrev armBackSmall :=
  backArmSmall A R G P hL (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)) (Bd := List Bool)
    (DG smallRecordGround Z) (earlyTwo (A := List T3 × List T3) (armDSmall A R G P hL).d₁)
    (seedEntry smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers)
    (armPbSmall Z) (Equiv.refl (List Bool)) sX
    (TypedOracleCompiler.Run.PQ.bodyS (DG smallRecordGround Z).a (DG smallRecordGround Z).base.plan.salt)
    (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)) _root_.Compile.serBits (99 + 1)

/-- **The arm's input**: `armSib`'s letters of data written, over the parameters. -/
def armWrittenSmall : ArmIn :=
  armSib smallRecordGround Z (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (armTSmall A R G P hL) 99 (chalP .two 99)
    (aT := (threeProtocolsFromDryRunAtSmallSize A R G).annT) (armDSmall A R G P hL).wT
    (oneExt (armDSmall A R G P hL).wB (armDSmall A R G P hL).z) (armDSmall A R G P hL).depthReq
    (armDSmall A R G P hL).depthReqT 0 smallRecordGround.q.given.plan.salt
    (armDSmall A R G P hL).embT
    (armDSmall A R G P hL).prjT (armDSmall A R G P hL).embB (armDSmall A R G P hL).prjB
    (armSSmall A R G P hL Z)
    (armDSmall A R G P hL).d₁ (digest_size Z) (armRestSmall Z)
    (8 * smallRecordGround.q.given.plan.salt)
    (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 (armQSmall A R G P hL)
    (armQSmall A R G P hL) (isP0Small A R G P hL _) (isP0Small A R G P hL _)
    (hp0Small A R G P hL _) (hp0Small A R G P hL _)
    (isPLAt (DG smallRecordGround Z) (armDSmall A R G P hL).d₁ (armL2Small A R G P hL)
      (armPbSmall Z))
    (hpLAt (DG smallRecordGround Z) (armDSmall A R G P hL).d₁ (armL2Small A R G P hL)
      (armPbSmall Z))
    codeA
    codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (armBackSmall A R G P hL Z sX)

/-- **The reading of the files there.** -/
def readWrittenSmall : Reading5 (armWrittenSmall A R G P hL Z sX).shape :=
  readSib smallRecordGround Z (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (armTSmall A R G P hL) 99 (chalP .two 99)
    (aT := (threeProtocolsFromDryRunAtSmallSize A R G).annT) (armDSmall A R G P hL).wT
    (oneExt (armDSmall A R G P hL).wB (armDSmall A R G P hL).z) (armDSmall A R G P hL).depthReq
    (armDSmall A R G P hL).depthReqT 0 smallRecordGround.q.given.plan.salt
    (armDSmall A R G P hL).embT
    (armDSmall A R G P hL).prjT (armDSmall A R G P hL).embB (armDSmall A R G P hL).prjB
    (armSSmall A R G P hL Z)
    (armDSmall A R G P hL).d₁ (digest_size Z) (armRestSmall Z)
    (8 * smallRecordGround.q.given.plan.salt)
    (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 (armQSmall A R G P hL)
    (armQSmall A R G P hL) (isP0Small A R G P hL _) (isP0Small A R G P hL _)
    (hp0Small A R G P hL _) (hp0Small A R G P hL _)
    (isPLAt (DG smallRecordGround Z) (armDSmall A R G P hL).d₁ (armL2Small A R G P hL)
      (armPbSmall Z))
    (hpLAt (DG smallRecordGround Z) (armDSmall A R G P hL).d₁ (armL2Small A R G P hL)
      (armPbSmall Z))
    codeA
    codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (armBackSmall A R G P hL Z sX)
    (armStringSmall (armTSmall A R G P hL) Z.digest (decAt smallRecordGround Z.digest))

/-- **The tie's three hypotheses for the entry file, at these values.** One hypothesis is left: Z's
parameter file says the ground's lines. -/
theorem entryPart_writtenSmall (hZ : smallRecordGround.SaysLines Z.pol) :
    EntryPart (armWrittenSmall A R G P hL Z sX).shape (readWrittenSmall A R G P hL Z sX) :=
  entryPart_sib smallRecordGround Z (C := ckP .two) (ds := dsSmall) (a := srS.P.T.a) (xs := srD.xs)
    (dec2 := fun rr => decSmallX (recX rr)) (armTSmall A R G P hL) 99 (chalP .two 99)
    (aT := (threeProtocolsFromDryRunAtSmallSize A R G).annT) (armDSmall A R G P hL).wT
    (oneExt (armDSmall A R G P hL).wB (armDSmall A R G P hL).z) (armDSmall A R G P hL).depthReq
    (armDSmall A R G P hL).depthReqT 0 smallRecordGround.q.given.plan.salt
    (armDSmall A R G P hL).embT
    (armDSmall A R G P hL).prjT (armDSmall A R G P hL).embB (armDSmall A R G P hL).prjB
    (armSSmall A R G P hL Z)
    (armDSmall A R G P hL).d₁ (digest_size Z) (armRestSmall Z)
    (8 * smallRecordGround.q.given.plan.salt)
    (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 (armQSmall A R G P hL)
    (armQSmall A R G P hL) (isP0Small A R G P hL _) (isP0Small A R G P hL _)
    (hp0Small A R G P hL _) (hp0Small A R G P hL _)
    (isPLAt (DG smallRecordGround Z) (armDSmall A R G P hL).d₁ (armL2Small A R G P hL)
      (armPbSmall Z))
    (hpLAt (DG smallRecordGround Z) (armDSmall A R G P hL).d₁ (armL2Small A R G P hL)
      (armPbSmall Z))
    codeA
    codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (armBackSmall A R G P hL Z sX)
    (armStringSmall (armTSmall A R G P hL) Z.digest (decAt smallRecordGround Z.digest))
    small_record_answers small_record_field hZ armFacts_small (sibLetters_small Z.digest).2.2.1
    (sibLetters_small Z.digest).2.2.2 (sibK_small Z.digest) (sibChal_small Z.digest)
    (sibSalt smallRecordGround Z.digest) rfl
    (fun rr => (congrFun (decRun_small Z.digest) (recX rr)).symm) (strLaws_small _ Z)
    (fun x => wire_recSeedK srT 19 1 (99 + 1) sr_seed_fits x) (room_recSeedK sr_seed_fits)
    (by norm_num)

/-- **The same at every Z whose parameter file begins with the example's 32 lines**: no hypothesis
is left. lay, KL: the two other public files; more: what follows the 32 lines. -/
theorem entryPart_writtenSmall_at (more lay KL : ByteArray) :
    EntryPart
      (armWrittenSmall A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩
        sX).shape
      (readWrittenSmall A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩
        sX) :=
  entryPart_writtenSmall A R G P hL _ sX (small_says_of_prefix more)

end

end OnBytes.K.Arm
