-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmWrittenFull.lean: the tie's three hypotheses for the entry file (`EntryPart`,
OnBytes/K/Parts.lean) at the input of the entry's arm `armSib` (Johnson/Top/TieArmSib.lean), at
the full size, with `armSib`'s letters of data written as terms over the parameters A, R, G, P,
hL, sX and Z, and every premise of `entryPart_sib` paid but that Z's parameter file says the
ground's lines.

`entryPart_sib` is general in its letters and asks premises of them. Here each letter of data is a
written term and each premise is paid by a theorem that lies:
 the ground `recordGround`; the object `restSibFull` at `threeProtocolsFromDryRunAtFullSize` (Johnson/Flat/RestSib.lean);
 140 + 1 blocks, with the written way `chalP .two 140` from blocks to verifier's messages;
 the wire records of the two big files, the four maps, `code`, `num`: the STAND-INS of
 Johnson/Flat/ArmData.lean: by the text of the arm neither its run nor the coding reads them; the
 session's wire of external strings, which is `oneExt`'s (Johnson/Flat/ArmSibMaker.lean), is read
 by what the arm promises alone;
 the test of equality of seeds, which the arm's run reads (every such test gives the same verdict),
 and the seed d₁, which the coding reads (the tie holds at every d₁): written terms of that file;
 the length of salts: the ground's own, on both sides; nb eight times that; depthReqL := 0;
 the record's wire `sdAtFull` under the tag of Test, at the digest of Z's files and the six words
 of the tables' shape; rest1: what stands behind the root in a table's name (nothing is asked of
 it);
 the plain part of the seeds' queries and the three tests: Johnson/Flat/ArmPlain.lean (the key
 file's first round can send that plain part: see there);
 the answers' code `codeA`; the total code behind the escape: `backArmFull`
 (Johnson/Flat/SerArmAt.lean); the way of typed strings: `armStringFull`
 (Johnson/Flat/ArmString.lean).
 The premises: OnBytes/K/Left/SibJoin.lean (the seven letters, the decision),
 OnBytes/K/Arm/ArmFacts.lean (what a yes of the program gives), Johnson/Top/ArmStrLaws.lean,
 OnBytes/K/Left/SeedWire.lean (wire, room), Johnson/Top/ArmOne.lean (the digest's 32 bytes).

Main definitions: `armWrittenFull`, `readWrittenFull`.
Main theorems.
 `entryPart_writtenFull`     `EntryPart` there. One hypothesis: Z's parameter file says the ground's
                  lines.
 `entryPart_writtenFull_at`  the same at every Z whose parameter file begins with the example's 32
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

Not claimed. Soundness or hiding. This is a wiring FOR THE ARM ALONE: 140 + 1 blocks are the entry's
count, and the two big files' wire records are stand-ins: no compiled verifier of the key file or
the proof file should be read at it. The object is the three files' own where hL is the provers'
own (Johnson/Flat/RestSib.lean, Johnson/Flat/WireAt.lean); the WIRE is not the one wiring's
(Johnson/Top/ArmTopFull.lean has that). The coding too serves the arm alone: it writes the
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
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A R G).Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))
  (Z : Pub) (sX : Ser X)

/-- The object: the three files' own parts, with `linkSibFull` for its link. -/
abbrev armTFull := restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL

/-- The stand-ins for the letters of data. -/
abbrev armDFull := armDataFull A R G P hL 140

/-- The wire. -/
abbrev armWFull :=
  wAtFull (armTFull A R G P hL) 140 (armDFull A R G P hL).wT
    (oneExt (armDFull A R G P hL).wB (armDFull A R G P hL).z) (armDFull A R G P hL).depthReq
    (armDFull A R G P hL).depthReqT recordGround.q.given.plan.salt (armDFull A R G P hL).embT
    (armDFull A R G P hL).prjT (armDFull A R G P hL).embB (armDFull A R G P hL).prjB

/-- The interface of the typed oracles. -/
abbrev armL2Full :=
  typedOracleCarrier (LrG (armTFull A R G P hL)) (List Bool) (threeProtocolsFromDryRunAtFullSize A R G).annT
    (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))

/-- The plain part of the seeds' two queries. -/
abbrev armQFull := p0Full A R G P hL (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))

/-- The record's wire. -/
abbrev armSFull :=
  sdAtFull (armTFull A R G P hL) (List Bool) (threeProtocolsFromDryRunAtFullSize A R G).annT (armWFull A R G P hL) .test
    (cfgL Z.digest)
    (shapeBits recordGround.q.link.table.code.logN recordGround.q.link.table.code.ell
      recordGround.q.link.table.code.r recordGround.q.link.table.v
      recordGround.q.link.table.answers recordGround.q.link.table.saltBytes)
    (armQFull A R G P hL) (armQFull A R G P hL) (armDFull A R G P hL).code (armDFull A R G P hL).num
    fr_seed_fits (armDFull A R G P hL).dS

/-- What stands behind the root in a table's name: the digest, then the six words of the tables'
shape. -/
abbrev armRestFull : ByteArray :=
  TypedOracleCompiler.Run.FirstName.restOf Z.digest recordGround.q.link.table.code.logN
    recordGround.q.link.table.code.ell recordGround.q.link.table.code.r recordGround.q.link.table.v
    recordGround.q.link.table.answers recordGround.q.link.table.saltBytes

/-- The correspondence of the link's plain parts. -/
abbrev armPbFull :=
  pbSib (DG recordGround Z) (ckP .two) dsFull (sibLetters_full Z.digest).1
    (sibLetters_full Z.digest).2.1

/-- The total code behind the escape. -/
abbrev armBackFull :=
  backArmFull A R G P hL (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)) (Bd := List Bool)
    (DG recordGround Z) (earlyTwo (A := List T3 × List T3) (armDFull A R G P hL).d₁)
    (seedEntry recordGround.q.link.table.cubeBits recordGround.q.link.table.answers)
    (armPbFull Z) (Equiv.refl (List Bool)) sX
    (TypedOracleCompiler.Run.PQ.bodyS (DG recordGround Z).a (DG recordGround Z).base.plan.salt)
    (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)) _root_.Compile.serBits (140 + 1)

/-- **The arm's input**: `armSib`'s letters of data written, over the parameters. -/
def armWrittenFull : ArmIn :=
  armSib recordGround Z (C := ckP .two) (ds := dsFull) (a := frS.P.T.a) (xs := frD.xs)
    (dec2 := fun rr => decFullX (recX rr)) (armTFull A R G P hL) 140 (chalP .two 140)
    (aT := (threeProtocolsFromDryRunAtFullSize A R G).annT) (armDFull A R G P hL).wT
    (oneExt (armDFull A R G P hL).wB (armDFull A R G P hL).z) (armDFull A R G P hL).depthReq
    (armDFull A R G P hL).depthReqT 0 recordGround.q.given.plan.salt (armDFull A R G P hL).embT
    (armDFull A R G P hL).prjT (armDFull A R G P hL).embB (armDFull A R G P hL).prjB
    (armSFull A R G P hL Z)
    (armDFull A R G P hL).d₁ (digest_size Z) (armRestFull Z) (8 * recordGround.q.given.plan.salt)
    (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 (armQFull A R G P hL)
    (armQFull A R G P hL) (isP0Full A R G P hL _) (isP0Full A R G P hL _)
    (hp0Full A R G P hL _) (hp0Full A R G P hL _)
    (isPLAt (DG recordGround Z) (armDFull A R G P hL).d₁ (armL2Full A R G P hL) (armPbFull Z))
    (hpLAt (DG recordGround Z) (armDFull A R G P hL).d₁ (armL2Full A R G P hL) (armPbFull Z)) codeA
    codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (armBackFull A R G P hL Z sX)

/-- **The reading of the files there.** -/
def readWrittenFull : Reading5 (armWrittenFull A R G P hL Z sX).shape :=
  readSib recordGround Z (C := ckP .two) (ds := dsFull) (a := frS.P.T.a) (xs := frD.xs)
    (dec2 := fun rr => decFullX (recX rr)) (armTFull A R G P hL) 140 (chalP .two 140)
    (aT := (threeProtocolsFromDryRunAtFullSize A R G).annT) (armDFull A R G P hL).wT
    (oneExt (armDFull A R G P hL).wB (armDFull A R G P hL).z) (armDFull A R G P hL).depthReq
    (armDFull A R G P hL).depthReqT 0 recordGround.q.given.plan.salt (armDFull A R G P hL).embT
    (armDFull A R G P hL).prjT (armDFull A R G P hL).embB (armDFull A R G P hL).prjB
    (armSFull A R G P hL Z)
    (armDFull A R G P hL).d₁ (digest_size Z) (armRestFull Z) (8 * recordGround.q.given.plan.salt)
    (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 (armQFull A R G P hL)
    (armQFull A R G P hL) (isP0Full A R G P hL _) (isP0Full A R G P hL _)
    (hp0Full A R G P hL _) (hp0Full A R G P hL _)
    (isPLAt (DG recordGround Z) (armDFull A R G P hL).d₁ (armL2Full A R G P hL) (armPbFull Z))
    (hpLAt (DG recordGround Z) (armDFull A R G P hL).d₁ (armL2Full A R G P hL) (armPbFull Z)) codeA
    codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (armBackFull A R G P hL Z sX)
    (armStringFull (armTFull A R G P hL) Z.digest (decAt recordGround Z.digest))

/-- **The tie's three hypotheses for the entry file, at these values.** One hypothesis is left: Z's
parameter file says the ground's lines. -/
theorem entryPart_writtenFull (hZ : recordGround.SaysLines Z.pol) :
    EntryPart (armWrittenFull A R G P hL Z sX).shape (readWrittenFull A R G P hL Z sX) :=
  entryPart_sib recordGround Z (C := ckP .two) (ds := dsFull) (a := frS.P.T.a) (xs := frD.xs)
    (dec2 := fun rr => decFullX (recX rr)) (armTFull A R G P hL) 140 (chalP .two 140)
    (aT := (threeProtocolsFromDryRunAtFullSize A R G).annT) (armDFull A R G P hL).wT
    (oneExt (armDFull A R G P hL).wB (armDFull A R G P hL).z) (armDFull A R G P hL).depthReq
    (armDFull A R G P hL).depthReqT 0 recordGround.q.given.plan.salt (armDFull A R G P hL).embT
    (armDFull A R G P hL).prjT (armDFull A R G P hL).embB (armDFull A R G P hL).prjB
    (armSFull A R G P hL Z)
    (armDFull A R G P hL).d₁ (digest_size Z) (armRestFull Z) (8 * recordGround.q.given.plan.salt)
    (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 (armQFull A R G P hL)
    (armQFull A R G P hL) (isP0Full A R G P hL _) (isP0Full A R G P hL _)
    (hp0Full A R G P hL _) (hp0Full A R G P hL _)
    (isPLAt (DG recordGround Z) (armDFull A R G P hL).d₁ (armL2Full A R G P hL) (armPbFull Z))
    (hpLAt (DG recordGround Z) (armDFull A R G P hL).d₁ (armL2Full A R G P hL) (armPbFull Z)) codeA
    codeA_inj
    (fun a a' => (codeA_length a).trans (codeA_length a').symm) (armBackFull A R G P hL Z sX)
    (armStringFull (armTFull A R G P hL) Z.digest (decAt recordGround Z.digest))
    record_answers record_field hZ armFacts_full (sibLetters_full Z.digest).2.2.1
    (sibLetters_full Z.digest).2.2.2 (sibK_full Z.digest) (sibChal_full Z.digest)
    (sibSalt recordGround Z.digest) rfl
    (fun rr => (congrFun (decRun_full Z.digest) (recX rr)).symm) (strLaws_full _ Z)
    (fun x => wire_recSeedK recT recLg recS (140 + 1) fr_seed_fits x) (room_recSeedK fr_seed_fits)
    (by norm_num)

/-- **The same at every Z whose parameter file begins with the example's 32 lines**: no hypothesis
is left. lay, KL: the two other public files; more: what follows the 32 lines. -/
theorem entryPart_writtenFull_at (more lay KL : ByteArray) :
    EntryPart
      (armWrittenFull A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩
        sX).shape
      (readWrittenFull A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩
        sX) :=
  entryPart_writtenFull A R G P hL _ sX (full_says_of_prefix more)

end

end OnBytes.K.Arm
