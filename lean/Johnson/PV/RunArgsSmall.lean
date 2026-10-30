-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/RunArgsSmall.lean: FIVE SMALL VALUES THAT A RUN OF THE ONE SHEET HANDS TO m (PV.MSmall.mS
  | famS) AND TO linkF, AT THE SMALL SIZE. ALL READ THE THREE PUBLIC FILES ALONE (bkShout reads
  nothing). No «noncomputable».
  digestsOf pol lay KL   (c, the seven): c := Params.configurationDigest [pol, lay, KL]; the seven
    := the digests (Fmt.formatHash 169 0 1 Fmt.zero32) of par7 smallRecordGround pol KL lay c's strings: our
    front's cBytes | parBytes | moreBytes (Johnson/Top/Fire/Code/PvFront.lean), to the letter.
                         par7's order (Johnson/Top/PreThreePub.lean:54-61): the entry's · the proof
                           file's first | shared | second · the key file's one-time | shared |
                           second. DUE: seven: THE PRINT MUST SHOW THE NUMBER.
  pd3At m i              three of the seven from place i on (a place that is not there gives no
    byte): dP := pd3At m 1 · dK := pd3At m 4
  pdLOf m                the first of the seven as a digest: for linkFS
  spS pol KL             the request's two strings: the value of the statement's item «request»,
    then the request file's bytes: reqS's text at the request alone
    (Johnson/RunOne/Closed.lean:237-238).
                         THE ITEM IS MADE AT THE SECOND HASH FUNCTION, A FIXED FUNCTION (that
                           file's own head).
  bkShout                A NAMED STAND-IN FOR bk: returns no bit and writes «BK IS READ …» to the
    error stream whenever it is called: THE PRINT MUST SHOW THE COUNT.
WHAT HAS RUN: digestsOf | pd3At | bkShout: these very texts (as W4R.…, in RunAt.lean, a file that is
  not in this library) in a run of this project: 16 of 16 starts as written down before the run.
  spS: NOT IN THIS FORM (there: reqS at a pair of a request and a record).


-/
import Johnson.Top.PreThreePub
import Johnson.Flat.ItemOf
import Johnson.Flat.WordsBytes
import Johnson.Flat.ClaimsTrue
import Johnson.Flat.SmallAtFiles
import OnBytes.Maker.Page.WithPd
import OnBytes.TypedOracleCompiler.Run.CodingImpl

set_option autoImplicit false

namespace PV.RunArgs
open OnBytes OnBytes.Flat VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The public digests, of the three public files: (c, the seven). -/
def digestsOf (pol lay KL : ByteArray) : ByteArray × List ByteArray :=
  let c := OnBytes.Params.configurationDigest [pol, lay, KL]
  (c, (OnBytes.K.Arm.Pub.par7 OnBytes.Tie.smallRecordGround pol KL lay c).map fun b => Fmt.formatHash 169 0 1
      Fmt.zero32 b)

/-- Three of the seven, from place i on. -/
def pd3At (m : List ByteArray) (i : Nat) : OnBytes.Maker.Page.Pd3 :=
  ⟨m.getD i ByteArray.empty, m.getD (i + 1) ByteArray.empty, m.getD (i + 2) ByteArray.empty⟩

/-- The entry's chain's parameters' digest. -/
def pdLOf (m : List ByteArray) : Dig 256 := _root_.Run.bytesToDig (m.getD 0 ByteArray.empty)

/-- The request's two strings. -/
def spS (pol KL : ByteArray) (x : ReqAt sizesSmall) : ByteArray × ByteArray :=
  ((itemOf pol KL x.val).getD ByteArray.empty, requestBytesOf x.val)

/-- THE STAND-IN BEHIND THE ESCAPE: no bit; it shouts when it is called. -/
def bkShout {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (_ : AllPts 256 K L) : List Bool :=
  dbgTrace "  BK IS READ: a string behind the escape is hashed" fun _ => []

/-- THE SAME STAND-IN AS ONE CONSTANT, for the fast family's long form (famSL | famFL | famSP |
  famFP … e; m := … (fun _ => eShout ())): no bit; it shouts when it is read. -/
def eShout : Unit → List Bool := fun _ => dbgTrace
    "  BK IS READ: a string behind the escape is hashed" fun _ => []

end PV.RunArgs
