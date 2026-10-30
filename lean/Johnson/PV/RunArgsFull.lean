-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/RunArgsFull.lean: FIVE SMALL VALUES THAT A RUN OF THE ONE SHEET HANDS TO m (PV.MFull.mF |
  famF | famFL) AND TO linkF, AT THE FULL SIZE. ALL READ THE THREE PUBLIC FILES ALONE (bkShout reads
  nothing). IT IMPORTS FILES OF THE LIBRARY's BUILD ALONE. No «noncomputable».
  digestsOf pol lay KL   (c, the seven): c := Params.configurationDigest [pol, lay, KL]; the seven
    := the digests (Fmt.formatHash 169 0 1 Fmt.zero32) of par7 recordGround pol KL lay c's strings:
    cBytes | parBytes | moreBytes (Johnson/Top/Fire/Code/PvFront.lean), to the letter.
                         par7's order (Johnson/Top/PreThreePub.lean:54-61): the entry's · the proof
                           file's first | shared | second · the key file's one-time | shared |
                           second: seven in all.
  pd3At m i              three of the seven from place i on (a place that is not there gives no
    byte): dP := pd3At m 1 · dK := pd3At m 4
  pdLOf m                the first of the seven as a digest: for linkFF
  spF pol KL             the request's two strings: the value of the statement's item «request»,
    then the request file's bytes: the text of reqS, WHICH IS THE SMALL SIZE's
    (Johnson/RunOne/Closed.lean:237-238), at the request alone, typed at the full size's requests;
    the full size's own like is reqS z (Johnson/RunOne/ClosedZ.lean:
    no file of that name is in this library): the same two calls.
                         THE ITEM IS MADE AT THE SECOND HASH FUNCTION, A FIXED FUNCTION (that
                           file's own head).
  bkShout                A NAMED STAND-IN FOR bk: returns no bit and writes «BK IS READ …» to the
    error stream whenever it is called: THE PRINT MUST SHOW THE COUNT.
WHAT HAS RUN: NOT THESE AT THE FULL SIZE.
  MADE BY PROGRAM OF RunArgsSmall.lean:
  it is not held against that file's text as it stands here.


-/
import Johnson.Top.PreThreePub
import Johnson.Flat.ItemOf
import Johnson.Flat.WordsBytes
import Johnson.Flat.ClaimsTrue
import Johnson.Flat.ThreeAtFiles
import OnBytes.Maker.Page.WithPd
import OnBytes.TypedOracleCompiler.Run.CodingImpl

set_option autoImplicit false

namespace PV.RunArgsF
open OnBytes OnBytes.Flat VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The public digests, of the three public files: (c, the seven). -/
def digestsOf (pol lay KL : ByteArray) : ByteArray × List ByteArray :=
  let c := OnBytes.Params.configurationDigest [pol, lay, KL]
  (c, (OnBytes.K.Arm.Pub.par7 OnBytes.Tie.recordGround pol KL lay c).map fun b => Fmt.formatHash 169 0 1
      Fmt.zero32 b)

/-- Three of the seven, from place i on. -/
def pd3At (m : List ByteArray) (i : Nat) : OnBytes.Maker.Page.Pd3 :=
  ⟨m.getD i ByteArray.empty, m.getD (i + 1) ByteArray.empty, m.getD (i + 2) ByteArray.empty⟩

/-- The entry's chain's parameters' digest. -/
def pdLOf (m : List ByteArray) : Dig 256 := _root_.Run.bytesToDig (m.getD 0 ByteArray.empty)

/-- The request's two strings. ReqAt Inst.Model.ppref is Flat.Req by unfolding
  (AskSize.req_full := rfl, declared nowhere in this library). -/
def spF (pol KL : ByteArray) (x : ReqAt Inst.Model.ppref) : ByteArray × ByteArray :=
  ((itemOf pol KL x.val).getD ByteArray.empty, requestBytesOf x.val)

/-- THE STAND-IN BEHIND THE ESCAPE: no bit; it shouts when it is called. -/
def bkShout {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (_ : AllPts 256 K L) : List Bool :=
  dbgTrace "  BK IS READ: a string behind the escape is hashed" fun _ => []

/-- THE SAME STAND-IN AS ONE CONSTANT, for the fast family's long form (famSL | famFL | famSP |
  famFP … e; m := … (fun _ => eShout ())): no bit; it shouts when it is read. -/
def eShout : Unit → List Bool := fun _ => dbgTrace
    "  BK IS READ: a string behind the escape is hashed" fun _ => []

end PV.RunArgsF
