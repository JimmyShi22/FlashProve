-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedTypedTop.lean: at the string that the typing of a whole file makes
(OnBytes/Maker/TypeFile.lean, typeFile), with the two lists taken off the same file as read
(OnBytes/Maker/ListedTyped.lean, ownOfRead, listedOfRead), the verifier along lists
(OnBytes/Maker/ListedWhole.lean, verifyWholeL) is the compiled verifier of one slot
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, verifyOneProtocol) at the file's own wire record, as a tree of
queries.

No soundness: a test. This module states laws on what the runs of lean/Ask/ call; it states nothing
on soundness.

It joins verifyWholeL_eq (OnBytes/Maker/ListedWholeTop.lean) with listedOK_typeFile and
ext_listed_typeFile (OnBytes/Maker/ListedTypedLaws.lean), which pay its two premises.

Main theorem. verifyTyped_eq.

Limits. One premise is left: the typing has returned the string, at the same a, W and r of which the
two lists are made. The lists must be these two functions of that r, run in Lean: lists that a
parser hands over are free arguments, of which this file says nothing. Of a string that comes from
elsewhere nothing is said. That the typing returns at any file is not shown here
(OnBytes/Maker/TypeFileOfRead.lean has laws of that form). Letters that
describe one public quantity are not tied to each other here: saltBytes and sMT; path's length and
depthReq. The equation holds at all of them; the caller owes the tie. Likewise a and W are the
caller's letters: that they are the data of a description of which another theorem speaks is not
said here; taken from the file, they are what the file chose. Nothing on time or memory. Nothing on
soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWholeTop
import OnBytes.Maker.ListedTypedLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (a : ℕ) (W : Three.Whole) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- **At the typing's string the verifier along the lists off the file as read is the compiled
verifier.** -/
theorem verifyTyped_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C (WholeD.of a W) tF tJ t3).sh) →
      OSym (chainsOf C (WholeD.of a W) tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (saltBytes : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r = some π) :
    verifyWholeL C K chal (WholeD.of a W) tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq
        cms x π (ownOfRead a W r) (listedOfRead a W r) =
      verifyOneProtocol sMT sFS t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embS embP xin embE depthReq cms x
        π :=
  verifyWholeL_eq C K chal (WholeD.of a W) tF tJ t3 silent run sMT sFS t embS embP xin embE
    depthReq cms x π (ownOfRead a W r) (listedOfRead a W r)
    (listedOK_typeFile C K chal a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r π h)
    (ext_listed_typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r π h)

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyTyped_eq
