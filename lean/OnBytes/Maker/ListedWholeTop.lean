-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeTop.lean: at the description of a whole file the verifier along lists
(OnBytes/Maker/ListedWhole.lean, verifyWholeL) is the compiled verifier of one slot
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, verifyOneProtocol) at the file's own wire record
(OnBytes/Maker/Wire.lean, wqWhole), as a tree of queries, wherever the two lists own and listed hold
every place at which an opening of the argument string stands.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

It joins three things. verifyBSL_eq (OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifierLaws.lean): the
equation at a letter, under five premises. leavesOK_whole (OnBytes/Maker/ListedWholeLaws.lean): the
read leaves that ListedWhole.lean makes of the wants are those of the description's set of positions
read. rdEWhole_eq and mem_all_weOne (OnBytes/Maker/ListedWholeExt.lean): the like for the stored
table.

Main theorem. verifyWholeL_eq.

Limits. hO and hE, on the argument string and the two lists, stay premises here. They are no
formality: at empty lists verifyWholeL tests no opening's place or salt, whatever the string holds,
and verifyWholeL itself tests neither hO nor hE. So lists that an untrusted program hands over have
no equation by this file. OnBytes/Maker/ListedTypedTop.lean pays both at the string of the typing.
C, K, chal, D and the other letters are the caller's: that they are the data of a description of
which another theorem speaks is not said here. No oracle functions come in: the two sides are one
tree of queries. Nothing on time or memory. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifierLaws
import OnBytes.Maker.ListedWholeLaws
import OnBytes.Maker.ListedWholeExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The verifier of a whole file along the lists is the compiled verifier at the file's wire
record.** -/
theorem verifyWholeL_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos)
    (hO : ListedOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh π.opens own)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) :
    verifyWholeL C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed =
      verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π :=
  verifyBSL_eq (wholeDesc C D tF tJ t3 silent run).batch (wqWhole C K chal D tF tJ t3 silent run)
    sMT sFS depthReq x π own listed embS embE cms t embP xin
    (fun _ ρ _ => rdWhole C D tF tJ t3 ρ) (fun _ ρ => rdEWhole C D tF tJ t3 ρ) hO hE
    (mem_all_weOne D.a) (fun ρ pl => leavesOK_whole C K chal D tF tJ t3 silent run x ρ pl)
    (fun ρ => rdEWhole_eq C D tF tJ t3 silent run x ρ _ fun _ => decide_eq_true_iff)

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyWholeL_eq
