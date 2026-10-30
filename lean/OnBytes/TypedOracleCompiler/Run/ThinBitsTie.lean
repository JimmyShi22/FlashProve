-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
TWO: OnBytes/TypedOracleCompiler/Run/ThinBitsTie.lean: the library's file of the same name said again over the
sibling, as text: one statement, Spec.thin_bits: the sibling's verifyPB at (fun _ => L), L.early,
L.late is the run of the sibling's verifyOneProtocol under the same oracle functions. The proof:
OnBytes/TypedOracleCompiler/Run/ThinBitsTieProofs.lean. NOT SAID: what the library's head below reports as seen in
runs was seen of the library's functions.

Run/ThinBitsTie.lean: THE PLAIN VERIFIER WITH DIGESTS AS DATA IN ITS WALKS (Run/ThinBits.lean:
verifyPB) IS THE RUN, UNDER THE SAME ORACLE FUNCTIONS, OF THE COMPILED VERIFIER OF ONE SLOT
(Compile.Batch.verifyOneProtocol) AT THE SKELETON'S PROTOCOL. One statement (Run.Thin.Spec.thin_bits); the
proof is in Run/ThinBitsTieProofs.lean. Generic: no format, no hash, no toy.
THE CHAIN OF EQUATIONS THAT ENDS HERE, each link for all arguments and without a hypothesis:
   verifyPB Lf g .. = verifyP Lf g .. Run/ThinBits.lean (verifyPB_eq): the walks up the trees on
   lists of bits in the place of digests that are functions
   verifyP (fun _ => L) g L.early L.late .. = (verifyOneProtocol .. P.up ..).det g Run/ThinTie.lean
   (thin_verify): skeletons of rounds and the interface behind a function of Unit; no monad
   Spec.thin_bits     verifyPB (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE
                      depthReq cms x π = (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms
                      x π).det g
 WHY verifyPB. A digest of the library is a FUNCTION of the bit's number; a function that returns
 one is, in compiled code, a closure that does its work anew at every bit read, and in a walk up a
 tree that work multiplies from level to level (seen in other runs, not shown
 here: verifyP at depth 10 did not come back). With the digests of the walks as data each vertex
 is MEANT to be hashed once: counted so in other runs at small
 trees, with a trace in the oracle; a word on compiled code: NOT SHOWN HERE.
WHAT IS NOT SAID. All that the head of Run/ThinTie.lean leaves out: nothing on soundness; the values
agree, the number of calls of g need not; where verifyOneProtocol stands; that a given protocol is P.up. THAT
AN EVALUATOR RUNS verifyPB IN A GIVEN TIME, OR AT ALL, IS NO THEOREM AND IS NOT TRIED HERE.


Terms: lean/GLOSSARY.md.

-/
import Run.ThinBitsTie
import OnBytes.TypedOracleCompiler.Run.ThinBits
import OnBytes.TypedOracleCompiler.Run.ThinTie

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

/-- THE PLAIN VERIFIER WITH DIGESTS AS DATA IS THE RUN OF THE COMPILED VERIFIER. -/
def Spec.thin_bits : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyPB (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

end TypedOracleCompiler.Run.Thin
