-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ThinTie.lean.
Run/ThinTie.lean: the evaluable form of the compiled verifier (verifyP, Run/ThinDefs.lean) is the
run of Compile.Batch.verifyOneProtocol under the same oracle functions. Statements (Run.Thin.Spec.thin_*);
the proofs are in Run/ThinTieProofs.lean. Generic: no format, no hash, no toy.

The compiled verifier is the verifier of the non-interactive argument that the library's compiler
makes of an interactive oracle protocol: Merkle trees for the oracles, a hash chain for the
challenges, proof of work (Compile.Batch.verifyOneProtocol). Run/ThinDefs.lean writes it again so that no
function on the run's path has a parameter of the type of a round, a shape, a protocol or the
interface: skeletons stand in their place, and the interface stands behind a function of Unit, Lf.
Here it is stated that at Lf := fun _ => L each of its functions is its namesake: of the library
(Compile/Batch/Verifier.lean), of the twin on the skeleton (Run/TwinDefs.lean), or of the plain
functions of Run/VerifyDet.lean, Run/TwinDet.lean.

Sources.  The four files just named.

1. What the file contains.  Five statements.
2. What is checked when the file compiles.  Only the types.
3. Statements.
     thin_chain      chainP (fun _ => L) g early late .. = chainTF g early late ..
     thin_strict     strictP .. = strictBT ..
     thin_after      afterP (fun _ => L) g .. = afterBOTF g ..
     thin_twin       verifyP (fun _ => L) g early late .. = verifyTF g early late ..
     thin_verify     verifyP (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE
                     depthReq cms x π = (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms
                     x π).det g (with Run/TwinDet.lean: twd_verify). It has no hypothesis.
   The equations for the some twenty-five helpers stand in the Proofs file, one lemma each, by name
   (splitP_eq, .., trP_eq, .., runForestsP_eq ..).
   So what verifyP says on an argument string is what verifyOneProtocol says, under the same oracle
   functions. Where verifyOneProtocol stands: the verifier of the scheme of Compile/Batch/Star.lean runs vTS,
   vLS, vBS on its three argument strings, and each of these is verifyOneProtocol at its data (the last lines
   of Compile/Batch/Verifier.lean); this is read off these terms.
   Which scheme a given top theorem is about has to be read at that theorem; a scheme whose
   verifier runs another function (the format with pruned strings: verifyBO) is not reached by this
   file.
4. What is not claimed. NO STATEMENT ON SOUNDNESS FOLLOWS: these are equations between ways of
computing one truth value. The values agree; the number of calls of g need not. THAT AN EVALUATOR
DOES NOT BUILD THE LISTS OF VERIFIER MESSAGES AT verifyP is a fact about a compiler and no theorem:
NOT SHOWN HERE, AND NOT TRIED BY THE WRITER OF THIS FILE. A test stands in Run/ThinGuard.lean: three
runs of verifyP by the evaluator at a toy of its own with one round of 2^192 verifier messages, with
a stub in the place of a hash. That a given protocol is P.up for a skeleton P, and a given wiring a
wiring of P.up, has to be shown by whoever runs (for rounds written in the usual way it holds by
definition).

Terms: lean/GLOSSARY.md.

-/
import Run.ThinTie
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.TwinDet

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

namespace Spec

def thin_chain : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (early : X → X)
      (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
      (rtreq : Dig lam) (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
      (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains (up S)),
    chainP (fun _ => L) g early late t cms x salt rtreq S A W embP i ph rts pls =
      chainTF g early late t cms x salt rtreq S A W embP i ph rts pls

def thin_strict : Prop :=
  ∀ (lam K : ℕ) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (P : PS Y E)
      (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam P.up)
      (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam),
    strictP sMT sFS P wq depthReq x π ρ rts ph = strictBT sMT sFS P wq depthReq x π ρ rts ph

def thin_after : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up)
      (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam),
    afterP (fun _ => L) g P wq embS embE depthReq cms x π ρ rts ph =
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph

def thin_twin : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyP (fun _ => L) g early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyTF g early late sMT sFS t P wq embS embP xin embE depthReq cms x π

/-- THE PLAIN VERIFIER IS THE RUN OF THE COMPILED VERIFIER. -/
def thin_verify : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))
      (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyP (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

end Spec
end TypedOracleCompiler.Run.Thin
