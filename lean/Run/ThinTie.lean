-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinTie.lean: the evaluable form of the compiled verifier (`verifyP`, Run/ThinDefs.lean) at
`fun _ => L`, `L.early`, `L.late` is the run of `Compile.Batch.verifyOneProtocol` at `P.up` under the same
oracle functions. Statements (each a `Prop` in `Run.Thin.Spec`); the proofs are in
Run/ThinTieProofs.lean. Generic: no format, no hash, no toy.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The compiled verifier is the verifier of the non-interactive argument that the library's compiler
makes of an interactive oracle protocol: Merkle trees for the oracles, a hash chain for the
challenges (`Compile.Batch.verifyOneProtocol`); proof of work is tested where the protocol's `accept` tests
it. Run/ThinDefs.lean writes the compiled verifier again. It is written so that no function of that
file has a parameter of the type of a round, a shape, a protocol or the interface. Skeletons stand
in the place of rounds, shapes and protocols, and the interface stands behind a function of `Unit`,
`Lf`. This file and the Proofs file (a lemma for each helper but `sExtP`) state that at
`Lf := fun _ => L` the functions of Run/ThinDefs.lean are their namesakes. The namesakes are
functions of the library (Compile/Batch/Verifier.lean), of the analogue on the skeleton
(Run/TwinDefs.lean), or plain functions of Run/VerifyDet.lean, Run/TwinDet.lean.

Sources. The four files just named.

1. What the file contains. Five statements.
2. What is checked when the file compiles. Only the types.
3. Statements.
     `thin_chain`: `chainP (fun _ => L) g early late .. = chainTF g early late ..`
     `thin_strict`: `strictP .. = strictBT ..`
     `thin_after`: `afterP (fun _ => L) g .. = afterBOTF g ..`
     `thin_twin`: `verifyP (fun _ => L) g early late .. = verifyTF g early late ..`
     `thin_verify`:
       `verifyP (fun _ => L) g L.early L.late sMT sFS t P .. = (verifyOneProtocol sMT sFS t P.up ..).det g`.
       It has no hypothesis beside whatever its arguments hold as proofs.
   Where `verifyOneProtocol` stands: the verifier of the scheme of Compile/Batch/Star.lean runs `vTS`, `vLS`,
   `vBS` on its three argument strings, and each of these is `verifyOneProtocol` at its data
   (Compile/Batch/Verifier.lean); this is by reading these terms, not by a theorem. Which scheme a
   given top theorem is about has to be read at that theorem; a scheme whose verifier runs another
   function (the format with pruned strings: `verifyBO`) is not reached by this file.
4. What is not claimed. No statement on soundness follows: these are equations between ways of
   computing one truth value. The values agree; the number of calls of g need not. That an evaluator
   does not build the lists of verifier messages at `verifyP` is a fact about a compiler and no
   theorem: not shown here, and not tried here. A test stands in Run/ThinGuard.lean: three runs of
   `verifyP` by the evaluator at a toy of its own with one round of 2^192 verifier messages, with a
   stub in the place of a hash. That a given protocol is `P.up` for a skeleton P, and a given wiring
   a wiring of `P.up`, has to be shown by whoever runs (for rounds written in the usual way it holds
   by definition).

Terms: lean/GLOSSARY.md.
-/
import Run.ThinDefs
import Run.TwinDet

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

namespace Spec

def thin_chain : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (early : X → X)
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
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up)
      (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam),
    afterP (fun _ => L) g P wq embS embE depthReq cms x π ρ rts ph =
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph

def thin_twin : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyP (fun _ => L) g early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyTF g early late sMT sFS t P wq embS embP xin embE depthReq cms x π

/-- States: `verifyP` at `fun _ => L`, g, `L.early`, `L.late` and a skeleton P is the run under g of
`verifyOneProtocol` at `P.up`, at all arguments. -/
def thin_verify : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyP (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

end Spec
end Run.Thin
