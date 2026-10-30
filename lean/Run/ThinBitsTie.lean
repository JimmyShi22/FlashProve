-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinBitsTie.lean: the plain verifier with digests as data in its walks (`verifyPB`,
Run/ThinBits.lean) at `fun _ => L`, `L.early`, `L.late` is the run, under the same oracle functions,
of the compiled verifier of one slot (`Compile.Batch.verifyOneProtocol`) at the skeleton's protocol.

One statement (`Run.Thin.Spec.thin_bits`); the proof is in Run/ThinBitsTieProofs.lean. Generic: no
format, no hash, no toy.
`verifyOneProtocol` (Compile/Batch/Verifier.lean) checks one argument string of a batch protocol and is
written as a tree of oracle queries (`OComp`); `OComp.det g` (Rom/Cache.lean) is the result of the
run under the oracle functions g in which every coin toss yields 0. `verifyPB` is a function without
a monad, made to be run by Lean's evaluator. A skeleton P (`PS`, Run/TwinDefs.lean) has the fields
of a batch protocol, with each round's instance `Fintype Chal` behind a function of `Unit`; `P.up`
is its protocol. (`L.early`: what of an instance is written into a chain's first query; `id`: the
whole; `BatchProtocol.early`, Iop/Batch.lean.) (`L.late`: the round into whose query the whole instance is
written; `none`: no such round; `BatchProtocol.late`, Iop/Batch.lean.)
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The chain of equations that ends here, each for all arguments and without a hypothesis beside
whatever the arguments hold as proofs:
  `verifyPB_eq` (Run/ThinBits.lean): `verifyPB Lf g .. = verifyP Lf g ..`.
  `thin_verify` (stated in Run/ThinTie.lean, proved in Run/ThinTieProofs.lean):
    `verifyP (fun _ => L) g L.early L.late .. = (verifyOneProtocol .. P.up ..).det g`: skeletons of rounds
    and the interface behind a function of `Unit`; no monad.

Why `verifyPB`: a digest of the library is a function of the bit's number. In compiled code a
function that returns one is a closure that does its work anew at every bit read. In a walk up a
tree that work multiplies from level to level. This was seen in other runs of this development:
`verifyP` at depth 10 did not come back. With the digests of the walks as data, each vertex is meant
to be hashed once. Other runs of this development, at small trees and with a trace in the oracle,
counted one hash for each vertex. What this paragraph says of compiled code, including that each
vertex is hashed once, is not shown here.

Notation:
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean);
  `t`: which compiled protocol: `test`, `link` or `onl` (`Tag`, Compile/Oracles.lean);
  `wq`: the wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean);
  `embS`, `embP`, `embE`: how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `xin`: a map; `xin x` is `recomputeChain`'s `x`, the whole instance (Compile/Batch/Verifier.lean);
  `depthReq`: depth of the request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `cms`: the external roots (`verifyB`, Compile/Batch/Verifier.lean).

Limits: what the head of Run/ThinTie.lean lists as not said is not said here either. (There: its
parts 3 and 4.) This file says nothing on soundness. The values agree; the number of calls of g need
not. It does not say where `verifyOneProtocol` stands, or that a given protocol is `P.up`. That an evaluator
runs `verifyPB` in a given time, or at all, is no theorem, and not tried here.

Terms: lean/GLOSSARY.md.
-/
import Run.ThinBits
import Run.ThinTie

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

/-- States: `verifyPB` at `fun _ => L`, g, `L.early`, `L.late` and a skeleton P is the run under g
of `verifyOneProtocol` at `P.up`, at all arguments. -/
def Spec.thin_bits : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L)) (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyPB (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

end Run.Thin
