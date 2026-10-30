-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsThin.lean: the definition's run of "the lenient parser's tree, then the compiled verifier
of one slot over the one oracle" is the point mass at the value of two plain functions, one after
the other: the parser's text in the identity monad, then the plain verifier.

One definition and one statement; the proof is in Run/RunIsThinProofs.lean. A join of two theorems;
nothing else is shown here. Generic in the protocol's data.

The definition's run of a tree of queries c at an oracle f is `c.run f` (ZKCP/Defs.lean): its output
distribution at f. The tree here (`thenV`, `exitV`), the coding m of typed queries into the one
oracle's strings and "the parser's text" are told in Run/RunIsV.lean. The plain verifier is
`verifyP` (Run/ThinDefs.lean), the compiled verifier's evaluable form: a plain function written for
an evaluator: no tree. (An evaluator: what runs the tests (`#guard`) when a file is compiled; not
the kernel.)

The two theorems: `run_verifyBS` (Run/RunIsVNoCoin.lean) and `thin_verify` (stated in
Run/ThinTie.lean, proved in Run/ThinTieProofs.lean), the second for a protocol given by its skeleton
(`P : PS Y E`, Run/TwinDefs.lean; the compiled verifier's protocol is `P.up`).

Main names:
  `thinVerdict`: the second of the two plain functions.
  `Spec.run_thin`: `((paOfLax sp T N hN).thenV (exitV m (verifyOneProtocol .. P.up ..)) ivk x b).run f` = the
    point mass at `thinVerdict .. f ivk x (keep ivk (parseLaxW (m := Id) (hI f) (sp x) T b))`. No
    hypothesis but that N bounds the parser's count, beside whatever the arguments hold as proofs.

Notation:
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean);
  `t`: which compiled protocol: `test`, `link` or `onl` (`Tag`, Compile/Oracles.lean);
  `wq`: the wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean);
  `embS`, `embP`, `embE`: how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `xin`: a map; `xin x` is `recomputeChain`'s `x`, the whole instance (Compile/Batch/Verifier.lean);
  `depthReq`: depth of the request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `ivk`: a list of digests, the key in `keep` (Run/ParsePaO.lean).

Limits: for whoever runs it: `thinVerdict` is a term to state with, not one to put under a guard (a
test, #guard). It takes the interface L as a value and reads `L.early`, `L.late` off it, and an
evaluator would build the interface. A run evaluates `verifyP` with these two written out (its
limits: part 4 of the head of Run/ThinDefs.lean). That this is the value of `thinVerdict` at a
closed description is then a matter of unfolding there: not shown here.
What the heads of Run/RunIsV.lean and Run/ThinTie.lean list as not said is not said here either.
Above all: no scheme, no bound. The compiled verifier of one slot, taken alone, belongs to no scheme
under a theorem. This ties a run to a term, not to a security statement.
This file does not say that the right side computes, or in what time: m is any coding,
`readBlocks m` asks all blocks of every typed answer. It does not say that f is the real hash, or
that a given protocol is `P.up`.

Terms: lean/GLOSSARY.md.
-/
import Run.RunIsVNoCoin
import Run.ThinTie

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- The second of the two plain functions: given what the parser gave. -/
def thinVerdict {I X : Type} {K : ℕ} (L : BatchProtocol I X) {Y : Type} {E : ExtSpec} (sMT sFS : ℕ) (t : Tag)
    (P : PS Y E) (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256) (f : ZKCP.Oracle 256)
    (ivk : List (Dig 256)) (x : Y) : Option (OneProtocolProof 256 P.up) → Bool
  | none => false
  | some π =>
    verifyP (fun _ => L) (readBlocks m (famOne f)) L.early L.late sMT sFS t P wq embS embP
      xin embE depthReq ivk x π

/-- States, under the hypotheses below: the definition's run is the point mass at the plain
functions' value. -/
def Spec.run_thin : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256)
      (sp : Y → _root_.Fmt.Spec) (T : Typing P.up) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N)
      (f : ZKCP.Oracle 256) (ivk : List (Dig 256)) (x : Y) (b : ByteArray),
    ((paOfLax sp T N hN).thenV
        (exitV m (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq)) ivk x b).run f =
      PMF.pure (thinVerdict L sMT sFS t P wq embS embP xin embE depthReq m f ivk x
          (keep ivk (parseLaxW (m := Id) (hI f) (sp x) T b)))

end Run
