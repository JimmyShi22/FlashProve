-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsThinFam.lean: under the hypotheses of its statements, the definition's run of "the lenient
parser's tree, then the compiled verifier of one slot over the one oracle" is the point mass at the
value of plain functions. This is the same as Run/RunIsThin.lean, with the typed oracles in a form
made for the evaluator (`famM`): the family that gives each answer's blocks as bytes first.

One definition and two statements; the proofs are in Run/RunIsThinFamProofs.lean. A join: nothing
else is shown here. Generic in the protocol's data.

Run/RunIsThin.lean's right side evaluates the plain verifier at `readBlocks m (famOne f)`: the typed
oracles that the coding m reads out of the oracle f. Run/FamThin.lean has the same family in another
form, `famM (fun _ => L) K m O`, for the one oracle given as a function O from bit strings into
bytes, and the equation between the two (`famM_one`) as soon as f's answers are the digests of O's.

Main names:
  `famVerdict`: the plain verifier (`verifyP`) at the family that gives bytes first (`famM`).
  `Spec.run_fam`: `f s = bytesToDig (O s)` for all s ⇒ the run at f is the point mass at the value
    of `famVerdict` at O, on what the parser's text gives at `hI f` (the key compared; "the parser's
    text": the head of Run/RunIsV.lean). No further hypothesis but that N bounds the parser's count,
    beside whatever the arguments hold as proofs.
  `Spec.run_fam_page`: the same at this library's extension of the format's oracle to bit strings
  (the format's
    own is on byte strings; at the bits of a byte string whose first byte is not 4 the extension is
    the format's oracle at that string: `oBits_bytes`, Run/OracleBits.lean): f := `oBits ()`, O :=
    `oBy` (Run/OracleBits.lean, Run/FamThin.lean): no hypothesis but that N bounds the parser's
    count, beside whatever the arguments hold as proofs.

Limits: what the head of Run/RunIsThin.lean lists as not said is not said here either (no scheme, no
bound: a run tied to a term, not to a security statement; `famVerdict`, like `thinVerdict`, is a
term to state with: it takes the interface L as a value). The parser's side still has
`hI (oBits ())`: the hash over `oB (oBits ())`: that this is the format's hash `Fmt.formatHash` on the calls
that the parser makes is not shown here. This file does not say that the coding's own code runs
fast. For a run the head of Run/FamThin.lean names `famC` (Run/CodingThin.lean), not `famM`.

Terms: lean/GLOSSARY.md.
-/
import Run.RunIsThin
import Run.FamThin

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- the plain verifier at the family that gives bytes first, given what the parser gave -/
def famVerdict {I X : Type} {K : ℕ} (L : BatchProtocol I X) {Y : Type} {E : ExtSpec} (sMT sFS : ℕ) (t : Tag)
    (P : PS Y E) (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256)
    (O : List Bool → ByteArray) (ivk : List (Dig 256)) (x : Y) : Option (OneProtocolProof 256 P.up) → Bool
  | none => false
  | some π =>
    verifyP (fun _ => L) (famM (fun _ => L) K m O) L.early L.late sMT sFS t P wq embS embP
      xin embE depthReq ivk x π

namespace Spec

def run_fam : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256)
      (sp : Y → _root_.Fmt.Spec) (T : Typing P.up) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N)
      (f : ZKCP.Oracle 256) (O : List Bool → ByteArray) (ivk : List (Dig 256)) (x : Y)
      (b : ByteArray),
    (∀ s, f s = bytesToDig (O s)) →
    ((paOfLax sp T N hN).thenV
        (exitV m (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq)) ivk x b).run f =
      PMF.pure (famVerdict L sMT sFS t P wq embS embP xin embE depthReq m O ivk x
          (keep ivk (parseLaxW (m := Id) (hI f) (sp x) T b)))

/-- States `run_fam`, under the hypotheses below, at this library's extension of the format's
oracle to bit strings (`oBits`; where it is the format's oracle: `oBits_bytes`,
Run/OracleBits.lean). -/
def run_fam_page : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256)
      (sp : Y → _root_.Fmt.Spec) (T : Typing P.up) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N)
      (ivk : List (Dig 256)) (x : Y) (b : ByteArray),
    ((paOfLax sp T N hN).thenV
          (exitV m (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq)) ivk x b).run
        (oBits ()) =
      PMF.pure (famVerdict L sMT sFS t P wq embS embP xin embE depthReq m oBy ivk x
          (keep ivk (parseLaxW (m := Id) (hI (oBits ())) (sp x) T b)))

end Spec
end Run
