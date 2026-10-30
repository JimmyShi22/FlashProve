-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParserHash.lean: at this library's extension of the format's oracle to bit strings, the hash
that the parser's text is given is the format's hash over the format's own oracle on byte strings;
so both sides of a run use that single oracle.

Trees of queries, their run and "the parser's text" are told in the head of Run/RunIsV.lean. Names
from other files: `hI` (Run/TieRules.lean), `oB` (Run/OCompM.lean), `oBy` (Run/FamThin.lean).

Why. Run/RunIsThinFam.lean's `run_fam_page` says what the definition's run of "the lenient parser's
tree, then the compiled verifier over a single oracle" is at the oracle `oBits ()`. On its right
side the verifier is evaluated at the typed oracle functions read out of the format's oracle
(`oBy`), but the parser's text still has `hI (oBits ()) = Fmt.HO (oB (oBits ()))`: the hash over
"the bits' oracle, asked at a byte string's bits, its answer as bytes". Here: that is
`Fmt.HO Fmt.oracle`.

How. `Fmt.HO` asks its oracle only at the strings `Fmt.oStr half ..` with the half 0 or 1. Such a
string's first byte is the half, so it is not the byte 4 by which this library's extension marks the
bit strings that are no byte strings, and the byte strings that begin with 4: at a byte string
whose first byte is not 4 the extension is the format's oracle (Run/OracleBits.lean: `oBits_bytes`).

1. What the file contains. Statements (each a `Prop` in `Run.Spec`); the proofs are in
   Run/ParserHashProofs.lean. Generic in the protocol's data.

2. What is checked when the file compiles.  Only the types.

3. Theorems stated.
   `ph_oStr`: `oB (oBits ()) (Fmt.oStr half n t i st bs) = Fmt.oracle (Fmt.oStr half n t i st bs)`,
     for the half 0 and the half 1.
   `ph_hI`: `hI (oBits ()) = Fmt.HO Fmt.oracle`, as functions. No hypothesis.
   `ph_run`: `run_fam_page` with the parser's text at `Fmt.HO Fmt.oracle`. No hypothesis but that N
     bounds the parser's count, beside whatever the arguments hold as proofs.

4. What is not claimed.
   That `Fmt.HO Fmt.oracle` is `Fmt.formatHash`. The two agree on the domain of the format's hash
   (Fmt/Rules23Laws.lean), and that every call of the parser lies in that domain is not shown in
   this file. So a run of which `ph_run` speaks evaluates the parser's text at `Fmt.HO Fmt.oracle`,
   not at `Fmt.formatHash`. Under four bounds on sizes that can be tested (`smallB`), the lenient parser
   gives the same at the two: Run/LaxDom.lean (`lax_dom`, `lax_HO`), proved in
   Run/LaxDomProofs.lean.
   What the heads of Run/RunIsThinFam.lean and Run/RunIsThin.lean list as not said is not said here
   either (no scheme, no bound: a run connected with a term, not with a security statement;
   `famVerdict` is a term to state with).

Terms: lean/GLOSSARY.md.
-/
import Run.RunIsThinFam
import Fmt.Rules23Laws

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

namespace Spec

def ph_oStr : Prop :=
  ∀ (half : UInt8) (n t i : Nat) (st bs : ByteArray), half = 0 ∨ half = 1 →
    oB (oBits ()) (_root_.Fmt.oStr half n t i st bs) =
      _root_.Fmt.oracle (_root_.Fmt.oStr half n t i st bs)

/-- States: at `oBits ()` the hash that the parser's text is given is the format's hash over the
format's oracle. -/
def ph_hI : Prop := hI (oBits ()) = _root_.Fmt.HO _root_.Fmt.oracle

/-- States `run_fam_page`, under the hypotheses below, with both sides of a run on the one oracle.
-/
def ph_run : Prop :=
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
          (keep ivk (parseLaxW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) (sp x) T b)))

end Spec
end Run
