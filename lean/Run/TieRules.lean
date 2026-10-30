-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TieRules.lean: the reader of a chain's file and the parser, as trees of queries, run at an
oracle f, give what the same definitions give as functions with f. A chain: a hash chain: the
non-interactive form of one protocol, from which its verifier messages are drawn, as a file or a
stored table's record has it; between two rounds it has a label, a value and the number of rounds
done (`Chain`, Fmt/Rules5.lean).

Two statements (`Run.Spec.tie_wholeChain`, `Run.Spec.tie_parseW`) and their proofs. They are
corollaries: no induction on a rule of the format is made here. A tree of queries is an oracle
computation (`OComp`, ZKCP/Defs.lean); its run at f is `OComp.det` (Run/OCompM.lean): the result at
f, every coin toss yielding 0. Many statements of this library are written twice: a definition in
the namespace `Spec` states a proposition, and a theorem of the same name outside that namespace
proves it (lean/GLOSSARY.md).

Why: trees can be part of a verifier, functions are what a run evaluates; used in
Run/ParsePaO.lean.

How: "run at f" is a morphism of monads from trees of queries to the identity monad
(Run/OCompHom.lean). That file proves that it takes the hash "ask" to the hash over the function oB
f. Every morphism of monads passes through the functions of Fmt/Rules23.lean to Fmt/Rules8.lean
that are written over a variable monad, up to the strict reader. Run/HomFmt.lean states this and
Run/HomFmtProofs.lean proves it; the functions that are one call of the hash need no statement.

Main names:
  `hT`, `hI f`: see their doc comments. A call of `hT` makes one query, or two under the number
    162. (162: the number of a round's query; under it alone a digest has 64 bytes, not 32.)
  `Spec.tie_wholeChain`: (Fmt.wholeChain hT S b).det f = Fmt.wholeChain (m := Id) (hI f) S b.
  `Spec.tie_parseW`: the same for the parser `parseW` (Run/ParseChain.lean): the fold, then the
    typed argument string.

Notation:
  `Fmt.HM ask`: the format's hash by asking the one oracle, in any monad (Fmt/Rules23.lean);
  `Fmt.HO O`: the same over an oracle that is a function (Fmt/Rules23.lean);
  the five arguments of `hT`, `hI f`: `number`, `tree`, `index`, `start`, `bytes`, as `Fmt.HM` names
    them;
  `askB s`: one query, the byte string's bits, the answer as bytes (Run/OCompM.lean);
  `oB f`: the oracle `f` as a function on byte strings (Run/OCompM.lean);
  `S`: a description (`Fmt.Spec`, Fmt/Rules8.lean), the data under which a file is read;
  `T`: what the protocol `Q` supplies to the parser (`Typing`, Run/ParseChain.lean);
  `b`: the file, as bytes.

Limits: this file does not say that the trees toss no coin, or how many queries they make: that is
in another file, Run/ParsePaO.lean, which uses Run/CostFmt.lean. It does not say that oB f at some
f is the real hash.

Terms: lean/GLOSSARY.md.
-/
import Run.HomFmtProofs
import Run.OCompHom
import Run.ParseChain

set_option autoImplicit false

namespace Run
open ZKCP

/-- The hash in the monad of trees of queries. -/
abbrev hT : Nat → Nat → Nat → ByteArray → ByteArray → OComp 256 ByteArray := _root_.Fmt.HM askB

/-- The hash over the oracle f as a function on byte strings. -/
abbrev hI (f : Oracle 256) : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  _root_.Fmt.HO (oB f)

namespace Spec

def tie_wholeChain : Prop :=
  ∀ (f : Oracle 256) (S : _root_.Fmt.Spec) (b : ByteArray),
    (_root_.Fmt.wholeChain hT S b).det f = _root_.Fmt.wholeChain (m := Id) (hI f) S b

open Iop Compile.Batch in
def tie_parseW : Prop :=
  ∀ (f : Oracle 256) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseW hT S T b).det f = parseW (m := Id) (hI f) S T b

end Spec

theorem tie_wholeChain : Spec.tie_wholeChain := by
  intro f S b
  rw [← detHom_app f]
  exact (Hom.wholeChain (detHom f) hT S b).trans
    (congrArg (fun h => _root_.Fmt.wholeChain (m := Id) h S b) (detHom_on_HM f))

theorem tie_parseW : Spec.tie_parseW := by
  intro f Y E Q S T b
  show ((_root_.Fmt.wholeChain hT S b) >>=
      fun o => (Pure.pure (o.bind (toBPrf T)) : OComp 256 _)).det f = _
  rw [OComp.det_bind', OComp.det_pure', tie_wholeChain]
  rfl

end Run
