-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParsePaOLax.lean: the lenient parser of a proof file as a tree of queries; and the parser alone
that is made of it.

A tree of queries is a term of `ZKCP.OComp` (ZKCP/Defs.lean): an algorithm with access to a random
oracle, written as a tree of queries and coin tosses. `c.run f` is its output distribution at the
oracle f (the definition's run); `c.det f` is its result at f with every coin toss read as 0
(Run/OCompM.lean).

The lenient parser's tree tosses no coin, asks at most twice the description's number (`laxN`), and
its run at an oracle is the point mass at what the same text computes as a function. One definition,
statements (each a `Prop` in `Run.Spec`) and proofs. The proofs are corollaries; no induction on a
rule of the format is made here. Everything is generic in the protocol. It is the counterpart of
Run/ParsePaO.lean, which has the same for the strict parser. Many statements of this library are
written twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same
name outside that namespace proves it (lean/GLOSSARY.md).

It uses, among others, Run/ParseLax.lean (`parseLaxW`: it cuts the file and leaves the tests of
work, the leaves and the walks to the typed verifier; proof of work is tested where the protocol's
`accept` tests it (`Q.loc.accept`); what the lenient reader still asks the hash, what it refuses and
what it does not test: part 1 of the head of Run/ParseLax.lean), Run/CostLax.lean (its count
`laxN S`, with no term for openings), Run/TransportOV.lean (a parser alone, `PaO`).

1. What the file contains.
   `paOfLax spec T N hN`: a parser alone. Key: the list that the typed verifier takes.
     `parse` := the lenient parser's tree, refused unless its own list is the key
       (Run/ParsePaO.lean: `keep`).
     `t` := N · 2 for any N that bounds `laxN (spec x)` at all x.

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems.
   `paL_tie`: `(parseLaxW hT S T b).det f = parseLaxW (m := Id) (hI f) S T b`.
   `paL_parse`: no coin; at most `laxN S` · 2 queries.
   `paL_run`: `(parseLaxW hT S T b).run f` = the point mass at `parseLaxW (m := Id) (hI f) S T b`.
   `paL_of_run`: what the parser of `paOfLax` gives at an oracle.
   So, with `paO_binding` (Run/TransportOV.lean), index binding is carried over from a scheme A to
   byte strings: if A has index binding with bound ε, for a blind extractor, then every scheme on
   byte strings whose verifier is "(paOfLax ..).V A" has index binding with the bound
   ε(t_C, t_P + 2 N).

Notation:
  `hT`: the hash in the monad of trees of queries (Run/TieRules.lean);
  `hI f`: the hash over the oracle `f` as a function on byte strings (Run/TieRules.lean);
  `oB f`: the oracle `f` as a function on byte strings (Run/OCompM.lean);
  `keep`: the argument string, if the parser's own list is the key (Run/ParsePaO.lean);
  `S`: a description (`Fmt.Spec`, Fmt/Rules8.lean), the data under which a file is read;
  `T`: what the protocol `Q` supplies to the parser (`Typing`, Run/ParseChain.lean);
  `b`: the file, as bytes;
  t_C, t_P: the numbers of queries allowed to the adversary's committer and prover
    (`HasIndexBindingWith`, ZKCP/Defs.lean).

4. What is not claimed. That a given run's verifier is `(paOfLax ..).V A` for a scheme A with a
   theorem: a run evaluates the function on the right of `paL_run` and then the typed verifier's
   run; no scheme A is named here. That `laxN` is sharp. Anything on a printer, completeness or
   privacy (see the head of Run/TransportOV.lean). That `oB f` at some f is the real hash.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParsePaO
import Run.HomLax
import Run.CostLax

set_option autoImplicit false

namespace Run
open ZKCP Iop Compile.Batch

namespace Spec

def paL_tie : Prop :=
  ∀ (f : Oracle 256) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseLaxW hT S T b).det f = parseLaxW (m := Id) (hI f) S T b

def paL_parse : Prop :=
  ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseLaxW hT S T b).NoCoin ∧ (parseLaxW hT S T b).QueryBound (laxN S * 2)

/-- States: the definition's run of the tree is what a program computes. -/
def paL_run : Prop :=
  ∀ (f : Oracle 256) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseLaxW hT S T b).run f = PMF.pure (parseLaxW (m := Id) (hI f) S T b)

end Spec

theorem paL_tie : Spec.paL_tie := by
  intro f Y E Q S T b
  rw [← detHom_app f]
  exact (Hom.parseLaxW (detHom f) hT S T b).trans
    (congrArg (fun h => parseLaxW (m := Id) h S T b) (detHom_on_HM f))

theorem paL_parse : Spec.paL_parse := fun _ _ _ S T b =>
  qp_out (parseLaxW hT S T b) (laxN S * 2) (CostP.parseLaxW (qp 256) hT 2 qp_HM S T b)

theorem paL_run : Spec.paL_run := fun f Y E Q S T b =>
  run_of f (parseLaxW hT S T b) (parseLaxW (m := Id) (hI f) S T b) (laxN S * 2)
    (paL_parse Y E Q S T b) (paL_tie f Y E Q S T b)

/-- The lenient parser that may stand in front of a verifier. -/
def paOfLax {X Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (spec : X → _root_.Fmt.Spec)
    (T : Typing Q) (N : ℕ) (hN : ∀ x, laxN (spec x) ≤ N) :
    PaO 256 (List (Dig 256)) X (OneProtocolProof 256 Q) ByteArray :=
  PaO.ofMap (fun x b => parseLaxW hT (spec x) T b) keep (fun x => laxN (spec x) * 2) (N * 2)
    (fun x => Nat.mul_le_mul_right 2 (hN x)) (fun x b => paL_parse Y E Q (spec x) T b)

/-- States what that parser gives at an oracle. -/
def Spec.paL_of_run : Prop :=
  ∀ (f : Oracle 256) (X Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E)
      (spec : X → _root_.Fmt.Spec) (T : Typing Q) (N : ℕ) (hN : ∀ x, laxN (spec x) ≤ N)
      (ivk : List (Dig 256)) (x : X) (b : ByteArray),
    ((paOfLax spec T N hN).parse ivk x b).run f =
      PMF.pure (keep ivk (parseLaxW (m := Id) (hI f) (spec x) T b))

theorem paL_of_run : Spec.paL_of_run := fun f _ Y E Q spec T N hN ivk x b =>
  PaO.ofMap_run (fun x b => parseLaxW hT (spec x) T b) keep (fun x => laxN (spec x) * 2) (N * 2)
    (fun x => Nat.mul_le_mul_right 2 (hN x)) (fun x b => paL_parse Y E Q (spec x) T b) f ivk x b
    (parseLaxW (m := Id) (hI f) (spec x) T b) (paL_run f Y E Q (spec x) T b)

end Run
