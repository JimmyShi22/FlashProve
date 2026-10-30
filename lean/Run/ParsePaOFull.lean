-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParsePaOFull.lean: the parser that fills whole paths, as a tree of queries that may stand in
front of a verifier.

A tree of queries is a term of `ZKCP.OComp` (ZKCP/Defs.lean): an algorithm with access to a random
oracle, written as a tree of queries and coin tosses. `c.run f` is its output distribution at the
oracle f (the definition's run); `c.det f` is its result at f with every coin toss read as 0
(Run/OCompM.lean). The parser is `parseFullW` (Run/ParseFull.lean): from the bytes of a proof file
to two of the compiled verifier's typed inputs, with a whole Merkle path for each opened leaf.

A counterpart of Run/ParsePaOLax.lean (the lenient parser), for any protocol Q and typing T.

1. What the file contains.
    `paOfFull spec T N hN`: the parser in front of a verifier: refused unless its own list (the
      parameters' digest) is the key. t := N · 2 for any N ≥ `fileN (spec x)` at all x.

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems.
    `paF_tie`: the tree, run at an oracle f (`det`), is the function with f as the hash's oracle.
    `paF_parse`: the tree tosses no coin and asks at most `fileN S` · 2 questions (Run/CostFmt.lean:
      `fileN`: the strict reader's number: this parser hashes leaves and vertices).
    `paF_run`: the definition's run of the tree at f is the point mass at the function's value.
    `paF_of_run`: what `paOfFull` gives at an oracle.

4. What is not claimed. What the heads of Run/ParsePaO.lean and Run/ParsePaOLax.lean list as not
   claimed is not claimed here either. Above all it is not claimed that a given run's verifier is
   `(paOfFull ..).V A` for a scheme A with a theorem. That the parser's calls lie in the hash's
   domain is not in this file; under bounds that can be tested (`smallF`) the parser gives the same
   at two hashes that agree on that domain, the first with answers of the lengths that the rules
   give: Run/FullDom.lean (`full_dom`, `full_HO`).
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParsePaO
import Run.HomFull
import Run.CostFull

set_option autoImplicit false

namespace Run
open ZKCP Iop Compile.Batch

namespace Spec

def paF_tie : Prop :=
  ∀ (f : Oracle 256) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseFullW hT S T b).det f = parseFullW (m := Id) (hI f) S T b

def paF_parse : Prop :=
  ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseFullW hT S T b).NoCoin ∧ (parseFullW hT S T b).QueryBound (fileN S * 2)

/-- States: the definition's run of the tree is what a program computes. -/
def paF_run : Prop :=
  ∀ (f : Oracle 256) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseFullW hT S T b).run f = PMF.pure (parseFullW (m := Id) (hI f) S T b)

end Spec

theorem paF_tie : Spec.paF_tie := by
  intro f Y E Q S T b
  rw [← detHom_app f]
  exact (Hom.parseFullW (detHom f) hT S T b).trans
    (congrArg (fun h => parseFullW (m := Id) h S T b) (detHom_on_HM f))

theorem paF_parse : Spec.paF_parse := fun _ _ _ S T b =>
  qp_out (parseFullW hT S T b) (fileN S * 2) (CostP.parseFullW (qp 256) hT 2 qp_HM S T b)

theorem paF_run : Spec.paF_run := fun f Y E Q S T b =>
  run_of f (parseFullW hT S T b) (parseFullW (m := Id) (hI f) S T b) (fileN S * 2)
    (paF_parse Y E Q S T b) (paF_tie f Y E Q S T b)

/-- The parser that fills whole paths, in front of a verifier. -/
def paOfFull {X Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (spec : X → _root_.Fmt.Spec)
    (T : Typing Q) (N : ℕ) (hN : ∀ x, fileN (spec x) ≤ N) :
    PaO 256 (List (Dig 256)) X (OneProtocolProof 256 Q) ByteArray :=
  PaO.ofMap (fun x b => parseFullW hT (spec x) T b) keep (fun x => fileN (spec x) * 2) (N * 2)
    (fun x => Nat.mul_le_mul_right 2 (hN x)) (fun x b => paF_parse Y E Q (spec x) T b)

/-- States what that parser gives at an oracle. -/
def Spec.paF_of_run : Prop :=
  ∀ (f : Oracle 256) (X Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E)
      (spec : X → _root_.Fmt.Spec) (T : Typing Q) (N : ℕ) (hN : ∀ x, fileN (spec x) ≤ N)
      (ivk : List (Dig 256)) (x : X) (b : ByteArray),
    ((paOfFull spec T N hN).parse ivk x b).run f =
      PMF.pure (keep ivk (parseFullW (m := Id) (hI f) (spec x) T b))

theorem paF_of_run : Spec.paF_of_run := fun f _ Y E Q spec T N hN ivk x b =>
  PaO.ofMap_run (fun x b => parseFullW hT (spec x) T b) keep (fun x => fileN (spec x) * 2) (N * 2)
    (fun x => Nat.mul_le_mul_right 2 (hN x)) (fun x b => paF_parse Y E Q (spec x) T b) f ivk x b
    (parseFullW (m := Id) (hI f) (spec x) T b) (paF_run f Y E Q (spec x) T b)

end Run
