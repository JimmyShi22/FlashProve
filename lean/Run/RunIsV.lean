-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsV.lean: under the hypotheses below, an evaluation by plain functions is the definition's
run of a verifier on strings: "parse with the hash as a function; refuse where that fails; else
evaluate the typed verifier at the typed oracles read out of the one oracle" is, at every oracle,
the definition's run of the tree "the parser's tree, then the typed verifier over the one oracle";
and that tree is the verifier on strings for the V in which the compiled theorems end.

Definitions and statements (each a `Prop` in `Run.Spec`); the proofs are in Run/RunIsVProofs.lean.
Generic: no protocol; no format but in the two statements on the lenient parser.

A tree of queries is a term of `ZKCP.OComp` (ZKCP/Defs.lean): an algorithm with access to a random
oracle, written as a tree of queries and coin tosses. `c.run f` is its output distribution at the
oracle f (the definition's run); `c.det f` is its result at f with every coin toss read as 0
(Run/OCompM.lean; for trees over typed oracles Rom/Cache.lean). The compiler's verifier asks several
typed oracles (a tree of `Rom.OComp S`); a coding `m : OracleCoding S lam` (Rom/Family.lean) turns each
typed query into queries to one random oracle on strings, one for each block of the typed answer.
The lenient parser `parseLaxW` (Run/ParseLax.lean: the lenient reader, then the step that types its
output) is written once, for any monad and any hash function into it; "the parser's text at h" is
that definition at the identity monad and h.

Main names:
  The two sides, for a bare typed verifier Vt : key, instance, typed proof ↦ a tree of queries to
  typed oracles, with a truth value.
  `exitV m Vt`: the tree.
  `p.thenV V'`: in front of it a parser alone p (`PaO`, Run/TransportOV.lean).
  `verdictV m Vt f ivk x v`: the function. v: what the parser gave ("a typed proof, or none"); none:
    false; a proof π: the typed verifier's result at the family of typed oracles that the coding
    reads out of f. No tree, no distribution.
  `exitOf m At`: for a whole scheme At with typed oracles: the form in which the compiled theorems
    end. `verdict m At`: the function at At.V.
  `Spec.run_draws`: "tosses no coin" of Run/OCompM.lean (`OComp.NoCoin`) holds of a tree if and only
    if ZKCP/Main.lean's `OComp.DrawsNoCoin` does.
  `Spec.run_bare`: Vt tosses no coin; the parser's run at f is the point mass at v ⇒
    `(p.thenV (exitV m Vt) ivk x b).run f` = the point mass at `verdictV m Vt f ivk x v`.
  `Spec.run_bare_lax`: the same at the lenient parser of a chain's file (Run/ParsePaOLax.lean:
    `paOfLax`), with v := what the parser's text gives at `hI f` (Run/TieRules.lean; the key
    compared): no hypothesis on the parser is left but that N bounds its count (`hN`).
  `Spec.run_exit_V`: what the V of `exitOf` and the verifier on strings are (by definition, and by
    cases on the parser's output).
  `Spec.run_isV`, `Spec.run_isV_lax`: the two statements at Vt := At.V, for `p.V (exitOf m At)`.

Why two forms: the bare form speaks of a typed verifier that belongs to no scheme (the function that
a compiler's verifier runs on each proof string, taken alone): it says that an evaluation is the
definition's run of a tree. The scheme's form joins with Run/TransportOV.lean's `paO_binding`: if
`exitOf m At` has index binding for a blind extractor with ε, every scheme on byte strings whose
verifier is `(paOfLax ..).V (exitOf m At)` has it with ε(t_C, t_P + 2 N), and by `run_isV_lax`, if
At.V tosses no coin, that verifier's answer at f is the value of `verdict`.

Limits: at the bare form: no scheme, no bound: Run/TransportOV.lean's `paO_binding` has nothing to
carry there. This file does not say that `verdictV` computes: m, Vt, At are any; where they stand
under "there are" (by choice) there is no program. It does not say that a given typed verifier
tosses no coin: a hypothesis. It does not say that f is the real hash: f is any oracle. The second
exit (only the needed blocks asked) and the typed oracles written directly from the format
(Run/CodingFn.lean: `famOf`; Run/CodingAgree.lean ties these two to each other): not this file's. It
says nothing on: completeness, privacy (head of Run/TransportOV.lean). It does not say that At is a
scheme under a theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.ParsePaOLax
import Run.DetOverOne
import ZKCP.SpecialAny
import ZKCP.Main
import Rom.NoCoinExits

set_option autoImplicit false

namespace Run
open ZKCP Rom

/-- A typed verifier over the one oracle: all blocks asked; as a tree of ZKCP/Defs.lean. -/
def exitV {S : OSpec} {lam : ℕ} {IVK X Pf : Type} (m : OracleCoding S lam)
    (Vt : IVK → X → Pf → Rom.OComp S Bool) :
    IVK → X → Pf → ZKCP.OComp lam Bool :=
  fun ivk x π => ofRom ((Vt ivk x π).overOne m)

/-- what is done with the parser's output -/
def afterV {lam : ℕ} {IVK X Pf : Type}
    (V' : IVK → X → Pf → ZKCP.OComp lam Bool) (ivk : IVK) (x : X) : Option Pf → ZKCP.OComp lam Bool
  | none => .pure false
  | some π => V' ivk x π

/-- The parser's tree, then a verifier. -/
def PaO.thenV {lam : ℕ} {IVK X Pf B : Type} (p : PaO lam IVK X Pf B)
    (V' : IVK → X → Pf → ZKCP.OComp lam Bool) :
    IVK → X → B → ZKCP.OComp lam Bool :=
  fun ivk x b => (p.parse ivk x b).bind (afterV V' ivk x)

/-- the oracle as the family with one member -/
def famOne {lam : ℕ} (f : Oracle lam) : Fam (rom lam) := fun _ => f

/-- The function, given what the parser gave. -/
def verdictV {S : OSpec} {lam : ℕ} {IVK X Pf : Type} (m : OracleCoding S lam)
    (Vt : IVK → X → Pf → Rom.OComp S Bool) (f : Oracle lam) (ivk : IVK) (x : X) : Option Pf → Bool
  | none => false
  | some π => (Vt ivk x π).det (readBlocks m (famOne f))

/-- The form in which the compiled theorems end: one oracle, all blocks asked, one request a call,
the syntax of ZKCP/Defs.lean. -/
def exitOf {S : OSpec} {lam : ℕ} {I X W IVK ISK Pf : Type}
    (m : OracleCoding S lam) (At : Gen.Arg S I X W IVK ISK Pf) : Arg lam I X W IVK ISK Pf :=
  SpecialAny.oneOf (schemeOverOneHashFunction m At)

/-- the function at a whole scheme's verifier -/
abbrev verdict {S : OSpec} {lam : ℕ} {I X W IVK ISK Pf : Type}
    (m : OracleCoding S lam) (At : Gen.Arg S I X W IVK ISK Pf) :
    Oracle lam → IVK → X → Option Pf → Bool := verdictV m At.V

namespace Spec

def run_draws : Prop := ∀ (lam : ℕ) (α : Type) (c : ZKCP.OComp lam α), c.NoCoin ↔ c.DrawsNoCoin

/-- States: if Vt tosses no coin and the parser's run at f is the point mass at v, the run of "the
parser's tree, then the typed verifier over the one oracle" is the point mass at the function's
value. -/
def run_bare : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (IVK X Pf B : Type) (m : OracleCoding S lam)
      (Vt : IVK → X → Pf → Rom.OComp S Bool) (p : PaO lam IVK X Pf B) (f : Oracle lam) (ivk : IVK)
      (x : X) (b : B) (v : Option Pf),
    (∀ ivk x π, (Vt ivk x π).NoCoin) → (p.parse ivk x b).run f = PMF.pure v →
    (p.thenV (exitV m Vt) ivk x b).run f = PMF.pure (verdictV m Vt f ivk x v)

open Iop Compile.Batch in
/-- States the same at the lenient parser of a chain's file, with no hypothesis on the parser but
that N bounds its count (`hN`). -/
def run_bare_lax : Prop :=
  ∀ (S : OSpec) (X Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (m : OracleCoding S 256)
      (Vt : List (Dig 256) → X → OneProtocolProof 256 Q → Rom.OComp S Bool) (spec : X → _root_.Fmt.Spec)
      (T : Typing Q) (N : ℕ) (hN : ∀ x, laxN (spec x) ≤ N) (f : Oracle 256) (ivk : List (Dig 256))
      (x : X) (b : ByteArray),
    (∀ ivk x π, (Vt ivk x π).NoCoin) →
    ((paOfLax spec T N hN).thenV (exitV m Vt) ivk x b).run f =
      PMF.pure (verdictV m Vt f ivk x (keep ivk (parseLaxW (m := Id) (hI f) (spec x) T b)))

def run_exit_V : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (I X W IVK ISK Pf B : Type) (m : OracleCoding S lam)
      (At : Gen.Arg S I X W IVK ISK Pf) (p : PaO lam IVK X Pf B),
    (exitOf m At).V = exitV m At.V ∧ p.V (exitOf m At) = p.thenV (exitV m At.V)

def run_isV : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (I X W IVK ISK Pf B : Type) (m : OracleCoding S lam)
      (At : Gen.Arg S I X W IVK ISK Pf) (p : PaO lam IVK X Pf B) (f : Oracle lam) (ivk : IVK)
      (x : X) (b : B) (v : Option Pf),
    (∀ ivk x π, (At.V ivk x π).NoCoin) → (p.parse ivk x b).run f = PMF.pure v →
    (p.V (exitOf m At) ivk x b).run f = PMF.pure (verdict m At f ivk x v)

open Iop Compile.Batch in
def run_isV_lax : Prop :=
  ∀ (S : OSpec) (I X W ISK Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (m : OracleCoding S 256)
      (At : Gen.Arg S I X W (List (Dig 256)) ISK (OneProtocolProof 256 Q)) (spec : X → _root_.Fmt.Spec)
      (T : Typing Q) (N : ℕ) (hN : ∀ x, laxN (spec x) ≤ N) (f : Oracle 256) (ivk : List (Dig 256))
      (x : X) (b : ByteArray),
    (∀ ivk x π, (At.V ivk x π).NoCoin) →
    ((paOfLax spec T N hN).V (exitOf m At) ivk x b).run f =
      PMF.pure (verdict m At f ivk x (keep ivk (parseLaxW (m := Id) (hI f) (spec x) T b)))

end Spec
end Run
