-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportO.lean: a scheme whose proofs are written as strings that can only be parsed with the
oracle's help, with the verifier "parse, asking the oracle; refuse where that fails; else run V":
what of the three properties is carried over, and at what price.

Definitions and statements; the proofs are in Run/TransportOProofs.lean. Generic: no protocol, no
code, no hash, no format occurs here. A scheme is an argument `A : Arg lam I X W IVK ISK Pf`
(ZKCP/Defs.lean): an index committer C, a prover P and a verifier V, each an oracle computation (a
tree of queries, `OComp`). The three properties are the three fields of `IsZKCPArgWith` in that
file. Many statements of this library are written twice: a definition in the namespace `Spec` states
a proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: Run/Transport.lean has the case of a parser that is a function of the string alone. A format
whose files hold no lengths and no chain values cannot be parsed so: how many bytes the next piece
has depends on what the oracle answered on the pieces before. The definition allows it: V is a tree
of queries (ZKCP/Defs.lean: `Arg.V`), so a parser that is such a tree may stand in front of V
inside V.

Main names:
  `WrO lam IVK X Pf B`: a way of writing: parse : key, instance, string ↦ a tree of queries with
    output "a proof, or none"; print : a function of the proof (to write, one drops lengths and
    chain values: no query); t : a bound on the parser's queries, on every string.
  `c.arg A`: the scheme on strings: C is A's; P prints what A's P makes; V, given a string: run the
    parser; where it gives none: "false"; else A's V on what was parsed.
  `Run.Blind E`: the witness extractor reads neither the proof nor the prover's trace (so: the key,
    the committer's trace and the instance alone).
  `WrO.ext d E`: the extractor on strings, for a blind E: E's two functions, the second at a fixed
    proof d and the empty trace. It does not parse.
  `c.sim S`: the simulator: S's, with its proofs printed.
  `c.Fair A`: at every oracle, key, instance and proof: the new V refuses the printed proof no more
    often than A's V refuses the proof.
  `c.Back A`: at every oracle: a proof that A's V accepts with positive chance comes back when it
    is printed and parsed. Not asked: that every proof comes back (one whose lengths do not fit the
    oracle's answers need not).
  `Spec.wrO_V`: the new V makes at most t more queries than A's.
  `Spec.wrO_fair`: c.Back A ⇒ c.Fair A.
  `Spec.wrO_complete`: under c.Fair A, completeness is carried over with the same bound.
  `Spec.wrO_binding`: E blind, binding of A for E with ε ⇒ binding of c.arg A for WrO.ext d E with
    ε'(t_C, t_P) = ε(t_C, t_P + t): the cheating prover is charged the parser's queries.
  `Spec.wrO_privacy`: privacy with the same bound (the clause does not read V; print asks nothing).
  `Spec.wrO_arg`: IsZKCPArgWith R A E S α ε ζ, E blind, c.Fair A ⇒ IsZKCPArgWith R (c.arg A)
    (WrO.ext d E) (c.sim S) α (fun tC tP => ε tC (tP + c.t)) ζ.

How (binding). A cheating prover that puts out strings is one for A that runs the parser on its own
output (it has the key from the cheating committer's state) and puts out what was parsed, d where
that fails: t more queries. Its trace is longer by the parser's queries, and its output is a typed
proof that the extractor on strings cannot know without the oracle's answers: an extractor is a
function of traces, it cannot ask. A blind extractor reads neither, so both experiments extract the
same. Where the string does not parse the new V refuses, which is not the bad event.

Notation:
  `lam`: the length in bits of the random oracle's answers (`Digest`, ZKCP/Defs.lean);
  `IVK`, `ISK`: the types of the verifier's key and of the prover's key (`Arg`, ZKCP/Defs.lean);
  `PP`: the type of `R.pp i` (`IndexedRelation`, ZKCP/Defs.lean);
  `B`: the type of the strings as which proofs are written;
  `α`, `ε`: the errors in `HasCompletenessError R A α`, `HasIndexBindingWith R A E ε`
    (ZKCP/Defs.lean);
  `tC`, `tP`, above t_C, t_P: the numbers of queries allowed to the adversary's committer and prover
    (`HasIndexBindingWith`);
  `ζ`: the last argument of `IsZKCPArgWith` (ZKCP/Defs.lean).

Limits: this file says nothing on index binding for an extractor that reads the proof or the
prover's trace: there the extractor on strings would have to parse with answers looked up in the two
traces, and the event "the parser asks a point that the adversary never asked" would have to be
bounded: not done. It does not say that a given extractor is blind, that a given format is a `WrO`,
fair or with c.Back. A blind extractor: Run/TransportOBlind.lean. This file says nothing on keys and
instances as strings. It says nothing on a printer that asks the oracle. Nothing says that a proof
has one string, or a string one proof at all oracles.
This file does not say that a given format's own prover is "print after A's prover". Where a file
holds random bytes of which the typed proof holds only a hash, there is no printer at all, and the
format's prover asks the oracle for a value that A's prover draws. Then wrO_complete and
wrO_privacy say nothing of that format's scheme. Binding does not read the prover and is carried
over all the same, for a blind extractor and with the parser's queries charged to the prover:
Run/TransportOV.lean, whose head says what lemma completeness and privacy would need.
-/
import ZKCP.KeyTag
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

/-- A way of writing proofs as strings that are parsed with the oracle's help. -/
structure WrO (lam : ℕ) (IVK X Pf B : Type) where
  parse : IVK → X → B → OComp lam (Option Pf)
  print : Pf → B
  t     : ℕ
  bound : ∀ ivk x b, (parse ivk x b).QueryBound t

/-- The witness extractor reads neither the proof nor the prover's trace. -/
def Blind {lam : ℕ} {I X W IVK Pf : Type} (E : Extractor lam I X W IVK Pf) : Prop :=
  ∀ ivk trC x π π' tr tr', E.Ew ivk trC x π tr = E.Ew ivk trC x π' tr'

namespace WrO
variable {lam : ℕ} {I X W PP IVK ISK Pf B : Type}

/-- What V does with the parser's output. -/
def after (A : Arg lam I X W IVK ISK Pf) (ivk : IVK) (x : X) : Option Pf → OComp lam Bool
  | none => .pure false
  | some π => A.V ivk x π

/-- The extractor on strings, for a blind extractor: it does not parse. -/
def ext (d : Pf) (E : Extractor lam I X W IVK Pf) : Extractor lam I X W IVK B :=
  ⟨E.Ei, fun ivk trC x _ _ => E.Ew ivk trC x d []⟩

variable (c : WrO lam IVK X Pf B)

/-- The scheme on strings. -/
def arg (A : Arg lam I X W IVK ISK Pf) : Arg lam I X W IVK ISK B where
  C := A.C
  P := fun isk x w => (A.P isk x w).mapO c.print
  V := fun ivk x b => (c.parse ivk x b).bind (after A ivk x)

/-- The simulator. -/
def sim (S : Simulator lam PP IVK X Pf) : Simulator lam PP IVK X B where
  St := S.St
  init := S.init
  answer := S.answer
  prove := fun s x => (S.prove s x).map fun o => (c.print o.1, o.2)

/-- The new V refuses a printed proof no more often than A's V refuses the proof, at every
oracle. -/
def Fair (A : Arg lam I X W IVK ISK Pf) : Prop :=
  ∀ (f : Oracle lam) ivk x π, prob (((c.arg A).V ivk x (c.print π)).run f) {b | b = false} ≤
    prob ((A.V ivk x π).run f) {b | b = false}

/-- A proof that A's V accepts with positive chance comes back, at every oracle. -/
def Back (A : Arg lam I X W IVK ISK Pf) : Prop :=
  ∀ (f : Oracle lam) ivk x π,
    true ∈ ((A.V ivk x π).run f).support → (c.parse ivk x (c.print π)).run f = PMF.pure (some π)

end WrO

namespace Spec

def wrO_V : Prop :=
  ∀ (lam : ℕ) (I X W IVK ISK Pf B : Type) (c : WrO lam IVK X Pf B)
      (A : Arg lam I X W IVK ISK Pf) (N : ℕ),
    (∀ ivk x π, (A.V ivk x π).QueryBound N) → ∀ ivk x b, ((c.arg A).V ivk x b).QueryBound (c.t + N)

def wrO_fair : Prop :=
  ∀ (lam : ℕ) (I X W IVK ISK Pf B : Type) (c : WrO lam IVK X Pf B) (A : Arg lam I X W IVK ISK Pf),
    c.Back A → c.Fair A

def wrO_complete : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : WrO lam IVK X Pf B) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (α : ℝ≥0∞),
    c.Fair A → HasCompletenessError R A α → HasCompletenessError R (c.arg A) α

/-- States, for a blind E and under binding of A for E with ε: `c.arg A` has binding for
`WrO.ext d E`; the cheating prover is charged the parser's queries. -/
def wrO_binding : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : WrO lam IVK X Pf B) (d : Pf)
      (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
      (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞),
    Blind E → HasIndexBindingWith R A E ε →
    HasIndexBindingWith R (c.arg A) (WrO.ext d E) fun tC tP => ε tC (tP + c.t)

def wrO_privacy : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : WrO lam IVK X Pf B) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞),
    HasStrongIndexPrivacyWith R A S ζ → HasStrongIndexPrivacyWith R (c.arg A) (c.sim S) ζ

/-- What is carried over. -/
def wrO_arg : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : WrO lam IVK X Pf B) (d : Pf)
      (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf)
      (S : Simulator lam PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    IsZKCPArgWith R A E S α ε ζ → Blind E → c.Fair A →
    IsZKCPArgWith R (c.arg A) (WrO.ext d E) (c.sim S) α (fun tC tP => ε tC (tP + c.t)) ζ

end Spec
end Run
