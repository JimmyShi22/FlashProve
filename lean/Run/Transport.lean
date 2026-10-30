-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Transport.lean: a scheme whose proofs are written as strings, with the verifier "parse; refuse
where that fails; else run V": the three properties are carried over with the same three bounds.

Definitions and statements; the proofs are in Run/TransportProofs.lean. Generic: no protocol, no
code, no hash, no format occurs here. A scheme is an argument `A : Arg lam I X W IVK ISK Pf`
(ZKCP/Defs.lean): an index committer C, a prover P and a verifier V, each an oracle computation.
The three properties are the three fields of `IsZKCPArgWith` in that file.

Why: the theorems on compiled schemes speak of a verifier V that is handed a proof as a typed
object (ZKCP/Defs.lean: Arg.V). A program is handed a file. Here: any type B of strings, a total
parser B → Option Pf, a printer Pf → B, and one law: what is printed parses back.

Main names:
  `Wr Pf B`: a way of writing: parse, print, back : parse (print π) = some π. Not asked: that parse
    is injective (two strings may be one proof); that print ∘ parse is the identity; that every
    string parses.
  `c.arg A`: the scheme on strings: C is A's; P prints what A's P makes; V, given a string: where
    it does not parse: "false", with no query and no coin; else A's V on what was parsed.
  `c.ext d E`: the extractor: the index extractor is E's; the witness extractor reads what was
    parsed (where nothing is parsed: a fixed proof d: V refuses there, so nothing hangs on it).
  `c.sim S`: the simulator: S's, with its proofs printed.
  `Spec.wr_V`: V on a printed proof is A's V on the proof, as a program; V on a string that does
    not parse is "false"; a bound on the queries of A's V holds for the new V.
  `Spec.wr_complete`, `wr_binding`, `wr_privacy`: the three clauses, each with the same bound.
  `Spec.wr_arg`: IsZKCPArgWith R A E S α ε ζ ⇒ IsZKCPArgWith R (c.arg A) (c.ext d E) (c.sim S) α ε
    ζ.

How (the proofs). Completeness: by the one law the experiment is the same program. Binding: a
cheating prover that puts out strings is one for A that parses its own output (d where that fails):
same queries, same trace; the two experiments differ only where the string does not parse, and
there the new V refuses, which is not the bad event. Privacy: both experiments are A's, for the
adversary and the environment that read printed proofs, with the proofs in the view printed at the
end; a function applied to both outputs does not raise the distance.

Limits: this file says nothing on a parser that asks the oracle (a format whose files hold no
lengths and no chain values): Run/TransportO.lean. It says nothing on keys and instances as
strings: only the proof is written here. It does not say that any given format is a `Wr`: that is
the format's files' matter. Since parse need not be injective, nothing here says that a proof has
one string: whoever alters a string may get another string of the same proof, which V accepts as
before.
-/
import ZKCP.KeyTag
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

/-- A way of writing proofs as strings. -/
structure Wr (Pf B : Type) where
  parse : B → Option Pf
  print : Pf → B
  back  : ∀ π, parse (print π) = some π

namespace Wr
variable {lam : ℕ} {I X W PP IVK ISK Pf B : Type} (c : Wr Pf B)

/-- The scheme on strings. -/
def arg (A : Arg lam I X W IVK ISK Pf) : Arg lam I X W IVK ISK B where
  C := A.C
  P := fun isk x w => (A.P isk x w).mapO c.print
  V := fun ivk x b => match c.parse b with
    | none => .pure false
    | some π => A.V ivk x π

/-- The extractor. -/
def ext (d : Pf) (E : Extractor lam I X W IVK Pf) : Extractor lam I X W IVK B :=
  ⟨E.Ei, fun ivk trC x b trP => E.Ew ivk trC x ((c.parse b).getD d) trP⟩

/-- The simulator. -/
def sim (S : Simulator lam PP IVK X Pf) : Simulator lam PP IVK X B where
  St := S.St
  init := S.init
  answer := S.answer
  prove := fun s x => (S.prove s x).map fun o => (c.print o.1, o.2)

end Wr

namespace Spec

/-- What the new V is. -/
def wr_V : Prop :=
  ∀ (lam : ℕ) (I X W IVK ISK Pf B : Type) (c : Wr Pf B) (A : Arg lam I X W IVK ISK Pf),
    (∀ ivk x π, (c.arg A).V ivk x (c.print π) = A.V ivk x π) ∧
    (∀ ivk x b, c.parse b = none → (c.arg A).V ivk x b = .pure false) ∧
    (∀ ivk x b π, c.parse b = some π → (c.arg A).V ivk x b = A.V ivk x π) ∧
    ∀ N : ℕ, (∀ ivk x π, (A.V ivk x π).QueryBound N) → ∀ ivk x b, ((c.arg A).V ivk x b).QueryBound N

def wr_complete : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : Wr Pf B) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (α : ℝ≥0∞),
    HasCompletenessError R A α → HasCompletenessError R (c.arg A) α

def wr_binding : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : Wr Pf B) (d : Pf) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞),
    HasIndexBindingWith R A E ε → HasIndexBindingWith R (c.arg A) (c.ext d E) ε

def wr_privacy : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : Wr Pf B) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞),
    HasStrongIndexPrivacyWith R A S ζ → HasStrongIndexPrivacyWith R (c.arg A) (c.sim S) ζ

/-- States: the three properties are carried over, with the same bounds. -/
def wr_arg : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf B : Type) (c : Wr Pf B) (d : Pf) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf)
      (S : Simulator lam PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    IsZKCPArgWith R A E S α ε ζ → IsZKCPArgWith R (c.arg A) (c.ext d E) (c.sim S) α ε ζ

end Spec
end Run
