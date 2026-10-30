-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportOV.lean: binding reads the verifier alone: it is carried over, for a blind extractor
and with the parser's queries charged to the prover, to every scheme on strings whose verifier is
"parse, asking the oracle; refuse where that fails; else run V", whatever its committer and its
prover are.

Definitions, statements and proofs. Generic: no format occurs here. A scheme is an argument `Arg`
(ZKCP/Defs.lean) with its committer C, prover P and verifier V; binding is that file's
`HasIndexBindingWith`; a blind extractor: `Run.Blind` (Run/TransportO.lean).

Why: Run/TransportO.lean takes a way of writing with a printer, and its scheme on strings has the
prover "print what A's prover makes". A format need not be of that kind: where a file holds random
bytes and the typed proof holds only a hash of them, no function of the typed proof gives the file
back, and the format's prover is not "print after A's prover": it asks the oracle for a value that
A's prover draws. The experiment of index binding (ZKCP/Defs.lean: `bindingExp`) runs a cheating
committer, a cheating prover and V: it reads neither C nor P.

Main names:
  `PaO lam IVK X Pf B`: a parser alone: parse : key, instance, string ↦ a tree of queries with
    output "a proof, or none"; t : a bound on its queries. No printer.
  `p.V A`: the verifier on strings: run the parser; none: "false"; else A's V on what was parsed.
  `c.pa`: the parser of a way of writing with a printer (Run/TransportO.lean: `WrO`); (c.arg A).V
    is c.pa.V A, by definition.
  `Spec.binding_of_V`: two schemes with the same V (any committers, provers, types of secret keys)
    have index binding for the same extractor with the same bound.
  `Spec.paO_binding`: E blind (Run/TransportO.lean), binding of A for E with ε ⇒ every scheme A' on
    strings with A'.V = p.V A has binding for WrO.ext d E with ε'(t_C, t_P) = ε(t_C, t_P + p.t).

Limits. What is not said: completeness and privacy of such an A'. They read its prover. For "print
after A's prover": Run/TransportO.lean. For a prover that asks the oracle, at a fresh random
string, for a value that A's prover draws: nothing is stated or shown in Run/ or Fmt/. (One way in
which the two provers differ: the string may have been asked before, and then the answer is no
fresh value.) What lemma would be needed: for the compiled prover, at the place where it draws its
salt: a bound on what "draw a string, ask the oracle at it, take the answer for the salt" in the
place of "draw the salt" changes in completeness and in the distance of the two views, with a
simulator that also answers at the drawn strings. Expected, not shown: a term of the order (chains
with random bytes) · (all queries) / 2^λ (a session can have several such chains). The same holds
of every typed value whose first part is such an answer (a leaf's salt that begins with it): that
part is not drawn either. (Compare `Rom.Spec.defer`, Rom/Defer.lean, under the hypotheses of its
statement, for programs of the token language of that file; proved in Rom/DeferProof_tail.lean; no
other file of Run/ names it.)
-/
import Run.TransportOProofs
import Run.OCompM

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

/-- A parser alone. -/
structure PaO (lam : ℕ) (IVK X Pf B : Type) where
  parse : IVK → X → B → OComp lam (Option Pf)
  t     : ℕ
  bound : ∀ ivk x b, (parse ivk x b).QueryBound t

/-- The verifier on strings. -/
def PaO.V {lam : ℕ} {I X W IVK ISK Pf B : Type}
    (p : PaO lam IVK X Pf B) (A : Arg lam I X W IVK ISK Pf) : IVK → X → B → OComp lam Bool :=
  fun ivk x b => (p.parse ivk x b).bind (WrO.after A ivk x)

/-- The parser of a way of writing with a printer. -/
def WrO.pa {lam : ℕ} {IVK X Pf B : Type} (c : WrO lam IVK X Pf B) : PaO lam IVK X Pf B :=
  ⟨c.parse, c.t, c.bound⟩

namespace Spec

/-- States that binding reads V alone: if `A'.V = A.V`, binding of A for E with ε gives binding of
A' for E with ε. -/
def binding_of_V : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK ISK' Pf : Type) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (A' : Arg lam I X W IVK ISK' Pf)
      (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞),
    A'.V = A.V → HasIndexBindingWith R A E ε → HasIndexBindingWith R A' E ε

/-- States, for a blind E and under binding of A for E with ε: every scheme A' on strings with
`A'.V = p.V A` has binding for `WrO.ext d E`, the prover's queries counted as tP + p.t. -/
def paO_binding : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK ISK' Pf B : Type) (p : PaO lam IVK X Pf B) (d : Pf)
      (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf)
      (ε : ℕ → ℕ → ℝ≥0∞) (A' : Arg lam I X W IVK ISK' B),
    A'.V = p.V A → Blind E → HasIndexBindingWith R A E ε →
    HasIndexBindingWith R A' (WrO.ext d E) fun tC tP => ε tC (tP + p.t)

end Spec

theorem pa_V {lam : ℕ} {I X W IVK ISK Pf B : Type}
    (c : WrO lam IVK X Pf B) (A : Arg lam I X W IVK ISK Pf) : (c.arg A).V = c.pa.V A := rfl

theorem binding_of_V : Spec.binding_of_V := by
  intro lam I X W PP IVK ISK ISK' Pf R A A' E ε hV h tC tP St Ct Pt hC hP
  have e : bindingExp A' E Ct Pt = bindingExp A E Ct Pt := by
    unfold bindingExp
    rw [hV]
  rw [e]
  exact h tC tP St Ct Pt hC hP

theorem paO_binding : Spec.paO_binding := by
  intro lam I X W PP IVK ISK ISK' Pf B p d R A E ε A' hV hB h tC tP St Ct Pt hC hP
  -- a printer is needed only to name the scheme of Run/TransportO.lean; the cheating prover's tree,
  -- run at some oracle, supplies a string for it
  let b₀ : B := ((Pt (Ct.det fun _ _ => false).2).det fun _ _ => false).2
  exact binding_of_V lam I X W PP IVK ISK ISK' B R
    ((⟨p.parse, fun _ => b₀, p.t, p.bound⟩ : WrO lam IVK X Pf B).arg A) A' (WrO.ext d E) _ hV
    (wrO_binding lam I X W PP IVK ISK Pf B ⟨p.parse, fun _ => b₀, p.t, p.bound⟩ d R A E ε hB h)
    tC tP St Ct Pt hC hP

end Run
