-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParsePaO.lean: the parser of a proof file as a tree of queries: it tosses no coin, asks at most
twice the description's number (`fileN`), and its run at an oracle is the point mass at what the
same text computes as a function; and the parser that may stand in front of a verifier.

A tree of queries is a term of `ZKCP.OComp` (ZKCP/Defs.lean): an algorithm with access to a random
oracle, written as a tree whose inner nodes are queries or coin tosses. `c.run f` is its output
distribution at the oracle f; this file calls it the definition's run, since the definitions of
ZKCP/Defs.lean are stated with it. The parser (`parseW`, Run/ParseChain.lean) is written over a
variable monad and hash: at the hash `hT` (Run/TieRules.lean) it is such a tree, at `hI f` a plain
function.

Three definitions, tools for a variable tree, statements (each a `Prop` in `Run.Spec`) and proofs.
The proofs are corollaries; no induction on a rule of the format is made here. Everything is generic
in the protocol.

It uses, among others, Run/TransportOV.lean (`PaO`: a parser alone; `paO_binding`: binding is
carried over from a scheme A with verifier V and bound ε, for a blind extractor, to every scheme
whose verifier is "the parser's tree, then V", at ε(t_C, t_P + p.t)).

1. What the file contains.
   `paOf spec T N hN`: a parser alone (Run/TransportOV.lean), for a protocol Q with its typing T.
     Key: the list that the typed verifier takes. Instance x ↦ the data `spec x` of its chain.
     `parse` := the parser's tree, refused unless its own list is the key (`keep`).
     `t` := N · 2 for any N that bounds `fileN (spec x)` at all x.
   The parser's own list (the parameters' digest, recomputed from the data `spec x`) is compared
   with the key, and the file is refused where the two differ: a file never sets a public parameter.

2. What is checked when the file compiles.  Only the types and proofs.

3. Theorems.
   `pa_whole`: the reader of a whole file at `hT`: no coin; at most `fileN S` · 2 queries. (`fileN`,
     Run/CostFmt.lean: a function of the description alone; 2: a hash asks at most twice.)
   `pa_parse`: the same for the parser.
   `pa_run`: its doc comment tells it.
   `pa_of_run`: what the parser of `paOf` gives at an oracle.

4. What is not claimed. The lenient reader (Run/ParsePaOLax.lean). That `fileN` is sharp. Anything
   on a printer, completeness or privacy (see the head of Run/TransportOV.lean). That `oB f` at some
   f is the real hash.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.TieRules
import Run.CostFmtProofs
import Run.OCompCostP
import Run.TransportOV

set_option autoImplicit false

namespace Run
open ZKCP Iop Compile.Batch

namespace Spec

def pa_whole : Prop :=
  ∀ (S : _root_.Fmt.Spec) (b : ByteArray),
    (_root_.Fmt.wholeChain hT S b).NoCoin ∧ (_root_.Fmt.wholeChain hT S b).QueryBound (fileN S * 2)

def pa_parse : Prop :=
  ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseW hT S T b).NoCoin ∧ (parseW hT S T b).QueryBound (fileN S * 2)

/-- States: the definition's run of the tree is what a program computes with f as its hash's oracle.
-/
def pa_run : Prop :=
  ∀ (f : Oracle 256) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    (parseW hT S T b).run f = PMF.pure (parseW (m := Id) (hI f) S T b)

end Spec

/-! ### Tools, for a variable tree c

Why, as observed: every attempt in which a statement that begins with "no coin" or "asks at most" at
the reader itself was the type that a term was elaborated against, or from which a component was
projected, ran out of time in normalisation; every attempt in which the statements met at the reader
begin with "for all", "and" or "=" took seconds. A conjecture on the cause, not confirmed: the two
predicates unfold to a "for all" at a query, and Lean normalises an expected type to see whether it
is one, and so evaluates the whole reader. So: projections are made here, at a variable. -/

theorem qp_out {α : Type} (c : OComp 256 α) (t : ℕ) (h : (qp 256).le c t fun _ => True) :
    c.NoCoin ∧ c.QueryBound t := ⟨h.1, h.2.1⟩

theorem then_pure {α β : Type} (c : OComp 256 α) (g : α → β)
    (t : ℕ) (h : c.NoCoin ∧ c.QueryBound t) :
    (c >>= fun a => (Pure.pure (g a) : OComp 256 β)).NoCoin ∧
    (c >>= fun a => (Pure.pure (g a) : OComp 256 β)).QueryBound t :=
  ⟨OComp.NoCoin.bind' h.1 fun _ => trivial, OComp.QueryBound.mapO g c t h.2⟩

theorem run_of {α : Type} (f : Oracle 256) (c : OComp 256 α) (v : α) (t : ℕ)
    (h : c.NoCoin ∧ c.QueryBound t) (e : c.det f = v) : c.run f = PMF.pure v := by
  rw [OComp.run_of_noCoin f c h.1, e]

theorem mapO_le {α β : Type} (c : OComp 256 α) (g : α → β) (s t : ℕ)
    (hst : s ≤ t) (h : c.NoCoin ∧ c.QueryBound s) : (c.mapO g).QueryBound t :=
  OComp.QueryBound.mapO g c t (OComp.QueryBound.mono c s t hst h.2)

theorem run_mapO_of {α β : Type} (f : Oracle 256) (c : OComp 256 α) (g : α → β)
    (v : α) (e : c.run f = PMF.pure v) :
    (c.mapO g).run f = PMF.pure (g v) := by
  rw [OComp.run_mapO, e, PMF.pure_map]

/-- the parser is the fold, then the typed argument string: by definition -/
theorem parseW_eq {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (S : _root_.Fmt.Spec) (T : Typing Q) (b : ByteArray) :
    parseW h S T b = _root_.Fmt.wholeChain h S b >>= fun o => pure (o.bind (toBPrf T)) := rfl

theorem pa_whole : Spec.pa_whole := fun S b =>
  qp_out (_root_.Fmt.wholeChain hT S b) (fileN S * 2) (CostP.wholeChain (qp 256) hT 2 qp_HM S b)

theorem pa_parse : Spec.pa_parse := by
  intro Y E Q S T b
  rw [parseW_eq]
  exact then_pure (_root_.Fmt.wholeChain hT S b) (fun o => o.bind (toBPrf T))
    (fileN S * 2) (pa_whole S b)

theorem pa_run : Spec.pa_run := fun f Y E Q S T b =>
  run_of f (parseW hT S T b) (parseW (m := Id) (hI f) S T b) (fileN S * 2)
    (pa_parse Y E Q S T b) (tie_parseW f Y E Q S T b)

/-- what is kept of the parser's output: the argument string, if the parser's own list is the key -/
def keep {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (ivk : List (Dig 256))
    (o : Option (List (Dig 256) × OneProtocolProof 256 Q)) : Option (OneProtocolProof 256 Q) :=
  o.bind fun r => if r.1 = ivk then some r.2 else none

/-- A parser alone from a family of trees P and a map on their outputs: for variable P. -/
def PaO.ofMap {IVK X B α Pf : Type} (P : X → B → OComp 256 α) (g : IVK → α → Option Pf) (n : X → ℕ)
    (t : ℕ) (hn : ∀ x, n x ≤ t) (h : ∀ x b, (P x b).NoCoin ∧ (P x b).QueryBound (n x)) :
    PaO 256 IVK X Pf B :=
  ⟨fun ivk x b => (P x b).mapO (g ivk),
    t,
    fun ivk x b => mapO_le (P x b) (g ivk) (n x) t (hn x) (h x b)⟩

theorem PaO.ofMap_run {IVK X B α Pf : Type} (P : X → B → OComp 256 α) (g : IVK → α → Option Pf)
    (n : X → ℕ) (t : ℕ) (hn : ∀ x, n x ≤ t) (h : ∀ x b, (P x b).NoCoin ∧ (P x b).QueryBound (n x))
    (f : Oracle 256) (ivk : IVK) (x : X) (b : B) (v : α) (e : (P x b).run f = PMF.pure v) :
    ((PaO.ofMap P g n t hn h).parse ivk x b).run f = PMF.pure (g ivk v) :=
  run_mapO_of f (P x b) (g ivk) v e

/-- The parser that may stand in front of a verifier. -/
def paOf {X Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (spec : X → _root_.Fmt.Spec) (T : Typing Q)
    (N : ℕ) (hN : ∀ x, fileN (spec x) ≤ N) :
    PaO 256 (List (Dig 256)) X (OneProtocolProof 256 Q) ByteArray :=
  PaO.ofMap (fun x b => parseW hT (spec x) T b) keep (fun x => fileN (spec x) * 2) (N * 2)
    (fun x => Nat.mul_le_mul_right 2 (hN x)) (fun x b => pa_parse Y E Q (spec x) T b)

/-- States what that parser gives at an oracle. -/
def Spec.pa_of_run : Prop :=
  ∀ (f : Oracle 256) (X Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E)
      (spec : X → _root_.Fmt.Spec) (T : Typing Q) (N : ℕ) (hN : ∀ x, fileN (spec x) ≤ N)
      (ivk : List (Dig 256)) (x : X) (b : ByteArray),
    ((paOf spec T N hN).parse ivk x b).run f =
      PMF.pure (keep ivk (parseW (m := Id) (hI f) (spec x) T b))

theorem pa_of_run : Spec.pa_of_run := fun f _ Y E Q spec T N hN ivk x b =>
  PaO.ofMap_run (fun x b => parseW hT (spec x) T b) keep (fun x => fileN (spec x) * 2) (N * 2)
    (fun x => Nat.mul_le_mul_right 2 (hN x)) (fun x b => pa_parse Y E Q (spec x) T b) f ivk x b
    (parseW (m := Id) (hI f) (spec x) T b) (pa_run f Y E Q (spec x) T b)

end Run
