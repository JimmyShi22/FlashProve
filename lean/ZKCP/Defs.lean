-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/Defs.lean -- the notion of a doubly zero-knowledge commit-and-prove argument.

  Definitions that the library proves theorems about, in Lean 4, under headings by topic; other
  files cite them by their Lean names. Follows the
  work that this protocol builds on (lean/CREDITS.md, "Further work"), definition by definition.
  A doc comment that begins with "Helper" marks a declaration that only serves the others.
  This file contains definitions and one instance (for do-notation): no theorem, no sorry, no axiom.
  Where a definition can be read in more than one way, the comment at that place says which reading
  is taken. Not defined in this library: computational index privacy (it needs a notion of running
  time), and a well-formedness predicate beside the two optional additions of ZKCP/Optional.lean.

  Credit. The public Lean library VCV-io (https://github.com/Verified-zkEVM/VCV-io) also represents
  an algorithm with oracle access as a tree of queries. OComp in this file is such a tree for the
  one oracle of this file; the general form is in Rom/OComp.lean. A comparison with VCV-io's
  source at commit afa6593f found, in its own words: "the coin node draws from n + 1 values, as
  VCV-io's uniform-selection oracle does (VCVio/OracleComp/OracleSpec.lean). A single natural
  convention." VCV-io is not a
  dependency: no file of this library imports it.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

/-! ## The random oracle model -/

/-- {0,1}^*: finite bit strings, the domain of the random oracle. -/
abbrev Str : Type := List Bool

/-- {0,1}^λ: bit strings of length exactly lam, the range of the random oracle. -/
abbrev Digest (lam : ℕ) : Type := Fin lam → Bool

/-- A whole function f : {0,1}^* → {0,1}^λ. -/
abbrev Oracle (lam : ℕ) : Type := Str → Digest lam

/-- U(λ), the uniform distribution on functions {0,1}^* → {0,1}^λ.
The domain is infinite, so this is a probability *measure* and not a finite distribution: it is
the product, over all strings q, of the uniform distribution on {0,1}^λ (every value f(q) is
uniform and all values are independent).  Lemmas.lean, U_cylinder, proves the property that
characterises it: for distinct q_1..q_n, Pr[f(q_1)=v_1 ∧ .. ∧ f(q_n)=v_n] = (2^λ)^(-n).
(λ is a keyword of Lean, so the file writes lam.) -/
def U (lam : ℕ) : Measure (Oracle lam) :=
  Measure.infinitePi fun _ : Str => (PMF.uniformOfFintype (Digest lam)).toMeasure

/-- Algorithms that may query f.  An oracle algorithm with private
coins and output in α, on a fixed input, is a finite-depth decision tree.  It either
* pure a     : halts with output a,
* query q k  : asks the oracle for f(q) and continues as k (f q), or
* sample n k : draws r uniformly from {0,..,n} with private coins and continues as k r
               (sample 1 is one fair coin flip).
There is no bound on running time: the next step is an arbitrary function of what was seen.
The tree is finite: for C, P and V this excludes rejection sampling and retry loops without a cap.
The simulator (`Simulator`), in contrast, may use any discrete distribution. -/
inductive OComp (lam : ℕ) (α : Type) : Type
  | pure (a : α) : OComp lam α
  | query (q : Str) (k : Digest lam → OComp lam α) : OComp lam α
  | sample (n : ℕ) (k : Fin (n + 1) → OComp lam α) : OComp lam α

namespace OComp
variable {lam : ℕ} {α β : Type}

/-- Helper.  Sequential composition: run c, then run g on its output. -/
def bind : OComp lam α → (α → OComp lam β) → OComp lam β
  | pure a, g => g a
  | query q k, g => query q fun r => (k r).bind g
  | sample n k, g => sample n fun r => (k r).bind g

/-- Helper.  This instance only provides the do-notation used in the experiments below. -/
instance : Monad (OComp lam) where
  pure := OComp.pure
  bind := OComp.bind

/-- Helper.  The output distribution of c^f for a fixed f: the probability is over c's private
coins only.  PMF α is Mathlib's type of discrete probability distributions on α. -/
def run (f : Oracle lam) : OComp lam α → PMF α
  | pure a => PMF.pure a
  | query q k => (k (f q)).run f
  | sample n k => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).run f

/-- A bound of t queries, on every path of the tree.  (This
includes paths that no oracle produces, on which a repeated query is answered differently; pruning
them changes no behaviour, so no adversary is lost.)  Repeated queries are counted every time.
Where an adversary takes a state isk~ or a key ivk, the definitions below ask the bound for every
state and every key, reachable or not. -/
def QueryBound : OComp lam α → ℕ → Prop
  | pure _, _ => True
  | query _ _, 0 => False
  | query _ k, t + 1 => ∀ r, (k r).QueryBound t
  | sample _ k, t => ∀ r, (k r).QueryBound t

end OComp

/-- A trace, the list of pairs (q, f(q)) in the order asked. -/
abbrev Trace (lam : ℕ) : Type := List (Str × Digest lam)

/-- tr(A), the trace of an oracle algorithm A.
c.withTrace behaves exactly as c and outputs, beside c's output, tr(c). -/
def OComp.withTrace {lam : ℕ} {α : Type} : OComp lam α → OComp lam (α × Trace lam)
  | .pure a => .pure (a, [])
  | .query q k => .query q fun r => (k r).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)
  | .sample n k => .sample n fun r => (k r).withTrace

/-- Helper.  Pr[ a ∈ E | a ← p ] for a discrete distribution p; it equals Σ_{a ∈ E} p(a). -/
def prob {α : Type} (p : PMF α) (E : Set α) : ℝ≥0∞ := p.toOuterMeasure E

/-- Helper.  Pr[ a ∈ E | a ← c^f ] for a fixed f: the probability is over c's coins only. -/
def PrCoins {lam : ℕ} {α : Type} (f : Oracle lam) (c : OComp lam α) (E : Set α) :
    ℝ≥0∞ :=
  prob (c.run f) E

/-- Helper. Pr[ a ∈ E(f) | f ← U(λ); a ← c^f ]: the average over f ← U(λ) of the probability over
c's coins. Every displayed probability of completeness and binding, and every event probability
of View_Real in `HasIndexPrivacy`, has this form, the experiment being written as one oracle
computation c. The event may speak of the whole function f (`badKeys` needs that); `fun _ => T`
below means that the event T does not mention f. This is the only integral sign in the file. All
integrands that occur are measurable functions of f (Lemmas.lean, measurable_prob_run; for
`badKeys`, Open.lean, measurable_refined_integrand), so it is the ordinary integral. -/
def Pr {lam : ℕ} {α : Type} (c : OComp lam α) (E : Oracle lam → Set α) : ℝ≥0∞ :=
  ∫⁻ f, PrCoins f c (E f) ∂(U lam)

/-- Δ(X,Y), the statistical distance, in the form
Δ(X,Y) = sup over all events E of |Pr[X ∈ E] − Pr[Y ∈ E]|, which equals half the L1 distance for
probability distributions.  A distribution is given here by its
event probabilities.  (Subtraction in ℝ≥0∞ is truncated at 0, hence the max of both orders.) -/
def SD {α : Type} (X Y : Set α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ E : Set α, max (X E - Y E) (Y E - X E)

/-- An indexed relation R, a set of triples (i, x, w), in which each
index i has public parameters pp(i) that may be revealed (for example, the index's size).
Indices, instances, witnesses and public parameters are arbitrary types; so are keys and proofs
(Arg, below). -/
structure IndexedRelation (I X W PP : Type) where
  /-- (i, x, w) ∈ R -/
  rel : I → X → W → Prop
  /-- pp(i) -/
  pp : I → PP

/-- L(i) := {x : ∃ w, (i, x, w) ∈ R} and L(⊥) := ∅.  none is ⊥. -/
def IndexedRelation.L {I X W PP : Type} (R : IndexedRelation I X W PP) : Option I → Set X
  | some i => {x | ∃ w, R.rel i x w}
  | none => ∅

/-- Helper.  (i*, x, w) ∈ R for i* ∈ {indices} ∪ {⊥}; no triple with i* = ⊥ is in R.  (Our
convention; it changes nothing, because x ∉ L(⊥) already puts an accepted session into the event of
`HasIndexBinding`.) -/
def IndexedRelation.rel' {I X W PP : Type} (R : IndexedRelation I X W PP) : Option I → X → W → Prop
  | some i, x, w => R.rel i x w
  | none, _, _ => False

/-! ## Syntax -/

/-- An argument ARG = (C, P, V) of three oracle algorithms.
The prover keeps no state from one session to the next: P's only output is the proof, so
there is nothing through which one session could reach another except ivk, isk, f and the inputs x
and w. -/
structure Arg (lam : ℕ) (I X W IVK ISK Pf : Type) where
  /-- C^f(i) → (ivk, isk), the index committer. -/
  C : I → OComp lam (IVK × ISK)
  /-- P^f(isk, x, w) → π, the prover. -/
  P : ISK → X → W → OComp lam Pf
  /-- V^f(ivk, x, π) → {0,1}, the verifier; true is 1. V may flip coins. They count in every
  probability in which V runs, and in `badKeys` in the inner one.  For a V without coins
  nothing changes. -/
  V : IVK → X → Pf → OComp lam Bool

section Properties
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-! ## Completeness -/

/-- Helper. One honest session on a given key: π ← P^f(isk, x, w), then V's bit V^f(ivk, x, π).
-/
def sessionExp (ivk : IVK) (isk : ISK) (x : X) (w : W) : OComp lam Bool := do
  let π ← A.P isk x w
  A.V ivk x π

/-- The experiment of completeness: (ivk, isk) ← C^f(i); π ← P^f(isk, x, w), then V's bit. In this
experiment and in `bindingExp` V's run is a step of the experiment, and the event speaks
of its output bit; the formulas in the comments write V^f(...) inside the event. -/
def completenessExp (i : I) (x : X) (w : W) : OComp lam Bool := do
  let (ivk, isk) ← A.C i
  sessionExp A ivk isk x w

/-- Completeness error α.  For every (i, x, w) ∈ R,
Pr[ V^f(ivk, x, π) = 0 | f ← U(λ); (ivk, isk) ← C^f(i); π ← P^f(isk, x, w) ] ≤ α. -/
def HasCompletenessError (α : ℝ≥0∞) : Prop :=
  ∀ i x w, R.rel i x w → Pr (completenessExp A i x w) (fun _ => {b | b = false}) ≤ α

/-- Perfect completeness, that is, completeness error 0. -/
def IsPerfectlyComplete : Prop := HasCompletenessError R A 0

/-- The event of `HasRefinedCompletenessError`, the bad keys for a fixed f: the keys for which some
(x, w) with (i, x, w) ∈ R has Pr_{π ← P^f(isk,x,w)}[ V^f(ivk, x, π) = 0 ] > α_P.  Here f and the key
are fixed, and the chance is over P's coins alone (and over V's coins, if it has any).
The ∃ over (x, w) is part of the event: a single such pair makes the key bad. -/
def badKeys (αP : ℝ≥0∞) (i : I) (f : Oracle lam) : Set (IVK × ISK) :=
  {key | ∃ x w, R.rel i x w ∧ PrCoins f (sessionExp A key.1 key.2 x w) {b | b = false} > αP}

/-- Completeness error (α_C, α_P).  For every i, the probability
over f ← U(λ); (ivk, isk) ← C^f(i) that (ivk, isk) is a bad key is ≤ α_C.  (The event is
measurable whatever the sets of instances and witnesses are: Open.lean,
measurable_refined_integrand.) -/
def HasRefinedCompletenessError (αC αP : ℝ≥0∞) : Prop :=
  ∀ i, Pr (A.C i) (fun f => badKeys R A αP i f) ≤ αC

/-! ## Index binding -/

/-- A deterministic extractor E = (E_i, E_w): two functions.
i* := E_i(ivk, tr_C) sees the key and the committer's trace alone;
w := E_w(ivk, tr_C, x, π, tr_P). No bound on running time is asked, as in the work that this
protocol builds on (lean/CREDITS.md, "Further work"): the two functions are arbitrary.
The witness clause of `HasIndexBinding` is then empty (Basic.lean, indexBinding_iff_sound).
E_w always answers with a witness, so the set of witnesses must be non-empty: if it is empty (and
there is at least one ivk, one instance and one proof), no extractor exists and index binding fails
even for a verifier that rejects everything. -/
structure Extractor (lam : ℕ) (I X W IVK Pf : Type) where
  Ei : IVK → Trace lam → Option I
  Ew : IVK → Trace lam → X → Pf → Trace lam → W

/-- Helper.  What the experiment of `HasIndexBinding` produces: V's bit, i*, x and w. -/
structure BindingOutcome (I X W : Type) where
  accept : Bool
  iStar : Option I
  x : X
  w : W

/-- The experiment of `HasIndexBinding`, step by step.  The adversary is a committer C~ with output
(ivk, isk~) and a prover P~ with input isk~; isk~ is any state, of any type St, that C~ hands
over, and P~ is given nothing else.  V's own queries enter neither trace. -/
def bindingExp {St : Type} (E : Extractor lam I X W IVK Pf) (Ct : OComp lam (IVK × St))
    (Pt : St → OComp lam (X × Pf)) : OComp lam (BindingOutcome I X W) := do
  let ((ivk, st), trC) ← Ct.withTrace              -- (ivk, isk~) ← C~^f with trace tr_C
  let iStar := E.Ei ivk trC                        -- i* := E_i(ivk, tr_C)
  let ((x, π), trP) ← (Pt st).withTrace            -- (x, π) ← P~^f(isk~) with trace tr_P
  let w := E.Ew ivk trC x π trP                    -- w := E_w(ivk, tr_C, x, π, tr_P)
  let b ← A.V ivk x π                              -- V^f(ivk, x, π)
  pure ⟨b, iStar, x, w⟩

/-- The event of `HasIndexBinding`: V^f(ivk, x, π) = 1 ∧ ( x ∉ L(i*) ∨ (i*, x, w) ∉ R ). -/
def bindingBad : Set (BindingOutcome I X W) :=
  {o | o.accept = true ∧ (o.x ∉ R.L o.iStar ∨ ¬ R.rel' o.iStar o.x o.w)}

/-- The bound of `HasIndexBinding` for a named extractor E: for every committer C~ with at most
t_C queries and every prover P~ with at most t_P queries, Pr[ bindingBad ] ≤ ε(t_C, t_P). -/
def HasIndexBindingWith (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (tC tP : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)),
    Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
      Pr (bindingExp A E Ct Pt) (fun _ => bindingBad R) ≤ ε tC tP

/-- Index-binding knowledge soundness with error ε(t_C, t_P):
some deterministic E = (E_i, E_w) has the bound above.  One extractor serves all budgets. -/
def HasIndexBinding (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ E : Extractor lam I X W IVK Pf, HasIndexBindingWith R A E ε

/-! ## Index privacy -/

/-- The adversarial verifier V~.  It is handed ivk and, session
by session, x_j and π_j; it can query f whenever it likes; it asks for a further session or halts.
As a tree: its state is the subtree that it has reached.
* halt       : halts (its output is a function of its view, so it is not recorded),
* query q k  : asks the random oracle,
* sample n k : draws r from {0,..,n} with its internal randomness,
* request k  : requests the next session and continues as k x_j π_j.
A request carries no message to the environment, as in that work's formula (at Env, below). -/
inductive AdvVerifier (lam : ℕ) (X Pf : Type) : Type
  | halt : AdvVerifier lam X Pf
  | query (q : Str) (k : Digest lam → AdvVerifier lam X Pf) : AdvVerifier lam X Pf
  | sample (n : ℕ) (k : Fin (n + 1) → AdvVerifier lam X Pf) : AdvVerifier lam X Pf
  | request (k : X → Pf → AdvVerifier lam X Pf) : AdvVerifier lam X Pf

/-- A bound of t queries for V~, in total over all
sessions, on every path (also on paths that no oracle produces, as in OComp.QueryBound). -/
def AdvVerifier.QueryBound : AdvVerifier lam X Pf → ℕ → Prop
  | halt, _ => True
  | query _ _, 0 => False
  | query _ k, t + 1 => ∀ r, (k r).QueryBound t
  | sample _ k, t => ∀ r, (k r).QueryBound t
  | request k, t => ∀ x π, (k x π).QueryBound t

/-- The view, View_Real := (ivk, (x_j, π_j)_{j ≤ N}, tr(V~), ρ),
where tr(V~) is the trace of V~'s oracle queries and ρ its coins (the values drawn, in order,
without their ranges).  The view does not record how sessions, queries and draws interleave; V~ is
a fixed algorithm, so the three lists determine both the ranges and the interleaving. -/
structure View (lam : ℕ) (IVK X Pf : Type) where
  ivk : IVK
  sessions : List (X × Pf)
  trace : Trace lam
  coins : List ℕ

/-- The environment Z. In words: Z chooses each pair (x, w) from i and what has
happened so far.
As a formula: (x_j, w_j) ← Z(i, x_1, π_1, ..., x_{j-1}, π_{j-1}). The words allow more than the
formula. Env takes the formula: Z is a function of exactly these arguments. (The stronger form at
the end of this file takes the words.)
The formula has ← for Z (and := for the extractor), so Z may be randomised; Env is a deterministic
function. This loses nothing: a Z with coins and memory is a mixture of deterministic ones (argued
on paper, not proved in Lean), and the bound of `HasIndexPrivacy` passes to mixtures (Basic.lean,
privacy_randomised_env; not all hypotheses are named here: see its statement).
Z has no sight of V~'s queries and no oracle. -/
abbrev Env (I X W Pf : Type) : Type := I → List (X × Pf) → X × W

/-- (i, x_j, w_j) ∈ R: on index i, Z outputs only pairs in R.
Z is total, so an index with empty L(i) has no valid Z, and index privacy asks nothing for it. -/
def Env.IsValid (Z : Env I X W Pf) (i : I) : Prop :=
  ∀ hist, R.rel i (Z i hist).1 (Z i hist).2

/-- Beyond the formula at Env, above. The form of environment that the two loops
below take, so that one pair of loops serves `HasIndexPrivacy` and its stronger form (end of this
file): a function of V~'s whole view so far, which may also decline (none); then the experiment
ends. It is chosen after i, so it knows i.  For `HasIndexPrivacy`, read `Z v` in the loops as
Z(i, x_1, π_1, ..., x_{j-1}, π_{j-1}); Env.onView and HasIndexPrivacyWith below make it so. -/
abbrev ViewEnv (lam : ℕ) (IVK X W Pf : Type) : Type := View lam IVK X Pf → Option (X × W)

/-- Helper.  Whatever such an environment outputs on index i is in the relation. -/
def ViewEnv.IsValid (Z : ViewEnv lam IVK X W Pf) (i : I) : Prop :=
  ∀ v x w, Z v = some (x, w) → R.rel i x w

/-- The environment `Env` as the loops take it: it reads i, x_1, π_1, ...,
x_{j-1}, π_{j-1} and nothing else of the view, and it never declines. -/
def Env.onView (Z : Env I X W Pf) (i : I) : ViewEnv lam IVK X W Pf :=
  fun v => some (Z i v.sessions)

/-- Steps 3, 4 of the real experiment `realExp`. n is the number of sessions still allowed
and v the view so far. N is an upper bound on the number of sessions: an early halt ends the
experiment, and so does a request made after N sessions. -/
def realLoop (Z : ViewEnv lam IVK X W Pf) (isk : ISK) :
    AdvVerifier lam X Pf → ℕ → View lam IVK X Pf → OComp lam (View lam IVK X Pf)
  | .halt, _, v => pure v                           -- 4. V~ halts; output its view
  | .query q k, n, v =>                             -- 3(a) V~ queries f whenever it likes
      .query q fun r => realLoop Z isk (k r) n { v with trace := v.trace ++ [(q, r)] }
  | .sample m k, n, v =>
      .sample m fun r => realLoop Z isk (k r) n { v with coins := v.coins ++ [r.val] }
  | .request _, 0, v => pure v                      -- a request after N sessions: as 4.
  | .request k, n + 1, v =>                         -- 3(a) V~ requests a session
      match Z v with                                -- 3(b) (x_j, w_j) ← Z; `Env`'s Z reads
      | none => pure v                              --      i, x_1, π_1, ... only, and is never none
      | some (x, w) =>
        (A.P isk x w).bind fun π =>                 -- 3(c) π_j ← P^f(isk, x_j, w_j)
          realLoop Z isk (k x π) n { v with sessions := v.sessions ++ [(x, π)] }

/-- The real experiment Real_ARG(V~, Z, i, N), as one oracle
computation whose output is View_Real.  Step 1, f ← U(λ), is supplied by Pr. -/
def realExp (Vt : IVK → AdvVerifier lam X Pf) (Z : ViewEnv lam IVK X W Pf) (i : I) (N : ℕ) :
    OComp lam (View lam IVK X Pf) := do
  let (ivk, isk) ← A.C i                            -- 2. (ivk, isk) ← C^f(i), give ivk to V~
  realLoop A Z isk (Vt ivk) N ⟨ivk, [], [], []⟩

/-- The simulator S, a stateful randomised algorithm with state
space St.  It starts from pp(i) and N and outputs ivk; it answers every oracle query of V~; it
makes each proof as π_j ← S(x_j).  Its type gives it neither i nor any witness w_j.
No bound on running time is asked, as in that work: the three maps are arbitrary randomised maps.
-/
structure Simulator (lam : ℕ) (PP IVK X Pf : Type) where
  St : Type
  init : PP → ℕ → PMF (IVK × St)
  answer : St → Str → PMF (Digest lam × St)
  prove : St → X → PMF (Pf × St)

/-- Steps 3 and 4 of the ideal experiment `idealExp`: the same loop as realLoop, with the
oracle and the prover replaced by S; s is S's state.  The witness w_j is not used. -/
def idealLoop (S : Simulator lam PP IVK X Pf) (Z : ViewEnv lam IVK X W Pf) :
    AdvVerifier lam X Pf → ℕ → View lam IVK X Pf → S.St → PMF (View lam IVK X Pf)
  | .halt, _, v, _ => PMF.pure v                    -- 4. V~ halts; output its view
  | .query q k, n, v, s =>                          -- 3(a) queries answered by S
      (S.answer s q).bind fun out =>
        idealLoop S Z (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2
  | .sample m k, n, v, s =>
      (PMF.uniformOfFintype (Fin (m + 1))).bind fun r =>
        idealLoop S Z (k r) n { v with coins := v.coins ++ [r.val] } s
  | .request _, 0, v, _ => PMF.pure v               -- a request after N sessions: as 4.
  | .request k, n + 1, v, s =>                      -- 3(a) V~ requests a session
      match Z v with                                -- 3(b) Z as in the real experiment
      | none => PMF.pure v                          --      (never, for `Env`'s Z)
      | some (x, _) =>                              --      w_j is not used
        (S.prove s x).bind fun out =>               -- 3(c) π_j ← S(x_j)
          idealLoop S Z (k x out.1) n { v with sessions := v.sessions ++ [(x, out.1)] } out.2

/-- The ideal experiment Ideal_ARG(S, V~, Z, i, N), with output View_Ideal. -/
def idealExp (S : Simulator lam PP IVK X Pf) (Vt : IVK → AdvVerifier lam X Pf)
    (Z : ViewEnv lam IVK X W Pf) (i : I) (N : ℕ) : PMF (View lam IVK X Pf) :=
  (S.init (R.pp i) N).bind fun out =>               -- 1., 2. S gets pp(i), 1^N and outputs ivk
    idealLoop S Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2

/-- Consistency, as a property of a trace: a repeated query has
one answer. -/
def Trace.Consistent (tr : Trace lam) : Prop :=
  ∀ q r r', (q, r) ∈ tr → (q, r') ∈ tr → r = r'

/-- The requirement of `HasIndexPrivacy` for one i and one Z: for every V~ with at most t_V
queries and every N, Δ(View_Real, View_Ideal) ≤ ζ(t_V, N).  Both views are given by their event
probabilities; the ideal experiment has no f, hence prob and not Pr.  The second clause is
the ideal experiment's condition on S, which may choose its answers freely if they are consistent:
the trace of the ideal view is consistent with probability 1.
(Read the body as: bound on V~ → ( distance ≤ ζ ∧ probability = 0 ).) -/
def PrivacyFor (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (i : I)
    (Z : ViewEnv lam IVK X W Pf) : Prop :=
  ∀ (tV : ℕ) (Vt : IVK → AdvVerifier lam X Pf) (N : ℕ), (∀ ivk, (Vt ivk).QueryBound tV) →
    SD (fun T => Pr (realExp A Vt Z i N) (fun _ => T))
       (fun T => prob (idealExp R S Vt Z i N) T) ≤ ζ tV N
    ∧ prob (idealExp R S Vt Z i N) {v | ¬ v.trace.Consistent} = 0

/-- The requirement of `HasIndexPrivacy` for a named simulator S: PrivacyFor holds for every index i
and every valid environment Z of the form `Env`, read through Env.onView. -/
def HasIndexPrivacyWith (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (Z : Env I X W Pf), Z.IsValid R i → PrivacyFor R A S ζ i (Z.onView i)

/-- Statistical index privacy with error ζ(t_V, N) holds if some
simulator S meets it.  One simulator serves all V~, all budgets and all N. -/
def HasIndexPrivacy (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ S : Simulator lam PP IVK X Pf, HasIndexPrivacyWith R A S ζ

/-! ## Summary of the primitive -/

/-- The primitive; other files call it a doubly
zero-knowledge commit-and-prove argument.  ARG = (C, P, V) is one with errors α, ε, ζ if it has the
three properties above: HasCompletenessError α, HasIndexBinding ε
and HasIndexPrivacy ζ. Other files call IsZKCPArg, and index privacy as
HasIndexPrivacy states it, the literal definition or the literal form, as against the stronger form
at the end of this file. λ is fixed here, as in every definition of this file: each definition
speaks of one fixed λ, and nothing in the file lets λ grow (which theorems are for every λ, and
where λ is 256: header of ZKCP/Main.lean).
Errors are values in [0, ∞], so a bound that is 1 or more makes its clause trivially true: the
three bounds of a theorem of this form are part of what a reader must check. -/
structure IsZKCPArg (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  completeness : HasCompletenessError R A α
  indexBinding : HasIndexBinding R A ε
  indexPrivacy : HasIndexPrivacy R A ζ

/-- The same with `HasRefinedCompletenessError`'s completeness error (α_C, α_P). -/
structure IsZKCPArgRefined (αC αP : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  completeness : HasRefinedCompletenessError R A αC αP
  indexBinding : HasIndexBinding R A ε
  indexPrivacy : HasIndexPrivacy R A ζ

/-! ## Beyond index privacy and the summary: the stronger form that our proofs establish -/

/-- Not `HasIndexPrivacyWith`, but stronger: that definition with our reading of the words on Z
(at Env, above), that Z chooses from what has happened so far: Z is given V~'s whole view so far, so
V~ can steer the choice of instances by its queries and coins. In addition, and beyond `Env`,
Z may decline. It implies `HasIndexPrivacyWith` with the same S and ζ, because `Env`'s Z is a
special case (Basic.lean, HasStrongIndexPrivacyWith.toHasIndexPrivacyWith). The two forms differ
(Separation.lean, leaky_isZKCPArg, leaky_not_strong). -/
def HasStrongIndexPrivacyWith (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (Z : ViewEnv lam IVK X W Pf), Z.IsValid R i → PrivacyFor R A S ζ i Z

/-- Not `IsZKCPArg`. The primitive with the extractor E and the simulator S named, so that a
reader can inspect them, and with the stronger form of privacy. It implies IsZKCPArg (Basic.lean,
IsZKCPArgWith.toIsZKCPArg). -/
structure IsZKCPArgWith (E : Extractor lam I X W IVK Pf) (S : Simulator lam PP IVK X Pf)
    (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  completeness : HasCompletenessError R A α
  indexBinding : HasIndexBindingWith R A E ε
  indexPrivacy : HasStrongIndexPrivacyWith R A S ζ

end Properties

end ZKCP
