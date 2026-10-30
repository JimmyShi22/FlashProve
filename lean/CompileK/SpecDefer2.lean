-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/SpecDefer2.lean: a lemma on programming a random oracle late: deferred programming
(Rom/Defer.lean; for one budget: Rom/SpecDeferTotal.lean) with two refinements of the count: (1) a
query is charged only against the marked evaluations of its own public class (a function of the
point that does not depend on the tokens' values: for instance oracle and round); (2) in classes
named for it, a point is charged to two tokens jointly: the bits of both count. The same language,
the same two modes; the hypothesis is on all states of the run, not on final states only.

In standard terms: in mode R one lazily sampled table, for all oracles, serves everybody; in mode I
the challenger's marked evaluations get fresh uniform answers, which are programmed into the table
only at their release, where the entry is still empty. `Spec.defer2` states, under the hypotheses of
its statement, a bound on the statistical distance of the adversary's outputs in the two modes. A
token is a string that the challenger names by a number: a uniform string that it draws
(`Step.fresh`), or the tail of a marked evaluation's answer. A marked evaluation (`Step.marked`) is
an evaluation of the challenger at a point made from tokens' values: it is charged to the first of
them; the others are its further tokens. The language is told in the head of Rom/Defer.lean.

Definitions and one statement (`Rom.Spec.defer2`); the proof: CompileK/Defer2Prob.lean (two hidden
coordinates), CompileK/Defer2Valid.lean (counts, invariant, hit bounds), CompileK/Defer2Step.lean (a
step), CompileK/Defer2.lean (a run; the last step). Nothing assumed beyond the hypotheses of the
statements, in the random-oracle model, on Lean's three axioms.

Why: in `Spec.defer` (Rom/Defer.lean) a marked evaluation is charged to one token, whatever further
secret tokens its point holds, and a query forms a pair with every marked evaluation of its oracle.
For a tree's inner vertex (point: two secret digests) that counts half of the secret bits; for a
chain of evaluations whose points hold the round's number in the open it counts all rounds together.

Main names:
  `PtFit cl J pt`: at a marked evaluation, statically: the class of the point does not depend on the
    tokens' values; in a joint class: the point is jointly injective in (the charged token, one
    further token).
  `MarkFit cl J d us pt`: at a marked evaluation, dynamically, in a joint class: us = [b]; b is not
    shown and stands in no earlier marked point of that oracle. (The language asks these two of the
    charged token only; that b exists and differs from the charged token is the language's own rule:
    a state without violation: so it is not repeated here.)
  `DSt.Ok2 cl J ℓ ks d`: a state is in order: no violation; every evaluation's class lies in ks;
    lengths: |charged| ≥ ℓ, in a joint class |charged| + |b| ≥ ℓ; in a joint class an unreleased
    evaluation's b is not shown.
  `Step.Alw`, `AdvAlw`: by recursion along the program and along the adversary, in mode I: `PtFit`,
    `MarkFit` at every marked evaluation; G (in `Spec.defer2`: `DSt.Ok2`) after every marked
    evaluation and every reveal; at a halt Fn (in `Spec.defer2`: the counts `DSt.CntK2`: plain
    evaluations of o at most e o, marked evaluations of class κ at most M κ).
  `Spec.defer2`: t queries in all and N calls (N is in no bound); `AdvAlw` at the start ⇒ the
    distance of the two modes is at most t · sup over κ ∈ ks of (M κ / 2^(ℓ κ)) + Σ over κ ∈ ks of M
    κ (e (oracle of κ) + M κ) / 2^(ℓ κ).

Why not final states: "b is not shown while the evaluation is unreleased" is no fact that only
grows: b shown now and the charged token later leaves a clean final state, and between the two the
adversary may ask.

Why "not shown" is "hidden" in this language (without it the statement would be false): b may be the
tail of another evaluation's answer and may stand in points of other oracles. The language's rule "a
released evaluation must have ALL its tokens shown, its tail included (else: violation)" forbids
that such an evaluation is released, and its answer written into the table, while b is unshown.

Against this protocol's technical report (lean/CREDITS.md; by a reading). Its lemma on programming
divides the honest side's programmed queries into sets with a hidden part and an open part, and
charges a query only against the sets of its own oracle whose open part it meets: (1) is that idea
in this library's language.
Its hidden part is some bits of the point at a fixed position, of any length: at an inner vertex
both children's labels: (2). Its hypothesis, too, is on every moment (the hidden part is
unpredictable at any time before the set is sent): in that `Spec.defer2` is nearer to it than
`Spec.defer`. Not the same lemma: its second summand counts, for each set, the other sets of that
oracle with the same open part, ours M κ (e + M κ): the oracle's plain evaluations too; its sets may
hold many points that differ in one field (all attempts of a round), which cost one set (in the
library the later tries go under further names); in its latest form the hidden part needs
min-entropy only: our tokens are uniform: the narrower case.

This file says nothing on whether the hypotheses of `Spec.defer2` can be met together. Guards of the
hypothesis `AdvAlw`: CompileK/Defer2Guard.lean (a toy with one vertex); at a program that shows b
alone it fails.

Limits: the setting of Rom/SpecDeferTotal.lean is the case K := the oracles' names, of := the
point's oracle, J := nowhere: the bound is then Rom/SpecDeferTotal.lean's, letter for letter; the
hypotheses differ in kind (all states | final states), so neither statement is an instance of the
other.
This file says nothing on any compiled prover: that its runs meet `AdvAlw` (both children of an
unreleased vertex unshown at every moment; each digest has one parent) is our own reasoning on the
scheme, proved nowhere, but for CompileK/Defer2Door.lean: under its hypotheses `door_alw3` proves
`AdvAlw` for the compiled prover's challenger, with the counts `eAllB`, `mAllU`, for every
admissible adversary, and `hopU2` applies this lemma there. In this file nothing is said on a
compiled prover.
This file says nothing on the value of any number.
-/
import Rom.DeferTotal

set_option autoImplicit false

open scoped ENNReal
open Prob
namespace Rom
open DeferTail

variable {S : OSpec} {K : Type}

/-- Classes of points: the oracle is a function of the class -/
structure PtCls (S : OSpec) (K : Type) where
  of : Pt S → K
  orc : K → S.ι
  orc_of : ∀ k, orc (of k) = k.1

/-- at a marked evaluation, statically -/
def PtFit (cl : PtCls S K) (J : K → Bool) {o : S.ι} (pt : Bits → List Bits → S.Dom o) : Prop :=
  (∀ v vs v' vs', cl.of ⟨o, pt v vs⟩ = cl.of ⟨o, pt v' vs'⟩) ∧
  (J (cl.of ⟨o, pt [] []⟩) = true → ∀ v v' x x', pt v [x] = pt v' [x'] → v = v' ∧ x = x')

/-- at a marked evaluation, in the state before it -/
def MarkFit (cl : PtCls S K) (J : K → Bool) (d : DSt S) {o : S.ι}
    (us : List Tok) (pt : Bits → List Bits → S.Dom o) : Prop :=
  J (cl.of ⟨o, pt [] []⟩) = true → ∃ b, us = [b] ∧ b ∉ d.shown ∧ ∀ v ∈ d.evs, v.o = o → b ≠ v.charged ∧ b ∉ v.others

/-- a state is in order -/
def DSt.Ok2 (cl : PtCls S K) (J : K → Bool) (ℓ : K → ℕ) (ks : Finset K) (d : DSt S) : Prop :=
  d.viol = false ∧ ∀ v ∈ d.evs, cl.of ⟨v.o, v.pt⟩ ∈ ks ∧
    (J (cl.of ⟨v.o, v.pt⟩) = false → ℓ (cl.of ⟨v.o, v.pt⟩) ≤ (d.val v.charged).length) ∧
    (J (cl.of ⟨v.o, v.pt⟩) = true → ∃ b, v.others = [b] ∧ ℓ (cl.of ⟨v.o, v.pt⟩) ≤ (d.val v.charged).length + (d.val b).length ∧ (v.released = false → b ∉ d.shown))

/-- the counts, at a halt -/
def DSt.CntK2 [DecidableEq K] (cl : PtCls S K) (e : S.ι → ℕ) (M : K → ℕ) (d : DSt S) : Prop :=
  (∀ o, d.nPlain o ≤ e o) ∧ ∀ κ, (d.evs.filter fun v => decide (cl.of ⟨v.o, v.pt⟩ = κ)).length ≤ M κ

/-- along a step of the challenger, in mode I -/
def Step.Alw {sp : Split S} (cl : PtCls S K) (J : K → Bool) (G : DSt S → Prop) {α : Type} :
    Step S sp α → DSt S → (α × DSt S → Prop) → Prop
  | .pure a, d, Post => Post (a, d)
  | .sample _ k, d, Post => ∀ r, (k r).Alw cl J G d Post
  | .plain o q k, d, Post => ∀ y ∈ (lazyAnswer d.table o q).support, (k y.1).Alw cl J G (postPlain d o y.2) Post
  | .fresh L k, d, Post => ∀ u : Fin L → Bool, (k d.vals.length).Alw cl J G (postFresh d (List.ofFn u)) Post
  | .marked o t us pt _ k, d, Post =>
    PtFit cl J pt ∧
    MarkFit cl J d us pt ∧
    ∀ r : S.Rng o,
      G (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table) ∧
      (k (sp.split o r).1 d.vals.length).Alw
        cl J G (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table) Post
  | .reveal ts k, d, Post =>
    G (postReveal true d ts) ∧ (k (ts.map d.val)).Alw cl J G (postReveal true d ts) Post

/-- along the adversary -/
def AdvAlw {sp : Split S} {Out In α : Type} (C : Chall S sp Out In) (cl : PtCls S K)
    (J : K → Bool) (G Fn : DSt S → Prop) :
    Adv S Out In α → C.τ × DSt S → Prop
  | .halt _, s => Fn s.2
  | .sample _ k, s => ∀ r, AdvAlw C cl J G Fn (k r) s
  | .query o q k, s => ∀ y ∈ (lazyAnswer s.2.table o q).support, AdvAlw C cl J G Fn (k y.1) (s.1, withT s.2 y.2)
  | .call m k, s => (C.step s.1 m).Alw cl J G s.2 fun y => AdvAlw C cl J G Fn (k y.1.1) (y.1.2, y.2)

/-- Deferred programming, by classes, with joint charges. -/
def Spec.defer2 : Prop :=
  ∀ (S : OSpec) (sp : Split S) (K : Type) [DecidableEq K] (Out In α : Type) (C : Chall S sp Out In)
    (s₀ : C.τ) (A : Adv S Out In α)
    (t : ℕ) (e : S.ι → ℕ) (M ℓ : K → ℕ) (N : ℕ) (ks : Finset K) (cl : PtCls S K) (J : K → Bool),
    A.TotalBound t N →
    AdvAlw C cl J (DSt.Ok2 cl J ℓ ks) (DSt.CntK2 cl e M) A (s₀, DSt.init S) →
    tv ((interact (C.world false) A (s₀, DSt.init S)).map Prod.fst)
       ((interact (C.world true) A (s₀, DSt.init S)).map Prod.fst)
      ≤ (t : ℝ≥0∞) * ks.sup (fun κ => (M κ : ℝ≥0∞) / 2 ^ ℓ κ) + ∑ κ ∈ ks, (M κ : ℝ≥0∞) * (e (cl.orc κ) + M κ : ℕ) / 2 ^ ℓ κ

end Rom
