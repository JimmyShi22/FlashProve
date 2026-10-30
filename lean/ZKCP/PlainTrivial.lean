-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PlainTrivial.lean: this file is about the definition of a commit-and-prove argument
(ZKCP/Defs.lean) itself, not about a protocol: it gives a degenerate scheme to hold the definition
against.
For every finite type of indices and every relation, with nothing assumed beyond the hypotheses of
the statement `bf_main` (in the random-oracle model, on Lean's three axioms), a scheme with empty
proofs (K ≥ 1 blocks), whose verifier searches all pairs (index, salt) for the key, meets the
definition of ZKCP/Defs.lean, in its named and stronger form, with three small errors (those of
`Spec.bf_main` below).

Definitions and one statement (`Spec.bf_main`); the proof: ZKCP/PlainTrivialProofs.lean.

Why: one can argue: the definition bounds no work of V and no size of a key or a proof; so "there
is a scheme that meets it" is true for a reason that has nothing to do with any proof system. Here the argument is a theorem.

Main names: the scheme, over one random oracle f of λ bits; K ≥ 1 blocks; M + 1 salts; R any
relation over a finite type I of indices:
  C(i) (of `bfArg`): draw a salt σ; the key is the list of the K answers of f at the strings of (i,
    σ) (`bfPts`); the prover's key is ().
  P: the proof is ().
  V(ivk, x, ()): go through all pairs (i', σ') in one fixed order (`bfAll`), ask f at the K strings
    of each, stop at the first pair whose answers are ivk; accept if there is one and x has a
    witness at i'. ("Has a witness" is decided classically: a step of an oracle algorithm of
    ZKCP/Defs.lean is an arbitrary function.)
  `bfSim`: a key of K uniform blocks; answers sampled on demand and remembered; every proof is ().
  `Spec.bf_main`: 0 < K, any w0 : W ⇒ ZKCP.IsZKCPArgWith R (bfArg ..) (bfExt ..) (bfSim ..) α ε ζ,
    with n := |I| (M + 1), u := 2^-λ: α = n u^K, ε tC tP = tC u + n u^K, ζ tV N = tV / (M + 1).

Limits: (i) "Meeting the definition says nothing about cost": this V asks f up to K |I| (M + 1)
times, and the definition is met. These files (ZKCP/PlainTrivial.lean, ZKCP/PlainTrivialProofs.lean)
have no theorem on what this V asks, from above or from below. What is a theorem: a scheme with
empty proofs meets the definition. That its V asks at most K |I| (M + 1) strings, and that, where
the index matters, every bound q on its queries has 1 ≤ 2 n u^K + 2 q / (M + 1), is proved in
ZKCP/HonestKeyVerBf.lean (`bfV_qb`, `bfV_lower`), under their hypotheses.
(ii) A sentence "there is a scheme that meets the definition at such errors" says nothing on any
protocol. What a theorem on a named scheme says is not touched: it says of that scheme what the
definition says; on cost it says nothing either.
This file does not say that the definition is at fault: it is a definition of security, and says
itself that it bounds no running time (ZKCP/Defs.lean: the docstrings of `OComp`, `Extractor`,
`Simulator`). [More exactly: for Extractor and Simulator the docstring gives it as that of the work
that this protocol builds on (lean/CREDITS.md, "Further work"); for OComp, so for C, P, V, the
sentence is this
library's reading. What is missing is our own sentence on cost in Lean.]

It does not say that this scheme is of any use. It says nothing for an infinite type of indices (V
must be a finite tree). It does not say that the three errors are tight.
At the edges the statement is true and void: with one salt (M = 0) ζ = tV, at least 1 from the first
query on; with λ = 0 all of α, ε are at least 1 as soon as there is an index; with no index at all
nothing is served. K = 0 is shut out by the premise (the empty key would fit every pair). The
premise is idle (no theorem here says so): at K = 0 the error α = n is at least 1 wherever
there is an index, and binding and privacy never use the premise: a fourth edge of the same kind.
-/
import ZKCP.HashToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace TopC
open ZKCP
open scoped ENNReal

/-- a string for three numbers: unary, parted by "false": one to one -/
def bfPt (k a σ : ℕ) : Str :=
  List.replicate k true ++ false :: (List.replicate a true ++ false :: List.replicate σ true)

/-- ask the oracle at the strings of a list, one after the other -/
def bfAsk (lam : ℕ) : List Str → OComp lam (List (Digest lam))
  | [] => .pure []
  | q :: qs => .query q fun r => (bfAsk lam qs).bind fun rs => .pure (r :: rs)

/-- n uniform blocks -/
def bfDraw (lam : ℕ) : ℕ → PMF (List (Digest lam))
  | 0 => PMF.pure []
  | n + 1 => (PMF.uniformOfFintype (Digest lam)).bind fun r => (bfDraw lam n).map fun rs => r :: rs

section
variable (lam K M : ℕ) {I X W PP : Type} [Fintype I]

/-- the K strings of a pair (index, salt) -/
def bfPts (p : I × Fin (M + 1)) : List Str :=
  (List.range K).map fun k => bfPt k (Fintype.equivFin I p.1).val p.2.val

/-- all pairs, in one fixed order -/
def bfAll : List (I × Fin (M + 1)) := Finset.univ.toList

open Classical in
/-- the first pair of a list whose K answers are ivk -/
def bfSearch (ivk : List (Digest lam)) :
    List (I × Fin (M + 1)) → OComp lam (Option (I × Fin (M + 1)))
  | [] => .pure none
  | p :: ps =>
    (bfAsk lam (bfPts K M p)).bind fun ds => if ds = ivk then .pure (some p) else bfSearch ivk ps

open Classical in
/-- The brute-force scheme. -/
def bfArg (R : IndexedRelation I X W PP) :
    Arg lam I X W (List (Digest lam)) Unit Unit where
  C := fun i => .sample M fun σ => (bfAsk lam (bfPts K M (i, σ))).bind fun ds => .pure (ds, ())
  P := fun _ _ _ => .pure ()
  V := fun ivk x _ => (bfSearch lam K M ivk (bfAll M)).bind fun o => .pure (o.elim false fun p => decide (∃ w, R.rel p.1 x w))

open Classical in
/-- the index of the first pair, in V's order, all of whose strings stand in the key maker's trace
with the answers ivk -/
def bfEi (ivk : List (Digest lam)) (trC : Trace lam) : Option I :=
  ((bfAll M).find? fun p : I × Fin (M + 1) =>
    decide (List.Forall₂ (fun q d => (q, d) ∈ trC) (bfPts K M p) ivk)).map Prod.fst

open Classical in
/-- Its extractor: the witness by choice (w0 if there is none). -/
def bfExt (R : IndexedRelation I X W PP) (w0 : W) :
    Extractor lam I X W (List (Digest lam)) Unit where
  Ei := bfEi lam K M
  Ew := fun ivk trC x _ _ => if h : ∃ w, R.rel' (bfEi lam K M ivk trC) x w then h.choose else w0

/-- Its simulator. -/
def bfSim : Simulator lam PP (List (Digest lam)) X Unit where
  St := Cache lam
  init := fun _ _ => (bfDraw lam K).map fun ds => (ds, fun _ => none)
  answer := fun c q => lazyAnswer c q
  prove := fun c _ => PMF.pure ((), c)

/-- n u^K: a bound on the chance that some pair of which nothing was asked has the key's K answers
-/
def bfAcc (I : Type) [Fintype I] : ℝ≥0∞ :=
  (Fintype.card (I × Fin (M + 1)) : ℝ≥0∞) * (((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹) ^ K

end

namespace Spec

/-- For K ≥ 1 blocks the brute-force scheme meets the definition, in the named and stronger form:
nothing assumed beyond the hypotheses of its statement (in the random-oracle model, on Lean's three
axioms) -/
def bf_main : Prop :=
  ∀ (lam K M : ℕ) (I X W PP : Type) [Fintype I] (R : IndexedRelation I X W PP) (w0 : W), 0 < K →
    IsZKCPArgWith R (bfArg lam K M R) (bfExt lam K M R w0) (bfSim lam K)
      (bfAcc lam K M I) (fun tC _ => (tC : ℝ≥0∞) * ((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹ + bfAcc lam K M I) (fun tV _ => (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞))

end Spec

end TopC
