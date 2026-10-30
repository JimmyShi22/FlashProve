-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecOverOneA.lean: the step to one hash function under an adaptive rule for which hash blocks of
an answer are queried (`OComp.overOneA`). Definitions and one statement (`Spec.ofNeedA`; its proof
is in Rom/OverOneA.lean); nothing is proved here.

Why. The step implements a family of typed oracles by one hash function f (Rom/Family.lean). In
Rom/OverOneN.lean a query to a typed oracle becomes queries to f only for the hash blocks that a
function of the query (`Need`) marks. An algorithm that makes the same kind of query again and again
until the first hash block of the answer passes a check (a search for a nonce: proof of work) reads
only the first hash block of a failed attempt. Whether an attempt fails is seen in its answer, not
in its query. So a function of the query counts, for every failed attempt, all hash blocks that the
final attempt needs. Here the rule sees the hash blocks obtained so far (`NeedA`, Rom/NeedA.lean),
and a failed attempt can cost one query to f.

The sections: 1, the step; 2, what is shown (the answer as the rule shows it: unqueried hash blocks
are the all-zero block); 3, costs; 4, a sanity statement.

Limits: this library does not state or prove that an algorithm under `overOneA` returns what it
returns under `overOne` (Rom/Family.lean), nor that completeness, index binding and index privacy
carry over: `OComp.overOneA` occurs in one statement only, `Spec.ofNeedA`, at a rule of the form
`NeedA.ofNeed need`, which does not look at the hash blocks so far. This file defines a bound for
the worst case only (`OComp.CostBoundV`): it says nothing on the mean number of queries. Without a
condition on the program the all-zero block can appear in a result.
-/
import Rom.NeedA
import Rom.OverOneNGen

set_option autoImplicit false

namespace Rom
open ZKCP
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {α : Type}

/-! ## 1. The step -/

/-- the strings of the hash blocks of the answer at (o, q); the empty string from the number of hash
blocks on, where nothing is ever queried -/
def strsOf (m : OracleCoding S lam) (o : S.ι) (q : S.Dom o) : ℕ → List Bool := fun j =>
  if h : j < m.blocks o then m.code o q ⟨j, h⟩ else []

/-- Go through K indices from j on; query f for hash block j if the rule says so, given the hash
blocks acc so far; else leave what acc has (at the start: the all-zero block). -/
def askA (lam : ℕ) (nd : ℕ → (ℕ → Dg lam) → Bool) (pts : ℕ → List Bool) :
    (K j : ℕ) → (ℕ → Dg lam) → OComp (rom lam) (ℕ → Dg lam)
  | 0, _, acc => .pure acc
  | K + 1, j, acc =>
      match nd j acc with
      | true =>
        .query (S := rom lam) () (pts j) fun r =>
          askA lam nd pts K (j + 1) (Function.update acc j r)
      | false => askA lam nd pts K (j + 1) acc

/-- The same algorithm over the hash function, under an adaptive rule. The hash blocks are joined as
in OComp.overOne: by (m.rng o).symm. -/
def OComp.overOneA (m : OracleCoding S lam) (need : NeedA S lam) : OComp S α → OComp (rom lam) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).overOneA m need
  | .query o q k =>
    (askA lam (need o q) (strsOf m o q) (m.blocks o) 0 (acc0 lam)).bind fun acc =>
      (k ((m.rng o).symm fun j => acc j)).overOneA m need

/-! ## 2. What is shown -/

/-- The answer as the rule shows it: the hash blocks that the rule does not query are the all-zero
block. -/
def shownA (m : OracleCoding S lam) (need : NeedA S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : S.Rng o :=
  (m.rng o).symm fun j => maskFrom (need o q) (extBl (m.rng o r)) (m.blocks o) 0 (acc0 lam) j


/-! ## 3. Costs -/

/-- how many hash blocks a rule queries on a given sequence: the recursion of maskFrom, counted -/
def cntFrom (nd : ℕ → (ℕ → Dg lam) → Bool) (bl : ℕ → Dg lam) : (K j : ℕ) → (ℕ → Dg lam) → ℕ
  | 0, _, _ => 0
  | K + 1, j, acc =>
      match nd j acc with
      | true => 1 + cntFrom nd bl K (j + 1) (Function.update acc j (bl j))
      | false => cntFrom nd bl K (j + 1) acc

/-- How many hash blocks the rule queries at (o, q) if the answer is r. -/
def numA (m : OracleCoding S lam) (need : NeedA S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : ℕ :=
  cntFrom (need o q) (extBl (m.rng o r)) (m.blocks o) 0 (acc0 lam)

/-- On every path the weights of the queries add up to at most t, where the weight of a query may
depend on its answer. (OComp.CostBoundAt of Rom/OverOneN.lean is the case of a weight that does
not.) -/
def OComp.CostBoundV (w : (o : S.ι) → S.Dom o → S.Rng o → ℕ) : OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ k, t => ∀ r, (k r).CostBoundV w t
  | .query o q k, t => ∀ r, ∃ t', w o q r + t' ≤ t ∧ (k r).CostBoundV w t'

/-! ## 4. A sanity statement -/

/-- a function that marks hash blocks (`Need`) as a rule: it does not look at the hash blocks so
far; from the number of hash blocks on it queries nothing -/
def NeedA.ofNeed {m : OracleCoding S lam} (need : Need m) : NeedA S lam := fun o q j _ =>
  if h : j < m.blocks o then need o q ⟨j, h⟩ else false

/-- Sanity statement: with such a function as the rule, `overOneA` is `overOneN` of
Rom/OverOneN.lean: the same results for every fixed hash function and every program; the answer as
the rule shows it agrees with the answer on the marked hash blocks; as many hash blocks are queried
as are marked. -/
def Spec.ofNeedA : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (m : OracleCoding S lam) (need : Need m),
    (∀ (α : Type) (g : Fam (rom lam)) (c : OComp S α),
      (c.overOneA m (NeedA.ofNeed need)).runEager g = (c.overOneN m need).runEager g) ∧
    (∀ o q r, Agree m need o q r (shownA m (NeedA.ofNeed need) o q r)) ∧
    (∀ o q r, numA m (NeedA.ofNeed need) o q r = need.num o q)

end Rom
