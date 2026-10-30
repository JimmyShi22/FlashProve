-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CostFmt.lean: how many questions are asked at most by the rules of the format that hash (those
named under 3). For the reader of a whole file the bound is made from a number that is a function
of the description alone.

A question is what a count `c : CostP m` counts: at the monad of trees of queries, a query to the
oracle. What a count says depends on the instance c: Run/CostP.lean, the head, 4. Bookkeeping on
this library's own terms: the functions are those of Fmt/Rules23.lean, Fmt/Rules4.lean,
Fmt/Rules5.lean, Fmt/Rules6.lean, Fmt/Rules6Round.lean, Fmt/Rules7.lean, Fmt/Rules8.lean, as they
stand. The proofs are in Run/CostFmtProofs.lean. The rule numbers are those of the format page
(docs/format/FORMAT.md, which comes with the programs).

1. What the file contains. Definitions and statements.
   `opensN L os`, `roundN r`, `roundsN rs`, `fileN S`: fileN S = 3 + the sum over the rounds of [
      (firstBlock work + (wordsAtMost + 3) / 4 + 1) / 2 + the sum over the round's openings of (a +
      1) · poss ]. Here S is a description (`Fmt.Spec`, Fmt/Rules8.lean); work and poss are fields
      of the round's entry, a is the depth of the opened tree.

2. What is checked when the file compiles. Only the types.

3. Theorems stated, for every count c : `CostP m` (Run/CostP.lean) and every hash h of which each
   call asks at most k.
   `cost_HM`: the hash by asking the single oracle (`HM`): 2 k' if one asking costs k'.
   `cost_first`: the head of a chain (`startChainW`): 2 k.
   `cost_round`: n calls (`fetchFrom`): n k; the blocks 0 .. n − 1 (`fetchW`): ((n + 1) / 2) k; the
      step of a chain with K blocks of the verifier's message (`Chain.queryW`): ((firstBlock work +
      K + 1) / 2) k.
   `cost_tree`: the walk, for any way of combining two values that costs k: a lone vertex: k; one
      depth: (the length of the list) k, and the list that comes out is no longer; from depth d to
      the root: d (length) k; the opened leaves: (length) k, and no more come out; an opening's
      reader at a tree of depth a and a list of L positions: (a + 1) L k.
   `cost_file`: `readOpens` at a list of L positions: (opensN L os) k; `step`: (roundN r) k;
      `foldRounds`: (roundsN rs) k; `readChain`, `wholeChain`: (fileN S) k.
   `cost_pure`: the two facts on pure functions that are used: the list of drawn positions is no
      longer than the draws; a round draws exactly as many positions as its entry says.
   The numbers are upper bounds: how many vertices a walk really hashes depends on the drawn list
   (vertices with two opened children are hashed once); nothing says that a bound is attained.
   Use. At the monad of trees of queries, c := "no coin, at most t queries, on every path", h :=
   "ask" (k = 2): the bound t that a parser which asks the oracle owes (Run/TransportO.lean).

4. What fileN does not count, and what is not claimed.
   (1) The configuration's digest (R4.9): the reader of a file does not compute it: where a rule
   takes it, it is handed in as a constant; whoever computes it from the public files asks one call
   more. (2) The seeds of a stored table's record (R4.8: a chain of its own), which a verifier of a
   chain that reads such a table makes again. (3) A session's several chains: fileN is one chain's.
   Nothing on what the functions compute.

Terms: lean/GLOSSARY.md.
-/
import Run.CostP
import Fmt.Rules8

set_option autoImplicit false

namespace Run
open _root_.Fmt

/-- The questions of the openings behind one draw of L positions at most, in units of k (an upper
bound: the head, 3). -/
def opensN (L : Nat) : List (Shape × Src) → Nat
  | [] => 0
  | (sh, _) :: os => (sh.a + 1) * L + opensN L os

/-- The questions of one round, in units of k (an upper bound: the head, 3). -/
def roundN (r : Round) : Nat :=
  (firstBlock r.entry.work + (wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 +
    opensN r.entry.poss r.opens

/-- The questions of the rounds, in units of k (an upper bound: the head, 3). -/
def roundsN : List Round → Nat
  | [] => 0
  | r :: rs => roundN r + roundsN rs

/-- The questions of a whole file, in units of k: a function of the description alone (an upper
bound: the head, 3; what it does not count: the head, 4). -/
def fileN (S : Fmt.Spec) : Nat := 3 + roundsN S.rounds

namespace Spec

def cost_pure : Prop :=
  (∀ l : List Nat, (listOf l).length ≤ l.length) ∧
  ∀ (f : Fld) (e : Entry) (kd : Kind) (row : Row), (drawRound f e kd row).poss.length = e.poss

def cost_HM : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m) (ask : ByteArray → m ByteArray) (k : Nat),
    (∀ s, c.le (ask s) k fun _ => True) →
    ∀ (number tree index : Nat) (start bytes : ByteArray),
      c.le (HM ask number tree index start bytes) (2 * k) fun _ => True

def cost_first : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat),
    (∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True) →
    ∀ (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray),
      c.le (startChainW h lab pd statement rnd) (2 * k) fun _ => True

def cost_round : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat),
    (∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True) →
    (∀ (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind)
          (w nonce n j : Nat) (acc : Array ByteArray),
        c.le (fetchFrom h lab rho i msg kind w nonce n j acc) (n * k) fun _ => True) ∧
    (∀ (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce n : Nat),
      c.le (fetchW h lab rho i msg kind w nonce n) ((n + 1) / 2 * k) fun _ => True) ∧
    ∀ (ch : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat),
      c.le (ch.queryW h msg kind work nonce K) ((firstBlock work + K + 1) / 2 * k) fun _ => True

def cost_tree : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m) (k : Nat),
    (∀ (α σ : Type) (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ)),
      (∀ a b x y, c.le (comb a b x y) k fun _ => True) →
      (∀ (d i : Nat) (x : α) (s : σ), c.le (walkLoneW comb give d i x s) k fun _ => True) ∧
      (∀ (d : Nat) (l : List (Nat × α)) (s : σ),
        c.le (walkLevelW comb give d l s) (l.length * k) fun r =>
          ∀ p, r = some p → p.1.length ≤ l.length) ∧
      ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
        c.le (walkW comb give d now s met) (d * (now.length * k)) fun _ => True) ∧
    ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray),
      (∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True) →
      (∀ (sh : Shape) (start : ByteArray) (xs : List Nat) (cs : List (List UInt64 × ByteArray)),
        c.le (leavesW h sh start xs cs) (xs.length * k) fun r => r.length ≤ xs.length) ∧
      ∀ (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray) (xs : List Nat)
          (b : ByteArray) (i : Nat),
        c.le (readOpeningW h cfg f salt sh start xs b i)
          ((sh.a + 1) * (xs.length * k)) fun _ => True

/-- States the bounds for the openings after a draw, a round, the rounds, a chain in a file, and a
whole file (upper bounds: the head, 3; what `fileN` does not count: the head, 4). -/
def cost_file : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat),
    (∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True) →
    (∀ (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (roots : Array ByteArray)
          (poss : List Nat) (b : ByteArray) (os : List (Shape × Src)) (sn : Seen) (i : Nat),
        c.le (readOpens h cfg P run roots poss b os sn i)
          (opensN poss.length os * k) fun _ => True) ∧
    (∀ (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St) (r : Round),
      c.le (step h cfg P run b s r) (roundN r * k) fun _ => True) ∧
    (∀ (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray)
          (rs : List Round) (s : St),
        c.le (foldRounds h cfg P run b rs s) (roundsN rs * k) fun _ => True) ∧
    (∀ (S : Fmt.Spec) (seen : Seen) (b : ByteArray) (i : Nat),
      c.le (readChain h S seen b i) (fileN S * k) fun _ => True) ∧
    ∀ (S : Fmt.Spec) (b : ByteArray), c.le (wholeChain h S b) (fileN S * k) fun _ => True

end Spec
end Run
