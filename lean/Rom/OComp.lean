-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/OComp.lean: oracle algorithms with private coins over a family of oracles; eager and lazy
  semantics. At S = `rom lam` (Rom/OSpec.lean) this corresponds to `ZKCP.OComp lam` of
  ZKCP/Defs.lean, constructor by constructor (Rom/Bridge.lean).

  Credit. The public Lean library VCV-io (https://github.com/Verified-zkEVM/VCV-io) also represents
  an algorithm with oracle access as a tree of queries.
  Here an algorithm is a tree with three kinds of nodes (an output, a query to one oracle of the
  family, a draw of private coins); the type has a Monad instance;
  a bound on the number of queries is a predicate on the tree; the oracles are either fixed or
  sampled lazily from a table, and the output has a law in Mathlib's PMF.
  OComp in ZKCP/Defs.lean is the same tree for that file's one oracle, with the same Monad instance
  and the same bound on queries; there the oracle is fixed or drawn from a measure on all functions,
  and nothing is sampled lazily. That file carries a short form of this credit. The coin node
  draws from n + 1 values, as VCV-io's uniform-selection oracle does at commit afa6593f
  (VCVio/OracleComp/OracleSpec.lean).

  VCV-io is not a dependency:
  no file of this library imports it.
-/
import Rom.OSpec
noncomputable section -- Lean tags what it cannot compile

namespace Rom
variable {S : OSpec} {α β : Type}

/-- An oracle algorithm on a fixed input: a tree. Running time is unbounded; only queries and coins
show. -/
inductive OComp (S : OSpec) (α : Type) : Type
  | pure (a : α) : OComp S α
  | query (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) : OComp S α
  | sample (n : ℕ) (k : Fin (n + 1) → OComp S α) : OComp S α

namespace OComp

def bind : OComp S α → (α → OComp S β) → OComp S β
  | pure a, g => g a
  | query o q k, g => query o q fun r => (k r).bind g
  | sample n k, g => sample n fun r => (k r).bind g

instance : Monad (OComp S) where
  pure := OComp.pure
  bind := OComp.bind

/-- one query, as an algorithm -/
def ask (o : S.ι) (q : S.Dom o) : OComp S (S.Rng o) := query o q pure

/-- at most t queries in all, on every path; a repeated query counts again -/
def QueryBound : OComp S α → ℕ → Prop
  | pure _, _ => True
  | query _ _ _, 0 => False
  | query _ _ k, t + 1 => ∀ r, (k r).QueryBound t
  | sample _ k, t => ∀ r, (k r).QueryBound t

/-- the same algorithm, which also outputs its own trace -/
def withTrace : OComp S α → OComp S (α × Trace S)
  | pure a => pure (a, [])
  | query o q k =>
    query o q fun r => (k r).withTrace.bind fun out => pure (out.1, ⟨o, q, r⟩ :: out.2)
  | sample n k => sample n fun r => (k r).withTrace

/-- the oracles fixed: the law of the output over the coins only -/
def runEager (f : Fam S) : OComp S α → PMF α
  | pure a => PMF.pure a
  | query o q k => (k (f o q)).runEager f
  | sample n k => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).runEager f

/-- lazy sampling from a table: an entry is sampled when it is first queried -/
def runLazy : OComp S α → Table S → PMF (α × Table S)
  | pure a, T => PMF.pure (a, T)
  | query o q k, T =>
      match T o q with
      | some r => (k r).runLazy T
      | none => (PMF.uniformOfFintype (S.Rng o)).bind fun r => (k r).runLazy (T.set o q r)
  | sample n k, T => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).runLazy T

/-- the law of the output under lazily sampled oracles, from the empty table -/
def law (c : OComp S α) : PMF α := (c.runLazy (Table.empty S)).map Prod.fst

end OComp
end Rom
