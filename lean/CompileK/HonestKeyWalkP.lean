-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyWalkP.lean: what the honest prover of the compiled scheme asks on one batch,
oracle name by oracle name, on every path, at any wire: rounds may have a search for a nonce.

This file is about the cost of proving: upper bounds on the number of oracle queries of the honest
prover on one batch, where rounds may have proof of work.
One definition and statements (the proofs: CompileK/HonestKeyWalkPProofs.lean). The analogue of
CompileK/HonestKeyWalk.lean, whose counts `hkSlot`, `hkShared` it uses, for the prover with free
empty slots (`PU`, Compile/Batch/StarU.lean). Generic: any interface, any wire: no hypothesis on
them beside whatever the arguments hold as proofs (among them `WireRB.pt`, Iop/BatchWire.lean: every
round's oracle part is a string that is read symbol by symbol: `Round.IsPoint`, Iop/Shape.lean).
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A price u : OracleName → ℕ is a weight on oracle names; `c.CostBound u t` (Rom/Cost.lean): on every path of
c the prices of its queries add up to at most t.

Main names:
  `hkPro W u n`: the shared part of one execution of the interface's batch protocol (`L.onlineBatch`) for
    the N slots + n · (one slot with a request).
  `Spec.honestKey_costP`: `(PU W WP p k b).CostBound u (hkPro W u b.length)` for every price u on
    names, every key k, every batch b.
  `Spec.honestKey_typedP`: the typed count (`hkPro W (fun _ => 1) b.length`): a query counts 1, a
    long answer once.
  `Spec.honestKey_stringsP`: over one oracle of λ > 0 bits, for every coding m: the prover of
    `schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))` on a batch b asks at most
    `hkPro W (blk W.K) b.length` strings: a chain query, a failed try too, costs W.K + 1 of them.
  `Spec.honestKey_sumP`: the typed count is the library's sum (`cPUW`) at "a failed try 1, a chain
    query 1" (Compile/Batch/OneCallCostR.lean), so that its closed upper bound (`cPUW_le`,
    Compile/Batch/OneCallCostClosed.lean) serves.

Limits: upper bounds on every path: the worst case over the oracle: every search runs to its cap. An
empty slot costs nothing but its share of the request tree's vertices.
This file says nothing on a lower bound, nothing on the value of any number, and nothing on the
mean. The key k is any key: this file says nothing on what the prover puts out. A component without
a tree is charged a tree of its depth. A query counts as one however long its string.

Terms: lean/GLOSSARY.md: chain query, coding, free empty slots, interface, proof of work, request
tree, slot, string (in the row of `Spec.honestKey_stringsP`), tries, typed query, wire.
-/
import CompileK.HonestKeyWalk

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.OneCall (cPUW)

/-- The count for the honest prover on a batch with n requests, at the prices u. -/
def hkPro {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (u : OracleName → ℕ) (n : ℕ) : ℕ :=
  hkShared u .onl L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh .first +
    n * hkSlot u .onl L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh .first

namespace Spec

/-- Name by name. -/
def honestKey_costP : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (u : OracleName → ℕ)
      (k : ISK lam L) (b : List (X × Unit)),
    (PU W WP p k b).CostBound u (hkPro W u b.length)

/-- The typed count. -/
def honestKey_typedP : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : ISK lam L) (b : List (X × Unit)),
    (PU W WP p k b).QueryBound (hkPro W (fun _ => 1) b.length)

/-- In strings, over one oracle, for every coding, if 0 < λ. -/
def honestKey_stringsP : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Wn : Type)
      (m : OracleCoding (spec lam W.K L) lam) (k : ISK lam L) (b : List (X × Wn)),
    0 < lam →
    ((schemeOverOneHashFunction m (Gen.withW Wn (argBKE W WP p))).P k b).QueryBound (hkPro W (blk W.K) b.length)

/-- States: the typed count is the library's sum at "a failed try 1, a chain query 1". -/
def honestKey_sumP : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (n : ℕ),
    hkPro W (fun _ => 1) n = cPUW W 1 (fun _ _ => 1) n

end Spec
end Compile.Batch
