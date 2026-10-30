-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecHop.lean: the bound of the game hop of deferred programming, as a parameter.
Definitions and their monotonicity only. (Words of this library: lean/GLOSSARY.md.)

In the proof of index privacy one game hop replaces the oracles' answers to the honest party's
queries on secret inputs by fresh ones (deferred programming). There are two bounds for it: one with
a query bound for each oracle (Rom/Defer.lean) and one for a total query bound
(Rom/SpecDeferTotal.lean). So that no form of the scheme is treated twice, the bound is a variable
h.

  `HopBAt`   h t n bounds the hop (the distance of mode R and mode I, Rom/Defer.lean), against an
             adversary with t queries in all, for every challenger whose runs in mode I obey the
             rules of deferred programming and keep these counts (`Rom.HopCost`,
             Rom/SpecHopCost.lean; `Rom.DSt.Within`): at most `eAllB` ordinary and at most m n o
             marked queries to each oracle o; marked queries only at the oracles `osBG`; every
             charged token at least as long as `rulesB` says
  `HopB`   the same at m = `mAllB`: the counts of one setup and n batches of the scheme that hashes
           every slot. So one hypothesis serves all forms of the scheme with these counts. The same
           by requests: `HopU` (Compile/Batch/PubProgMainBGr.lean). For a total query bound:
           Compile/Batch/HopTot.lean
  `zetaBGen`   ζ with h in place of the hash terms: t n ↦ the overrun term (p.leaves * `binTail` n
               p.leaves p.s1; what an overrun is: Prob/Tail.lean) + h t n + the terms of the record
               of protocols (M.zT + p.leaves * M.zL + n * (L.maxBatchSize * M.zO))

Notation: `t`, `n`: natural numbers: t: in `Rom.HopCost` (Rom/SpecHopCost.lean): `A.TotalBound t N`;
n: "one setup and n batches" (the doc comment of `HopBAt`); `m`: of type `ℕ → OracleName → ℕ`; `h`, ζ: of
type `ℕ → ℕ → ℝ≥0∞`; ζ: the last argument of `Gen.IsZKCPArgWith` (ZKCP/Gen.lean); `M`: an `LH.Nums`
(Iop/InteractiveOracleProof.lean): "All numbers of the interface"; `M.zT`, `M.zL`, `M.zO`: in `ℝ≥0∞`: the arguments
of `L.Hiding` in `BatchProtocol.Props` (Iop/Batch.lean); `p`: a `Params` (Compile/Star.lean), `p.s1` a field
of it; `p.leaves`: `p.M + 1` (Compile/Spec.lean); `L.maxBatchSize`: "the number of slots" (`BatchProtocol`,
Iop/Batch.lean).

Limits: nothing about any scheme.
-/
import Compile.Batch.SpecGrind
import Compile.Batch.SpecDiscipline
import Rom.SpecHopCost

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- h bounds the game hop for every challenger whose runs in mode I obey the rules and make at most
m n o marked queries to o in one setup and n batches (the ordinary queries, the lengths and the
oracles are those of the compiled scheme) -/
def HopBAt {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (m : ℕ → OracleName → ℕ) (h : ℕ → ℕ → ℝ≥0∞) :
    Prop :=
  ∀ n, Rom.HopCost (spec lam W.K L) (Disc.eAllB W p n) (m n) (Disc.rulesB W.K L lam p).bits
    (Disc.osBG (maxMoreB W)) fun t => h t n

theorem HopBAt.mono {L : BatchProtocol I X} {W : QueryLayout lam L} {p : Params} {m : ℕ → OracleName → ℕ}
    {h h' : ℕ → ℕ → ℝ≥0∞} (hh : HopBAt W p m h) (hle : ∀ t n, h t n ≤ h' t n) : HopBAt W p m h' :=
  fun n => (hh n).mono fun t => hle t n

/-- fewer marked queries: the same bound -/
theorem HopBAt.anti {L : BatchProtocol I X} {W : QueryLayout lam L} {p : Params} {m m' : ℕ → OracleName → ℕ}
    {h : ℕ → ℕ → ℝ≥0∞} (hm : ∀ n o, m n o ≤ m' n o) (hh : HopBAt W p m' h) : HopBAt W p m h :=
  fun n => Rom.HopCost.anti (fun _ => le_rfl) (hm n) (fun _ => le_rfl) (Finset.Subset.refl _) (hh n)

/-- `HopBAt` at the counts of the scheme that hashes every slot: one setup and n batches of maxBatchSize slots
-/
def HopB {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (h : ℕ → ℕ → ℝ≥0∞) : Prop :=
  HopBAt W p (Disc.mAllB W p) h

theorem HopB.mono {L : BatchProtocol I X} {W : QueryLayout lam L} {p : Params} {h h' : ℕ → ℕ → ℝ≥0∞}
    (hh : HopB W p h) (hle : ∀ t n, h t n ≤ h' t n) : HopB W p h' :=
  HopBAt.mono hh hle

/-- ζ with h in place of the hash terms -/
def zetaBGen (L : BatchProtocol I X) (p : Params) (M : LH.Nums) (h : ℕ → ℕ → ℝ≥0∞) :
    ℕ → ℕ → ℝ≥0∞ := fun t n =>
  p.leaves * binTail n p.leaves p.s1 + h t n + (M.zT + p.leaves * M.zL + n * (L.maxBatchSize * M.zO))

end Compile.Batch
