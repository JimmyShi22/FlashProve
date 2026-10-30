-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineCnt.lean: bounds on the marked queries of the Fiat-Shamir chains of a batch.
Definitions (words of this library: lean/GLOSSARY.md).

For `Spec.safeChainT0` (Compile/Batch/DisciplineProve.lean). That the programs keep these bounds is
proved in Compile/Batch/DisciplineChain.lean, Compile/Batch/DisciplineJoin.lean,
Compile/Batch/DisciplineChainAll.lean; that they add up, round by round, in
Compile/Batch/DisciplineChainNum.lean.

  `MFb t m`  The marked queries of one Fiat-Shamir query with at most m attempts after the first
             (`fbG`, Compile/Batch/Prover.lean): one to `fb t`, and one to each ghost name
             `fbw t k`, k < m. A bound: the search may end earlier. Without proof-of-work bits: m =
             0.
  `osTry t n`  The oracles of a search whose final attempt has the number n, in the order of the
               attempts. `count_osTry_le`: they are within `MFb t m`, if n ≤ m.
  `MTrees`, `MLo`  The trees of one component, by the list of their depths; one slot in a local
                   round (bounds: a component without a tree has no leaf and no node).
  `jn`, `MCh`  The rounds that are left, with Ns slots, from the phase ph on. `MCh_first`: from the
               start it is `mProveB` (Compile/Batch/SpecDiscipline.lean).

Notation:
  `lam`, `K`: natural numbers; `L`: an `BatchProtocol I X` (Iop/Batch.lean);
  `s`, `A`, `W`: a `Shape`; a `RoundSplits s` (Iop/Batch.lean): the annotation of a shape; a
    `RoundsQueryLayout lam K s A` (Iop/BatchWire.lean): a `WireRB` for each round;
  `ph`: a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`, `shr tk0` or `aft`;
  `dJ`: a natural number; `safe_eachLo` (Compile/Batch/DisciplineChain.lean) has `w.depthJ` there:
    the depth of the tree over a slot's component m_j (`WireRB`, Iop/BatchWire.lean);
  `cnt1 o₀ n` (Compile/Discipline.lean): the count n at the oracle o₀ and 0 elsewhere;
  `cTrees s A W Ns` (Compile/Batch/Counts.lean): leaves (and, as a bound, inner nodes) of all
    trees of one execution with Ns slots, at most;
  `cTry k Ns s A W` (Compile/Batch/Counts.lean): queries to the ghost name fbw t k, that is,
    attempts number k + 1 (from 0), of one execution with Ns slots, at most;
  `joins s A` (Compile/Batch/SpecDiscipline.lean): 1 if the chains of an execution can join (there
    is a shared round), else 0;
  `osB` (Compile/Batch/SpecDiscipline.lean): the oracles with marked queries (without the ghost
    names `fbw t k`: `osBG`).
-/
import Compile.Batch.Discipline
noncomputable section -- Lean tags what it cannot compile

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem fb_mem_osB (t : Tag) : OracleName.fb t ∈ osB := by cases t <;> decide
theorem g_mem_osB (t : Tag) : OracleName.g t ∈ osB := by cases t <;> decide
/-- the rules allow a marked query to fb t (`g_mk`, `fbw_mk`: to g t, to a ghost name) -/
theorem fb_mk (t : Tag) : OracleName.fb t ∈ osB ∨ ∃ t' k, OracleName.fb t = OracleName.fbw t' k := Or.inl (fb_mem_osB t)
theorem g_mk (t : Tag) : OracleName.g t ∈ osB ∨ ∃ t' k, OracleName.g t = OracleName.fbw t' k := Or.inl (g_mem_osB t)
theorem fbw_mk (t : Tag) (j : ℕ) : OracleName.fbw t j ∈ osB ∨ ∃ t' k, OracleName.fbw t j = OracleName.fbw t' k :=
  Or.inr ⟨t, j, rfl⟩

/-- The marked queries of one Fiat-Shamir query with at most m attempts after the first (a bound).
-/
def MFb (t : Tag) (m : ℕ) : OracleName → ℕ
  | .fb t' => if t' = t then 1 else 0
  | .fbw t' k => if t' = t then (if k < m then 1 else 0) else 0
  | _ => 0

/-- the oracles of the attempts 0, .., n, in this order -/
def osTry (t : Tag) (n : ℕ) : List OracleName := OracleName.fb t :: (List.range n).map (OracleName.fbw t)

theorem osTry_succ (t : Tag) (n : ℕ) : osTry t (n + 1) = osTry t n ++ [OracleName.fbw t n] := by
  unfold osTry
  rw [List.range_succ, List.map_append]
  rfl

theorem osTry_nodup (t : Tag) (n : ℕ) : (osTry t n).Nodup := by
  refine List.nodup_cons.mpr ⟨fun h => ?_, (List.nodup_range).map fun a b h => (OracleName.fbw.inj h).2⟩
  obtain ⟨_, _, e⟩ := List.mem_map.mp h
  cases e

theorem mem_osTry {t : Tag} {n : ℕ} {o : OracleName} :
    o ∈ osTry t n ↔ o = OracleName.fb t ∨ ∃ k < n, o = OracleName.fbw t k := by
  unfold osTry
  rw [List.mem_cons, List.mem_map]
  exact or_congr_right ⟨fun ⟨k, hk, e⟩ => ⟨k, List.mem_range.mp hk, e.symm⟩,
    fun ⟨k, hk, e⟩ => ⟨k, List.mem_range.mpr hk, e.symm⟩⟩

/-- The attempts of a search are within the bound, if n ≤ m. -/
theorem count_osTry_le (t : Tag) {n m : ℕ} (h : n ≤ m) (o : OracleName) :
    (osTry t n).count o ≤ MFb t m o := by
  by_cases ho : o ∈ osTry t n
  · rw [List.count_eq_one_of_mem (osTry_nodup t n) ho]
    rcases mem_osTry.mp ho with rfl | ⟨k, hk, rfl⟩
    · simp [MFb]
    · simp [MFb, lt_of_lt_of_le hk h]
  · rw [List.count_eq_zero_of_not_mem ho]
    exact Nat.zero_le _

/-- the queries that the trees of the depths ds cost (a bound): no tree, no query -/
noncomputable def MTrees (lam K : ℕ) (L : BatchProtocol I X) (ds : List ℕ) : OracleName → ℕ := fun o =>
  cnt1 (S := spec lam K L) OracleName.leaf (ds.map (2 ^ ·)).sum o +
    cnt1 (S := spec lam K L) OracleName.node (ds.map (2 ^ ·)).sum o

theorem MTrees_cons (depth : ℕ) (ds : List ℕ) (o : OracleName) :
    MTrees lam K L (depth :: ds) o =
      (cnt1 (S := spec lam K L) OracleName.leaf (2 ^ depth) o +
        cnt1 (S := spec lam K L) OracleName.node (2 ^ depth) o) + MTrees lam K L ds o := by
  unfold MTrees
  rw [List.map_cons, List.sum_cons]
  unfold cnt1
  split <;> split <;> omega

theorem MTrees_nil (o : OracleName) : MTrees lam K L [] o = 0 := by
  simp [MTrees, cnt1]

/-- the queries of one slot in a local round (a bound); m: the attempts after the first -/
def MLo (lam K : ℕ) (L : BatchProtocol I X) (t : Tag) (dJ m : ℕ) : OracleName → ℕ := fun o =>
  cnt1 (S := spec lam K L) OracleName.leaf (2 ^ dJ) o +
    cnt1 (S := spec lam K L) OracleName.node (2 ^ dJ) o + MFb t m o

/-- in the phases first and loc: 1 if a shared round is left (`joins`), else 0; a bound -/
def jn : PhT → (s : Shape) → RoundSplits s → ℕ
  | .first, s, A => joins s A
  | .loc, s, A => joins s A
  | _, _, _ => 0

/-- The marked queries of the rounds that are left (bounds), with Ns slots, from the phase ph on. At
`leaf` and `node`: `cTrees`; at `rleaf`, `rnode` and `g t`: Ns if `jn` is 1, else 0; at `fb t`: Ns +
1 for each round that is left (each slot's query and the shared one: both are counted whatever the
kind of the round); at `fbw t k`: `cTry k`; elsewhere 0. -/
def MCh (t : Tag) (ph : PhT) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (Ns : ℕ) : OracleName → ℕ
  | .leaf => cTrees s A W Ns
  | .node => cTrees s A W Ns
  | .rleaf => jn ph s A * Ns
  | .rnode => jn ph s A * Ns
  | .fb t' => if t' = t then (Ns + 1) * s.length else 0
  | .fbw t' k => if t' = t then cTry k Ns s A W else 0
  | .g t' => if t' = t then jn ph s A * Ns else 0
  | _ => 0

theorem MCh_first (t : Tag) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (Ns : ℕ) :
    MCh t PhT.first s A W Ns = mProveB t s A W Ns := by
  funext o
  cases o <;> rfl

end Compile.Batch.Disc
