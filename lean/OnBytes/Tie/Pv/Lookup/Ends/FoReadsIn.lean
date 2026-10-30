-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoReadsIn.lean.
The law of the reads, from the relation before the smallness test's round.

The calls' theorems ask of a world the law of the reads: Fo.ReadsAll
(OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean), at all tables of
a sub-proof, and Fo.ReadsLaw (OnBytes/Tie/Pv/Lookup/Port/FoReads.lean), at the three tables of a
lookup's planes. The relation
before the smallness test's round says, table by table: for each column c and each stretch sg of len
rows, entry start + c * (m / len) + sg of the vector of reads is the sum of the cells of that
stretch of that column under the table's weights.

States:
  readsAll_of_reads: that clause, in plain letters (u3: the vector of reads; phi n: the weights of
    table number n; a: the cells, by matrix, column and row), gives Fo.ReadsAll with the cells a, if
    u3 is read in the world's entries at the places that the tables name, and phi n is the weights
    of the n-th table of the list, read.
  PlaneTab ρ mats funs cellM f t w h lm ν: the table f is a table of a lookup's planes: a member of
    the list, in the vector of reads, with the first entry t, 2^lm rows in one stretch, at least the
    planes' columns, the weights w, on a matrix whose cells are the lookup's cells under ν.
  readAt_of_funRead: at such a table Fo.FunRead gives Fo.ReadAt in the planes' terms.
  readsLaw_of_readsAll: Fo.ReadsAll and three such tables, with the weights of the two points and
    the powers of two, give Fo.ReadsLaw.
Limits: the clause is a hypothesis here, in plain letters: no statement of this file ties it to a
relation of the library. It is meant of the stage before the matrix of the smallness test is drawn,
and is reached from what the one equation gives only by a count over that draw, which is not made
here. PlaneTab is a
hypothesis on the tables.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The law of the reads at all tables, from the clause on the vector of reads. -/
theorem readsAll_of_reads (mats : Array TMat) (funs : Array HFun) (entry : ℕ → ℕ → ℕ → K)
    (iU3 K3 : ℕ) (u3 : ℕ → K) (phi : ℕ → ℕ → K) (a : ℕ → ℕ → ℕ → K)
    (hu : ∀ f ∈ funs.toList, f.tree = 2 → ∀ c < (mats.getD f.mat {}).k,
      ∀ sg < (mats.getD f.mat {}).m / f.len,
        u3 (f.start + c * ((mats.getD f.mat {}).m / f.len) + sg) =
          u3Val entry iU3 K3 (f.start + c * ((mats.getD f.mat {}).m / f.len) + sg))
    (hphi : ∀ n f, funs.toList[n]? = some f → ∀ j < f.len,
      phi n j = ρ.val (f.phi.getD j zeroE))
    (h : ∀ n f, funs.toList[n]? = some f → f.tree = 2 → ∀ c < (mats.getD f.mat {}).k,
      ∀ sg < (mats.getD f.mat {}).m / f.len,
        u3 (f.start + c * ((mats.getD f.mat {}).m / f.len) + sg) =
          ∑ j ∈ range f.len, phi n j * a f.mat c (sg * f.len + j)) :
    ReadsAll ρ mats funs entry iU3 K3 fun m r c => a m c r := by
  intro f hf ht col hcol
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hf
  have hpos : 0 < (mats.getD f.mat {}).m / f.len := by
    rcases Nat.eq_zero_or_pos ((mats.getD f.mat {}).m / f.len) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcol
      exact absurd hcol (Nat.not_lt_zero _)
    · exact h0
  have hc : col / ((mats.getD f.mat {}).m / f.len) < (mats.getD f.mat {}).k :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
  have hsg : col % ((mats.getD f.mat {}).m / f.len) < (mats.getD f.mat {}).m / f.len :=
    Nat.mod_lt _ hpos
  have e : f.start + col = f.start + col / ((mats.getD f.mat {}).m / f.len) *
      ((mats.getD f.mat {}).m / f.len) + col % ((mats.getD f.mat {}).m / f.len) := by
    rw [Nat.add_assoc, Nat.div_add_mod']
  rw [e, ← hu f hf ht _ hc _ hsg, h n f hn ht _ hc _ hsg]
  exact sum_congr rfl fun j hj => by rw [hphi n f hn j (mem_range.mp hj)]

/-- A table of a lookup's planes. -/
structure PlaneTab (mats : Array TMat) (funs : Array HFun) (cellM : ℕ → ℕ → ℕ → K) (f : HFun)
    (t : ℕ) (w : ℕ → K) (h : FoNums.Sh) (lm : ℕ) (ν : Pl → K) : Prop where
  mem : f ∈ funs.toList
  tree : f.tree = 2
  start : f.start = t
  len : f.len = 2 ^ lm
  one : (mats.getD f.mat {}).m / f.len = 1
  cols : planeCols h lm ≤ (mats.getD f.mat {}).k
  phi : ∀ j < 2 ^ lm, ρ.val (f.phi.getD j zeroE) = w j
  cell : ∀ r < 2 ^ lm, ∀ c < planeCols h lm, cellM f.mat r c = ν (.cell r c)

/-- At a table of the planes the law of the reads gives the law in the planes' terms. -/
theorem readAt_of_funRead {mats : Array TMat} {funs : Array HFun} {cellM : ℕ → ℕ → ℕ → K}
    {f : HFun} {t : ℕ} {w : ℕ → K} {h : FoNums.Sh} {lm : ℕ} {ν : Pl → K}
    (T : PlaneTab ρ mats funs cellM f t w h lm ν) {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ}
    (hf : FunRead ρ mats entry iU3 K3 cellM f) :
    ReadAt entry iU3 K3 t w (fun r c => ν (.cell r c)) (2 ^ lm) (planeCols h lm) := by
  intro col hcol
  have e := hf col (by rw [T.one, Nat.mul_one]; exact lt_of_lt_of_le hcol T.cols)
  rw [T.start, T.one, T.len] at e
  rw [e]
  refine sum_congr rfl fun r hr => ?_
  show ρ.val (f.phi.getD r zeroE) * cellM f.mat (col % 1 * 2 ^ lm + r) (col / 1) =
    w r * ν (.cell r col)
  rw [T.phi r (mem_range.mp hr), Nat.mod_one, Nat.zero_mul, Nat.zero_add, Nat.div_one,
    T.cell r (mem_range.mp hr) col hcol]

/-- The law of the reads at the three tables of the planes. -/
theorem readsLaw_of_readsAll {mats : Array TMat} {funs : Array HFun} {cellM : ℕ → ℕ → ℕ → K}
    {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ} (hA : ReadsAll ρ mats funs entry iU3 K3 cellM)
    {h : FoNums.Sh} {lm : ℕ} {zb0 zb1 : List K} {ν : Pl → K} {f0 f1 fP : HFun} {tB0 tB1 tP : ℕ}
    (T0 : PlaneTab ρ mats funs cellM f0 tB0 (fun r => (phiBK h lm zb0).getD r 0) h lm ν)
    (T1 : PlaneTab ρ mats funs cellM f1 tB1 (fun r => (phiBK h lm zb1).getD r 0) h lm ν)
    (TP : PlaneTab ρ mats funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) h lm ν) :
    ReadsLaw h lm zb0 zb1 ν entry iU3 K3 tB0 tB1 tP :=
  ⟨readAt_of_funRead ρ T0 (hA f0 T0.mem T0.tree), readAt_of_funRead ρ T1 (hA f1 T1.mem T1.tree),
    readAt_of_funRead ρ TP (hA fP TP.mem TP.tree)⟩

end
end Fo
