-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawItems.lean: THE SMALLNESS TEST: THE PLAIN ITEMS OF ITS ROW OF THE TABLE OF
JOINTS, IN A FILE OF THEIR OWN: so that the law on its first half (the draw of the matrix) and the
law on its second half (the claims) can meet at one name.

Each item is a sentence on the carried record and a table of cells A (array, row, column ↦ an
element of the field), which a witness w gives. No signature, no decoder, no message stands in them.
  `TieOf tl A`, `TieAt A s w`: IN FRONT OF THE DRAW: "the tie": there are integers, one for each
    cell of each matrix, each below twice the shift in absolute value; the symbol arrays' cells are
    their packing; every entry of every table of reads is the weighted sum of its stretch of them.
  `SmallAt A s w`: BEHIND THE DRAW: every single equation of the library's list of the smallness
    test's equations (`rowsTail`, OnBytes/Tie/Pv/Tail/EndRows.lean), at the record's own closed list
    of tables, holds at A w. FREE OF THE BATCHING'S DRAW: the list's exponents are not read.
  `small_any`: the number at which the list's exponents start does not matter.
  `small_iff_ledger`: **at the cells of committed entries m (A := Y.cellAt m) it says just that the
    library's ledger of that list (`rowsLedger`) holds on m.**
  `DigitsAt A s w`: BEHIND THE DRAW: the digits are in their tables.
  `Extra s`: two conditions on the record: the shapes fit the matrices; every table lies on the
    third vector of reads.
Definitions, two statements and their proofs.
Limits. DEFINITIONS: nothing is said here of any block. That `SmallAt` and `DigitsAt` behind give
`TieAt` in front, but for an error, is the law of the first half
(Johnson/Desc/First/K8/LawRow.lean).

-/
import Johnson.Desc.First.State
import OnBytes.Tie.Pv.Tail.EndsAtPort
import OnBytes.Tie.Pv.Tail.HostLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port

/-- **The tie**, at a record of the smallness test and a table of cells. -/
def TieOf (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop :=
  ∃ a : ℕ → ℕ → ℕ → ℤ,
    (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
      |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
    (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
      ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
        A (tl.gtTree.getD μ 0) i' c =
          ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
            Cb.Gl.E)) ∧
    (∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
      A (u3Of tl) 0 pos =
        ∑ j ∈ Finset.range Fn.len,
          Reading.gl.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E))

/-- The tie at the carried record: a link is open, and the tie holds at its record. -/
def TieAt {W : Type} (A : W → ℕ → ℕ → ℕ → Cb.Gl.E) (s : S) (w : W) : Prop :=
  ∃ tl, s.tl? = some tl ∧ TieOf tl (A w)

/-- The same in the type of the table's letter. -/
def tieK8 {P W Strs : Type} (A : W → ℕ → ℕ → ℕ → Cb.Gl.E) : ℕ → P × S → Strs → W → Prop :=
  fun _ a _ w => TieAt A a.2 w

/-- **The forms of the run «small» are worth 0**: the reader of the run's forms off the record. -/
def SmallAt {W : Type} (A : W → ℕ → ℕ → ℕ → Cb.Gl.E) (s : S) (w : W) : Prop :=
  ∃ tl, s.tl? = some tl ∧ ∀ r ∈ rowsTail Reading.gl tl tl.funs 0, r.2 (A w) = 0

/-- The number at which the list's exponents start does not matter. -/
theorem small_any (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (pc pc' : ℕ) :
    (∀ r ∈ rowsTail Reading.gl tl tl.funs pc, r.2 A = 0) ↔
      ∀ r ∈ rowsTail Reading.gl tl tl.funs pc', r.2 A = 0 :=
  (rows_iff Reading.gl A tl tl.funs pc).trans (rows_iff Reading.gl A tl tl.funs pc').symm

/-- At the cells of committed entries: every form of the library's ledger of the list holds. -/
theorem small_iff_ledger {J : Type} [Fintype J] (Y : Lay J) (tl : HTailF2) (m : J → Cb.Gl.E)
    (pc : ℕ) :
    (∀ r ∈ rowsTail Reading.gl tl tl.funs 0, r.2 (fun a r c => Y.cellAt m a r c) = 0) ↔
      TWhole.Ledger.Holds (rowsLedger Reading.gl Y tl tl.funs pc) m :=
  (small_any tl _ 0 pc).trans (rowsLedger_holds Reading.gl Y tl tl.funs pc m).symm

/-- **The digits are in their tables.** -/
def DigitsAt {W : Type} (A : W → ℕ → ℕ → ℕ → Cb.Gl.E) (s : S) (w : W) : Prop :=
  ∃ tl, s.tl? = some tl ∧ ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m →
    Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.lo
        (A w tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i)) ∧
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.hi
        (A w tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i))

/-- Two conditions more on the record in the state. -/
def Extra (s : S) : Prop :=
  ∀ tl, s.tl? = some tl → OnBytes.Tie.Pv.Tail.Port.Fits tl ∧ ∀ Fn ∈ tl.funs.toList, Fn.tree = 2

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.small_any
#print axioms VerifiableInference.Desc.First.K8.small_iff_ledger
