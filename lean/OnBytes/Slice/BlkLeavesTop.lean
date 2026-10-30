-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkLeavesTop.lean: the program's pending row on the matrix holds exactly if the claim
on the leaves of the part's key tree holds.

OnBytes/Slice/KeyLeavesFuel.lean proves the statement for the functions over the field
(OnBytes/Slice/KeyLeaves.lean). OnBytes/Slice/BlkLeavesRead.lean and
OnBytes/Slice/BlkLeavesRows.lean show that the program's functions, read in the field, are these.
This file joins them: the statement is on `Wf.pendingRow` at `Lkp.keysOf` and `Wf.eqPlaces`, the
terms that `Wf.pendingOf` forms in a run on a view (OnBytes/Iop/Wf.lean).

How a row of the program is read (`readTRow`): the weight of a row of the matrix is the sum of the
entries of the row's structured vectors at that row's number, read; point, mask form and target are
read entry by entry.

Main definitions: `readTRow`, `padOf`.
Main theorems.
 `read_pendingRow_holds`   the program's pending row, read, holds exactly if the row over the field
                     does.
 `read_natE`, `read_padOf`   what a place of padding holds is the lookup's padding key, read.
 `prog_top`           the statement.

Not claimed. That a run of the program's block on a view forms these terms. What the matrix is.
Nothing on soundness or on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkLeavesRows
import OnBytes.Slice.KeyLeavesFuel

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Slice.PscF (World)

/-- A row of the program on the matrix, read. -/
def readTRow (t : TensorRow) : TRowF :=
  ⟨fun row => (t.g.map fun v => readE (v.entry row)).sum, t.psi.map readE, readForm t.masks,
    readE t.target⟩

/-- The rows that the runs read, in the two forms. -/
theorem rowsIn'_of {l : WfLookup} {R : ℕ} {runs : List WfRun} (pad : GE)
    (h : RowsIn (lkOf l pad) R runs) : RowsIn' l R runs := by
  intro r hr w hw
  refine h r hr (readE (OnBytes.ofF w.1), w.2) ?_
  show _ ∈ (l.digitWeight.map fun w => readE (OnBytes.ofF w)).zipIdx
  rw [map_zipIdx]
  exact List.mem_map.2 ⟨w, hw, rfl⟩

/-- The program's pending row, read, holds exactly if the row over the field does. -/
theorem read_pendingRow_holds (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (claim : Lkp.Keys)
    (e : Array E) (pad : GE) (W : World) (M : ℕ → ℕ → GE)
    (h : RowsIn (lkOf l pad) m.rows p.runs) :
    (readTRow (Wf.pendingRow m l p claim e)).Holds W M m.rows m.kCol ↔
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).Holds W M
        m.rows m.kCol := by
  have hk : m.rows ≤ 2 ^ m.kRow := le_two_pow_ceilLog2 m.rows
  have h' : RowsIn' l (2 ^ m.kRow) p.runs := fun r hr w hw =>
    le_trans (rowsIn'_of pad h r hr w hw) hk
  unfold TRowF.Holds
  have e1 : ∑ r ∈ Finset.range m.rows, ∑ c ∈ Finset.range (2 ^ m.kCol),
      (readTRow (Wf.pendingRow m l p claim e)).g r *
        eqW (readTRow (Wf.pendingRow m l p claim e)).psi c * M r c =
      ∑ r ∈ Finset.range m.rows, ∑ c ∈ Finset.range (2 ^ m.kCol),
        (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).g r *
          eqW (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim)
            (e.toList.map readE)).psi c * M r c := by
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun c _ => ?_
    have hg := read_pendingRow_g m l p claim e pad r
      (lt_of_lt_of_le (Finset.mem_range.1 hr) hk) h'
    have hpsi : (readTRow (Wf.pendingRow m l p claim e)).psi =
        (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).psi :=
      List.map_take
    rw [hpsi]
    exact congrArg (· * _ * _) hg
  have e2 : (readTRow (Wf.pendingRow m l p claim e)).target =
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).target := by
    show readE (subE claim.target (mulE (Wf.coveredSum p e) (OnBytes.ofF l.offset))) = _
    rw [readE_sub, readE_mul, read_coveredSum]
    rfl
  rw [e1, e2]
  rfl

/-! ## What a place of padding holds -/

/-- What a place of padding of a lookup holds, read: the table's row at the padding key's number. -/
def padOf (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ : E) : GE :=
  readE (Lkp.rowAt (Wf.lookupOf id m l) θ l.paddingKey.toNat)

/-- A number below 2 ^ 64 as an element of the program, read. -/
theorem read_natE (n : ℕ) (h : n < 2 ^ 64) : readE (Lkp.natE n) = (n : GE) := by
  unfold Lkp.natE
  rw [readE_ofF, toF_normF]
  unfold toF
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h, map_natCast]

/-- What a place of padding holds is the lookup's padding key, read, if the key's number is a
row of the range table. -/
theorem read_padOf (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ : E)
    (h : l.paddingKey.toNat < 2 ^ l.d) : padOf id m l θ = readE (OnBytes.ofF l.paddingKey) := by
  have h64 : l.paddingKey.toNat < 2 ^ 64 := l.paddingKey.toNat_lt
  have hr : Lkp.rowAt (Wf.lookupOf id m l) θ l.paddingKey.toNat =
      addE (Lkp.natE (l.paddingKey.toNat % 2 ^ l.d)) (mulE (Lkp.natE 0) θ) := by
    unfold Lkp.rowAt
    simp [Wf.lookupOf, h]
  unfold padOf
  rw [hr, readE_add, readE_mul, Nat.mod_eq_of_lt h, read_natE _ h64, read_natE 0 (by decide),
    Nat.cast_zero, zero_mul, add_zero, readE_ofF]
  unfold toF
  rw [map_natCast]

/-- The program's pending row on the matrix, read, holds exactly if the claim on the leaves of the
part's key tree, read, holds: for every matrix, every world of mask entries, every alpha and theta
and every claim whose point has one coordinate for each bit of a key's number. Asked: the program's
public tests on the lookup and the matrix's size. -/
theorem prog_top (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (θ α : E) (W : World)
    (M : ℕ → ℕ → GE) (c : PointClaim) (hl : Wf.lookupOk Wf.fBits l = true)
    (hm : Wf.fitsMatrix m l = true) (hp : l.parts[i]? = some p)
    (hz : c.point.length = m.kCol + p.logPlaces) :
    (readPC c).Holds W (treeMap (m.kCol + p.logPlaces)
        (leafTab (readE α) (key (lkOf l (padOf id m l θ)) M m.kCol p.runs))) ↔
      (readTRow (Wf.pendingRow m l p (Lkp.keysOf (Wf.lookupOf id m l) θ α i c)
        (Wf.eqPlaces m c.point))).Holds W M m.rows m.kCol := by
  have hmem : p ∈ l.parts := List.mem_of_getElem? hp
  have hL : (lkOf l (padOf id m l θ)).dw.length = l.digitWeight.length := List.length_map _
  rw [read_pendingRow_holds m l p _ _ (padOf id m l θ) W M (rowsIn_of _ hL hm hmem), read_keysOf,
    read_eqPlaces]
  exact leaves_top m l id i p _ _ _ _ _ W M (readPC c) hl hm hp hL rfl
    (by rw [← hz]; exact List.length_map _) (covered_of_tests m l id hl hm)

end OnBytes.Slice.Leaves
