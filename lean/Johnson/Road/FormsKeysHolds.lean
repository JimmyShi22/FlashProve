-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysHolds.lean: if every table of the reads holds what it says of its matrix, the
reads are true of the cells that are read in the matrices' entries.

The theorems on the forms of the lookup's segments have one hypothesis on the world: TrueAt, which
Johnson/Road/FormsKeysPoint.lean shows to be SummedAt: each entry of six families of tables is a sum
of cells under the verifier's own weights. There the cells are free. Here they are cellsAt y M, the
cells read in the entries M of the sub-proof's matrices (Johnson/Road/FormsKeysMat.lean; M is any
function), and SummedAt follows from Holds: each table's entry for a column and a run of rows is the
sum of the column's entries in that run under the table's weights.

What is compared with what: the verifier's numbering of the entries of a family of tables, as its
forms use it (entry e of the family), with its numbering in the smallness test (part, column, run of
rows). The record Laid1 says how the two meet for one family.

Main definitions: Laid1.
Main theorems: short_cell, long_cell (two identities on indices); short_of_holds, long_of_holds (one
family); summed_of_holds (the six); holds_zero.

What is not claimed. That the families of the verifier's layout meet Laid1 is shown in
Johnson/Road/FormsKeysTab.lean, not here. The verifier never tests Holds (see
Johnson/Road/FormsKeysMat.lean). The program does not import this file.
-/
import Johnson.Road.FormsKeysMat
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff HFun HTailF2 eqTab longPhi)
open OnBytes.Model.Layer (Env Lay)

/-! ## Two identities on indices -/

/-- The number (p k + c) n + s, with c < k and s < n, taken apart. -/
theorem split_entry {p k c n s : ℕ} (hc : c < k) (hs : s < n) :
    ((p * k + c) * n + s) / n = p * k + c ∧ ((p * k + c) * n + s) % n = s ∧
      (p * k + c) / k = p ∧ (p * k + c) % k = c := by
  have hn : 0 < n := by omega
  have hk : 0 < k := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hs, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  · rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt hc, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

section Cells

variable {K : Type} (y : Lay) (M : Mats K) (mat : ℕ)

/-- The cell of feature (p k + c) fc + s, with c a column of a part and s below the features of a
column: it stands in part p, column c, row s T + i. -/
theorem short_cell {p c s : ℕ} (hc : c < colsM y mat) (hs : s < fcM y mat) (i : ℕ) :
    cellsAt y M mat ((p * colsM y mat + c) * fcM y mat + s) i =
      M (firstM y mat + p) (s * y.T + i) c := by
  obtain ⟨e1, e2, e3, e4⟩ := split_entry (p := p) hc hs
  unfold cellsAt
  rw [e1, e2, e3, e4]

/-- The cell of feature b S + r, where b = (p k + c) n + s is the number of a block of S features,
a column holds n blocks, and r < S: it stands in part p, column c, row (s S + r) T + i. -/
theorem long_cell {S n p c s r : ℕ} (hfc : fcM y mat = n * S) (hc : c < colsM y mat) (hs : s < n)
    (hr : r < S) (i : ℕ) :
    cellsAt y M mat (((p * colsM y mat + c) * n + s) * S + r) i =
      M (firstM y mat + p) ((s * S + r) * y.T + i) c := by
  have e : ((p * colsM y mat + c) * n + s) * S + r =
      (p * colsM y mat + c) * fcM y mat + (s * S + r) := by
    rw [hfc]
    ring
  have hlt : s * S + r < fcM y mat := by
    rw [hfc]
    calc s * S + r < s * S + S := by omega
      _ = (s + 1) * S := by ring
      _ ≤ n * S := Nat.mul_le_mul_right S hs
  rw [e, short_cell y M mat hc hlt]

end Cells

/-! ## One family of tables -/

section Family

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- How the two numberings of the entries of one family of tables meet. The family begins at entry
tb of the reads; it belongs to the matrix with the kit's number mat; its tables have runs of L rows
and the weights phi; a column has n runs. For every entry e that the forms can name (U3at returns a
form) there are a part p, a column c and a run s with e = (p k + c) n + s; the form is worth the
hidden value at the place tb + e of the array of reads; the table of part p stands in the verifier's
list of tables funs; and the smallness test has that very place for its column c and run s. -/
def Laid1 (v : Env) (tl : HTailF2) (funs : Array HFun) (tb mat L n : ℕ) (phi : Array E) : Prop :=
  ∀ e a, v.U3at tb e = some a → ∃ p c s start, c < colsM v.y mat ∧ s < n ∧
    e = (p * colsM v.y mat + c) * n + s ∧
    a.value ρ W = W.entry v.iU3 ((tb + e) / v.K3) ((tb + e) % v.K3) ∧
    ({ mat := firstM v.y mat + p, len := L, phi := phi, tree := 2, start := start } : HFun) ∈
      funs ∧
    tl.tabAt { mat := firstM v.y mat + p, len := L, phi := phi, tree := 2, start := start } c s =
      some (tb + e)

variable {ρ W} {v : Env} {tl : HTailF2} {funs : Array HFun} {M : Mats K}

/-- A family of short tables: runs of T rows, as many in a column as it has features. If all tables
of the list hold, entry e of the family is the sum of the cells of feature e under the table's
weights. -/
theorem short_of_holds (H : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) {tb mat : ℕ}
    {phi : Array E} (L1 : Laid1 ρ W v tl funs tb mat v.y.T (fcM v.y mat) phi) {e : ℕ} {a : Aff}
    (h : v.U3at tb e = some a) :
    a.value ρ W = ∑ i ∈ range v.y.T, ρ.val (phi.getD i zeroE) * cellsAt v.y M mat e i := by
  obtain ⟨p, c, s, start, hc, hs, he, hv, hm, ht⟩ := L1 e a h
  rw [hv, H _ hm c s _ ht]
  refine sum_congr rfl fun i _ => ?_
  rw [he, short_cell v.y M mat hc hs]

/-- A family of long tables: runs of S T rows, the rows of a block of S features; a column holds n
blocks. If all tables of the list hold, entry b of the family is the sum of the cells of the
features b S + r, r < S, under the table's weights, which are numbered r T + i. -/
theorem long_of_holds (H : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) {tb mat S n : ℕ}
    {phi : Array E} (hfc : fcM v.y mat = n * S) (L1 : Laid1 ρ W v tl funs tb mat (S * v.y.T) n phi)
    {b : ℕ} {a : Aff} (h : v.U3at tb b = some a) :
    a.value ρ W = ∑ r ∈ range S, ∑ i ∈ range v.y.T,
      ρ.val (phi.getD (r * v.y.T + i) zeroE) * cellsAt v.y M mat (b * S + r) i := by
  obtain ⟨p, c, s, start, hc, hs, he, hv, hm, ht⟩ := L1 b a h
  rw [hv, H _ hm c s _ ht]
  show ∑ j ∈ range (S * v.y.T), _ = _
  rw [sum_blocks]
  refine sum_congr rfl fun r hr => sum_congr rfl fun i _ => ?_
  rw [he, long_cell v.y M mat hfc hc hs (mem_range.mp hr)]
  have e2 : s * (S * v.y.T) + (r * v.y.T + i) = (s * S + r) * v.y.T + i := by ring
  show _ * M _ (s * (S * v.y.T) + (r * v.y.T + i)) c = _
  rw [e2]

/-- The six families. If all tables of the verifier's list hold what they say of the matrices M, and
each of the six families meets Laid1, then the entries of the six families are sums, under the
verifier's own weights, of the cells that are read in the entries of M. -/
theorem summed_of_holds (H : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) {Z zt : Array E}
    (hT : v.y.T = 2 ^ zt.size)
    (LL : ∀ p ∈ [("af" ++ "@" ++ "Z", 0), ("qa" ++ "@" ++ "Z", 3), ("xbI" ++ "@" ++ "Z", 4),
      ("xbO" ++ "@" ++ "Z", 5)], ∀ tb, v.tabAt p.1 = some tb → ∃ n,
        fcM v.y p.2 = n * 2 ^ v.y.ls ∧
        Laid1 ρ W v tl funs tb p.2 (2 ^ v.y.ls * v.y.T) n (longPhi Z v.y.ls zt.size))
    (LS : ∀ p ∈ [("ad" ++ "@" ++ "zt", 1), ("ar" ++ "@" ++ "zt", 2)], ∀ tb,
      v.tabAt p.1 = some tb → Laid1 ρ W v tl funs tb p.2 v.y.T (fcM v.y p.2) (eqTab zt)) :
    SummedAt ρ W v (cellsAt v.y M) Z zt := by
  refine ⟨fun p hp tb htb b a hba => ?_, fun p hp tb htb φ a hφ => ?_⟩
  · obtain ⟨n, hfc, L1⟩ := LL p hp tb htb
    rw [long_of_holds H hfc L1 hba, hT]
  · rw [short_of_holds H (LS p hp tb htb) hφ, hT]

/-- The hypothesis that all tables hold can be met: with all entries of the matrices 0, in a world
in which every hidden value is 0, every table holds. This shows no more than that the hypothesis is
not empty. -/
theorem holds_zero (ρ : Reading K) (tl : HTailF2) (iU3 K3 : ℕ) (Fn : HFun) :
    Holds ρ ⟨fun _ => 0, fun _ _ _ => 0⟩ tl iU3 K3 (fun _ _ _ => 0) Fn := by
  intro c sg pos _
  exact (sum_eq_zero fun j _ => mul_zero _).symm

end Family

#print axioms short_cell
#print axioms long_cell
#print axioms short_of_holds
#print axioms long_of_holds
#print axioms summed_of_holds
#print axioms holds_zero

end OnBytes.Road
