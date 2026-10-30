-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Reads.lean: CONDITIONAL.

Not shown here. That the input's cells are the matrices' entries (CellsOn), and that the honest
side's list of points is a part of the verifier's (PtsPart): both are hypotheses. ON THE MATRIX OF
THE LOOKUP's PLANES NOTHING IS SAID unless G names it. Nothing is said of an entry at which
Reads.has is false. That the verifier's functions layTables and funsOf return is a hypothesis; so
is that the smallness test's list of matrices has the plan's sizes (hm) and that NM is its length
(hNM). What the lookup has sampled stands under two letters: fo in the honest reads, fo' in the
verifier's list of tables: where G names the matrix of the lookup's planes the two are asked to be
one (hfo), and that they are one at a run is not shown. No example is known. No property is
claimed.

THE HONEST SIDE's READS ARE THE TRUE ENTRIES. The honest side of the sub-protocol K4 computes an
entry of the reads from the cells (readsAt, Johnson/Desc/K4/Honest/Cells.lean). The library says
what a table's entry holds (saysOf, Johnson/Road/FormsKeysMet.lean) and lays that as the true value
of an entry (entryOf, entryTrue: Johnson/Road/K4/EntryTrue.lean). Here: the two agree, read in the
field, wherever the honest side says that the entry's family has its weights.

  getD_map_default, mats_at   the matrices' sizes in the two lists.
  reads_true    an entry of the honest reads, at the place of column c and run number sg (of Fn.len
                rows) of a table of the verifier's list, is what that table says (saysOf).
  has_owned     a place at which Reads.has is true is the place of some table of the list.
  reads_entry   the true entry at such a place is the honest entry.
-/
import Johnson.Road.K4.C.ReadsKit
import Johnson.Road.K4.EntryTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks funsOf matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads matsOf readsAt)
open OnBytes.Road.K4 (entryOf)

variable {Q : K4Pub} {w : K4In} {fo fo' : Forest.Heard} {pt pts : List (String × Array E)}
  {R : Reads} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2}
  {Mm : Mats Cb.Gl.E} {G : ℕ → Prop}

/-- An entry of the image of an array, at the image of the default. -/
theorem getD_map_default {α β : Type} (a : Array α) (f : α → β) (i : ℕ) (d : α) :
    (a.map f).getD i (f d) = f (a.getD i d) := by
  by_cases h : i < a.size
  · exact getD_map_lt a f h (f d) d
  · simp [Array.getD, h]

/-- The rows and the columns of a matrix, in the two lists. -/
theorem mats_at (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (i : ℕ) :
    (matsOf Q).getD i (0, 0) = ((tl.mats.getD i {}).m, (tl.mats.getD i {}).k) := by
  rw [← hm]
  exact getD_map_default tl.mats (fun M => (M.m, M.k)) i {}

/-- **An entry of the honest reads is what its table says.** pt: the honest side's points; pts: the
verifier's; funs: the verifier's list of tables. -/
theorem reads_true {funs : Array HFun} (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsOn G (matsOf Q) w.cell Mm) :
    ∀ Fn ∈ funs, G Fn.mat → ∀ c sg pos, tl.tabAt Fn c sg = some pos → R.has pos = true →
      Reading.gl.val (R.u3 pos) = saysOf Reading.gl Mm Fn c sg := by
  intro Fn hF hGm c sg pos hpos hhas
  obtain ⟨t, ht, phi, hphi, rfl⟩ := funsOf_inv hf hF
  obtain ⟨q, hq, hm'⟩ := List.mem_flatMap.mp ht
  obtain ⟨m, hmq, rfl⟩ := List.mem_map.mp hm'
  obtain ⟨-, -, hc, hsg, rfl⟩ := tailAt_inv tl _ hpos
  have hmk := mats_at (Q := Q) hm m.1
  have hc' : c < (tl.mats.getD m.1 {}).k := hc
  have hsg' : sg < (tl.mats.getD m.1 {}).m / q.1.L := hsg
  have hhas' : R.has (m.2 + (c * ((tl.mats.getD m.1 {}).m / q.1.L) + sg)) = true := by
    rw [← Nat.add_assoc]
    exact hhas
  show Reading.gl.val (R.u3 (m.2 + c * ((tl.mats.getD m.1 {}).m / q.1.L) + sg)) = _
  rw [Nat.add_assoc, reads_sum hR hl hp hq hmq (by rw [hmk]) (by rw [hmk]; exact hc') hsg' hhas'
    (hfo.imp (fun h => named_of_off hl hq hmq (h _ hGm)) id) hphi]
  unfold saysOf
  refine Finset.sum_congr rfl fun j hj' => ?_
  have hjL : j < q.1.L := Finset.mem_range.mp hj'
  have hrow : sg * q.1.L + j < (tl.mats.getD m.1 {}).m := by
    calc sg * q.1.L + j < (sg + 1) * q.1.L := by rw [Nat.succ_mul]; omega
      _ ≤ (tl.mats.getD m.1 {}).m / q.1.L * q.1.L := Nat.mul_le_mul_right _ hsg'
      _ ≤ (tl.mats.getD m.1 {}).m := Nat.div_mul_le_self _ _
  show _ = Reading.gl.val (phi.getD j zeroE) * Mm m.1 (sg * q.1.L + j) c
  rw [hC m.1 hGm (sg * q.1.L + j) c (by rw [hmk]; exact hrow) (by rw [hmk]; exact hc')]

/-- **A place at which the honest side's test is true is the place of some table of the list.** -/
theorem has_owned {funs : Array HFun} (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size) :
    ∀ pos, R.has pos = true →
      ∃ z : HFun × ℕ × ℕ, z.1 ∈ funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some pos := by
  intro pos hhas
  obtain ⟨q, hq, m, hm1, c, sg, hc, hsg, rfl⟩ := place_of_has hR hl hhas
  obtain ⟨phi, -, hmem⟩ := funsOf_mem hf hq
  have hmk := mats_at (Q := Q) hm m.1
  rw [hmk] at hc hsg ⊢
  have hc' : c < (tl.mats.getD m.1 {}).k := hc
  have hsg' : sg < (tl.mats.getD m.1 {}).m / q.1.L := hsg
  have hL : q.1.L ≠ 0 := by
    intro z
    rw [z, Nat.div_zero] at hsg'
    exact Nat.not_lt_zero _ hsg'
  have hin' : m.1 < tl.NM := by
    rw [hNM]
    by_contra hge
    have e0 : tl.mats.getD m.1 {} = {} := by simp [Array.getD, hge]
    rw [e0] at hc'
    exact Nat.not_lt_zero _ hc'
  refine ⟨({ mat := m.1, len := q.1.L, phi := phi, tree := 2, start := m.2 }, c, sg),
    hmem m hm1, ?_⟩
  have e1 := tailAt_some tl { mat := m.1, len := q.1.L, phi := phi, tree := 2, start := m.2 }
    (c := c) (sg := sg) hin' hL hc' hsg'
  rw [e1]
  show some (m.2 + c * ((tl.mats.getD m.1 {}).m / q.1.L) + sg) = _
  rw [Nat.add_assoc]

/-- **The true entry is the honest entry.** iU3, K3: the number of the array of the reads and the
number of its columns. hG: a table that has the place stands on a matrix that G names. At what a
hearing has returned, entryOf at o.funs, o.v.iU3 and o.v.K3 is entryTrue. -/
theorem reads_entry {funs : Array HFun} (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf Q) w.cell Mm) (iU3 K3 : ℕ) {row idx : ℕ}
    (hh : R.has (row * K3 + idx) = true)
    (hG : ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (row * K3 + idx) → G z.1.mat) :
    entryOf Reading.gl tl funs iU3 K3 Mm iU3 row idx = Reading.gl.val (R.u3 (row * K3 + idx)) := by
  classical
  obtain ⟨z, hz, hzp⟩ := has_owned hR hl hf hm hNM _ hh
  have hl' : layTables (tl.mats.map fun M => (M.m, M.k)) (tableAsks Q.P.y Q.P.rd Q.g) 0 =
      some r := by
    rw [hm]
    exact hl
  have hA : Apart tl funs := apart_of_run hl' hf hNM
  rw [reads_true hR hl hf hp hfo hm hC z.1 hz (hG z hz hzp) z.2.1 z.2.2 _ hzp hh]
  show (if iU3 = iU3 then
    (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some (row * K3 + idx)
     then saysOf Reading.gl Mm h.choose.1 h.choose.2.1 h.choose.2.2 else 0) else 0) =
    saysOf Reading.gl Mm z.1 z.2.1 z.2.2
  rw [if_pos rfl]
  have hex : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧
      tl.tabAt x.1 x.2.1 x.2.2 = some (row * K3 + idx) := ⟨z, hz, hzp⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  obtain ⟨e1, e2, e3⟩ := hA _ h1 _ hz _ _ _ _ _ h2 hzp
  rw [e1, e2, e3]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.getD_map_default
#print axioms OnBytes.Road.K4.C.mats_at
#print axioms OnBytes.Road.K4.C.reads_true
#print axioms OnBytes.Road.K4.C.has_owned
#print axioms OnBytes.Road.K4.C.reads_entry
