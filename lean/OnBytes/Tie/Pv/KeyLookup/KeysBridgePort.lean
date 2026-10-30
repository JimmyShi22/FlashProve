-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/KeysBridgePort.lean: the described lookup's end claim on a part's keys and
the pending row that the program's caller makes are one affine form in the matrix, for all
challenges and all matrices.

The end claim is the library's `MCl.Holds` (Cb/Ld/LdLkpTree.lean): the extension of all 2^v keys of
a part at a point, plus a mask form, is a target. The pending row is `Wf.pendingRow` at `Lkp.keysOf`
(OnBytes/Iop/Wf.lean, OnBytes/Iop/Lkp.lean). Cb/Pv/KeyLookup/KeysBridge.lean has the identities on
extensions with a public padding value; this file ties them to the program's records.

Letters. m, l, id, i, p: the matrix's size, the lookup, the message's number, and part number i,
which is p: the program's own records. v := m.kCol + p.logPlaces. GE is Cb.Gl.E. L : `Leaves.LkF`:
the offset, what a place of padding holds, and the digits' weights, in the field. M: the matrix by
row and column. `Leaves.key L M m.kCol p.runs b` (OnBytes/Slice/KeyLeaves.lean): key number b as a
function of the matrix. c: the program's claim on the leaves alpha - key: a point listed with bit t
at place t, a mask form, a value. cl : `MCl GE N`: the described lookup's claim, tied to c by:
`lowPt v cl.pt` is c's point (the library lists the top bit first), and cl.tg = alpha - c's value.
`covP runs u`: place u is covered by a run. `padB kCol runs b`: key number b stands at a place that
no run covers.
  `eqW_eq_eqLow`   the equality vector by a list (`Leaves.eqW`, OnBytes/Slice/KeyLeaves.lean) is
                   `eqLow` of KeysBridge.lean.
  `ext_eq_sum`   ext v f cl.pt = Σ_j Leaves.eqW (lowPt v cl.pt) j * f j.
  `pendingF_form`   over the field: (the pending row's value on M) - (its target) = Σ_j eqW point j
                   * key j - (alpha - value).
  `claim_form`   so: (the pending row's value on M) - (its target) = ext v key cl.pt - cl.tg, for
                   every M.
  `key_pad`, `key_cov`   `Leaves.key` is L.pad at the places of `padB`, and L.off + (a sum that is
                   linear in M) at the others.
  `pending_target`   the pending row's target = cl.tg - L.pad * padW - L.off * covW (the sums of
                   KeysBridge.lean at `padB`).
  `prog_row`   the program's pending row, read (`readE`) and cut at the matrix's rows, is that row
                   over the field; its column point and mask form are written out.
  `prog_form`   `claim_form` for the program's row.
  `claim_iff_pending`   cl.Holds v key μ exactly if the program's pending row, read, holds of M in
                   the world W, where ⟨cl.mf, μ⟩ = -(c's mask form in W).
Under: the program's own public tests `Wf.lookupOk`, `Wf.fitsMatrix`; l.parts[i]? = some p; the
point has v coordinates; the tie of cl to c.
What is not claimed: that the described lookup's side on the keys ends at the program's point, mask
form and value; that `isPad` of Cb/Pv/KeyLookup/Letters.lean at `pubOf (Wf.lookupOf ..)` is `padB`;
anything on the rows beside the claims; anything on a run on a view. On hiding: nothing.
Built on: `keys_sum` (OnBytes/Slice/KeyLeavesRuns.lean); `keysOfF_target`, `pad_sum`,
`padding_filter` (OnBytes/Slice/KeyLeavesTop.lean); `prog_top` (OnBytes/Slice/BlkLeavesTop.lean);
`read_pendingRow_eq` (OnBytes/Slice/BlkLeavesCutRow.lean); `read_keysOf`, `read_eqPlaces`
(OnBytes/Slice/BlkLeavesRead.lean). The first lines of the proof of `pendingF_form` are those of
`leaves_top` (OnBytes/Slice/KeyLeavesTop.lean).

-/
import OnBytes.Slice.BlkLeavesCutRow
import Cb.Pv.KeyLookup.KeysBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Finset Blocks Cb.LdLkp OnBytes OnBytes.Slice OnBytes.Slice.Leaves
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ### the equality vector -/

theorem eqW_eq_eqLow : ∀ (z : List GE) (j : ℕ), eqW z j = eqLow z j
  | [], _ => rfl
  | x :: xs, j => by
    show (if j % 2 = 1 then x else 1 - x) * eqW xs (j / 2) =
      (if j % 2 = 1 then x else 1 - x) * eqLow xs (j / 2)
    rw [eqW_eq_eqLow xs (j / 2)]

theorem ext_eq_sum (v : ℕ) (f pt : ℕ → GE) :
    Blocks.ext v f pt = ∑ j ∈ range (2 ^ v), eqW (lowPt v pt) j * f j := by
  unfold Blocks.ext
  exact sum_congr rfl fun j _ => by rw [eqN_eq_eqLow, eqW_eq_eqLow]

/-! ### the row over the field -/

/-- The value of a row's weights on a matrix of R rows and 2^kCol columns. -/
def rowVal (t : TRowF) (M : ℕ → ℕ → GE) (R kCol : ℕ) : GE :=
  ∑ r ∈ range R, ∑ x ∈ range (2 ^ kCol), t.g r * eqW t.psi x * M r x

theorem holds_iff_rowVal (W : PscF.World) (M : ℕ → ℕ → GE) (R kCol : ℕ) (t : TRowF) :
    t.Holds W M R kCol ↔ rowVal t M R kCol + W.form t.masks = t.target := Iff.rfl

/-- Over the field: the pending row and the sum of the equality vector times the keys. -/
theorem pendingF_form (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (L : LkF)
    (rowV natV : ℕ → GE) (θ α : GE) (M : ℕ → ℕ → GE) (c : PscF.PointClaim)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true)
    (hp : l.parts[i]? = some p) (hL : L.dw.length = l.digitWeight.length)
    (hpad : rowV l.paddingKey.toNat = L.pad) (hz : c.point.length = m.kCol + p.logPlaces) :
    rowVal (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)) M m.rows m.kCol -
      (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).target =
    ∑ j ∈ range (2 ^ (m.kCol + p.logPlaces)), eqW c.point j * key L M m.kCol p.runs j -
      (α - c.value) := by
  have hc := covered_of_tests m l id hl hm
  have hmem : p ∈ l.parts := List.mem_of_getElem? hp
  have hr := runsOk_of hl hmem
  have hR := rowsIn_of L hL hm hmem
  have ht := keysOfF_target (Wf.lookupOf id m l) _ rfl rfl rowV natV θ α i c
  rw [padding_filter id m l i p hp,
    pad_sum c.point m.kCol p.logPlaces i l.paddingKey.toNat rowV hz _ (gaps_le _ _ _ hr)
      (fun q hq => hc q (by
        have := padding_filter id m l i p hp
        rw [← this] at hq
        exact (List.mem_filter.1 hq).1)), hpad] at ht
  have hs := keys_sum L M m.kCol p.logPlaces m.rows p.runs c.point hz hr hR
    (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
  have e : (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).target =
      (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c).target -
        coveredSumF p.runs (eqPlacesF m.kCol c.point) * L.off := rfl
  rw [e, ht, hs]
  unfold rowVal
  show (∑ r ∈ range m.rows, ∑ x ∈ range (2 ^ m.kCol),
      (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).g r * eqW (c.point.take m.kCol) x * M r x) - _ = _
  ring

/-- The described lookup's end claim and the pending row over the field are one affine form in the
matrix. -/
theorem claim_form {N : Type} (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (L : LkF)
    (rowV natV : ℕ → GE) (θ α : GE) (M : ℕ → ℕ → GE) (c : PscF.PointClaim) (cl : MCl GE N)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true)
    (hp : l.parts[i]? = some p) (hL : L.dw.length = l.digitWeight.length)
    (hpad : rowV l.paddingKey.toNat = L.pad)
    (hpt : lowPt (m.kCol + p.logPlaces) cl.pt = c.point) (htg : cl.tg = α - c.value) :
    rowVal (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)) M m.rows m.kCol -
      (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).target =
    Blocks.ext (m.kCol + p.logPlaces) (key L M m.kCol p.runs) cl.pt - cl.tg := by
  have hz : c.point.length = m.kCol + p.logPlaces := by rw [← hpt, lowPt_length]
  rw [pendingF_form m l id i p L rowV natV θ α M c hl hm hp hL hpad hz, ext_eq_sum, hpt, htg]

/-! ### which keys are padding, and the target written out -/

/-- Place u is covered by a run. -/
def covP (runs : List WfRun) (u : ℕ) : Bool :=
  runs.any fun r => decide (r.firstPlace ≤ u ∧ u < r.firstPlace + r.places)

/-- Key number b stands at a place that no run covers. -/
def padB (kCol : ℕ) (runs : List WfRun) (b : ℕ) : Bool := !covP runs (b / 2 ^ kCol)

theorem keyAt_pad' (L : LkF) (M : ℕ → ℕ → GE) : ∀ (runs : List WfRun) (u x : ℕ),
    covP runs u = false → keyAt L M runs u x = L.pad
  | [], _, _, _ => rfl
  | r :: rs, u, x, h => by
    simp only [covP, List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    unfold keyAt
    rw [if_neg h.1]
    exact keyAt_pad' L M rs u x h.2

/-- What is left of a covered key beside the offset; 0 where no run covers the place. -/
def linAt (L : LkF) (M : ℕ → ℕ → GE) : List WfRun → ℕ → ℕ → GE
  | [], _, _ => 0
  | r :: rs, u, x =>
    if r.firstPlace ≤ u ∧ u < r.firstPlace + r.places then
      (L.dw.zipIdx.map fun w => w.1 * M (r.firstRow + (u - r.firstPlace) + w.2 * r.stride) x).sum
    else linAt L M rs u x

theorem keyAt_cov (L : LkF) (M : ℕ → ℕ → GE) : ∀ (runs : List WfRun) (u x : ℕ),
    covP runs u = true → keyAt L M runs u x = L.off + linAt L M runs u x
  | [], _, _, h => by simp [covP] at h
  | r :: rs, u, x, h => by
    unfold keyAt linAt
    by_cases hr : r.firstPlace ≤ u ∧ u < r.firstPlace + r.places
    · rw [if_pos hr, if_pos hr]
      rfl
    · rw [if_neg hr, if_neg hr]
      refine keyAt_cov L M rs u x ?_
      simp only [covP, List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact absurd h hr
      · exact h

theorem linAt_zero (L : LkF) : ∀ (runs : List WfRun) (u x : ℕ), linAt L (fun _ _ => 0) runs u x = 0
  | [], _, _ => rfl
  | r :: rs, u, x => by
    unfold linAt
    split
    · simp
    · exact linAt_zero L rs u x

theorem key_pad (L : LkF) (M : ℕ → ℕ → GE) (kCol : ℕ) (runs : List WfRun) (b : ℕ)
    (h : padB kCol runs b = true) : key L M kCol runs b = L.pad :=
  keyAt_pad' L M runs _ _ (by simpa [padB] using h)

theorem key_cov (L : LkF) (M : ℕ → ℕ → GE) (kCol : ℕ) (runs : List WfRun) (b : ℕ)
    (h : padB kCol runs b = false) :
    key L M kCol runs b = L.off + linAt L M runs (b / 2 ^ kCol) (b % 2 ^ kCol) :=
  keyAt_cov L M runs _ _ (by simpa [padB] using h)

/-- The padding's share and the offset's share are out of the target. -/
theorem pending_target {N : Type} (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (L : LkF)
    (rowV natV : ℕ → GE) (θ α : GE) (c : PscF.PointClaim) (cl : MCl GE N)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true)
    (hp : l.parts[i]? = some p) (hL : L.dw.length = l.digitWeight.length)
    (hpad : rowV l.paddingKey.toNat = L.pad)
    (hpt : lowPt (m.kCol + p.logPlaces) cl.pt = c.point) (htg : cl.tg = α - c.value) :
    (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).target =
      cl.tg - L.pad * padW (m.kCol + p.logPlaces) cl.pt (padB m.kCol p.runs) -
        L.off * covW (m.kCol + p.logPlaces) cl.pt (padB m.kCol p.runs) := by
  have h0 := claim_form m l id i p L rowV natV θ α (fun _ _ => 0) c cl hl hm hp hL hpad hpt htg
  have hv : rowVal (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
      (eqPlacesF m.kCol c.point)) (fun _ _ => 0) m.rows m.kCol = 0 := by
    unfold rowVal
    simp
  rw [hv, ext_split _ _ cl.pt (padB m.kCol p.runs) L.pad
      (fun b _ hb => key_pad L _ m.kCol p.runs b hb),
    sum_off _ _ (fun _ => 0) cl.pt (padB m.kCol p.runs) L.off
      (fun b _ hb => by rw [key_cov L _ m.kCol p.runs b hb, linAt_zero])] at h0
  simp only [mul_zero, sum_const_zero, add_zero] at h0
  linear_combination -h0

/-! ### the program's row -/

/-- The program's pending row, read and cut at the matrix's rows, is the row over the field. -/
theorem prog_row (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (θ α : E) (c : PointClaim)
    (hm : Wf.fitsMatrix m l = true) (hp : l.parts[i]? = some p) :
    readTRowAt m.rows (Wf.pendingRow m l p (Lkp.keysOf (Wf.lookupOf id m l) θ α i c)
        (Wf.eqPlaces m c.point)) =
      pendingRowF m.kCol (lkOf l (padOf id m l θ)) p.runs
        (keysOfF (Wf.lookupOf id m l) (fun t => readE (Lkp.rowAt (Wf.lookupOf id m l) θ t))
          (fun n => readE (Lkp.natE n)) (readE θ) (readE α) i (readPC c))
        (eqPlacesF m.kCol (readPC c).point) := by
  have hmem : p ∈ l.parts := List.mem_of_getElem? hp
  have hL : (lkOf l (padOf id m l θ)).dw.length = l.digitWeight.length := List.length_map _
  rw [read_pendingRow_eq m l p _ _ (padOf id m l θ) (rowsIn_of _ hL hm hmem), read_keysOf,
    read_eqPlaces]
  rfl

/-- The described lookup's end claim and the program's pending row, read, are one affine form in the
matrix. -/
theorem prog_form {N : Type} (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (θ α : E)
    (M : ℕ → ℕ → GE) (c : PointClaim) (cl : MCl GE N) (hl : Wf.lookupOk Wf.fBits l = true)
    (hm : Wf.fitsMatrix m l = true) (hp : l.parts[i]? = some p)
    (hpt : lowPt (m.kCol + p.logPlaces) cl.pt = c.point.map readE)
    (htg : cl.tg = readE α - readE c.value) :
    rowVal (readTRowAt m.rows (Wf.pendingRow m l p (Lkp.keysOf (Wf.lookupOf id m l) θ α i c)
        (Wf.eqPlaces m c.point))) M m.rows m.kCol -
      (readTRowAt m.rows (Wf.pendingRow m l p (Lkp.keysOf (Wf.lookupOf id m l) θ α i c)
        (Wf.eqPlaces m c.point))).target =
    Blocks.ext (m.kCol + p.logPlaces) (key (lkOf l (padOf id m l θ)) M m.kCol p.runs) cl.pt -
      cl.tg := by
  rw [prog_row m l id i p θ α c hm hp]
  exact claim_form m l id i p _ _ _ _ _ M (readPC c) cl hl hm hp (List.length_map _) rfl hpt htg

/-- The described lookup's end claim holds exactly if the program's pending row, read, holds. -/
theorem claim_iff_pending {N : Type} [Fintype N] (m : Wf.Matrix) (l : WfLookup) (id i : ℕ)
    (p : WfPart) (θ α : E) (W : PscF.World) (M : ℕ → ℕ → GE) (c : PointClaim) (cl : MCl GE N)
    (μ : N → GE) (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true)
    (hp : l.parts[i]? = some p) (hpt : lowPt (m.kCol + p.logPlaces) cl.pt = c.point.map readE)
    (htg : cl.tg = readE α - readE c.value)
    (hmf : ∑ j, cl.mf j * μ j = -W.form (readForm c.masks)) :
    cl.Holds (m.kCol + p.logPlaces) (key (lkOf l (padOf id m l θ)) M m.kCol p.runs) μ ↔
      (readTRow (Wf.pendingRow m l p (Lkp.keysOf (Wf.lookupOf id m l) θ α i c)
        (Wf.eqPlaces m c.point))).Holds W M m.rows m.kCol := by
  have hz : c.point.length = m.kCol + p.logPlaces := by
    have := congrArg List.length hpt
    rw [lowPt_length, List.length_map] at this
    exact this.symm
  rw [← prog_top m l id i p θ α W M c hl hm hp hz]
  unfold MCl.Holds PscF.PointClaim.Holds
  rw [treeMap_leafTab _ _ _ (readPC c).point (by rw [← hz]; exact List.length_map _), ext_eq_sum,
    hpt, htg, hmf]
  show _ ↔ readE α - ∑ j ∈ range (2 ^ (m.kCol + p.logPlaces)), eqW (c.point.map readE) j *
      key (lkOf l (padOf id m l θ)) M m.kCol p.runs j + W.form (readForm c.masks) = readE c.value
  constructor <;> intro h <;> linear_combination -h

end Lk6

#print axioms Lk6.ext_eq_sum
#print axioms Lk6.pendingF_form
#print axioms Lk6.claim_form
#print axioms Lk6.pending_target
#print axioms Lk6.prog_row
#print axioms Lk6.prog_form
#print axioms Lk6.claim_iff_pending
