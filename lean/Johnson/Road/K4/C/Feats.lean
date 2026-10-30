-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Feats.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side. A maker is a function of
the honest side that makes the values which a part sends. The cells that the makers read straight
(Johnson/Desc/K4/Honest/Cells.lean: featAt, featCell, streamLimb), read into the field, are the
library's cells of the matrices Mm (cellsAt, Johnson/Road/FormsKeysMat.lean). Definitions of
hypotheses; statements and proofs.

  `crossK`       the makers count the stream that leaves the group as kind 4 and the one that
                 enters it as kind 5; the library counts them 5 and 4. One matrix each on both
                 sides: the numbers alone are crossed.
  `MatsLaid`     public: each part of each of the six matrices stands in the plan's list, with the
                 layout's rows and columns, and is not the matrix of the lookup's planes.
  `InMat`        public: a feature lies inside a matrix's parts.
  `cell_at`, `feat_read`    a feature's cell for a token.
  `StreamsIn`    public: the features of the streams' limbs lie inside their matrices.
  `limb_read`    a limb of a residual stream that a norm reads is the library's bS.

Not shown here. That the hypotheses hold anywhere: no example is known. Nothing says that the cells
are those of an inference. Nothing on the matrix of the lookup's planes: CellsAre (Cells.lean)
leaves it out.
No property is claimed.
-/
import Johnson.Road.K4.C.Cells
import Johnson.Desc.K4.Honest.Norms
import Johnson.Road.FormsKeysIdnW
import Johnson.Road.K4.SquaresPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten matIx)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest

/-- The library's number of the matrix that the makers count as kind k: 4 and 5 are crossed. -/
def crossK : ℕ → ℕ
  | 4 => 5
  | 5 => 4
  | k => k

/-- **Each part of each of the six matrices stands in the plan's list.** Public. This defines a
hypothesis; the definition claims nothing. -/
def MatsLaid (Q : K4Pub) : Prop :=
  ∀ mat, mat < 6 → ∀ part, part < partsM Q.P.y mat →
    firstM Q.P.y mat + part ≠ (matIx Q.P.y).iB ∧
      (matsOf Q).getD (firstM Q.P.y mat + part) (0, 0) = (rowsM Q.P.y mat, colsM Q.P.y mat)

/-- Feature ft lies inside the parts of the library's matrix number mat. Public. -/
def InMat (y : Lay) (mat ft : ℕ) : Prop := mat < 6 ∧ ft < partsM y mat * colsM y mat * fcM y mat

/-- The cell at the place that the makers' rule names, in the library's numbers. -/
theorem cell_at {Q : K4Pub} {w : K4In} {Mm : Mats Cb.Gl.E} (C : CellsAre Q w Mm)
    (L : MatsLaid Q) {mat ft t : ℕ} (hf : InMat Q.P.y mat ft) (ht : t < Q.P.y.T) :
    Reading.gl.val (ofF (w.cell
        (firstM Q.P.y mat + ft / (colsM Q.P.y mat * (rowsM Q.P.y mat / Q.P.y.T)))
        (ft % (rowsM Q.P.y mat / Q.P.y.T) * Q.P.y.T + t)
        (ft / (rowsM Q.P.y mat / Q.P.y.T) % colsM Q.P.y mat))) =
      cellsAt Q.P.y Mm mat ft t := by
  obtain ⟨hm, hft⟩ := hf
  have hfc : 0 < fcM Q.P.y mat := by
    rcases Nat.eq_zero_or_pos (fcM Q.P.y mat) with h | h
    · rw [h, Nat.mul_zero] at hft
      exact absurd hft (Nat.not_lt_zero _)
    · exact h
  have hk : 0 < colsM Q.P.y mat := by
    rcases Nat.eq_zero_or_pos (colsM Q.P.y mat) with h | h
    · rw [h, Nat.mul_zero, Nat.zero_mul] at hft
      exact absurd hft (Nat.not_lt_zero _)
    · exact h
  have hpart : ft / (colsM Q.P.y mat * fcM Q.P.y mat) < partsM Q.P.y mat :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos hk hfc)).mpr (by rw [← Nat.mul_assoc]; exact hft)
  obtain ⟨hB, hmk⟩ := L mat hm _ hpart
  have hrow : ft % fcM Q.P.y mat * Q.P.y.T + t < rowsM Q.P.y mat := by
    have h1 : ft % fcM Q.P.y mat + 1 ≤ fcM Q.P.y mat := Nat.mod_lt _ hfc
    have h2 : (ft % fcM Q.P.y mat + 1) * Q.P.y.T ≤ fcM Q.P.y mat * Q.P.y.T :=
      Nat.mul_le_mul_right _ h1
    have h3 : fcM Q.P.y mat * Q.P.y.T ≤ rowsM Q.P.y mat := Nat.div_mul_le_self _ _
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have hcol : ft / fcM Q.P.y mat % colsM Q.P.y mat < colsM Q.P.y mat := Nat.mod_lt _ hk
  have e := C (firstM Q.P.y mat + ft / (colsM Q.P.y mat * fcM Q.P.y mat)) hB
    (ft % fcM Q.P.y mat * Q.P.y.T + t) (ft / fcM Q.P.y mat % colsM Q.P.y mat)
    (by rw [hmk]; exact hrow) (by rw [hmk]; exact hcol)
  show _ = Mm (firstM Q.P.y mat + ft / fcM Q.P.y mat / colsM Q.P.y mat) _ _
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (fcM Q.P.y mat)]
  exact e.symm

/-- **A feature's cell for a token**, read into the field, is the library's cell. THE NUMBERS 4 AND
5 ARE CROSSED. -/
theorem feat_read {Q : K4Pub} {w : K4In} {Mm : Mats Cb.Gl.E} (C : CellsAre Q w Mm)
    (L : MatsLaid Q) {kind ft t : ℕ} (hf : InMat Q.P.y (crossK kind) ft) (ht : t < Q.P.y.T) :
    Reading.gl.val (ofF (featCell Q.P.y w.cell kind ft t)) =
      cellsAt Q.P.y Mm (crossK kind) ft t := by
  have hk : kind < 6 := by
    have h := hf.1
    unfold crossK at h
    split at h <;> omega
  interval_cases kind
  all_goals simp only [featCell, featAt]
  · exact cell_at (mat := 0) C L hf ht
  · exact cell_at (mat := 1) C L hf ht
  · exact cell_at (mat := 2) C L hf ht
  · exact cell_at (mat := 3) C L hf ht
  · exact cell_at (mat := 5) C L hf ht
  · exact cell_at (mat := 4) C L hf ht

/-- **The features of the streams' limbs lie inside their matrices.** Public. This defines a
hypothesis; the definition claims nothing. -/
structure StreamsIn (y : Lay) : Prop where
  first : ∀ l, l < 5 → ∀ j, j < y.h.d → InMat y 4 (tenCell y.xb l 0 j)
  inner : ∀ l, l < 5 → ∀ i, i + 1 < y.NI → ∀ j, j < y.h.d →
    InMat y (tensorOf y "xs").mat (tenCell (tensorOf y "xs").place l i j)

variable {W : World Cb.Gl.E} {v : Env} {t : Cell → Cb.Gl.E} [scl : Scl] {D : Dim}
  {low u : ℕ → Cb.Gl.E} {Q : K4Pub} {w : K4In} {Mm : Mats Cb.Gl.E}

/-- **A limb of a residual stream that a norm reads**, read into the field, is the library's. -/
theorem limb_read (F : Fits Reading.gl W v D (cellsAt v.y Mm) t low u) (hy : Q.P.y = v.y)
    (C : CellsAre Q w Mm) (L : MatsLaid Q) (S : StreamsIn Q.P.y)
    (hT : Q.P.y.T = 2 ^ D.lT) (hNI : Q.P.y.NI = D.nNu) {ν l j i : ℕ}
    (hν : ν < D.nNu) (hl : l < 5) (hj : j < D.d) (hi : i < 2 ^ D.lT) :
    Reading.gl.val (ofF (streamLimb Q.P.y w.cell (tensorOf Q.P.y "xs") ν l j i)) =
      bS D t ν l j i := by
  obtain ⟨_, _, _, txs, _, _, _, hxs, hm, T0, _, Ts, _⟩ := F.stream
  have hj' : j < Q.P.y.h.d := by rw [hy, F.d]; exact hj
  have hi' : i < Q.P.y.T := by rw [hT]; exact hi
  have hten : tensorOf Q.P.y "xs" = txs := by
    unfold tensorOf
    rw [hy, hxs]
    rfl
  by_cases h0 : ν = 0
  · subst h0
    show Reading.gl.val (ofF (featCell Q.P.y w.cell 5 (tenCell Q.P.y.xb l 0 j) i)) =
      t ⟨.x0, l, 0, j, i⟩
    rw [T0.2, ← hy]
    exact feat_read C L (kind := 5) (S.first l hl j hj') hi'
  · have hN2 : D.nNu = 2 * D.nl := rfl
    have h8 : ν ≠ 2 * D.nl := by omega
    have h8' : (ν == Q.P.y.NW * Q.P.y.Lam) = false := by
      rw [hy, F.last]
      simpa using h8
    have h0' : (ν == 0) = false := by simpa using h0
    unfold streamLimb bS Inst.Model.FFSeg.streamAt
    rw [if_neg h0, if_neg h8]
    simp only [h0', h8', Bool.false_eq_true, if_false]
    show _ = t ⟨.xs, l, ν - 1, j, i⟩
    rw [Ts.2, ← hy, ← hten]
    have hin := S.inner l hl (ν - 1) (by rw [hNI]; omega) j hj'
    have hc : crossK (tensorOf Q.P.y "xs").mat = (tensorOf Q.P.y "xs").mat := by
      rw [hten, hm]
      rfl
    have e := feat_read C L (kind := (tensorOf Q.P.y "xs").mat) (ft :=
      tenCell (tensorOf Q.P.y "xs").place l (ν - 1) j) (t := i) (by rw [hc]; exact hin) hi'
    rw [hc] at e
    exact e

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cell_at
#print axioms OnBytes.Road.K4.C.feat_read
#print axioms OnBytes.Road.K4.C.limb_read
