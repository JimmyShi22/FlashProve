-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowFields.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the hypothesis RowFields
(Norms.lean) from the law on the honest reads. The makers value the verifier's forms of a norm's
four fields on the honest reads with the point r_tV laid at a token's bits (rowMaps,
Johnson/Desc/K4/Honest/Norms.lean); in a world with the true entries at that list of points the
forms have the library's values at the corner, and an extension at a corner is the entry
(ext_corner, CornerKit.lean). Definitions of hypotheses; statements and proofs.

  `CornerWorld`     a world with the true entries at token i's corner.
  **`rowFields_read`**   RowFields.

Not shown here. That the hypotheses hold anywhere: no example is known. THAT THERE IS A WORLD AT
EACH TOKEN's CORNER (CornerWorld) IS A HYPOTHESIS: it asks the library's structures Fits and
TrueAt3 at a list of points whose point r_tV is the corner, and that the tables which own the
places that the rows' forms name stand off the matrix of the lookup's planes. The law on the honest
reads (valAff_true, ValAff.lean) is called. Nothing says that the cells are those of an inference.
No property is claimed.
-/
import Johnson.Road.K4.C.Norms
import Johnson.Road.K4.C.RowMaps
import Johnson.Road.K4.C.ValAff
import Johnson.Road.K4.W.RowsZero
import Johnson.Road.FormsKeysFac

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten matIx TableAsk TableAt layTables tableAsks funsOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4 (entryOf)

/-- **A world with the true entries at token i's corner.** funs: the verifier's list of tables at a
list of points pts whose point r_tV is the corner, and at any values fo of the lookup's. Every slot
holds 0. This defines a hypothesis; the definition claims nothing. -/
def CornerWorld [scl : Scl] (Q : K4Pub) (v : Env) (tl : HTailF2)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (Mm : Mats Cb.Gl.E) (D : Dim)
    (t : Cell → Cb.Gl.E) (i : ℕ) : Prop :=
  ∃ (W : World Cb.Gl.E) (funs : Array HFun) (fo : Forest.Heard) (pts : List (String × Array E))
    (low u lowV uV uP lowE uE : ℕ → Cb.Gl.E),
    Fits Reading.gl W v D (cellsAt v.y Mm) t low u ∧
    TrueAt3 Reading.gl W v D.lT (cellsAt v.y Mm) lowV uV uP
      (pt Reading.gl (cornerPt D.lT i)) lowE uE ∧
    W.entry = entryOf Reading.gl tl funs v.iU3 v.K3 Mm ∧ (∀ j, W.slot j = 0) ∧
    funsOf Q.P.y fo pts r.2.1 = some funs ∧ PtsPart [("r_tV", cornerPt D.lT i)] pts ∧
    ∀ fs, rowForms v = some fs → ∀ a ∈ fs.toList, ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ,
      z.1 ∈ funs → tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) →
      z.1.mat ≠ (matIx Q.P.y).iB

variable {v : Env} {t : Cell → Cb.Gl.E} [scl : Scl] {D : Dim} {Q : K4Pub} {w : K4In}
  {Mm : Mats Cb.Gl.E} {p : Pts} {tl : HTailF2}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **THE FOUR FIELDS OF EACH NORM's ROW AT EACH TOKEN**, as the makers' tables hold them, read as
the library's. -/
theorem rowFields_read (hv : envOf Q p = some v)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (C : CellsAre Q w Mm) (hlt : Q.P.y.h.lt = D.lT) (hNI : Q.P.y.NI = D.nNu)
    (hW : ∀ i, i < 2 ^ D.lT → CornerWorld Q v tl r Mm D t i) : RowFields Q w p D t := by
  intro ms hms ν hν i hi
  have hy := envOf_y hv
  obtain ⟨Dg, R, fs, hD, hR, hfs, hk⟩ := rowMaps_at hms hv (ν := ν) (i := i)
    (by rw [hy, hNI]; exact hν) (by rw [hlt]; exact hi)
  rw [hlt] at hR
  obtain ⟨W, funs, fo, pts, low, u, lowV, uV, uP, lowE, uE, F, T3, hWe, hW0, hf, hp, hOff⟩ :=
    hW i hi
  have val : ∀ k, k < 4 → Reading.gl.val ((ms.getD (4 * ν + k) #[]).getD i zeroE) =
      ((fieldsOf Dg).getD k Model.Layer.aff0).value Reading.gl W := by
    intro k hk4
    obtain ⟨hmem, hfit, e⟩ := hk k hk4
    rw [e]
    exact valAff_true hR hl hf hp (Or.inl fun _ h => h) hm hNM C hfit hWe
      (fun x _ => by rw [hW0]; exact Reading.gl.zero.symm) (hOff fs hfs _ hmem)
  have hd : ∀ n, n < 99 → Desc.First.P6.dv Reading.gl W Dg n = led t ν i n := fun n hn =>
    ((Road.K4.W.digits_value F T3 ν).2 Dg hD n hn).trans (ext_corner D.lT _ hi)
  obtain ⟨va, vb, vl, vh⟩ := Desc.First.P6.fields_value Reading.gl W Dg
  exact ⟨(val 0 (by omega)).trans (va.trans (D6.Bridge.sa_congr hd)),
    (val 1 (by omega)).trans (vb.trans (D6.Bridge.sb_congr hd)),
    (val 2 (by omega)).trans (vl.trans (D6.Bridge.Rlo_congr hd)),
    (val 3 (by omega)).trans (vh.trans (D6.Bridge.Rhi_congr hd))⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rowFields_read
