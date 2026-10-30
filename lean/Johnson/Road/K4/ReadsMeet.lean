-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsMeet.lean: on true reads, the entries of the array of reads that hold the cells
of the norms' rows, of the scores and of the selectors, where the verifier can name them, are worth
the extensions of the library's cells of these names.

The dictionaries of Johnson/Road/Rows/LayerTermsPort.lean (TermsDict.row) and of
Johnson/Road/K4/LedPort.lean (LedDict.rowR, rowP) ask that an entry of the reads, readAtW, is worth
a library-side entry. The library's late entries are meant to be extensions of cells: cell n of the
row of norm ν has the name ⟨.D, 0, ν, n, p⟩ at position p (normsFm and termsFm in
Cb/Pv/Lay/End/NormsA.lean and TermsA.lean). This file says what readAtW is worth at these places,
from the records on true tables, for the three token points at which the rows are read; and
the same for the cells of the scores and of the selectors' entries (TermsDict.sc, sel; HotDict.sel
in Johnson/Road/Rows/LayerHotPort.lean).

Main names:
  `cell_meet`: an entry that the verifier can name in a true short table of a tied array is worth
    the extension of the library's cell.
  `row_meet`: the same for cell n of row ν of the tensor of rows, at a token point named P.
  `row_meet_P`, `row_meet_R`: at the points named P_V and r_tV, from Fits and TrueAt3.
  `row_meet_T`: at the point named rt, from Fits and TrueAt2.
  `rows_meet_of_forms`: at r_tV and P_V for every norm of the group, where rowsForms returns.
  `shA_meet`: limb k of an entry that shA returns, in a true short table of a tied array.
  `sc_meet_T`, `sel_meet_T`: the scores and the selectors at rt, from PortFits.
  `sel_meet_Z`: the selectors at the lookup's token point, named zt, from Fits.
Limits. ShortTrue speaks only of entries for which U3at returns a form, while readAtW is defined at
every place. So each statement asks that the verifier can name the entry: that U3at returns, that
rowCells returns for the row, that shA returns for the entry, or that rowsForms returns. Fits,
PortFits, TrueAt2 and TrueAt3 are premises: that the reads are true is not shown here. t: any cells
that the record ties. The points u, uP, uR, u', zh are the letters of the records: that they are the
readings of the verifier's points is not said here. No library-side entry occurs. Nothing on
soundness.


-/
import Johnson.Road.Rows.LayerHotPort
import Johnson.Road.FormsKeysTrue2
import Johnson.Road.FormsKeysTrue3
import OnBytes.Desc.First.K4.RowsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff TenAt tenCell)
open OnBytes.Model.Layer (Env Ten Heard aff0)
open OnBytes.Road.Rows (readAtW U3at_read foldForms_there)
open OnBytes.Desc.First.K4 (rowsForms digitsAt rowsForms_mem)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K}
  {t : Cell → K}

/-- An entry of a true short table of the matrix mat, at the place of limb k of entry (inst, j) of
an array X that is tied to that matrix: if the verifier can name it (U3at returns a form), the entry
of the reads is worth the extension of the library's cell over the positions, at the table's
point. -/
theorem cell_meet {tb mat lt : ℕ} {u : ℕ → K} (R : ShortTrue ρ W v tb mat lt c u) {X : Arr}
    {pl : TenAt} (T : Tied c t X mat pl) {k inst j : ℕ} {a : Aff}
    (h : v.U3at tb (tenCell pl k inst j) = some a) :
    readAtW W v tb (tenCell pl k inst j) = Blocks.ext lt (fun p => t ⟨X, k, inst, j, p⟩) u :=
  (U3at_read (ρ := ρ) h).symm.trans ((R _ _ h).trans (by simp only [T.2]))

/-- Cell n of row ν of the tensor of rows, in true short tables of its matrix at a token point named
P. Asked beside: a row has 99 cells; the array D is tied to the tensor; rowCells returns for the
row. -/
theorem row_meet {P : String} {b : ℕ} {trow : Ten} {lT : ℕ} {u : ℕ → K} (hJ : trow.J = 99)
    (T : Tied c t .D trow.mat trow.place) (R : ShortTrue ρ W v b trow.mat lT c u)
    (hb : v.tabAt ("ar@" ++ P) = some b) (hrow : v.y.T_ "row" = some trow) {ν : ℕ}
    {cells : Array Aff} (hc : v.rowCells P ν 99 = some cells) {n : ℕ} (hn : n < 99) :
    readAtW W v b (trow.OFF + ν * 99 + n) = Blocks.ext lT (fun p => t ⟨.D, 0, ν, n, p⟩) u := by
  unfold Env.rowCells at hc
  obtain ⟨b', hb', hc⟩ := bind_some hc
  obtain ⟨tr', hr', hc⟩ := bind_some hc
  have e1 : b' = b := Option.some.inj (hb'.symm.trans hb)
  have e2 : tr' = trow := Option.some.inj (hr'.symm.trans hrow)
  subst e1
  subst e2
  have h1 := range_mapM_get aff0 hc hn
  have hcell : tr'.OFF + ν * 99 + n = tenCell tr'.place 0 ν n := by
    show _ = tr'.OFF + (0 * tr'.cnt + ν) * tr'.J + n
    rw [hJ, Nat.zero_mul, Nat.zero_add]
  rw [hcell] at h1 ⊢
  exact cell_meet R T h1

/-- Limb k of entry (i, j) of a tensor that tensorAt finds under the name Xn at the point named Pn,
in true short tables of its matrix, for an array X that is tied to the tensor. Asked beside: shA
returns for the entry, and k is below the tensor's number of limbs. -/
theorem shA_meet {Xn Pn : String} {X : Arr} {ten : Ten} {tb lT : ℕ} {u : ℕ → K}
    (hX : v.tensorAt Xn Pn = some (ten, tb)) (T : Tied c t X ten.mat ten.place)
    (R : ShortTrue ρ W v tb ten.mat lT c u) {i j : ℕ} {a : Aff} (h : v.shA Xn Pn i j = some a)
    {k : ℕ} (hk : k < ten.nl) :
    readAtW W v tb (tenCell ten.place k i j) = Blocks.ext lT (fun p => t ⟨X, k, i, j, p⟩) u := by
  unfold Env.shA at h
  rw [hX] at h
  have h3 : v.limbs tb ten.nl (fun l => tenCell ten.place l i j) = some a := h
  unfold Env.limbs at h3
  obtain ⟨x, hx⟩ := foldForms_there _ (List.range ten.nl) _ _ h3 k (List.mem_range.mpr hk)
  obtain ⟨a', ha', _⟩ := map_some hx
  exact cell_meet R T ha'

section Records

variable [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE low' u' z zh : ℕ → K}

/-- The rows at the norms' token point, named P_V: from Fits (the tensor of rows and its tie) and
TrueAt3 (the tables of ar at P_V are true at uP), for a row ν for which rowCells returns. -/
theorem row_meet_P (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) {ν : ℕ} {cells : Array Aff}
    (hc : v.rowCells "P_V" ν 99 = some cells) :
    ∀ tb tr, v.tabAt ("ar@" ++ "P_V") = some tb → v.y.T_ "row" = some tr → ∀ n, n < 99 →
      readAtW W v tb (tr.OFF + ν * 99 + n) = Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) uP := by
  intro tb tr hb htr n hn
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  obtain rfl : trow = tr := Option.some.inj (hrow.symm.trans htr)
  exact row_meet hJ T (by rw [hm]; exact T3.arP tb hb) hb hrow hc hn

/-- The rows at the end point of the token sumcheck of the row products, named r_tV: as row_meet_P,
at uR. -/
theorem row_meet_R (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) {ν : ℕ} {cells : Array Aff}
    (hc : v.rowCells "r_tV" ν 99 = some cells) :
    ∀ tb tr, v.tabAt ("ar@" ++ "r_tV") = some tb → v.y.T_ "row" = some tr → ∀ n, n < 99 →
      readAtW W v tb (tr.OFF + ν * 99 + n) = Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) uR := by
  intro tb tr hb htr n hn
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  obtain rfl : trow = tr := Option.some.inj (hrow.symm.trans htr)
  exact row_meet hJ T (by rw [hm]; exact T3.arR tb hb) hb hrow hc hn

/-- The rows at the end point of the second token sumcheck, named rt: from Fits and TrueAt2 (the
tables of ar at rt are true at u'), for a row ν for which rowCells returns. -/
theorem row_meet_T (F : Fits ρ W v D c t low u) (T2 : TrueAt2 ρ W v D.lT c low' u') {ν : ℕ}
    {cells : Array Aff} (hc : v.rowCells "rt" ν 99 = some cells) :
    ∀ tb tr, v.tabAt ("ar@" ++ "rt") = some tb → v.y.T_ "row" = some tr → ∀ n, n < 99 →
      readAtW W v tb (tr.OFF + ν * 99 + n) = Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) u' := by
  intro tb tr hb htr n hn
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  obtain rfl : trow = tr := Option.some.inj (hrow.symm.trans htr)
  exact row_meet hJ T (by rw [hm]; exact T2.ar tb hb) hb hrow hc hn

/-- Where rowsForms returns, rowCells returns for every norm of the group at both points: so the
entries of the reads at r_tV and at P_V are worth the cells' extensions at uR and at uP, in the
binders of LedDict.rowR and rowP, for ν below the verifier's number of norms. -/
theorem rows_meet_of_forms (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) {H : Heard} {l : List Aff}
    (h : rowsForms v H = some l) :
    (∀ tb tr, v.tabAt ("ar@" ++ "r_tV") = some tb → v.y.T_ "row" = some tr →
      ∀ ν n, ν < v.y.NI → n < 99 → readAtW W v tb (tr.OFF + ν * 99 + n) =
        Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) uR) ∧
    ∀ tb tr, v.tabAt ("ar@" ++ "P_V") = some tb → v.y.T_ "row" = some tr →
      ∀ ν n, ν < v.y.NI → n < 99 → readAtW W v tb (tr.OFF + ν * 99 + n) =
        Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) uP := by
  constructor
  · intro tb tr hb htr ν n hν hn
    obtain ⟨Dr, _, hDr, _, _⟩ := rowsForms_mem h hν
    unfold digitsAt at hDr
    obtain ⟨cells, hc, _⟩ := Option.map_eq_some_iff.mp hDr
    exact row_meet_R F T3 hc tb tr hb htr n hn
  · intro tb tr hb htr ν n hν hn
    obtain ⟨_, Dp, _, hDp, _⟩ := rowsForms_mem h hν
    unfold digitsAt at hDp
    obtain ⟨cells, hc, _⟩ := Option.map_eq_some_iff.mp hDp
    exact row_meet_P F T3 hc tb tr hb htr n hn

/-- The cells of the score of routed layer l at the end point of the second token sumcheck, named
rt: from PortFits (the array sc is found, tied and true at zh), where shA returns for the score. -/
theorem sc_meet_T (P : PortFits ρ W v D c t low z zh) {l : ℕ} {a : Aff}
    (h : v.shA "sc" "rt" l 0 = some a) :
    ∀ X tb, v.tensorAt "sc" "rt" = some (X, tb) → ∀ k, k < X.nl →
      readAtW W v tb (tenCell X.place k l 0) =
        Blocks.ext D.lT (fun p => t ⟨.sc, k, l, 0, p⟩) zh := by
  intro X tb hX k hk
  obtain ⟨ten, b, h1, T, R⟩ := P.short2 .sc rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (h1.symm.trans hX))
  exact shA_meet hX T R h hk

/-- The cells of entry x of the selector of routed layer l at rt: as sc_meet_T. -/
theorem sel_meet_T (P : PortFits ρ W v D c t low z zh) {l x : ℕ} {a : Aff}
    (h : v.shA "sel" "rt" l x = some a) :
    ∀ X tb, v.tensorAt "sel" "rt" = some (X, tb) → ∀ k, k < X.nl →
      readAtW W v tb (tenCell X.place k l x) =
        Blocks.ext D.lT (fun p => t ⟨.sel, k, l, x, p⟩) zh := by
  intro X tb hX k hk
  obtain ⟨ten, b, h1, T, R⟩ := P.short2 .sel rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (h1.symm.trans hX))
  exact shA_meet hX T R h hk

/-- The cells of entry x of the selector of routed layer l at the lookup's token point, named zt:
from Fits (the array sel is found, tied and true at u), where shA returns for the entry. -/
theorem sel_meet_Z (F : Fits ρ W v D c t low u) {l x : ℕ} {a : Aff}
    (h : v.shA "sel" "zt" l x = some a) :
    ∀ X tb, v.tensorAt "sel" "zt" = some (X, tb) → ∀ k, k < X.nl →
      readAtW W v tb (tenCell X.place k l x) =
        Blocks.ext D.lT (fun p => t ⟨.sel, k, l, x, p⟩) u := by
  intro X tb hX k hk
  obtain ⟨ten, b, h1, T, R⟩ := F.short .sel rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (h1.symm.trans hX))
  exact shA_meet hX T R h hk

end Records

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cell_meet
#print axioms OnBytes.Road.K4.row_meet
#print axioms OnBytes.Road.K4.row_meet_P
#print axioms OnBytes.Road.K4.row_meet_R
#print axioms OnBytes.Road.K4.row_meet_T
#print axioms OnBytes.Road.K4.rows_meet_of_forms
#print axioms OnBytes.Road.K4.shA_meet
#print axioms OnBytes.Road.K4.sc_meet_T
#print axioms OnBytes.Road.K4.sel_meet_T
#print axioms OnBytes.Road.K4.sel_meet_Z
