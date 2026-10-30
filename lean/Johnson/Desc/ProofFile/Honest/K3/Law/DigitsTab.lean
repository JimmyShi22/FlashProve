-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/DigitsTab.lean: the reader of the input at a lookup on the
digits with tables (`tabAsk`, Honest/K3/WitDigitsTab.lean) is `fastAsk`
(Honest/K3/WitDigitsFast.lean). Theorems; all but two small ones without a hypothesis.

Terms. Honest/K3/GLOSSARY.md; the head of Honest/K3/WitDigitsTab.lean.

What is shown.
  `comb_at`        `comb` is `combAt` at the matrix's first column, its number of columns and its
                   row
  `cellTab_read`   read at a row of the cells' tables is the cells' own function
  `combG_some`, `combG_none`   `combG` at a row of cells that is found, and beyond all rows
  `combTab_eq`     the combinations' table, made over the cells' tables, is the table of `combG`
  `digitBy_comb`   `digitBy` over `combG` is `digitAt`
  `digitBy_tab`    so `digitBy` over the table's reading is `digitAt`
  `hitsTab_eq`     `hitsTab` at the table of the digits' rows is `hitsZ` at the digits as elements
  `tabLookZ_eq`    `tabLookZ tl dg` is `fastLookZ tl` at the digits laid into the base field
  `tabAsk_eq`      the main theorem: `tabAsk X link rng C heard = fastAsk X link rng C heard`: at
                   every public part, link, round's number, reader of the cells and list of
                   challenges

Hypotheses that remain. None in `tabAsk_eq` and the seven equations beneath it: beyond a table's end
the function itself is read, so no size is asked for. `combG_some` and `combG_none` each take what
`rowAt` yields at the row (`h`).

Imported. Honest/K3/WitDigitsTab.lean and what stands beneath it.

Users. Honest/K3/Law/WitTab.lean [not in this library], Honest/K3/Tab/TabAllLaw.lean
[not in this library] and Honest/K3/Tab/TabAll2Law.lean import this file. With `fastAsk_eq`
(Honest/K3/WitDigitsFast.lean) and `boundWit_eq` (Honest/K3/WitBound.lean) a reader that holds
`tabAsk` at the digits is the filling's own.

Limits. The equations say that the terms are equal, not how long either takes. Nothing says that
either reader is right.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitDigitsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Hits padZ firstRow tabOf hitsZ hitsOf kvZ)
open OnBytes.DgP (digInCall)
open ProofFile.Honest.K8 (parOfTail cellsAtOf)
open VerifiableInference.Desc.First.K8 (Par firstColumns)
open VerifiableInference.Desc.First.K8.Honest (CellsAt comb allRows rowAt low high digitAt)

/-- `comb` is `combAt` at the matrix's first column, its number of columns and its row of cells. -/
theorem comb_at (p : Par) (cell : CellsAt) (drawn : Array Int) (mu i u : ℕ) :
    comb p cell drawn mu i u =
      combAt p.tau ((firstColumns p).getD mu 0) (p.ks.getD mu 0) drawn (cell mu i) u := rfl

/-- Read at a row of the cells' tables is the cells' own function. -/
theorem cellTab_read (p : Par) (cell : CellsAt) (mu i : ℕ) :
    Memo.read (((cellTab p cell).getD mu #[]).getD i #[]) (cell mu i) = cell mu i := by
  funext c
  unfold cellTab
  rw [Memo.getD_tab]
  by_cases h : mu < p.ks.length
  · rw [if_pos h]
    exact Memo.read_row _ _ (cell mu) i c
  · rw [if_neg h]
    exact Memo.read_empty (cell mu i) c

/-- At a row of cells of a matrix `combG` is that matrix's `comb`. Conditional on the row's being
found there. -/
theorem combG_some (p : Par) (cell : CellsAt) (drawn : Array Int) {g mu i : ℕ}
    (h : rowAt p.ms 0 g = some (mu, i)) : combG p cell drawn g = comb p cell drawn mu i := by
  funext u
  unfold combG
  simp only [h]

/-- Beyond all rows of cells `combG` is 0. Conditional on the row's not being found. -/
theorem combG_none (p : Par) (cell : CellsAt) (drawn : Array Int) {g : ℕ}
    (h : rowAt p.ms 0 g = none) : combG p cell drawn g = fun _ => 0 := by
  funext u
  unfold combG
  simp only [h]

/-- **The combinations' table, made over the cells' tables, is the table of `combG`.** -/
theorem combTab_eq (p : Par) (cell : CellsAt) (drawn : Array Int) :
    combTab p cell drawn (cellTab p cell) = Memo.tab2 (allRows p) p.tau (combG p cell drawn) := by
  unfold combTab Memo.tab2
  dsimp only
  refine congrArg (Memo.tab (allRows p)) (funext fun g => ?_)
  cases h : rowAt p.ms 0 g with
  | none => rw [combG_none p cell drawn h]
  | some x =>
    obtain ⟨mu, i⟩ := x
    rw [combG_some p cell drawn h]
    dsimp only
    rw [cellTab_read]
    rfl

/-- `digitBy` over `combG` is `digitAt`. -/
theorem digitBy_comb (p : Par) (cell : CellsAt) (drawn : Array Int) (u col : ℕ) :
    digitBy p (combG p cell drawn) u col = digitAt p cell drawn u col := by
  unfold digitBy digitAt
  dsimp only
  cases h : rowAt p.ms 0 (if col < allRows p then col else col - allRows p) with
  | none => rfl
  | some x =>
    obtain ⟨mu, i⟩ := x
    rw [combG_some p cell drawn h]

/-- **`digitBy` over the reading of the combinations' table is `digitAt`.** -/
theorem digitBy_tab (p : Par) (cell : CellsAt) (drawn : Array Int) :
    digitBy p (Memo.read2 (combTab p cell drawn (cellTab p cell)) (combG p cell drawn)) =
      digitAt p cell drawn := by
  have e : Memo.read2 (combTab p cell drawn (cellTab p cell)) (combG p cell drawn) =
      combG p cell drawn := by
    funext g u
    rw [combTab_eq]
    exact Memo.read2_tab2 _ _ _ g u
  rw [e]
  funext u col
  exact digitBy_comb p cell drawn u col

/-- **`hitsTab` at the table of the digits' rows is `hitsZ` at the digits as elements.** -/
theorem hitsTab_eq (tl : HTailF2) (dg : ℕ → ℕ → ℕ) :
    hitsTab tl dg (rowTab tl.f9) =
      hitsZ tl (inExt fun u col => ((dg u col : ℕ) : Cb.Gl.F)) := by
  unfold hitsTab hitsZ hitsOf
  congr 1
  funext c i
  unfold padZ kvZ rowTab
  cases digInCall tl c i with
  | none => rfl
  | some t =>
    show Memo.read2 (Memo.tab2 tl.f9.NC (2 ^ tl.f9.kT) (rowOfDigit tl.f9)) (rowOfDigit tl.f9) c
      (dg t.2.2 (c * tl.mz + t.2.1)) = _
    rw [Memo.read2_tab2]
    rfl

/-- **`tabLookZ tl dg` is `fastLookZ tl` at the digits laid into the base field.** -/
theorem tabLookZ_eq (tl : HTailF2) (dg : ℕ → ℕ → ℕ) :
    tabLookZ tl dg = fastLookZ tl fun u col => ((dg u col : ℕ) : Cb.Gl.F) := by
  unfold tabLookZ fastLookZ
  simp only [hitsTab_eq]

/-- **THE THEOREM: the reader with tables is `fastAsk`.** -/
theorem tabAsk_eq (X : OnBytes.Model.Verify.Public) (link rng : ℕ) (C : Cells)
    (heard : List Fmt.Drawn) : tabAsk X link rng C heard = fastAsk X link rng C heard := by
  unfold tabAsk fastAsk
  simp only [digitBy_tab, tabLookZ_eq]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.comb_at
#print axioms ProofFile.Honest.K3.cellTab_read
#print axioms ProofFile.Honest.K3.combG_some
#print axioms ProofFile.Honest.K3.combG_none
#print axioms ProofFile.Honest.K3.combTab_eq
#print axioms ProofFile.Honest.K3.digitBy_comb
#print axioms ProofFile.Honest.K3.digitBy_tab
#print axioms ProofFile.Honest.K3.hitsTab_eq
#print axioms ProofFile.Honest.K3.tabLookZ_eq
#print axioms ProofFile.Honest.K3.tabAsk_eq
