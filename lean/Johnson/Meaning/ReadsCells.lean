-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsCells.lean: the law of the reads at THE cells behind the committed symbols.

Johnson/Meaning/ReadsLaw.lean gets the law of the reads (Fo.ReadsAll) from the relation in front of
the draw of the smallness test's matrix, at integers that stand under "there are". Small integers
with the committed packing are unique (Cb/Pv/Tail/Unique.lean), so they can be named: the library's
`cellsOf`, a function of the committed symbols alone, and `cellVal`, its image in the field
(Cb/Pv/Tail/CellMap.lean). Whoever reads a matrix's cells off the committed symbols by `cellVal` or
`cellValS` (Cb/Pv/Tail/InLink.lean) reads the cells of which the law of the reads speaks.

Main names (namespace `Meaning.Reads`).
  `cellN`: cell (row r, column c) of matrix μ behind the letters' committed symbols, at plain
      numbers: `cellVal` inside the record's sizes, 0 outside.
  `readsAll_cells_congr`: Fo.ReadsAll reads the cells inside the matrices' sizes alone.
  `readsAll_cells`: **from the relation in front of the draw: Fo.ReadsAll at `cellN`**, in the
      library's field, at any letters over the record's sizes, and at tables funs that have the
      shapes of the record's.
  `cellN_syms`: `cellN` hangs on the committed symbols alone: it is `cellValS` of them.

Limits. As Johnson/Meaning/ReadsLaw.lean's: the relation in front of the draw is a premise, and so
are the two premises on the letters. `cellsOf` is found by choice: no program is given. Nothing on
soundness.
-/
import Johnson.Meaning.ReadsLaw
import Cb.Pv.Tail.InLink
import OnBytes.Tie.Pv.Tail.SizeUniq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open Finset
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop

/-- The law of the reads reads the cells inside the matrices' sizes alone. -/
theorem readsAll_cells_congr {K : Type} [CommRing K] (ρ : Reading K) {mats : Array TMat}
    {funs : Array HFun} {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ} {cellM cellM' : ℕ → ℕ → ℕ → K}
    (e : ∀ f ∈ funs.toList, f.tree = 2 → ∀ c < (mats.getD f.mat {}).k,
      ∀ r < (mats.getD f.mat {}).m, cellM f.mat r c = cellM' f.mat r c)
    (h : ReadsAll ρ mats funs entry iU3 K3 cellM) : ReadsAll ρ mats funs entry iU3 K3 cellM' := by
  intro f hf ht col hcol
  have hq : 0 < (mats.getD f.mat {}).m / f.len := by
    rcases Nat.eq_zero_or_pos ((mats.getD f.mat {}).m / f.len) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcol
      exact absurd hcol (Nat.not_lt_zero _)
    · exact h0
  have hc : col / ((mats.getD f.mat {}).m / f.len) < (mats.getD f.mat {}).k :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
  have hs := Nat.mod_lt col hq
  rw [h f hf ht col hcol]
  refine Finset.sum_congr rfl fun row hrow => ?_
  have hr : col % ((mats.getD f.mat {}).m / f.len) * f.len + row < (mats.getD f.mat {}).m := by
    have h1 : col % ((mats.getD f.mat {}).m / f.len) * f.len + row <
        (col % ((mats.getD f.mat {}).m / f.len) + 1) * f.len := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left (mem_range.mp hrow) _
    have h2 : (col % ((mats.getD f.mat {}).m / f.len) + 1) * f.len ≤
        (mats.getD f.mat {}).m / f.len * f.len := Nat.mul_le_mul_right _ hs
    exact lt_of_lt_of_le h1 (le_trans h2 (Nat.div_mul_le_self _ _))
  show _ * cellM f.mat _ _ = _ * cellM' f.mat _ _
  rw [e f hf ht _ hc _ hr]

/-- Cell (row r, column c) of matrix μ behind the letters' committed symbols; 0 outside the record's
sizes. -/
noncomputable def cellN (tl : HTailF2) (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf tl)) (msg : Θ.M)
    (μ r c : ℕ) : Cb.Gl.E :=
  if h : μ < tl.NM ∧ c < (tl.mats.getD μ {}).k ∧ r < (tl.mats.getD μ {}).m then
    cellVal Θ.letters msg ⟨⟨μ, h.1⟩, ⟨c, h.2.1⟩, ⟨r, h.2.2⟩⟩
  else 0

/-- **The law of the reads at THE cells behind the committed symbols.** -/
theorem readsAll_cells (ρ : Reading Cb.Gl.E) (tl : HTailF2)
    (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf tl)) {x : Θ.X} {msg : Θ.M}
    (h : relIn Θ.letters x msg) (funs : Array HFun)
    (hsh : (Tie.Pv.Tail.sizeOf tl).tabs =
      funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (iU3 K3 : ℕ)
    (hphi : ∀ n Fn, funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (hu : ∀ f ∈ funs.toList, f.tree = 2 → ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val entry iU3 K3 (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg))
    (hNM : ∀ f ∈ funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ReadsAll ρ tl.mats funs entry iU3 K3 (cellN tl Θ msg) := by
  obtain ⟨a, h1, h2, h3⟩ := readsAll_of_relIn ρ tl Θ h funs hsh entry iU3 K3 hphi hu hNM
  refine readsAll_cells_congr ρ (fun f hf ht c hc r hr => ?_) h3
  have hμ := hNM f hf ht
  have hP : Packs Θ.letters msg ⟨f.mat, hμ⟩ ⟨c, hc⟩
      (fun i : Fin (tl.mats.getD f.mat {}).m => a f.mat c i) :=
    ⟨fun i => h1 f.mat hμ c hc i i.2, fun i' => h2 f.mat hμ c hc i' i'.2⟩
  have e := packs_unique Θ.letters Cb.Gl.p (sizeOf_uniq tl) (fun _ => rfl) hP
    (packs_cellsOf Θ.letters ⟨_, hP⟩)
  show ((a f.mat c r : ℤ) : Cb.Gl.E) = cellN tl Θ msg f.mat r c
  unfold cellN
  rw [dif_pos ⟨hμ, hc, hr⟩]
  show _ = ((cellsOf Θ.letters msg ⟨f.mat, hμ⟩ ⟨c, hc⟩ ⟨r, hr⟩ : ℤ) : Cb.Gl.E)
  rw [← e]

/-- `cellN` hangs on the committed symbols alone. -/
theorem cellN_syms (tl : HTailF2) (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf tl)) (msg : Θ.M)
    (μ r c : ℕ) (hμ : μ < tl.NM) (hc : c < (tl.mats.getD μ {}).k)
    (hr : r < (tl.mats.getD μ {}).m) :
    cellN tl Θ msg μ r c =
      cellValS (Θ.letters.sym msg) ⟨⟨μ, hμ⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩ := by
  unfold cellN
  rw [dif_pos ⟨hμ, hc, hr⟩, cellVal_eq]

#print axioms readsAll_cells_congr
#print axioms readsAll_cells
#print axioms cellN_syms

end Meaning.Reads
