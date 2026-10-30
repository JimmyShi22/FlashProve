-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoReadH.lean.
Reading the head's tables: what Head.tabAt and Head.U3at return, and what an entry is worth under
the law of the reads.

States:
  tabAt_ok: Head.tabAt returns the first entry of the table that is found under the name.
  U3at_ok: Head.U3at returns the form of one entry of the vector of reads.
  U3at_val: so its value in a world is that entry.
  read_part: under the law of the reads (Fo.ReadsAll at Fo.funsH), entry i of part p of a table that
    Fo.TabIs describes is the sum over a block of rows of weight times cell.
Premises of read_part: the part's record (Fo.partRec) is in the list of the head's tables; the
part's matrix is not the planes' matrix; i lies below the part's length. Premise of tabAt_ok: the
name is found in the list of the tables' names. The first three speak of runs that return.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTabsH2
import OnBytes.Tie.Pv.Lookup.Ends.FoKeysH
import OnBytes.Tie.Pv.Lookup.Ends.FoNatVal

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.PscRun

theorem tabAt_ok (R : Head.Run) (nm : String) (p0 len : ℕ) (F : Fork) (c : Ctx)
    (r : (ℕ × Fork) × Ctx)
    (hf : (R.t.tab.find? fun e => e.1 == nm) = some (nm, p0, len))
    (h : Head.tabAt R nm F c = .ok r) : r = ((p0, F), c) := by
  unfold Head.tabAt at h
  obtain ⟨a, e1, e2⟩ := getAsL_ok _ _ F c r h
  rw [hf] at e1
  have : p0 = a := Option.some.inj e1
  rw [e2, this]

theorem U3at_ok (R : Head.Run) (t i : ℕ) (F : Fork) (c : Ctx) (r : (Aff × Fork) × Ctx)
    (h : Head.U3at R t i F c = .ok r) :
    r = ((u3Form R.iU3 (colsOf F R.iU3) (t + i), F), c) := by
  unfold Head.U3at at h
  obtain ⟨_, h2⟩ := bindMustAs_ok _ _ _ F c r h
  exact uEnt_ok _ _ F c r h2

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem U3at_val (R : Head.Run) (t i : ℕ) (F G : Fork) (c c' : Ctx) (a : Aff) (W : World K)
    (h : Head.U3at R t i F c = .ok ((a, G), c')) :
    a.value ρ W = u3Val W.entry R.iU3 (colsOf F R.iU3) (t + i) := by
  have e := U3at_ok R t i F c _ h
  have e1 : a = u3Form R.iU3 (colsOf F R.iU3) (t + i) :=
    congrArg (fun y : (Aff × Fork) × Ctx => y.1.1) e
  rw [e1, u3Form_value]

/-- An entry of a part of a table, under the law of the reads. -/
theorem read_part (R : Head.Run) (entry : ℕ → ℕ → ℕ → K) (K3 : ℕ) (cellM : ℕ → ℕ → ℕ → K)
    (hU : ReadsAll ρ R.hp.tl.mats (funsH R) entry R.iU3 K3 cellM) (M0 Lf p0 : ℕ) (phi : Array E)
    (p : ℕ) (hm : partRec R.hp.tl.mats M0 Lf p0 phi p ∈ R.t.funs.toList)
    (hb : M0 + p ≠ R.h.NHf + 2) (i : ℕ) (hi : i < partLen R.hp.tl.mats Lf (M0 + p)) :
    u3Val entry R.iU3 K3 (partStart R.hp.tl.mats M0 Lf p0 p + i) =
      ∑ row ∈ range Lf, ρ.val (phi.getD row zeroE) *
        cellM (M0 + p) (i % ((R.hp.tl.mats.getD (M0 + p) {}).m / Lf) * Lf + row)
          (i / ((R.hp.tl.mats.getD (M0 + p) {}).m / Lf)) := by
  have hf : partRec R.hp.tl.mats M0 Lf p0 phi p ∈ (funsH R).toList := by
    unfold funsH
    rw [Array.toList_filter, List.mem_filter]
    exact ⟨hm, by simpa [partRec] using hb⟩
  exact hU _ hf rfl i hi

end
end Fo
