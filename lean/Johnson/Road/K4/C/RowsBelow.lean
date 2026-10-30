-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowsBelow.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the tables which own the
places that the rows' forms name stand off the matrix of the lookup's planes: the hypothesis hOff
of GroundCorner.lean and RowFieldsOf.lean. Each entry that a form of rowForms
(Johnson/Desc/K4/Honest/Norms.lean) names lies in front of the first place of the family "b-bits-0"
(Below.lean), and what lies there is owned off that matrix (hG_of_lt, OffPlanes.lean). Statements
and proofs.

  `below_digit`     a digit's form.
  `below_fields`    the four forms of a row's fields.
  `rowForms_mem`    each member of rowForms is one of some norm's four.
  **`rows_off`**      hOff.

Not shown here. That the premises hold anywhere: no example is known. That layTables returns, that
the environment's list of places is the one it returns, and that the family "b-bits-0" has a place
there are premises.
No property is claimed.
-/
import Johnson.Road.K4.C.Below
import Johnson.Road.K4.C.RowMaps
import Johnson.Road.K4.Reads.NormRowEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env TableAsk TableAt layTables tableAsks funsOf matIx aff0)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (digitsAt mapM_range_get)
open OnBytes.Desc.First.K4.Reads (entsIn_ofConst entsIn_add ofDigits_four)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf rowForms)

variable {v : Env} {tB0 : ℕ}

/-- A digit's form names entries in front of tB0 alone. -/
theorem below_digit (F : TabFront v tB0) {P : String} {i : ℕ} {Dg : ℕ → Aff}
    (hD : digitsAt v P i = some Dg) (n : ℕ) : Below v tB0 (Dg n) := by
  obtain ⟨cells, hc, rfl⟩ := Option.map_eq_some_iff.mp hD
  exact entsIn_add (below_rowCells F hc n) (entsIn_ofConst _)

/-- **The four forms of a row's fields** name entries in front of tB0 alone: the library's law
ofDigits_four (Johnson/Road/K4/Reads/NormRowEnts.lean). -/
theorem below_fields {Dg : ℕ → Aff} (hD : ∀ n, Below v tB0 (Dg n)) :
    ∀ a ∈ fieldsOf Dg, Below v tB0 a :=
  ofDigits_four hD

/-- **Each member of rowForms is one of some norm's four.** -/
theorem rowForms_mem {fs : Array Aff} (hfs : rowForms v = some fs) {a : Aff}
    (ha : a ∈ fs.toList) :
    ∃ ν Dg, digitsAt v "r_tV" ν = some Dg ∧ a ∈ fieldsOf Dg := by
  unfold rowForms at hfs
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hfs
  have ha' : a ∈ L.flatten := by simpa using ha
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha'
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hl
  have hlen : L.length = v.y.NI := by
    rw [(list_mapM_some _ _ _ hL).1, List.length_range]
  have hkN : k < v.y.NI := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨b, hb, hg⟩ := mapM_range_get _ hL hkN
  obtain rfl : b = l := Option.some.inj (hg.symm.trans hk)
  obtain ⟨Dg, hD, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨k, Dg, hD, hal⟩

variable {Q : K4Pub} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2}

/-- **THE TABLES WHICH OWN THE PLACES THAT THE ROWS' FORMS NAME STAND OFF THE MATRIX OF THE LOOKUP's
PLANES**, at every list of tables that funsOf makes of the laid families. -/
theorem rows_off (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hv : v.tab = r.1) (hB : v.tabAt "b-bits-0" = some tB0) (fo : Forest.Heard) :
    ∀ (pts' : List (String × Array E)) (funs' : Array HFun),
      funsOf Q.P.y fo pts' r.2.1 = some funs' → ∀ fs, rowForms v = some fs → ∀ a ∈ fs.toList,
      ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs' →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) → z.1.mat ≠ (matIx Q.P.y).iB := by
  intro pts' funs' hf fs hfs a ha
  obtain ⟨ν, Dg, hD, hmem⟩ := rowForms_mem hfs ha
  have F := tabFront_of_lay hl hv hB
  exact hG_of_lt hl hf hv hB
    ((below_iff v tB0 a).mp (below_fields (fun n => below_digit F hD n) a hmem))

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.below_digit
#print axioms OnBytes.Road.K4.C.below_fields
#print axioms OnBytes.Road.K4.C.rowForms_mem
#print axioms OnBytes.Road.K4.C.rows_off
