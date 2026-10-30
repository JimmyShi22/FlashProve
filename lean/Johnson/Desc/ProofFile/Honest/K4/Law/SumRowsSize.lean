-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumRowsSize.lean: CONDITIONAL.

What is here. Where the maker of the tables of the norms' rows returns (`rowMaps`,
Johnson/Desc/K4/Honest/Norms.lean) it returns four tables for each norm; so the job of the sumcheck
on the row products has four end values for each norm, at every list of challenges. Statements and
proofs.

  `flatten_length`, `mapM_forall`, `arr_mapM_size`   lists of one length; makers that may return
     nothing
  `envOf_y`, `rowForms_size`, `rowMaps_size`   four forms, and four tables, for each norm
  `rows_ends_length`, `rows_ends_call`   the job's end values

Limits. THAT THE MAKER RETURNS IS A PREMISE. A count alone: nothing on the tables' own sizes or on
what they hold. That the call states just so many end values wants norms of five limbs (`ledNO`): a
premise of `rows_ends_call`. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRows
import OnBytes.Maker.TablesLaws
import Johnson.Desc.First.K4.RunsLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Aff ledNO)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes.Desc.First.K4 (flatten_length mapM_mem)

/-- An array of values is as long as the array. -/
theorem arr_mapM_size {α β : Type} (f : α → Option β) (a : Array α) (b : Array β)
    (h : a.mapM f = some b) : b.size = a.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h
  rw [← e, List.size_toArray, OnBytes.Maker.mapM_length _ _ _ hl, Array.length_toList]

/-- The structure that the verifier's forms read holds the place's layout. -/
theorem envOf_y (Q : K4Pub) (p : Pts) (v : OnBytes.Model.Layer.Env) (h : envOf Q p = some v) :
    v.y = Q.P.y := by
  unfold envOf at h
  obtain ⟨iU3, _, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x, _, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨tab, a, b⟩ := x
  rw [← Option.some.inj h2]

/-- Four forms for each norm. -/
theorem rowForms_size (v : OnBytes.Model.Layer.Env) (fs : Array Aff) (h : rowForms v = some fs) :
    fs.size = 4 * v.y.NI := by
  unfold rowForms at h
  obtain ⟨L, hL, e⟩ := Option.map_eq_some_iff.mp h
  have h4 : ∀ x ∈ L, x.length = 4 := fun x hx => by
    obtain ⟨i, hb⟩ := mapM_mem _ L hL x hx
    obtain ⟨D, _, hD⟩ := Option.map_eq_some_iff.mp hb
    rw [← hD]
    rfl
  rw [← e, List.size_toArray, flatten_length 4 L h4, OnBytes.Maker.mapM_length _ _ _ hL,
    List.length_range]

/-- **Four tables for each norm.** -/
theorem rowMaps_size (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (h : rowMaps Q w p = some ms) : ms.size = 4 * Q.P.y.NI := by
  unfold rowMaps at h
  obtain ⟨v, hv, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fs, hfs, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨Rs, _, h3⟩ := Option.bind_eq_some_iff.mp h2
  rw [arr_mapM_size _ _ _ h3, rowForms_size v fs hfs, envOf_y Q p v hv]

/-- **The job has four end values for each norm**, at every list of challenges. -/
theorem rows_ends_length (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (h : rowMaps Q w p = some ms) (rs : List E) :
    ((rowsJobOf Q p ms).ends rs).length = 4 * Q.P.y.NI := by
  show ((rowsJobOf Q p ms).cube.valuesAt rs).toList.length = _
  rw [Array.length_toList, valuesAt_size]
  exact rowMaps_size Q w p ms h

/-- That is the number that the row's second call states, at norms of five limbs. -/
theorem rows_ends_call (Q : K4Pub) (w : K4In) (p : Pts) (ms : Array Tab)
    (h : rowMaps Q w p = some ms) (hxl : Q.P.y.h.xl = 5) (rs : List E) :
    ((rowsJobOf Q p ms).ends rs).length = ledNO Q.P.y.h.xl * Q.P.y.NI := by
  rw [rows_ends_length Q w p ms h rs, hxl]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.arr_mapM_size
#print axioms ProofFile.Honest.K4.envOf_y
#print axioms ProofFile.Honest.K4.rowForms_size
#print axioms ProofFile.Honest.K4.rowMaps_size
#print axioms ProofFile.Honest.K4.rows_ends_length
#print axioms ProofFile.Honest.K4.rows_ends_call
