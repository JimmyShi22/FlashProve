-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FitRows.lean: CONDITIONAL.

What is here. Two more of the fifteen clauses of the public test `k4MakersFit`
(Johnson/Desc/ProofFile/Honest/K4/Part.lean), each brought down to ONE return: wherever the honest
side's function that lays the rows' fields as tables on the tokens returns (`rowMaps`,
Johnson/Desc/K4/Honest/Norms.lean), the list of row products has as many entries as the row states
(`rowProducts_length`), and the function for the row products' token sumcheck returns a job of its
call's public shape (`rows_fit`); at every input w, at all sampled values p whose point PV has lt
coordinates; where a stream's word has five limbs: rowProducts_length takes that as a hypothesis of
its own (hxl); rows_fit draws it from the plan's nine public facts (`K4Plan`), of which it spends
nothing else. The tables' number is Law/SumRowsSize.lean's; that each has one entry a token is
`rowMaps_tabs`.

  `rowMaps_tabs`   each of the rows' tables has 2 ^ lt entries.
  `rowProducts_length`   ledNP xl times NI entries.
  `rows_fit`   the row products' job.

Not shown here. THAT rowMaps RETURNS (h): a hypothesis HERE; Johnson/Road/K4/C/RowMapsOf.lean's
rowMaps_returns has it, at every input and all sampled values, from K4Plan and five further public
facts. K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES); the
number of limbs (hxl); the size of PV: hypotheses. The other clauses of k4MakersFit. What the tables
hold. By a walk of import lines the closure holds no module under Johnson/RecCompile/, Johnson/Goal/
or Johnson/D/. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRowsSize
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelLists
import Johnson.Desc.ProofFile.Honest.K4.Law.TripsOf
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.FormsKeysFac
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 ledNP ledNO orderDefault)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First (P6.rowProducts)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {w : K4In} {p : Pts} {ms : Array Tab}

/-- **Each of the rows' tables has one entry a token.** CONDITIONAL: on the return. -/
theorem rowMaps_tabs (h : rowMaps Q w p = some ms) :
    ∀ t ∈ ms.toList, t.size = 2 ^ Q.P.y.h.lt := by
  unfold rowMaps at h
  obtain ⟨v, _, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fs, _, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨Rs, hRs, h3⟩ := Option.bind_eq_some_iff.mp h2
  intro t ht
  obtain ⟨f, hf⟩ := amapM_mem h3 t ht
  rw [arr_mapM_size _ _ _ hf]
  exact amapM_range_size _ hRs

/-- **THE ROW PRODUCTS ARE AS MANY AS THE ROW STATES.** CONDITIONAL: on the return and the number of
limbs. -/
theorem rowProducts_length (h : rowMaps Q w p = some ms) (hxl : Q.P.y.h.xl = 5) :
    (rowProducts Q w p).length = ledNP Q.P.y.h.xl * Q.P.y.NI := by
  unfold rowProducts
  rw [h]
  dsimp only
  rw [OnBytes.Road.flatMap_length _ 7 _ fun i _ => by rw [List.length_map]; rfl,
    List.length_range, hxl, Nat.mul_comm]
  rfl

variable {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- **THE ROW PRODUCTS' JOB IS MADE AND HAS ITS CALL's SHAPE.** CONDITIONAL: on A, the return and
the size. -/
theorem rows_fit (A : K4Plan hS pc Q.P Q.g tl D) (h : rowMaps Q w p = some ms)
    (hV : p.PV.size = Q.P.y.h.lt) :
    ∃ j, jobRows Q w p = some j ∧
      k4JobFits (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) j = true := by
  have hxl : Q.P.y.h.xl = 5 := by
    rw [(OnBytes.Road.admitted_of_layout A.lay A.sw.p3).shape]
    exact A.sw.xl
  have hsz := rowMaps_size Q w p ms h
  have hfit : (rowsJobOf Q p ms).cube.fits = true := by
    refine fits_of _ ?_ ?_ (rowMaps_tabs h) ?_ ?_
    · show (orderDefault Q.P.y.h.lt).length = Q.P.y.h.lt
      simp [orderDefault]
    · intro v hv
      show v ∈ orderDefault Q.P.y.h.lt
      simpa [orderDefault] using hv
    · intro x hx
      obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have hi' : i < Q.P.y.NI := List.mem_range.mp hi
      have hz4 : z.1.1 < 4 ∧ z.1.2 < 4 := by
        have hm : z.1 ∈ P6.rowProducts := (List.mem_zipIdx hz).2.2 ▸ List.getElem_mem _
        simp only [P6.rowProducts, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with e | e | e | e | e | e | e <;> rw [e] <;> exact ⟨by decide, by decide⟩
      show 4 * i + z.1.1 < ms.size ∧ 4 * i + z.1.2 < ms.size
      rw [hsz]
      omega
    · intro r hr
      have h' : Way.point p.PV = Way.point r := hr
      rw [← Way.point.inj h']
      exact hV
  refine ⟨rowsJobOf Q p ms, by rw [jobRows_eq, h]; show (if _ then _ else _) = _; rw [if_pos hfit],
    ?_⟩
  have he := rows_ends_call Q w p ms h hxl (List.replicate Q.P.y.h.lt zeroE)
  unfold k4JobFits
  rw [hfit]
  simp [k4TokenShape, rowsJobOf, VerifiableInference.Desc.Part.MaskedSum.Var.d] at he ⊢
  exact he

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.rowMaps_tabs
#print axioms ProofFile.Honest.K4.W.rowProducts_length
#print axioms ProofFile.Honest.K4.W.rows_fit
