-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05ReadersRows.lean: kind K5: WHICH ENTRIES THE KIND's TWO READERS' FORMS
NAME: every entry of a form that the readers hand the lookup argument's run on the planes names row
0 of the plan's array of the reads.

Why. The premise "every entry of the planes' claims' forms names row 0 of A.iU3" of
K05_host_planes_door (Johnson/Desc/First/Att/K05HostPlanesDoor.lean) has two halves: the claims'
forms name no entry but their bit and pin forms' (the lookup argument's files' law on its run:
planes_rowsIn_bare, PlanesRowsIn.lean); the bit and pin forms are the kind's readers': this file.

IS IT EMPTY HERE? NO MEMBER IS SHOWN.

Main names:
  `readers_rows`: at a verifier's state sP whose open segment is an attention segment a₀ with U3At A
    (plannedK A) a₀.F, where the claims' seat's reading answers (i, K) and the readers are r: every
    entry of every form of r.1 and of r.2 names row 0 of A.iU3.
  `bit_pin_rows`: the same of fun e col => (r.1 e col).getD (Aff.ofConst zeroE) and fun col => (r.2
    col).getD (Aff.ofConst zeroE): the forms in which the row K05_host_planes hands them to the run.
CALLED: readers_forms (Johnson/Desc/First/Att/K05ReadersThere.lean) ·
row0_of_cov (Johnson/Desc/First/Att/Claims/CoveredApart.lean) · inOf_isAt, inAt_parts · the
library's len_in (Johnson/Desc/First/Att/Claims/Covered.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadersThere
import Johnson.Desc.First.Att.K05PlanesWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open K5Law (inOf_isAt inAt_parts len_in row0_of_cov Cov)

/-- **Every entry of the two readers' forms names row 0 of the array A.iU3.** -/
theorem readers_rows (A : Attention.Plan) {sP : First.S} {a₀ : First.AttOwn} {i : Runs.In} {K : ℕ}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hs : sP.here = .att a₀)
    (hU : U3At A (plannedK A) a₀.F)
    (hr : readersOfK (seatCO (parCOf A)) (parCOf A) sP = some r)
    (hin : inOf (seatCO (parCOf A)) (parCOf A) sP = some (i, K)) :
    (∀ e col f, r.1 e col = some f → ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0) ∧
      ∀ col f, r.2 col = some f → ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0 := by
  have hK := width_of_inOf A hs hU hin
  obtain ⟨T, _, hTK, hW, _⟩ := hU
  have hWK : A.nW ≤ K := by rw [hK, ← hTK]; exact hW
  have h' := hin
  rw [inOf_isAt hs] at h'
  obtain ⟨g, _, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨hh, _, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨eg, eu, _, _, ht⟩ := inAt_parts h'
  have eg' : i.g = (parCOf A).geo := eg
  have eu' : i.iU3 = A.iU3 := eu
  have ht' : tablesP i.g (parCOf A).mats (parCOf A).nW (lookOfO (parCOf A).geo.lmb g) i.p = some i.t := by
    rw [eg']
    exact ht
  obtain ⟨c1, c2⟩ := readers_forms (Ps := fun _ => True) hin (len_in ht') hr
  refine ⟨fun e col f hf y hy => ?_, fun col f hf y hy => ?_⟩
  · obtain ⟨a, b, _⟩ := row0_of_cov hWK ((c1 e col f hf).2 y hy)
    exact ⟨a.trans eu', b⟩
  · obtain ⟨a, b, _⟩ := row0_of_cov hWK ((c2 col f hf).2 y hy)
    exact ⟨a.trans eu', b⟩

/-- The same of the forms in which the row hands them to the run. -/
theorem bit_pin_rows (A : Attention.Plan) {sP : First.S} {a₀ : First.AttOwn} {i : Runs.In} {K : ℕ}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hs : sP.here = .att a₀)
    (hU : U3At A (plannedK A) a₀.F)
    (hr : readersOfK (seatCO (parCOf A)) (parCOf A) sP = some r)
    (hin : inOf (seatCO (parCOf A)) (parCOf A) sP = some (i, K)) :
    (∀ e col, ∀ y ∈ ((r.1 e col).getD (Aff.ofConst zeroE)).ents.toList, y.tree = A.iU3 ∧ y.row = 0) ∧
      ∀ col, ∀ y ∈ ((r.2 col).getD (Aff.ofConst zeroE)).ents.toList, y.tree = A.iU3 ∧ y.row = 0 := by
  obtain ⟨c1, c2⟩ := readers_rows A hs hU hr hin
  refine ⟨fun e col y hy => ?_, fun col y hy => ?_⟩
  · cases hf : r.1 e col with
    | none =>
      rw [hf] at hy
      simp [Aff.ofConst] at hy
    | some f =>
      rw [hf] at hy
      exact c1 e col f hf y hy
  · cases hf : r.2 col with
    | none =>
      rw [hf] at hy
      simp [Aff.ofConst] at hy
    | some f =>
      rw [hf] at hy
      exact c2 col f hf y hy

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readers_rows
#print axioms VerifiableInference.Desc.First.Att.P.bit_pin_rows
