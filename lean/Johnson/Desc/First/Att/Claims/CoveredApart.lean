-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/CoveredApart.lean: kind K5: Claims/Covered.lean's law reads_covered_K05 A RUN AT A TIME: of "first" from the
return of "first" alone, of "second" from the return of "second" alone. That law takes both returns at once: at a record where one
run returns and the other does not it cannot be called; a law that asks a run at a time (on the worth of the entries that a run's
forms name) needs the halves.

Main names: first_cov_K05 · second_cov_K05. row0_of_cov: where the array has at least nW columns, an entry of the tables' part names
row 0, and its place is below nW.
The proofs are the halves of reads_covered_K05's, over its own lemmas cv_claim3 … cv_claim8.
IS IT EMPTY HERE? As Claims/Covered.lean says of its law. LenIn and RowsCov are shown of nothing here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Covered

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

variable {K nW : ℕ} {i : P.Runs.In}

/-- **"first", from its own return.** -/
theorem first_cov_K05 {l₁ : List Aff} {j : JoinsP} (hL : LenIn i nW) (hR : RowsCov i K nW)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) : ∀ f ∈ l₁, Cov i.iU3 K nW f := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  simp only [Option.map_eq_some_iff] at h1
  obtain ⟨_, ⟨y1, hy1, rfl⟩, e1⟩ := h1
  have c1 := (CV.bind (C := Cov i.iU3 K nW) (cv_claim3 hL _) fun j3 _ => CV.bind (cv_claim4 hL hR j3)
    fun j4 _ => cv_claim5 hL hR j4) #[] y1 hy1 (by simp)
  have a1 : l₁ = y1.2.toList := (Prod.mk.inj e1).1.symm
  exact fun f h => c1.2 f (a1 ▸ h)

/-- **"second", from its own return.** -/
theorem second_cov_K05 {l₂ : List Aff} (hL : LenIn i nW) (hR : RowsCov i K nW)
    (h2 : P.Runs.secondRun i K = some l₂) : ∀ f ∈ l₂, Cov i.iU3 K nW f := by
  unfold P.Runs.secondRun P.Runs.gather at h2
  simp only [Option.map_eq_some_iff] at h2
  obtain ⟨_, ⟨y2, hy2, rfl⟩, e2⟩ := h2
  have c2 := (CV.bind (C := Cov i.iU3 K nW) (cv_claim6 hL hR) fun _ _ => CV.bind (cv_claim7 hL hR)
    fun _ _ => cv_claim8 hL hR) #[] y2 hy2 (by simp)
  have a2 : l₂ = y2.2.toList := e2.symm
  exact fun f h => c2.2 f (a2 ▸ h)

/-- Where the array is at least as wide as the tables' part is long, such an entry names row 0. -/
theorem row0_of_cov {iU3 : ℕ} {e : Ent} (hK : nW ≤ K) (h : EntIn iU3 K nW e) :
    e.tree = iU3 ∧ e.row = 0 ∧ e.idx < nW := by
  obtain ⟨x, hx, e1, e2, e3⟩ := h
  have hxK : x < K := Nat.lt_of_lt_of_le hx hK
  exact ⟨e1, by rw [e2, Nat.div_eq_of_lt hxK], by rw [e3, Nat.mod_eq_of_lt hxK]; exact hx⟩

end K5Law

#print axioms K5Law.first_cov_K05
#print axioms K5Law.second_cov_K05
#print axioms K5Law.row0_of_cov
