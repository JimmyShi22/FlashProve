-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05CovOfRows.lean: kind K5: THE PREMISE hE OF THE ATTENTION SEGMENTS' HALF OF
THE EXCHANGE (armCellIn_att, Johnson/Desc/First/Att/ArmAtt.lean): "every form of the reader's answer
has Cov": FROM "every entry names row 0 of the array of the reads", the public test on the forms
(formsInT, Johnson/Desc/First/Batch/FormsIn.lean) and one fact on public data.

Why. Cov (Johnson/Desc/First/Att/Claims/Covered.lean) bounds an entry's place in the row by nW. For
the lookup argument's run on the planes the laws that lie speak of an entry's array and row alone.
The place's bound is the public test's: both arms of entInT bound it by the layout's array's number
of columns.

IS IT EMPTY HERE? NO MEMBER IS SHOWN.

Main names:
  `ranges_of_entInT`: an accept of entInT at x: the layout has the array that the list names at
    x.tree, and x.row, x.idx lie inside its sizes.
  `entIn_of_row0`: x.tree = t, x.row = 0, x.idx < nW ≤ K give EntIn t K nW x.
  `cov_of_rows`: **hE**, general in the readers, the piece and the run's name.
PREMISES LEFT: hE₀: every entry of every form of the reader's answer names row 0 of A.iU3 (it runs
over the WHOLE list of the answer) · hC: the layout's array of the reads has at most nW columns
(public; no law) · the accept of formsInT (a premise of the exchange itself) · nW ≤ K. Nothing is
claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.Covered
import Johnson.Desc.Sound.StatedCellIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Readers segAt? formsInT entInT entIn arrayIn arrayIn_some)
open VerifiableInference.Desc.Sound (entInT_of_formsInT)
open K5Law (Cov EntIn)

/-- An accept of the public test at an entry: the layout has the named array; the entry lies inside
its sizes. -/
theorem ranges_of_entInT (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part) (x : Ent)
    (h : entInT own a x = true) :
    ∃ b Ar, a.L.arrayOf[x.tree]? = some b ∧ reqArray a.L.check.rows.layout b.1 b.2 = some Ar ∧
      x.row < Ar.sizeI ∧ x.idx < Ar.sizeC := by
  unfold entInT at h
  rcases Eq.mp (Bool.or_eq_true _ _) h with h | h
  · unfold entIn at h
    cases e : arrayIn own a x.tree with
    | none =>
      rw [e] at h
      cases h
    | some Ar =>
      rw [e] at h
      obtain ⟨b, _, _, hb, hA, _, _⟩ := arrayIn_some own a x.tree Ar e
      obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
      exact ⟨b, Ar, hb, hA, of_decide_eq_true h1, of_decide_eq_true h2⟩
  · cases hb : a.L.arrayOf[x.tree]? with
    | none =>
      rw [hb] at h
      cases h
    | some b =>
      rw [hb] at h
      dsimp only at h
      cases hA : reqArray a.L.check.rows.layout b.1 b.2 with
      | none =>
        rw [hA] at h
        cases h
      | some Ar =>
        rw [hA] at h
        obtain ⟨_, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
        obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _) h2
        exact ⟨b, Ar, rfl, hA, of_decide_eq_true h3, of_decide_eq_true h4⟩

/-- An entry of row 0 below nW lies in the tables' part. -/
theorem entIn_of_row0 {t K nW : ℕ} {x : Ent} (h1 : x.tree = t) (h2 : x.row = 0) (h3 : x.idx < nW)
    (hW : nW ≤ K) : EntIn t K nW x :=
  ⟨x.idx, h3, h1, by rw [h2, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h3 hW)],
    (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h3 hW)).symm⟩

/-- **hE.** -/
theorem cov_of_rows (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) {s : First.S}
    {a : VerifiableInference.Desc.K9.Part} {t K nW : ℕ} (ha : segAt? s = some a)
    (hT : formsInT Rd own piece run s = true)
    (hE₀ : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
      x.tree = t ∧ x.row = 0)
    (hC : ∀ c Ar, a.L.arrayOf[t]? = some c → reqArray a.L.check.rows.layout c.1 c.2 = some Ar →
      Ar.sizeC ≤ nW)
    (hW : nW ≤ K) :
    ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, Cov t K nW f := by
  intro R hR f hf x hx
  obtain ⟨e1, e2⟩ := hE₀ R hR f hf x hx
  obtain ⟨b, Ar, hb, hA, _, h4⟩ :=
    ranges_of_entInT own a x (entInT_of_formsInT Rd own piece run s a ha hT R hR f hf x hx)
  rw [e1] at hb
  exact entIn_of_row0 e1 e2 (Nat.lt_of_lt_of_le h4 (hC b Ar hb hA)) hW

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.ranges_of_entInT
#print axioms VerifiableInference.Desc.First.Att.P.entIn_of_row0
#print axioms VerifiableInference.Desc.First.Att.P.cov_of_rows
