-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaidLists.lean: THE WAY BACK AND THE FORMAT's RULE UNDO EACH
OTHER, OF AN ARRAY's LIST OF LAID BLOCKS AND OF A MESSAGE's ARRAYS: arrayBack and laidBack
(Johnson/Desc/ProofFile/Honest/LaidData.lean) against the library's laidAt
(Johnson/Desc/LaidAt.lean). Over the law of one laid block (Law/LaidBack.lean). Theorems on public
data alone; no definition outside the tests.

Main names (namespace ProofFile.Honest).
  arrayBack_of_laidAt   laidAt a i c = some (r, j) gives arrayBack a r j = some (i, c): where each
      laid block is as large in the table as in the array, and no two meet IN THE TABLE.
  laidAt_of_arrayBack   the converse: where no two meet IN THE ARRAY.
  laidAt_iff_arrayBack   both ways.
  fits_he, fits_hT, fits_hA   these three premises, for every array of a list that the plan's own
      test passes (Own.laidFits, Johnson/Desc/Own/Req.lean).
  one_array   two arrays of such a list whose ways back speak at one place are one.
  listBack_iff, laidBack_iff   laidBack lay l m r j = some (a, i, c) exactly if a is an array of
      segment l in message m and laidAt a i c = some (r, j): under Own.laidFits at that filtered
      list: the list at which Own.reqMessageLaid holds it.

By calls: back_of_place, place_of_back, fits_even (Law/LaidBack.lean); back_rect (Law/LaidLaw.lean);
core's List.pairwise_flatMap, List.Pairwise.forall, List.exists_of_findSome?_eq_some. Kin, not
called, over the files of other sub-protocols: pairwise_of_noPair
(Johnson/Desc/First/Look/K3CallerLaid.lean: noTwo_pairwise at the program's noPair), meet_of_holds
(Johnson/Desc/First/Att/K05CellAt.lean).

Limits. SEVEN STATEMENTS BEAR A PREMISE THAT DOES NOT STAND AT THEIR OWN LINES: hf : Own.laidFits as
R P = true, laid by the section Plan's «variable» and «include»: fits_matrix, fits_table, fits_he,
fits_hA, fits_hT, one_array, listBack_iff. It is a public test on a layout. That every ELEMENT of an
array has a place is not proved here (kin: laidAt_of_matrixOk,
Johnson/Goal/Meaning/LaidCovered.lean). What laidData's "lays" and "entry" inherit:
Law/LaidSent.lean. Tests: five #guard lines at the foot: the premises can be met; at two laid blocks
that share a place the plan's test rejects, and the way back hands another element than the rule
laid. Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaidBack
import Johnson.Desc.ProofFile.Honest.Law.LaidLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (LaidBlock ReqArray)
open VerifiableInference.Desc (laidIn laidAt)
open VerifiableInference.Desc.Own (noTwo laidMeets laidFits laidMatrixFits laidBlockFits)

/-! ## 1 Lists -/

theorem noTwo_pairwise {α : Type} (r : α → α → Bool) : ∀ l : List α, noTwo r l = true →
    l.Pairwise fun a b => r a b = false
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
      unfold noTwo at h
      rw [Bool.and_eq_true, List.all_eq_true] at h
      exact List.Pairwise.cons (fun b hb => by simpa using h.1 b hb) (noTwo_pairwise r l h.2)

/-- Where one member speaks and all that speak say the same, the first that speaks says it. -/
theorem findSome_of_one {α β : Type} (f : α → Option β) (v : β) : ∀ (l : List α) (a : α), a ∈ l →
    f a = some v → (∀ a' ∈ l, ∀ w, f a' = some w → w = v) → l.findSome? f = some v
  | [], _, h, _, _ => absurd h (List.not_mem_nil)
  | x :: l, a, h, ha, hu => by
      rw [List.findSome?_cons]
      cases hx : f x with
      | some w => rw [hu x (List.mem_cons_self) w hx]
      | none =>
          rcases List.mem_cons.1 h with rfl | h'
          · rw [hx] at ha
            exact absurd ha (by simp)
          · exact findSome_of_one f v l a h' ha fun a' m => hu a' (List.mem_cons_of_mem _ m)

/-! ## 2 What a laid block holds lies in its two rectangles -/

theorem place_rect {b : LaidBlock} {i c : Nat} {p : Nat × Nat} (h : laidIn b i c = some p) :
    b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI ∧ b.firstC ≤ c ∧ c < b.firstC + 2 ^ b.bitsC := by
  unfold laidIn at h
  simp only at h
  split at h
  · rename_i hh
    exact hh
  · exact absurd h (by simp)

/-- Two stretches that hold one number meet. -/
theorem meets_of_both {a aBits b bBits n : Nat} (h1 : a ≤ n) (h2 : n < a + 2 ^ aBits) (h3 : b ≤ n)
    (h4 : n < b + 2 ^ bBits) : laidMeets a aBits b bBits = true := by
  unfold laidMeets
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  omega

theorem laidMeets_comm (a aBits b bBits : Nat) :
    laidMeets a aBits b bBits = laidMeets b bBits a aBits := by
  unfold laidMeets
  rw [Bool.and_comm]

/-- Of a list whose members are apart under a symmetric test: two members that meet are one. -/
theorem same_of_meet {α : Type} (r : α → α → Bool) (hs : ∀ x y, r x y = r y x) {l : List α}
    (hp : l.Pairwise fun a b => r a b = false) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (h : r x y = true) : x = y := by
  by_contra hne
  have := hp.forall (fun a b e => by rw [hs b a]; exact e) hx hy hne
  rw [h] at this
  exact absurd this (by simp)

/-! ## 3 An array's list of laid blocks -/

/-- **THE WAY BACK UNDOES THE RULE, OF AN ARRAY**: where each laid block is as large in the table as
in the array, and no two meet in the table. -/
theorem arrayBack_of_laidAt (a : ReqArray)
    (he : ∀ b ∈ a.blocks, b.rowBits + b.placeBits = b.bitsI + b.bitsC)
    (hT : a.blocks.Pairwise fun x y => (laidMeets x.firstRow x.rowBits y.firstRow y.rowBits &&
      laidMeets x.firstPlace x.placeBits y.firstPlace y.placeBits) = false)
    {i c r j : Nat} (h : laidAt a i c = some (r, j)) : arrayBack a r j = some (i, c) := by
  unfold laidAt at h
  obtain ⟨b, hb, hbi⟩ := List.exists_of_findSome?_eq_some h
  have h0 := back_of_place b (he b hb) hbi
  refine findSome_of_one _ _ _ b hb h0 fun b' hb' w hw => ?_
  obtain ⟨p1, p2, p3, p4⟩ := back_rect _ _ _ _ h0
  obtain ⟨q1, q2, q3, q4⟩ := back_rect _ _ _ _ hw
  have e : b = b' := same_of_meet _
    (fun x y => by rw [laidMeets_comm x.firstRow, laidMeets_comm x.firstPlace]) hT hb hb'
    (by rw [Bool.and_eq_true]; exact ⟨meets_of_both p1 p2 q1 q2, meets_of_both p3 p4 q3 q4⟩)
  subst e
  rw [h0] at hw
  exact (Option.some.inj hw).symm

/-- **THE RULE UNDOES THE WAY BACK, OF AN ARRAY**: where no two laid blocks meet in the array. -/
theorem laidAt_of_arrayBack (a : ReqArray)
    (hA : a.blocks.Pairwise fun x y => (laidMeets x.firstI x.bitsI y.firstI y.bitsI &&
      laidMeets x.firstC x.bitsC y.firstC y.bitsC) = false)
    {i c r j : Nat} (h : arrayBack a r j = some (i, c)) : laidAt a i c = some (r, j) := by
  unfold arrayBack at h
  obtain ⟨b, hb, hbi⟩ := List.exists_of_findSome?_eq_some h
  have h0 := place_of_back b hbi
  refine findSome_of_one _ _ _ b hb h0 fun b' hb' w hw => ?_
  obtain ⟨p1, p2, p3, p4⟩ := place_rect h0
  obtain ⟨q1, q2, q3, q4⟩ := place_rect hw
  have e : b = b' := same_of_meet _
    (fun x y => by rw [laidMeets_comm x.firstI, laidMeets_comm x.firstC]) hA hb hb'
    (by rw [Bool.and_eq_true]; exact ⟨meets_of_both p1 p2 q1 q2, meets_of_both p3 p4 q3 q4⟩)
  subst e
  rw [h0] at hw
  exact (Option.some.inj hw).symm

/-- **BOTH WAYS, OF AN ARRAY.** -/
theorem laidAt_iff_arrayBack (a : ReqArray)
    (he : ∀ b ∈ a.blocks, b.rowBits + b.placeBits = b.bitsI + b.bitsC)
    (hT : a.blocks.Pairwise fun x y => (laidMeets x.firstRow x.rowBits y.firstRow y.rowBits &&
      laidMeets x.firstPlace x.placeBits y.firstPlace y.placeBits) = false)
    (hA : a.blocks.Pairwise fun x y => (laidMeets x.firstI x.bitsI y.firstI y.bitsI &&
      laidMeets x.firstC x.bitsC y.firstC y.bitsC) = false)
    (i c r j : Nat) : laidAt a i c = some (r, j) ↔ arrayBack a r j = some (i, c) :=
  ⟨arrayBack_of_laidAt a he hT, laidAt_of_arrayBack a hA⟩

/-! ## 4 The premises, from the plan's own tests -/

section Plan
variable {as : List ReqArray} {R P : Nat} (hf : laidFits as R P = true)
include hf

theorem fits_matrix {a : ReqArray} (ha : a ∈ as) : laidMatrixFits a R P = true := by
  unfold laidFits at hf
  rw [Bool.and_eq_true, List.all_eq_true] at hf
  exact hf.1 a ha

theorem fits_table : (as.flatMap (·.blocks)).Pairwise fun x y =>
    (laidMeets x.firstRow x.rowBits y.firstRow y.rowBits &&
      laidMeets x.firstPlace x.placeBits y.firstPlace y.placeBits) = false := by
  unfold laidFits at hf
  rw [Bool.and_eq_true] at hf
  exact noTwo_pairwise _ _ hf.2

theorem fits_he {a : ReqArray} (ha : a ∈ as) :
    ∀ b ∈ a.blocks, b.rowBits + b.placeBits = b.bitsI + b.bitsC := by
  intro b hb
  have h := fits_matrix hf ha
  unfold laidMatrixFits at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact fits_even (h.1.1 b hb).1.1

theorem fits_hA {a : ReqArray} (ha : a ∈ as) : a.blocks.Pairwise fun x y =>
    (laidMeets x.firstI x.bitsI y.firstI y.bitsI &&
      laidMeets x.firstC x.bitsC y.firstC y.bitsC) = false := by
  have h := fits_matrix hf ha
  unfold laidMatrixFits at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact noTwo_pairwise _ _ h.1.2

theorem fits_hT {a : ReqArray} (ha : a ∈ as) : a.blocks.Pairwise fun x y =>
    (laidMeets x.firstRow x.rowBits y.firstRow y.rowBits &&
      laidMeets x.firstPlace x.placeBits y.firstPlace y.placeBits) = false :=
  (List.pairwise_flatMap.1 (fits_table hf)).1 a ha

/-! ## 5 A message's arrays -/

/-- Two arrays of the list whose ways back both speak at one place are one. -/
theorem one_array {a a' : ReqArray} (ha : a ∈ as) (ha' : a' ∈ as) {r j : Nat} {p p' : Nat × Nat}
    (h : arrayBack a r j = some p) (h' : arrayBack a' r j = some p') : a = a' := by
  by_contra hne
  unfold arrayBack at h h'
  obtain ⟨b, hb, hbi⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨b', hb', hbi'⟩ := List.exists_of_findSome?_eq_some h'
  obtain ⟨p1, p2, p3, p4⟩ := back_rect _ _ _ _ hbi
  obtain ⟨q1, q2, q3, q4⟩ := back_rect _ _ _ _ hbi'
  have hp := (List.pairwise_flatMap.1 (fits_table hf)).2
  have hsym : Symmetric fun a₁ a₂ : ReqArray => ∀ x ∈ a₁.blocks, ∀ y ∈ a₂.blocks,
      (laidMeets x.firstRow x.rowBits y.firstRow y.rowBits &&
        laidMeets x.firstPlace x.placeBits y.firstPlace y.placeBits) = false := by
    intro a₁ a₂ e u hu v hv
    rw [laidMeets_comm u.firstRow, laidMeets_comm u.firstPlace]
    exact e v hv u hu
  have := hp.forall hsym ha ha' hne b hb b' hb'
  rw [meets_of_both p1 p2 q1 q2, meets_of_both p3 p4 q3 q4] at this
  exact absurd this (by simp)

/-- **BOTH WAYS, OF A LIST OF ARRAYS THAT THE PLAN's TEST PASSES.** -/
theorem listBack_iff (a : ReqArray) (i c r j : Nat) :
    (as.findSome? fun a => (arrayBack a r j).map fun p => (a, p.1, p.2)) = some (a, i, c) ↔
      a ∈ as ∧ laidAt a i c = some (r, j) := by
  constructor
  · intro h
    obtain ⟨a', ha', e⟩ := List.exists_of_findSome?_eq_some h
    cases hb : arrayBack a' r j with
    | none => rw [hb] at e; exact absurd e (by simp)
    | some p =>
        rw [hb] at e
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, e1, e2⟩ := e
        refine ⟨ha', laidAt_of_arrayBack a' (fits_hA hf ha') ?_⟩
        rw [hb, ← e1, ← e2]
  · rintro ⟨ha, h⟩
    have h0 := arrayBack_of_laidAt a (fits_he hf ha) (fits_hT hf ha) h
    refine findSome_of_one _ _ _ a ha (by rw [h0]; rfl) fun a' ha' w hw => ?_
    cases hb : arrayBack a' r j with
    | none => rw [hb] at hw; exact absurd hw (by simp)
    | some p =>
        have e : a = a' := one_array hf ha ha' h0 hb
        subst e
        rw [h0] at hw
        exact (Option.some.inj hw).symm

end Plan

/-- **THE SAME AT laidBack ITSELF** (Johnson/Desc/ProofFile/Honest/LaidData.lean): under the plan's
test at the arrays of segment l that lie in message m: the list at which Own.reqMessageLaid holds
it. -/
theorem laidBack_iff (lay : OnBytes.Params.ReqLayout) (l m R P : Nat)
    (hf : laidFits ((lay.link.getD l []).filter fun a => a.message == m) R P = true)
    (a : ReqArray) (i c r j : Nat) :
    laidBack lay l m r j = some (a, i, c) ↔
      a ∈ ((lay.link.getD l []).filter fun a => a.message == m) ∧ laidAt a i c = some (r, j) :=
  listBack_iff hf a i c r j

/-! ### Tests -/

namespace LaidListsToy

/-- two laid blocks of 2 x 2 elements, side by side in the array and in the table -/
def good : ReqArray :=
  ⟨"T", 0, 2, 4, [⟨0, 0, 0, 0, 1, 1, 1, 1, true⟩, ⟨0, 2, 0, 2, 1, 1, 1, 1, true⟩]⟩

/-- the same, but the second lies on the first's places of the table -/
def bad : ReqArray :=
  ⟨"T", 0, 2, 4, [⟨0, 0, 0, 0, 1, 1, 1, 1, true⟩, ⟨0, 2, 0, 0, 1, 1, 1, 1, true⟩]⟩

#guard laidFits [good] 1 2
#guard (List.range 2).all fun i => (List.range 4).all fun c =>
  ((laidAt good i c).bind fun p => arrayBack good p.1 p.2) == some (i, c)
-- a negative test: the plan's test rejects the second array; and there the way back hands ANOTHER
-- element than the one that the rule laid
#guard !laidFits [bad] 1 2
#guard laidAt bad 0 2 == some (0, 0)
#guard arrayBack bad 0 0 == some (0, 0)

end LaidListsToy

end ProofFile.Honest

#print axioms ProofFile.Honest.noTwo_pairwise
#print axioms ProofFile.Honest.findSome_of_one
#print axioms ProofFile.Honest.place_rect
#print axioms ProofFile.Honest.meets_of_both
#print axioms ProofFile.Honest.laidMeets_comm
#print axioms ProofFile.Honest.same_of_meet
#print axioms ProofFile.Honest.arrayBack_of_laidAt
#print axioms ProofFile.Honest.laidAt_of_arrayBack
#print axioms ProofFile.Honest.laidAt_iff_arrayBack
#print axioms ProofFile.Honest.fits_matrix
#print axioms ProofFile.Honest.fits_table
#print axioms ProofFile.Honest.fits_he
#print axioms ProofFile.Honest.fits_hA
#print axioms ProofFile.Honest.fits_hT
#print axioms ProofFile.Honest.one_array
#print axioms ProofFile.Honest.listBack_iff
#print axioms ProofFile.Honest.laidBack_iff
#print axioms ProofFile.Honest.LaidListsToy.good
#print axioms ProofFile.Honest.LaidListsToy.bad
