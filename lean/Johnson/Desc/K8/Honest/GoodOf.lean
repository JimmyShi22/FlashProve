-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/GoodOf.lean: THE SMALLNESS TEST: `PlanesGood` AND `DigitsGood`
(Johnson/Desc/K8/Honest/PlanesLiveOf.lean, DigitsLiveOf.lean) FROM CONDITIONS THAT COME APART:
VALUES AND SHAPES OF WHAT THE DIGITS' LOOKUP HAS HEARD ON ONE SIDE, A TEST ON PUBLIC NUMBERS ON THE
OTHER. A definition with code, statements and proofs. On plain data: no block, no prover. Lemmas;
none of the library's goals.

tl: the smallness test's data; g: what its lookup has heard.
  `addSlots_ents`, **`rowForm_ents`**   an entry that the form of a sumcheck's claim names stands at
      the place of an entry that the form which the sumcheck was handed names
  **`planesGood_of`**   the form that the leaves' sumcheck was handed names no entry; eps and the
      leaves' factor are not 0; no coordinate number 5 to 5 + kT + cK - 1 of the two points on the
      planes is 0 or 1 (`mem_extract`: so where none of all is); each of the two points has at least
      5 + kT + cK coordinates: then `PlanesGood tl g`
  `piecesFit tl`   with code, on public numbers: for each piece of the two calls, its index and its
      stretch of coordinates lie within the call's number of coordinates, and it has no more columns
      than its table has entries
  **`digitsGood_of`**   the form of the key side's end names no entry; the two calls' weights are
      not 0; no coordinate of the two calls' points is 0 or 1; each call's point has the call's
      number of coordinates; `piecesFit tl`: then `DigitsGood tl g`
By: `addMul_ents`, `mem_extract`, `pair_lt` (DigitsLiveOf.lean) · Psc.rowForm, addSlots
(OnBytes/Model/Psc.lean) · bzColumns (OnBytes/Model/Tail.lean) · eqIndexOK
(OnBytes/Model/Frame.lean).
Limits. Every condition is a premise: that any state's data meet them is not shown here. Nothing on
any measure.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.DigitsLiveOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

theorem no_ent (a : Aff) (h : a.ents.isEmpty = true) (x : Ent) : x ∉ a.ents.toList := by
  have h0 : a.ents = #[] := Array.isEmpty_iff.1 h
  rw [h0]
  exact List.not_mem_nil

theorem addSlot_fold : ∀ (l : List E) (s : Nat × Aff) (x : Ent),
    x ∈ (l.foldl addSlot s).2.ents.toList → x ∈ s.2.ents.toList
  | [], _, _, h => h
  | c :: l, (j, u), x, h => by
    rw [List.foldl_cons] at h
    have h1 : x ∈ (Aff.addMul u (Aff.slot j) c).ents.toList := addSlot_fold l _ x h
    rcases addMul_ents _ _ _ x h1 with h2 | ⟨y, hy, -⟩
    · exact h2
    · simp [Aff.slot] at hy

/-- The slots' terms bring no entry. -/
theorem addSlots_ents (a : Aff) (first : Nat) (form : Array E) (x : Ent)
    (h : x ∈ (addSlots a first form).ents.toList) : x ∈ a.ents.toList := by
  unfold addSlots at h
  rw [← Array.foldl_toList] at h
  exact addSlot_fold _ _ x h

/-- **The entries of the form of a sumcheck's claim.** -/
theorem rowForm_ents (p : Psc) (S0 : E) (x : Ent) (h : x ∈ (p.rowForm S0 {}).ents.toList) :
    ∃ y ∈ p.start.ents.toList, x.tree = y.tree ∧ x.row = y.row ∧ x.idx = y.idx := by
  unfold Psc.rowForm at h
  rcases addMul_ents _ _ _ x h with h1 | ⟨y, hy, -⟩
  · rcases addMul_ents _ _ _ x h1 with h2 | ⟨y, hy, e1, e2, e3⟩
    · have h3 := addSlots_ents _ _ _ x h2
      simp [Aff.ofConst] at h3
    · rcases addMul_ents _ _ _ y hy with h4 | ⟨z, hz, f1, f2, f3⟩
      · simp [Aff.ofConst] at h4
      · exact ⟨z, hz, e1.trans f1, e2.trans f2, e3.trans f3⟩
  · exact absurd hy List.not_mem_nil

theorem size_stretch (z : Array E) (a n : Nat) (h : a + n ≤ z.size) :
    (z.extract a (a + n)).size = n := by
  rw [Array.size_extract]
  omega

/-- **`PlanesGood` from values and shapes of what was heard.** -/
theorem planesGood_of (tl : HTailF2) (g : Forest.Heard)
    (hs : g.leaves.start.ents.isEmpty = true) (heps : Reading.gl.val g.leaves.eps ≠ 0)
    (hA : Reading.gl.val g.leavesA ≠ 0)
    (h0 : ∀ w ∈ (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)).toList,
      Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1)
    (h1 : ∀ w ∈ (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)).toList,
      Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1)
    (s0 : 5 + tl.f9.kT + tl.f9.cK ≤ g.zb0.size) (s1 : 5 + tl.f9.kT + tl.f9.cK ≤ g.zb1.size) :
    PlanesGood tl g where
  rowFree := fun x hx => by
    obtain ⟨y, hy, -⟩ := rowForm_ents _ _ x hx
    exact absurd hy (no_ent _ hs y)
  eps := heps
  leavesA := hA
  zb0 := h0
  zb1 := h1
  wide0 := by
    have e : (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)).size = tl.f9.kT + tl.f9.cK := by
      rw [Nat.add_assoc]
      exact size_stretch _ _ _ (by omega)
    rw [e]
    unfold HTailF2.bzColumns
    exact Nat.le_refl _
  wide1 := by
    have e : (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)).size = tl.f9.kT + tl.f9.cK := by
      rw [Nat.add_assoc]
      exact size_stretch _ _ _ (by omega)
    rw [e]
    unfold HTailF2.bzColumns
    exact Nat.le_refl _

/-- On public numbers: each piece's index and stretch fit its call. -/
def piecesFit (tl : HTailF2) : Bool :=
  (joinPairs tl).all fun x =>
    decide (x.2.b ≤ (tl.zOf x.1).call.n) && decide ((tl.zOf x.1).call.n - x.2.b ≤ 63) &&
      decide (x.2.off / 2 ^ x.2.b < 2 ^ ((tl.zOf x.1).call.n - x.2.b)) &&
      decide ((tl.zOf x.1).call.n - x.2.b + x.2.a + clog2 x.2.CP ≤ (tl.zOf x.1).call.n) &&
      decide (x.2.Cp ≤ 2 ^ clog2 x.2.CP)

/-- **`DigitsGood` from values and shapes of what was heard, and the public test.** -/
theorem digitsGood_of (tl : HTailF2) (g : Forest.Heard) (hc : g.cEnd.ents.isEmpty = true)
    (he : ∀ q, q < 2 → Reading.gl.val (g.e.getD q zeroE) ≠ 0)
    (hz : ∀ q, q < 2 → ∀ w ∈ (g.zk.getD q #[]).toList,
      Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1)
    (hn : ∀ q, q < 2 → (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (hP : piecesFit tl = true) : DigitsGood tl g where
  cEndFree := fun x hx => absurd hx (no_ent _ hc x)
  e := he
  zk := hz
  idx := fun x hx => by
    have hf := List.all_eq_true.1 hP x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨⟨f1, f2⟩, f3⟩, -⟩, -⟩ := hf
    have hsz := hn x.1 (pair_lt tl x hx)
    have e : ((g.zk.getD x.1 #[]).extract 0 ((tl.zOf x.1).call.n - x.2.b)).size =
        (tl.zOf x.1).call.n - x.2.b := by
      rw [Array.size_extract]
      omega
    unfold eqIndexOK
    rw [e, decide_eq_true f2, decide_eq_true f3]
    rfl
  wide := fun x hx => by
    have hf := List.all_eq_true.1 hP x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨-, f4⟩, f5⟩ := hf
    have hsz := hn x.1 (pair_lt tl x hx)
    have e : (Fo.joinZc tl g x.1 x.2).size = clog2 x.2.CP := by
      unfold Fo.joinZc
      exact size_stretch _ _ _ (by omega)
    rw [e]
    exact f5

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.addSlots_ents
#print axioms VerifiableInference.Desc.First.K8.Honest.rowForm_ents
#print axioms VerifiableInference.Desc.First.K8.Honest.planesGood_of
#print axioms VerifiableInference.Desc.First.K8.Honest.digitsGood_of
