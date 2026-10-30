-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StatedCellIn.lean: THE FORM OF A KIND's HALF OF THE EXCHANGE (ArmCell, Johnson/Desc/Sound/StatedCell.lean) WITH THE RANGES HANDED IN. One definition, three theorems.
WORDS. "The verifier's state": the value of type First.S that the verifier carries between two sub-protocols.
WHY: ArmCell asks its equation at the entries that the run's forms name; that such an entry lies INSIDE THE ARRAY's RANGES (x.row < A.sizeI, x.idx < A.sizeC: at the array of the reads: one row) is the public test's second arm (entInT, inside formsInT): ArmCell's binders do not carry it: "three kinds, three unfoldings".
  ArmCellIn: ArmCell with one hypothesis more behind "x is an entry of the form": entInT own a x = true. A WEAKER DEMAND ON THE KIND's FILES.
  entInT_of_formsInT: the unfolding, once: the public test's yes at the state in front gives entInT at every entry of every form of the run.
  second_ranges: at the name c of x's array, where the entry is no cell of an array that is there already (entIn own a x = false), entInT gives the layout's array A of that name with x.row < A.sizeI and x.idx < A.sizeC.
  armCell_of_in: ArmCellIn and the public test give ArmCell: so hcell_of_arm | formsTQ_of_arm are called as they lie.

Limits. A rule. Nobody's ArmCellIn is shown here. At a place inside the ranges that no table owns the committed cell and the stated sum need not agree: that the tables tile the array is the approximate range proof's own check, at the state behind the sending: each kind's files will want that fact: not handed in here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StatedCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.K9 (segAt? Read Readers formsInT affInT entInT entIn atMoment1 mergeOf)

section
variable (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S) (a b : K9.Part)
  (rd : ℕ × ℕ → MsgQ)

/-- **THE FORM OF A KIND's HALF, the public test on the entry handed in.** -/
def ArmCellIn (u : UFn) : Prop :=
  ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
    entInT own a x = true → ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c → second s c = true →
      (dataQ own' b rd).cell c.1 c.2 x.row x.idx = u s (dataQ own a rd) c x.row x.idx

/-- The public test's yes, unfolded once. -/
theorem entInT_of_formsInT (ha : segAt? s = some a) (hin : formsInT Rd own piece run s = true)
    (R : Read) (hR : Rd.forms piece run s = some R) (f : Aff) (hf : f ∈ R.forms) (x : Ent)
    (hx : x ∈ f.ents.toList) : entInT own a x = true := by
  unfold formsInT at hin
  rw [ha, hR] at hin
  obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  have hi : affInT own (mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hf
  unfold affInT at hi
  obtain ⟨h1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hi
  exact List.all_eq_true.1 h1 x hx

/-- **ArmCellIn and the public test give ArmCell.** -/
theorem armCell_of_in (u : UFn) (ha : segAt? s = some a)
    (hin : formsInT Rd own piece run s = true)
    (h : ArmCellIn Rd own own' piece run s a b rd u) : ArmCell Rd own own' piece run s a b rd u :=
  fun R hR f hf x hx c hc hs =>
    h R hR f hf x hx (entInT_of_formsInT Rd own piece run s a ha hin R hR f hf x hx) c hc hs

end

/-- **The ranges**: what entInT's second arm gives at an entry that is no cell of an array that is there already. -/
theorem second_ranges (own : List (ℕ × ℕ)) (a : K9.Part) (x : Ent) (c : ℕ × String)
    (hc : a.L.arrayOf[x.tree]? = some c) (h : entInT own a x = true) (h0 : entIn own a x = false) :
    ∃ A, reqArray a.L.check.rows.layout c.1 c.2 = some A ∧ atMoment1 a c A = true ∧
      x.row < A.sizeI ∧ x.idx < A.sizeC := by
  unfold entInT at h
  rw [h0, Bool.false_or, hc] at h
  dsimp only at h
  cases hA : reqArray a.L.check.rows.layout c.1 c.2 with
  | none => rw [hA] at h; cases h
  | some A =>
    rw [hA] at h
    obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
    obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _) h2
    exact ⟨A, rfl, h1, of_decide_eq_true h3, of_decide_eq_true h4⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.entInT_of_formsInT
#print axioms VerifiableInference.Desc.Sound.armCell_of_in
#print axioms VerifiableInference.Desc.Sound.second_ranges
