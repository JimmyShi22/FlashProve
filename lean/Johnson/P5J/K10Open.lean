-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Open.lean: THREE FACTS ON THE TABLE's WRITTEN LISTS AT THE PLACES OF THE KIND K10:
the premises hOut, hO and hP of `k10_hQ_at_fa` (Johnson/Desc/First/Close/Law/HQAtFa.lean).
Statements and proofs; six evaluations by the kernel.

  `oAt i`: what is open at border i: the list at which the table's promise speaks there (`onQ`,
    Johnson/Desc/Sound/BordersQ.lean).
  `okOut d a`: "pinKept" of link (the place's link + d) is among what the place's row opens. `okRows
    a O`: every item that the row closes or reads is open in O. `okPins a O`: a moment's samples'
    class of the place's link is open in O only at a moment below 3 whose pin is open in O.
    `k10OpenBy ok`: the test ok at every place of the kind K10 of `At.ps`, with the open list there:
    one walk.
  `k10_open_full`: the three together say yes: by the kernel.
  NEGATIVE TESTS, ONE A TEST, EACH BY THE KERNEL: `k10_open_bent`: with "pinKept" of the NEXT link
    in `okOut`'s place the walk says no. `k10_rows_bent`: `okRows` at the open list without the
    link's own rows (`okRowsBent`) says no. `k10_pins_bent`: `okPins` with moments below 2 alone
    allowed (`okPinsBent`) says no. `k10_pins_not_idle`: at every such place a samples' class of the
    place's own link is open (`someSample`): `okPins` is idle nowhere.
  `k10_out_at`, `k10_rows_open_at`, `k10_samples_pins_at`: hOut, hO, hP at fullLinks, At.ps, k := i,
    O := `oAt i`, the link the place's own. Beneath: `openSets_length`, `k10_open_at`, `rowQ_at`.
Limits. Facts on the table's written lists. Nothing on the laws. Nothing on soundness.

-/
import Johnson.P5J.K10Ins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace P5J

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (Item RowClass ModelPart rowOf openSets start)
open VerifiableInference.Desc.Sound (insQ outsQ rowQ)

/-- What is open at border i. -/
def oAt (i : ℕ) : List Item := (openSets fullLinks At.ps (start fullLinks))[i]?.getD []

/-- "pinKept" of link (the place's + d) is among what the row opens. -/
def okOut (d : ℕ) (a : Place) : Bool :=
  (rowOf fullLinks a).outs.contains (Item.pinKept (a.link.getD 0 + d))

/-- Every item that the row closes or reads is open. -/
def okRows (a : Place) (O : List Item) : Bool :=
  ((rowOf fullLinks a).ins ++ (rowOf fullLinks a).ctx).all O.contains

/-- A moment's samples are open only with that moment's pin. -/
def okPins (a : Place) (O : List Item) : Bool :=
  O.all fun it => match it with
    | .row m (.sample t) => m != a.link.getD 0 || (decide (t < 3) && O.contains (Item.pin m t))
    | _ => true

/-- One walk along the places and the open lists. -/
def k10OpenBy (ok : Place → List Item → Bool) : Bool :=
  (At.ps.zip (openSets fullLinks At.ps (start fullLinks))).all fun x =>
    x.1.kind != KindName.K10 || ok x.1 x.2

theorem k10_open_full :
    k10OpenBy (fun a O => okOut 0 a && okRows a O && okPins a O) = true := by decide +kernel

/-- A negative test: the next link's "pinKept" is not what the row opens. -/
theorem k10_open_bent :
    k10OpenBy (fun a O => okOut 1 a && okRows a O && okPins a O) = false := by decide +kernel

/-- The like of `okRows`, asked of the open list WITHOUT its rows of the place's own link. -/
def okRowsBent (a : Place) (O : List Item) : Bool :=
  okRows a (O.filter fun it => match it with
    | .row m _ => m != a.link.getD 0
    | _ => true)

/-- The like of `okPins`, with moments below 2 alone allowed. -/
def okPinsBent (a : Place) (O : List Item) : Bool :=
  O.all fun it => match it with
    | .row m (.sample t) => m != a.link.getD 0 || (decide (t < 2) && O.contains (Item.pin m t))
    | _ => true

/-- A samples' class of the place's own link is open. -/
def someSample (a : Place) (O : List Item) : Bool :=
  O.any fun it => match it with
    | .row m (.sample _) => m == a.link.getD 0
    | _ => false

/-- A negative test: `okRows` says no where the link's own rows are struck from the open list. -/
theorem k10_rows_bent : k10OpenBy okRowsBent = false := by decide +kernel

/-- A negative test: `okPins` says no where moment 2 is not allowed. -/
theorem k10_pins_bent : k10OpenBy okPinsBent = false := by decide +kernel

/-- `okPins` is idle at no place: a samples' class of the place's own link is open there. -/
theorem k10_pins_not_idle : k10OpenBy someSample = true := by decide +kernel

theorem openSets_length (links : List ModelPart) : ∀ (ps : List Place) (O : List Item),
    (openSets links ps O).length = ps.length + 1
  | [], _ => rfl
  | _ :: ps, _ => by
    show (openSets links ps _).length + 1 = _
    rw [openSets_length links ps]
    rfl

/-- The three tests at one place. -/
theorem k10_open_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    okOut 0 a = true ∧ okRows a (oAt i) = true ∧ okPins a (oAt i) = true := by
  have hi : i < At.ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have hl : i < (openSets fullLinks At.ps (start fullLinks)).length := by
    rw [openSets_length]
    omega
  have hO : (openSets fullLinks At.ps (start fullLinks))[i]? = some (oAt i) := by
    unfold oAt
    rw [List.getElem?_eq_getElem hl]
    rfl
  have hz : (At.ps.zip (openSets fullLinks At.ps (start fullLinks)))[i]? = some (a, oAt i) :=
    List.getElem?_zip_eq_some.2 ⟨ha, hO⟩
  have h := List.all_eq_true.1 k10_open_full _ (List.mem_of_getElem? hz)
  have h1 : (a.kind != KindName.K10 || (okOut 0 a && okRows a (oAt i) && okPins a (oAt i))) =
      true := h
  rw [hk] at h1
  have h2 : (okOut 0 a && okRows a (oAt i) && okPins a (oAt i)) = true := h1
  rw [Bool.and_eq_true, Bool.and_eq_true] at h2
  exact ⟨h2.1.1, h2.1.2, h2.2⟩

theorem rowQ_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a) :
    rowQ fullLinks At.ps i = rowOf fullLinks a := by
  unfold rowQ
  rw [ha]
  rfl

/-- **hOut.** -/
theorem k10_out_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    outsQ fullLinks At.ps i (Item.pinKept (a.link.getD 0)) := by
  have h := (k10_open_at i a ha hk).1
  unfold outsQ
  rw [rowQ_at i a ha]
  exact List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.1 h))

/-- **hO.** -/
theorem k10_rows_open_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) (c : RowClass)
    (h : insQ fullLinks At.ps i (Item.row (a.link.getD 0) c)) :
    Item.row (a.link.getD 0) c ∈ oAt i := by
  have h2 := (k10_open_at i a ha hk).2.1
  unfold insQ at h
  rw [rowQ_at i a ha] at h
  rcases List.mem_append.1 h with hm | hm
  · exact List.contains_iff_mem.1 (List.all_eq_true.1 h2 _ hm)
  · simp at hm

/-- **hP.** -/
theorem k10_samples_pins_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) (t : ℕ)
    (h : Item.row (a.link.getD 0) (.sample t) ∈ oAt i) :
    t < 3 ∧ Item.pin (a.link.getD 0) t ∈ oAt i := by
  have h3 := List.all_eq_true.1 (k10_open_at i a ha hk).2.2 _ h
  have h4 : (a.link.getD 0 != a.link.getD 0 ||
      (decide (t < 3) && (oAt i).contains (Item.pin (a.link.getD 0) t))) = true := h3
  have h5 : (decide (t < 3) && (oAt i).contains (Item.pin (a.link.getD 0) t)) = true := by
    simpa using h4
  rw [Bool.and_eq_true] at h5
  exact ⟨of_decide_eq_true h5.1, List.contains_iff_mem.1 h5.2⟩

end P5J

#print axioms P5J.k10_open_full
#print axioms P5J.k10_open_bent
#print axioms P5J.k10_rows_bent
#print axioms P5J.k10_pins_bent
#print axioms P5J.k10_pins_not_idle
#print axioms P5J.openSets_length
#print axioms P5J.k10_open_at
#print axioms P5J.rowQ_at
#print axioms P5J.k10_out_at
#print axioms P5J.k10_rows_open_at
#print axioms P5J.k10_samples_pins_at
