-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ExchangeStep.lean: two premises of the exchange across a segment's second
sending (`formsTQ_of_arm`, Johnson/Desc/Sound/StatedCell.lean) from the relation `Rides`
(Johnson/Desc/Sound/FormsQ.lean), where the seats read in front are among the seats read behind.

Why. The exchange reads the witness at two lists of seats: own, the first sending's, at the state in
front; own', the seats read behind. `cell_rides` and `mask_rides` of FormsQ.lean speak at one list.

Main names:
  `seatAt_wider`, `tabQ_rides2`, `cell_rides2`, `mask_rides2`: the same at two lists.
  `otherCells_of_rides`: `OtherCells`: at an array that is not of the second sending the cell read
    behind is the cell read in front.
  `hmask_of_rides`: the like for the entries of the mask row that a form names.
  `formsTQ_of_step`: the exchange with these two, and its premises on the arrays' list and the
    filled slots, paid by `Rides`.

What is not claimed. `ArmCell`, `StatedIs`, `Rides`, the reader's one answer and the public test
`formsInT` stay premises. That a sub-protocol's acceptance gives `Rides` is not shown here. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Sound.StatedCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound dataOf maskOracle)
open VerifiableInference.Desc.K9 (segAt? seatAt seatAt_mem arrayIn_some entIn entIn_some entInT
  atMoment1 affInT slotIn maskSeat maskAt Read Readers formsInT mergeOf)
open VerifiableInference.Desc.Sound (MsgQ GQ tabQ dataQ Rides Stated UFn StatedIs ArmCell
  OtherCells second formsQ formsTQ formsTQ_of_arm slotIn_mask maskAt_eq)

section
variable (own own' : List (ℕ × ℕ))

/-- A seat of the narrower list, in an earlier book, is a seat of the wider list in a later one. -/
theorem seatAt_wider (hsub : ∀ x ∈ own, x ∈ own') (book book' : OnBytes.TreeBook) (o : ℕ)
    (x : ℕ × ℕ) (hb : ∀ y, book.place[o]? = some y → book'.place[o]? = some y)
    (e : seatAt own book o = some x) : seatAt own' book' o = some x := by
  have hx : x ∈ own := seatAt_mem own book o x e
  unfold seatAt at e
  obtain ⟨y, h1, hy⟩ := Option.bind_eq_some_iff.1 e
  have hyx : y = x := by
    by_cases hc : own.contains y = true
    · rw [if_pos hc] at hy
      exact Option.some.inj hy
    · rw [if_neg hc] at hy
      exact nomatch hy
  subst hyx
  unfold seatAt
  rw [hb y h1, Option.bind_some, if_pos (List.contains_iff_mem.2 (hsub y hx))]

/-- At a seated message the later table, read at the wider list, is the earlier one's. -/
theorem tabQ_rides2 (st st' : OnBytes.Statement) (book book' : OnBytes.TreeBook)
    (rd : ℕ × ℕ → MsgQ) (o : ℕ) (x : ℕ × ℕ) (part : OnBytes.Part)
    (e : seatAt own book o = some x) (e' : seatAt own' book' o = some x)
    (hr : st'.rowBits o part = st.rowBits o part) :
    tabQ own' st' book' rd o part = tabQ own st book rd o part := by
  funext J
  unfold tabQ
  rw [e, e', hr]

/-- A cell of a seated array is the same at both states, read at the two lists. -/
theorem cell_rides2 (hsub : ∀ x ∈ own, x ∈ own') (a b : K9.Part) (rd : ℕ × ℕ → MsgQ)
    (h : Rides own a b) (c : ℕ × String) (A : Params.ReqArray) (o : ℕ) (x : ℕ × ℕ)
    (hA : reqArray a.L.check.rows.layout c.1 c.2 = some A)
    (ho : a.L.check.frame.whereIs c.1 A.message = some o)
    (hx : seatAt own a.d.book o = some x) (r i : ℕ) :
    (dataQ own' b rd).cell c.1 c.2 r i = (dataQ own a rd).cell c.1 c.2 r i := by
  have hx' := seatAt_wider own own' hsub a.d.book b.d.book o x (h.book o) hx
  have ht := tabQ_rides2 own own' a.d.st b.d.st a.d.book b.d.book rd o x .main hx hx'
    (h.bits o x .main hx).1
  simp only [dataQ, dataOf, h.rows, hA, ho, h.sent c.1 A.message o ho, ht,
    (h.bits o x .main hx).1, (h.bits o x .main hx).2]

/-- The mask row is the same at both states, read at the two lists. -/
theorem mask_rides2 (hsub : ∀ x ∈ own, x ∈ own') (a b : K9.Part) (rd : ℕ × ℕ → MsgQ)
    (h : Rides own a b) (x : ℕ × ℕ) (hm : maskSeat own a = some x) (j : ℕ) :
    (dataQ own' b rd).mask j = (dataQ own a rd).mask j := by
  unfold maskSeat at hm
  rw [maskAt_eq] at hm
  obtain ⟨o, ho, hx⟩ := Option.bind_eq_some_iff.1 hm
  have hx' := seatAt_wider own own' hsub a.d.book b.d.book o x (h.book o) hx
  have ht := tabQ_rides2 own own' a.d.st b.d.st a.d.book b.d.book rd o x .mask hx hx'
    (h.bits o x .mask hx).1
  simp only [dataQ, dataOf, ho, h.mask o ho, ht]

variable (Rd : Readers) (piece : ℕ) (run : String) (s : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ)

/-- What the public test says of one form of the run. -/
theorem affInT_of_formsInT (ha : segAt? s = some a) (hin : formsInT Rd own piece run s = true)
    (R : Read) (hR : Rd.forms piece run s = some R) (f : Aff) (hf : f ∈ R.forms) :
    affInT own (mergeOf s) R.late a f = true := by
  unfold formsInT at hin
  rw [ha, hR] at hin
  exact List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) hin).2 f hf

/-- **`OtherCells`.** -/
theorem otherCells_of_rides (hsub : ∀ x ∈ own, x ∈ own') (ha : segAt? s = some a)
    (hin : formsInT Rd own piece run s = true) (hr : Rides own a b) :
    OtherCells Rd own own' piece run s a b rd := by
  intro R hR f hf x hx c hc hs2
  have hi := affInT_of_formsInT own Rd piece run s a ha hin R hR f hf
  unfold affInT at hi
  have hx1 : entInT own a x = true :=
    List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) hi).1 x hx
  unfold entInT at hx1
  rcases Eq.mp (Bool.or_eq_true _ _) hx1 with h1 | h1
  · obtain ⟨A, hA⟩ := entIn_some own a x h1
    obtain ⟨c', o, y, hc', hq, ho, hy⟩ := arrayIn_some own a x.tree A hA
    obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
    exact cell_rides2 own own' hsub a b rd hr c' A o y hq ho hy x.row x.idx
  · exfalso
    rw [hc] at h1
    unfold second at hs2
    rw [ha] at hs2
    replace h1 : (match reqArray a.L.check.rows.layout c.1 c.2 with
      | none => false
      | some A => atMoment1 a c A && (decide (x.row < A.sizeI) && decide (x.idx < A.sizeC))) =
        true := h1
    replace hs2 : (match reqArray a.L.check.rows.layout c.1 c.2 with
      | some A => atMoment1 a c A
      | none => false) = false := hs2
    cases hq : reqArray a.L.check.rows.layout c.1 c.2 with
    | none => rw [hq] at h1; cases h1
    | some A =>
      rw [hq] at h1 hs2
      have h2 : atMoment1 a c A = true := (Eq.mp (Bool.and_eq_true _ _) h1).1
      have h3 : atMoment1 a c A = false := hs2
      rw [h2] at h3
      cases h3

/-- **The entries of the mask row that a form names are the same.** -/
theorem hmask_of_rides (hsub : ∀ x ∈ own, x ∈ own') (ha : segAt? s = some a)
    (hin : formsInT Rd own piece run s = true) (hr : Rides own a b) :
    ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQ own' b rd).mask x.1 = (dataQ own a rd).mask x.1 := by
  intro R hR f hf x hx
  have hi := affInT_of_formsInT own Rd piece run s a ha hin R hR f hf
  unfold affInT at hi
  have hs1 : slotIn own (mergeOf s) R.late a x.1 = true :=
    List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) hi).2 x hx
  obtain ⟨y, hy⟩ := slotIn_mask own (mergeOf s) R.late a x.1 hs1
  exact mask_rides2 own own' hsub a b rd hr y hy x.1

end

/-- **The exchange over a step that rides**: "forms" at the state behind gives "formsT" at the state
in front. -/
theorem formsTQ_of_step (Rd : Readers) (St : Stated) (u : UFn) (own own' : List (ℕ × ℕ))
    (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ)
    (hsub : ∀ x ∈ own, x ∈ own') (hSt : StatedIs St u s) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsInT Rd own piece run s = true) (hr : Rides own a b)
    (h2 : ArmCell Rd own own' piece run s a b rd u) (h : formsQ Rd own' piece run s' rd) :
    formsTQ Rd St own piece run s rd :=
  formsTQ_of_arm Rd St u own own' piece run s s' a b rd hSt ha hb hl hin hr.arrays hr.filled h2
    (otherCells_of_rides own own' Rd piece run s a b rd hsub ha hin hr)
    (hmask_of_rides own own' Rd piece run s a b rd hsub ha hin hr) h

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.otherCells_of_rides
#print axioms VerifiableInference.Desc.K1.hmask_of_rides
#print axioms VerifiableInference.Desc.K1.formsTQ_of_step
