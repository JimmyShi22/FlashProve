-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K3RowXB.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): THE SIX HYPOTHESES
ON THE PUBLIC DATA ALONE (`ReadsX X`, K3RowX.lean) AS ONE TEST WITH CODE. Definitions, and laws
without a kernel fact.
  `sameCall`, `sameList`, `sameView`: tests with code on calls WITHOUT A TABLE, on lists of them and
    on views; `sameCall_eq`, `sameList_eq`, `sameView_eq`: a yes gives the equation. A call with a
    table is refused on either side.
  `readsXAt X i`, `readsXB X : Bool`: at each of the 25 segments: the two views; at both lookups the
    host's count, the padding key's test and whether a step without a round stands behind; whether
    the caller's readers are there.
  `readsX_of`: **`readsXB X = true → ReadsX X`.**
WHAT IT READS OF X, by the texts of lookAt, laidAt, padKeyAt, quietAt (Johnson/Desc/First/Look/) and
K3Lot.readersAt: layers (y.h.p4 · y.NGr · y.cl · y.fo · y.h.lidb · y.h.lmb · wsLay.lk · what
laidLayers reads) · G (each plan's Fp · ns · tl) · A (each plan's S · fs · lid · seam.Fp · seam.tl ·
ns) · hS · HLy (cl · fs) · H (Fp.trees · ns · tl). NOT: P · the digests · owner.
IS THE TEST STRONGER THAN `ReadsX`? By its text, nowhere: where a lookup's place is not there it
says no, as the hypothesis does; "both tables are none" is what the equation with a written call
(whose table is none) says; at the calls the views compared are the stripped ones (`viewOf true`).
The converse is not stated.
Limits. That the test says yes at any public data is not said here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RowX

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt)
open VerifiableInference.Desc.First.Look (lookAt laidAt padKeyAt)

/-- Two calls without a table are one. -/
def sameCall (a b : Call) : Bool :=
  a.name == b.name && a.n == b.n && a.iota == b.iota && a.k == b.k && a.kappa == b.kappa &&
    a.fn == b.fn && a.t0 == b.t0 && a.tau.isNone && b.tau.isNone && a.pub == b.pub &&
    a.heavy == b.heavy

theorem sameCall_eq {a b : Call} (h : sameCall a b = true) : a = b := by
  cases a
  cases b
  simp only [sameCall, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩, e11⟩ := h
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  rfl

def sameList : List Call → List Call → Bool
  | [], [] => true
  | a :: l, b :: m => sameCall a b && sameList l m
  | _, _ => false

theorem sameList_eq : ∀ {l m : List Call}, sameList l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [sameList, Bool.and_eq_true] at h
    rw [sameCall_eq h.1, sameList_eq h.2]
  | [], _ :: _, h => by simp [sameList] at h
  | _ :: _, [], h => by simp [sameList] at h

/-- Two views are one. -/
def sameView (v w : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat) : Bool :=
  v.1 == w.1 && v.2.1 == w.2.1 && sameList v.2.2.1.toList w.2.2.1.toList && v.2.2.2 == w.2.2.2

theorem sameView_eq {v w : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat}
    (h : sameView v w = true) : v = w := by
  obtain ⟨v1, v2, v3, v4⟩ := v
  obtain ⟨w1, w2, w3, w4⟩ := w
  simp only [sameView, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h
  have e3' : v3 = w3 := Array.toList_inj.1 (sameList_eq e3)
  subst e1 e2 e3' e4
  rfl

/-- The test at one segment. -/
def readsXAt (X : Verify.Public) (i : Nat) : Bool :=
  ((lookAt X i false).any fun x => sameView (viewOf true x) (viewW i false)) &&
    ((lookAt X i true).any fun x => sameView (viewOf false x) (viewW i true)) &&
    ([false, true].all fun d => laidAt X i d == some (pubW (sortOf i) d) &&
      padKeyAt X i d == some true && (quietAt X i d).isSome == quietW i d) &&
    ((K3Lot.readersAt X i).isSome == callerW i)

/-- **THE SIX, AS ONE TEST WITH CODE.** -/
def readsXB (X : Verify.Public) : Bool := (List.range 25).all (readsXAt X)

theorem view_of_any {o : Option First.Look.Place} {s : Bool}
    {w : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat}
    (h : (o.any fun x => sameView (viewOf s x) w) = true) : ∃ x, o = some x ∧ viewOf s x = w := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, sameView_eq (by simpa using h)⟩

/-- **A YES GIVES THE SIX.** -/
theorem readsX_of {X : Verify.Public} (h : readsXB X = true) : ReadsX X := by
  have H : ∀ i < 25, readsXAt X i = true := fun i hi =>
    List.all_eq_true.1 h i (List.mem_range.2 hi)
  have D : ∀ i < 25, ∀ d, (laidAt X i d == some (pubW (sortOf i) d) &&
      padKeyAt X i d == some true && (quietAt X i d).isSome == quietW i d) = true := by
    intro i hi d
    have h0 := H i hi
    simp only [readsXAt, Bool.and_eq_true] at h0
    exact List.all_eq_true.1 h0.1.2 d (by cases d <;> simp)
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi d => ?_, fun i hi d => ?_, fun i hi d => ?_,
    fun i hi => ?_⟩
  · have h0 := H i hi
    simp only [readsXAt, Bool.and_eq_true] at h0
    exact view_of_any h0.1.1.1
  · have h0 := H i hi
    simp only [readsXAt, Bool.and_eq_true] at h0
    exact view_of_any h0.1.1.2
  · have h0 := D i hi d
    simp only [Bool.and_eq_true, beq_iff_eq] at h0
    exact h0.1.1
  · have h0 := D i hi d
    simp only [Bool.and_eq_true, beq_iff_eq] at h0
    exact h0.1.2
  · have h0 := D i hi d
    simp only [Bool.and_eq_true, beq_iff_eq] at h0
    exact h0.2
  · have h0 := H i hi
    simp only [readsXAt, Bool.and_eq_true, beq_iff_eq] at h0
    exact h0.2

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.sameCall_eq
#print axioms Johnson.AtFull.Lots.K3.sameList_eq
#print axioms Johnson.AtFull.Lots.K3.sameView_eq
#print axioms Johnson.AtFull.Lots.K3.view_of_any
#print axioms Johnson.AtFull.Lots.K3.readsX_of
