-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05FormsKept.lean: kind K5: THE PUBLIC TESTS "a form names only what is there"
(FormsIn.lean: slotIn, lateOk, entInT, affInT, formsInT) OVER THE HEARING's LAY:
what held of a list of forms at the record in front holds of THE SAME LIST at the record behind.

BUILT ON Johnson/Desc/First/Batch/FormsIn.lean AND WHAT IT IMPORTS:
imported, not turned.
Main names:
  `LedgerUp a b`: of two parts (K9.Part): the link's context and the chain's state are the same; the
    ledger of b is sized, holds what a's held (Stays, Att/K5Said.lean) and is Below a's
    (Att/K05HearBelow.lean).
  `slotIn_up`, `lateOk_up`, `entInT_up`, `affInT_up`: the tests ride from a to b; lateOk under: the
    late slots lie below the next free number of a's ledger.
  `segAt_front`, `segAt_behind`, `ledgerUp_behind`: at an open attention segment, over the lay.
  `formsInT_kept`: **formsInT Rd own k r rides over the lay**, UNDER TWO PREMISES: hR: the reader
    gives at the record behind what it gave in front; hl: its late slots lie below the next free
    number in front.
Limits. hR IS THE RUN's FILES' DEBT (for the lookup's runs "objects" and "guests": its files'): a
reader that is the run itself, called at the record, reads the ledger, which the lay turns. Nothing
on the runs that the lay itself makes readable. EMPTY AT: a reader that gives nothing in front.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindLay
import Johnson.Desc.First.Att.K05Paid
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9 (seatAt arrayIn entIn maskSeat lateAt lateOk slotIn atMoment1 entInT
  affInT Read Readers segAt? formsInT mergeOf)

/-- The later part has the earlier part's context and state; its ledger has grown. -/
structure LedgerUp (a b : K9.Part) : Prop where
  L : b.L = a.L
  d : b.d = a.d
  sized : Sized b.F
  stays : Stays a.F b.F
  below : Below a.F b.F

section
variable (own : List (Nat × Nat)) (free : Option Nat) (late : List (Nat × E × E)) {a b : K9.Part}

theorem maskSeat_up (u : LedgerUp a b) : maskSeat own b = maskSeat own a := by
  unfold maskSeat
  rw [u.L, u.d]

theorem slotIn_up (u : LedgerUp a b) (j : Nat) (h : slotIn own free late a j = true) :
    slotIn own free late b j = true := by
  unfold slotIn at h ⊢
  rw [maskSeat_up own u, u.below.ns]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rcases h4 with h4 | ⟨h4, _, _⟩
  · exact Or.inl h4
  · refine Or.inr ⟨(u.stays j _ _ ⟨h4, rfl, rfl⟩).1, ?_, ?_⟩
    · rw [u.sized.vp, u.below.ns]
      exact h1
    · rw [u.sized.mf, u.below.ns]
      exact h1

theorem lateOk_up (u : LedgerUp a b) (hl : ∀ x ∈ late, x.1 < a.F.next)
    (h : lateOk late a = true) : lateOk late b = true := by
  unfold lateOk at h ⊢
  refine List.all_eq_true.2 fun x hx => ?_
  have h0 := List.all_eq_true.1 h x hx
  obtain ⟨p1, p2, p3⟩ := u.below.2.2 x.1 (hl x hx)
  rw [u.below.ns, p1, p2, p3 false]
  exact h0

theorem entInT_up (u : LedgerUp a b) (x : Ent) : entInT own b x = entInT own a x := by
  unfold entInT entIn arrayIn atMoment1
  rw [u.L, u.d]

theorem affInT_up (u : LedgerUp a b) (f : Aff) (h : affInT own free late a f = true) :
    affInT own free late b f = true := by
  unfold affInT at h ⊢
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
  · refine List.all_eq_true.2 fun x hx => ?_
    rw [entInT_up own u x]
    exact List.all_eq_true.1 h1 x hx
  · exact List.all_eq_true.2 fun x hx => slotIn_up own free late u x.1 (List.all_eq_true.1 h2 x hx)

end

section
variable {s : First.S} {a : First.AttOwn} {own5 : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : Heard} {G : Fork}

/-- The open segment's part in front. -/
def partAt (s : First.S) (a : First.AttOwn) (F : Fork) (owed : Option Nat) : K9.Part :=
  { owed := owed, used := F.next, laid := K9.laidOf a.tl, L := a.L, F := F,
    d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } }

theorem segAt_front (e : s.here = .att a) : segAt? s = some (partAt s a a.F (K9.owedOf s)) := by
  unfold segAt?
  rw [link_front e, fork_front e, tl_front e]
  unfold K9.usedOf
  rw [e]
  rfl

theorem segAt_behind : segAt? (behind s a h G) = some (partAt s a G none) := rfl

theorem ledgerUp_behind (hh : hear own5 (a.F, rs, 0) = some (h, G, [], 0)) (hz : Sized a.F)
    (o o' : Option Nat) : LedgerUp (partAt s a a.F o) (partAt s a G o') := by
  obtain ⟨_, _, _, _, st, _⟩ := hear_law_paid hh hz
  obtain ⟨zG, bl⟩ := hear_below hh hz
  exact ⟨rfl, rfl, zG, st, bl⟩

theorem mergeOf_behind (e : s.here = .att a) : mergeOf (behind s a h G) = mergeOf s := by
  unfold mergeOf
  rw [e]
  rfl

/-- **The test beside "the forms of a run are worth 0" rides over the hearing's lay.** -/
theorem formsInT_kept (Rd : Readers) (own : List (Nat × Nat)) (k : Nat) (r : String)
    (e : s.here = .att a) (hh : hear own5 (a.F, rs, 0) = some (h, G, [], 0)) (hz : Sized a.F)
    (hR : Rd.forms k r (behind s a h G) = Rd.forms k r s)
    (hl : ∀ R, Rd.forms k r s = some R → ∀ x ∈ R.late, x.1 < a.F.next)
    (hin : formsInT Rd own k r s = true) : formsInT Rd own k r (behind s a h G) = true := by
  unfold formsInT at hin ⊢
  rw [segAt_behind, hR, mergeOf_behind e]
  rw [segAt_front e] at hin
  cases hq : Rd.forms k r s with
  | none =>
    rw [hq] at hin
    cases hin
  | some R =>
    rw [hq] at hin
    have u := ledgerUp_behind (s := s) hh hz (K9.owedOf s) none
    obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    refine Eq.mpr (Bool.and_eq_true _ _) ⟨lateOk_up R.late u (hl R hq) h1, ?_⟩
    exact List.all_eq_true.2 fun f hf =>
      affInT_up own (mergeOf s) R.late u f (List.all_eq_true.1 h2 f hf)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.slotIn_up
#print axioms VerifiableInference.Desc.First.Att.P.lateOk_up
#print axioms VerifiableInference.Desc.First.Att.P.affInT_up
#print axioms VerifiableInference.Desc.First.Att.P.ledgerUp_behind
#print axioms VerifiableInference.Desc.First.Att.P.formsInT_kept
