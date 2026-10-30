-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FormsAcross.lean: K11's SECOND TIE, THE SIX RUNS THAT ARE OPEN ON BOTH SIDES
OF THE MERGE: THE PUBLIC TEST "forms" (`K9.formsIn`, Johnson/Desc/First/Batch/FormsIn.lean) PASSES
THE MERGE's ACCEPTING STEP, AT ANY RUN WHOSE READER ANSWERS BEHIND WHAT IT ANSWERS IN FRONT. A
theorem, general in the run: a call of the kind-free `formsIn_fwd`
(Johnson/Desc/Reads/FormsPass.lean), with its premises `Rides` and `More` PAID at this step.

What is said.
  `rides_of_later`, `lateOk_of_later`, `ne_of_lateAt_none`: three lemmas free of the kind: a part
    with the same link context, statement and book and a later ledger rides; the late slots' test
    passes a later ledger that fills none of them.
  `seg_at_merge`: the open segment's part in front of and behind the step: the same but for the
    ledger (and three numbers that no test here reads).
  `formsIn_merge`: **from a yes of the merge's decision from s to s'; the part pa in front, its
    ledger of the right sizes; the slot of the merge's end value (pa.F.next + 2 lk + 2) free in
    front; `Fwd Rd piece run s s'`; that slot is none of the run's late slots; the test at s: the
    test at s'.**
  `formsQ_merge`: **the sentence "forms" at s' gives the sentence at s, at one witness**: for K11's
    fifth tie: a call of `forms_back` with the same `Rides`; it asks neither the sizes, nor "free in
    front", nor "not late".
WHO PAYS WHAT IS LEFT: `Fwd`: each run's owner · "free in front": the table's public test that every
slot at or above the ledger's next free number is free · "not late": each run's own (its late slots
lie below the next free number) · the sizes: the table's public test on the ledger.

Bricks: `decide_later` (Keeps.lean) · `decide_inv` (Says.lean) · `mergeHear_inv` (Hear.lean) ·
`isLocal` (Law.lean) · `merge_ledger` (LedgerBehind.lean: behind the step just one slot more is
filled).
Limits. Implications: shown at no real state. `Fwd` is shown here of no run. Nothing on soundness.

-/
import Johnson.Desc.Reads.FormsPass
import Johnson.Top.H0.MergeLaw.LedgerBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.K9 (segAt? lateAt lateOk formsIn mergeOf Readers)
open VerifiableInference.Desc.Sound (Rides)
open VerifiableInference.Reads.Pass
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-! ## Free of the kind -/

/-- A part with the same link context, statement and book, and a later ledger, rides. -/
theorem rides_of_later (own : List (ℕ × ℕ)) (a b : K9.Part) (hL : b.L = a.L)
    (hst : b.d.st = a.d.st) (hbk : b.d.book = a.d.book) (hl : Later a.F b.F) : Rides own a b where
  arrays := by rw [hL]
  rows := by rw [hL]
  sent := fun _ _ _ h => by rw [hL]; exact h
  mask := fun _ h => by rw [hL]; exact h
  book := fun _ _ h => by rw [hbk]; exact h
  bits := fun _ _ _ _ => by rw [hst]; exact ⟨rfl, rfl⟩
  filled := fun j _ hj => (hl.keep j hj).2

/-- The late slots' test passes a later ledger that fills none of them. -/
theorem lateOk_of_later (late : List (ℕ × E × E)) (a b : K9.Part) (h : lateOk late a = true)
    (hl : Later a.F b.F)
    (hfree : ∀ x ∈ late, a.F.gotF.getD x.1 false = false → b.F.gotF.getD x.1 false = false) :
    lateOk late b = true := by
  unfold lateOk at h ⊢
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h x hx)
  rw [hl.ns, h1, Bool.true_and]
  cases hg : a.F.gotF.getD x.1 false with
  | false =>
    rw [hfree x hx hg]
    rfl
  | true =>
    rw [hg] at h2
    obtain ⟨k1, k2, k3⟩ := hl.keep x.1 hg
    rw [show b.F.gotF.getD x.1 false = true from k1, k2, k3]
    exact h2

/-- No member of the list has the number j, where the list says nothing at j. -/
theorem ne_of_lateAt_none (late : List (ℕ × E × E)) (j : ℕ) (h : lateAt late j = none) :
    ∀ x ∈ late, x.1 ≠ j := by
  intro x hx e
  unfold lateAt at h
  have h' : (late.find? fun y => y.1 == j) = none := by
    cases hf : late.find? fun y => y.1 == j with
    | none => rfl
    | some y =>
      rw [hf] at h
      cases h
  have := List.find?_eq_none.1 h' x hx
  simp [e] at this

/-! ## At the merge's step -/

/-- **The open segment's part in front of and behind the merge's accepting step.** -/
theorem seg_at_merge (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (pa : K9.Part) (hpa : segAt? s = some pa) :
    ∃ a a' pb, s.here = .head a ∧ s'.here = .head a' ∧ segAt? s' = some pb ∧ pa.F = a.F ∧
      pb.F = a'.F ∧ pb.L = pa.L ∧ pb.d.st = pa.d.st ∧ pb.d.book = pa.d.book := by
  obtain ⟨a, a', ha, ha', ho, ho', _⟩ := merge_ledger P h
  obtain ⟨a₁, a₁', e1, e1', e, ea, _⟩ := isLocal P s rs s' h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hL : s.link? = some a₁.L := by
    unfold S.link?
    rw [ha]
    simp only [ho, if_true]
  have hF : s.fork? = some a₁.F := by
    unfold S.fork?
    rw [ha]
    simp only [ho, if_true]
  have hT : s.tl? = some a₁.tl := by
    unfold S.tl?
    rw [ha]
    simp only [ho, if_true]
  have hL' : s'.link? = some a₁'.L := by
    unfold S.link?
    rw [ha']
    simp only [ho', if_true]
  have hF' : s'.fork? = some a₁'.F := by
    unfold S.fork?
    rw [ha']
    simp only [ho', if_true]
  have hT' : s'.tl? = some a₁'.tl := by
    unfold S.tl?
    rw [ha']
    simp only [ho', if_true]
  have eL : a₁'.L = a₁.L := by rw [ea]
  have est : s'.st = s.st := by rw [e]
  have ebk : s'.book = s.book := by rw [e]
  simp only [segAt?, hL, hF, hT, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hpa
  subst hpa
  have hpb : ∃ pb, segAt? s' = some pb ∧ pb.F = a₁'.F ∧ pb.L = a₁'.L ∧ pb.d.st = s'.st ∧
      pb.d.book = s'.book := by
    simp only [segAt?, hL', hF', hT', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨pb, p1, p2, p3, p4, p5⟩ := hpb
  exact ⟨a₁, a₁', pb, ha, ha', p1, rfl, p2, p3.trans eL, p4.trans est, p5.trans ebk⟩

/-- `merge_ledger`'s last clause at the two named head's parts. -/
theorem merge_at (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') {a a' : HeadOwn} (ha : s.here = .head a)
    (ha' : s'.here = .head a') (hz : Sized a.F) :
    ∀ j, j ≠ a.F.next + 2 * P.lay.lk + 2 → (Filled a'.F j ↔ Filled a.F j) := by
  obtain ⟨a₁, a₁', e1, e1', _, _, H⟩ := merge_ledger P h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  exact (H hz).2.2.2

/-- **THE TEST "forms" ACROSS THE MERGE's ACCEPTING STEP, AT ANY RUN.** -/
theorem formsIn_merge (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok s')
    (pa : K9.Part) (hpa : segAt? s = some pa) (hS : Sized pa.F)
    (hfree : pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false)
    (hf : Fwd Rd piece run s s')
    (hlate : ∀ R, Rd.forms piece run s = some R →
      lateAt R.late (pa.F.next + 2 * P.lay.lk + 2) = none)
    (hin : formsIn Rd own piece run s = true) : formsIn Rd own piece run s' = true := by
  obtain ⟨a, a', pb, ha, ha', hpb, eF, eF', eL, est, ebk⟩ := seg_at_merge P h pa hpa
  obtain ⟨a₁, a₁', e1, e1', hl⟩ := decide_later h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hl' : Later pa.F pb.F := by
    rw [eF, eF']
    exact hl
  obtain ⟨a₂, a₂', _, G, _, _, wo, f1, f1', _, _, hwo, _, hm, _, _⟩ := decide_inv h
  obtain rfl : a₂' = a₁' := by
    rw [ha'] at f1'
    exact (Here.head.inj f1').symm
  obtain rfl : a₂ = a₁ := by
    rw [ha] at f1
    exact (Here.head.inj f1).symm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsF, _⟩ := mergeHear_inv hm
  have hmo : mergeOf s' = some (pa.F.next + 2 * P.lay.lk + 2) := by
    have e0 : mergeOf s' = a₂'.wo.map (·.sFv) := by
      unfold mergeOf
      rw [ha']
    rw [e0, hwo, Option.map_some, hsF, eF]
    congr 1
    omega
  have hsame : ∀ j, j ≠ pa.F.next + 2 * P.lay.lk + 2 → (Filled pb.F j ↔ Filled pa.F j) := by
    intro j hj
    rw [eF, eF']
    exact (merge_at P h ha ha' (by rw [← eF]; exact hS)) j (by rw [← eF]; exact hj)
  refine formsIn_fwd Rd own piece run s s' pa pb hpa hpb hf
    (rides_of_later own pa pb eL est ebk hl') (fun R hR => ?_) hin
  have hS' := hl'.sized hS
  have hlo : lateOk R.late pa = true := by
    unfold formsIn at hin
    rw [hpa, hR] at hin
    exact (Eq.mp (Bool.and_eq_true _ _) hin).1
  refine ⟨hl'.ns, fun j hj => (hl'.keep j hj).1, ?_, ?_,
    Or.inr ⟨_, hmo, hfree, hlate R hR⟩, ?_⟩
  · rw [hS.1, hS'.1, hl'.ns]
  · rw [hS.2.1, hS'.2.1, hl'.ns]
  · refine lateOk_of_later R.late pa pb hlo hl' fun x hx hg => ?_
    have hne := ne_of_lateAt_none R.late _ (hlate R hR) x hx
    cases hb : pb.F.gotF.getD x.1 false with
    | false => rfl
    | true =>
      have := (hsame x.1 hne).1 hb
      rw [show pa.F.gotF.getD x.1 false = true from this] at hg
      cases hg

/-- **THE SENTENCE "forms" BACK ACROSS THE MERGE's ACCEPTING STEP, AT ANY RUN**: at one witness. -/
theorem formsQ_merge (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok s')
    (pa : K9.Part) (hpa : segAt? s = some pa) (hf : Fwd Rd piece run s s')
    (hin : formsIn Rd own piece run s = true) (rd : ℕ × ℕ → Sound.MsgQ)
    (hq : Sound.formsQ Rd own piece run s' rd) : Sound.formsQ Rd own piece run s rd := by
  obtain ⟨a, a', pb, ha, ha', hpb, eF, eF', eL, est, ebk⟩ := seg_at_merge P h pa hpa
  obtain ⟨a₁, a₁', e1, e1', hl⟩ := decide_later h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hl' : Later pa.F pb.F := by
    rw [eF, eF']
    exact hl
  exact forms_back Rd own piece run s s' pa pb rd hpa hpb hf hin
    (rides_of_later own pa pb eL est ebk hl') hq

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.rides_of_later
#print axioms VerifiableInference.Desc.First.MergeLaw.lateOk_of_later
#print axioms VerifiableInference.Desc.First.MergeLaw.seg_at_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.formsIn_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.formsQ_merge
