-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/ReaderAtK4.lean: THE GENERIC READER OF A RUN (K9.readerOf,
Johnson/Desc/First/Batch/ReaderOf.lean) AT K4's TWO RUNS OF CLAIMS, IN CLOSED FORM; and the parts of
the public test on a run's forms (K9.formsInT, Johnson/Desc/First/Batch/FormsIn.lean) that hang on
the ledger alone. Statements and proofs. No Mathlib beneath.

  `find_of_lookup`: a run that List.lookup finds under a name is found by find? on that name.
  `forms_claimOf`: the forms of forms carried over as claims are the forms.
  `readerAt`: the reader at a run of blockAtC p whose untyped run returns at s.
  `reader_front`, `reader_back`: where the chain stands in a layers' link a, what was heard lies in
    it, the plain listing returns (ff, G₁) at a's ledger, and every entry of every form names row 0
    of an array of one own row: the reader gives the forms ff and late := lateOf a.F G₁.
  `lateOk_late`: the test on the late slots holds AT THE LEDGER IN FRONT OF THE RUN: a late slot is
    free there, by lateOf's own filter.
  `slotIn_of`: the test on a slot holds if the slot is below the number of slots, the mask row is
    seated, the slot is not the free one, and it is filled in the ledger behind the run.
  `mergeOf_lay`: at a layers' link the free slot is the merge's end value's, o.wo.sFv.
  `segAt_lay`: at a layers' link the open segment's part is there, with the link's ledger and
    context.
No new argument: the texts unfolded; frontAtS_returns, backAtS_returns
(Johnson/Road/K4/Total/AtSeat.lean), atClaims_run (Johnson/Desc/First/K4/AtCLaws.lean).
**Limits.** PREMISES OF reader_front AND reader_back, none paid here: hst (block number b of the
segment states K4's runs); ha, ho (kept behind a yes of K4's block); hf (the end of the law
RunsReturn, which stands under the premise "member"); hrow (every entry names row 0 of an array that
has one own row in a's ledger: NOBODY HOLDS IT: row 0 hangs on a line on the plan that nobody pays,
"the plan's length of the reads is at most the array's number of columns"). Of slotIn_of: six, on
the ledgers and the seat. Implications to "true": no converse. The test on entries (entInT) is not
touched. formsInT is not concluded here. Nothing on soundness. The law of K4's kind on its claims is
NOT proved by this. Met through Lean at no member.


-/
import Johnson.Road.K4.Total.AtSeat
import Johnson.Desc.First.K4.AtCLaws
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.InT

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4.Total (frontAtS_returns backAtS_returns)
open VerifiableInference.Desc (Claim K9.readerOf K9.lateOf K9.lateOk K9.lateAt K9.slotIn K9.ownRow
  K9.maskSeat K9.mergeOf K9.segAt? K9.RunOf K9.Part K9.Read)
open VerifiableInference.Desc.First (S LayOwn)

/-- A run that lookup finds under a name is found by find? on that name. -/
theorem find_of_lookup {β : Type} : ∀ (l : List (String × β)) (name : String) (run : β),
    l.lookup name = some run → l.find? (fun r => r.1 == name) = some (name, run)
  | [], _, _, h => by simp at h
  | (k, v) :: l, name, run, h => by
    cases hb : (name == k) with
    | true =>
      have ek : name = k := by simpa using hb
      subst ek
      simp only [List.lookup_cons, hb, Option.some.injEq] at h
      subst h
      rw [List.find?_cons_of_pos (by simp)]
    | false =>
      simp only [List.lookup_cons, hb] at h
      have hne : ¬ (k == name) = true := fun e => by
        have ek : k = name := by simpa using e
        subst ek
        simp at hb
      have hkn : (k == name) = false := by
        cases hk : (k == name) with
        | false => rfl
        | true => exact absurd hk hne
      simp only [List.find?_cons, hkn]
      exact find_of_lookup l name run h

/-- The forms of forms carried over as claims are the forms. -/
theorem forms_claimOf : ∀ l : List Aff, (l.map claimOf).map (·.form) = l
  | [] => rfl
  | x :: l => by
    show (claimOf x).form :: (l.map claimOf).map (·.form) = x :: l
    rw [forms_claimOf l]
    rfl

/-- The reader at a run of the typed block whose untyped run returns at s. -/
theorem readerAt {states : Nat → List (K9.RunOf S)} {b : Nat} {p : Par} {name : String} {s s' : S}
    {a : LayOwn} {ff : Array Aff} {G₁ : Fork}
    {run : Nat → S → Except String (List Aff × S)} (hst : states b = (blockAtC p).claims)
    (hl : (blockAtS p).claims.lookup name = some run) (hrun : run 0 s = .ok (ff.toList, s'))
    (hw : Wrote s a G₁ s') (hrow : ∀ f ∈ ff.toList, f.ents.all (K9.ownRow a.F) = true) :
    K9.readerOf states b name s = some { forms := ff.toList, late := K9.lateOf a.F G₁ } := by
  have hC : (blockAtC p).claims.lookup name =
      some fun n s => (run n s).map fun y => (y.1.map claimOf, y.2) := by
    show (atClaims (blockAtS p)).claims.lookup name = _
    rw [atClaims_run, hl]
    rfl
  have hfind := find_of_lookup _ _ _ hC
  have hF : s.fork? = some a.F := by simp only [S.fork?, hw.1]
  have hG : s'.fork? = some G₁ := by
    rw [hw.2]
    rfl
  have hall : ((ff.toList.map claimOf).all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow a.F)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hc
    show ((#[] : Array Run2).isEmpty && (none : Option Nat).isNone &&
      f.ents.all (K9.ownRow a.F)) = true
    rw [hrow f hf']
    rfl
  unfold K9.readerOf
  rw [hst, hfind, Option.bind_some]
  simp only [hrun, Except.map, hF, hG, Option.bind_some]
  rw [if_pos hall, forms_claimOf]

/-- **The reader at K4's run "front".** -/
theorem reader_front {states : Nat → List (K9.RunOf S)} {b : Nat} {p : Par} {s : S} {a : LayOwn}
    {o : Own} {ff : Array Aff} {G₁ : Fork} (hst : states b = (blockAtC p).claims)
    (ha : s.here = .lay a) (ho : a.own = some o) (hf : frontOf p o a.F = some (ff, G₁))
    (hrow : ∀ f ∈ ff.toList, f.ents.all (K9.ownRow a.F) = true) :
    K9.readerOf states b "front" s = some { forms := ff.toList, late := K9.lateOf a.F G₁ } := by
  obtain ⟨run, s', hl, hrun, hw⟩ := frontAtS_returns ha ho hf
  exact readerAt hst hl (hrun 0) hw hrow

/-- **The reader at K4's run "back".** -/
theorem reader_back {states : Nat → List (K9.RunOf S)} {b : Nat} {p : Par} {s : S} {a : LayOwn}
    {o : Own} {ff : Array Aff} {G₁ : Fork} (hst : states b = (blockAtC p).claims)
    (ha : s.here = .lay a) (ho : a.own = some o) (hf : formsBack o a.F = some (ff, G₁))
    (hrow : ∀ f ∈ ff.toList, f.ents.all (K9.ownRow a.F) = true) :
    K9.readerOf states b "back" s = some { forms := ff.toList, late := K9.lateOf a.F G₁ } := by
  obtain ⟨run, s', hl, hrun, hw⟩ := backAtS_returns ha ho hf
  exact readerAt hst hl (hrun 0) hw hrow

/-- A slot is in the list of late slots just if it is below the later ledger's number of slots, free
in the earlier ledger and filled in the later. One direction. -/
theorem mem_lateOf {F G : Fork} {j : Nat} (hj : j < G.ns) (h0 : F.gotF.getD j false = false)
    (h1 : G.gotF.getD j false = true) :
    (j, G.vp.getD j zeroE, G.mf.getD j zeroE) ∈ K9.lateOf F G := by
  unfold K9.lateOf
  refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
  rw [if_pos (by rw [h0, h1]; rfl)]

/-- **The test on the late slots holds at the ledger in front of the run.** -/
theorem lateOk_late (A : K9.Part) (G₁ : Fork) (hns : G₁.ns = A.F.ns) :
    K9.lateOk (K9.lateOf A.F G₁) A = true := by
  unfold K9.lateOk
  refine List.all_eq_true.2 fun x hx => ?_
  unfold K9.lateOf at hx
  obtain ⟨j, hj, hx'⟩ := List.mem_filterMap.1 hx
  by_cases hc : (!(A.F.gotF.getD j false) && G₁.gotF.getD j false) = true
  · rw [if_pos hc] at hx'
    obtain rfl := Option.some.inj hx'
    have hj' : j < A.F.ns := hns ▸ List.mem_range.1 hj
    have h0 : (!(A.F.gotF.getD j false)) = true := (Bool.and_eq_true _ _ ▸ hc).1
    show (decide (j < A.F.ns) && (!(A.F.gotF.getD j false) || _)) = true
    rw [h0, Bool.true_or, Bool.and_true]
    exact decide_eq_true hj'
  · rw [if_neg hc] at hx'
    exact nomatch hx'

/-- **The test on a slot.** -/
theorem slotIn_of {own : List (Nat × Nat)} {free : Option Nat} {A : K9.Part} {G₁ : Fork} {j : Nat}
    (hj : j < A.F.ns) (hm : (K9.maskSeat own A).isSome = true) (hfree : free ≠ some j)
    (hfil : Filled G₁ j) (hS : Sized A.F) (hns : G₁.ns = A.F.ns) :
    K9.slotIn own free (K9.lateOf A.F G₁) A j = true := by
  have hfr : (free != some j) = true := by simpa using hfree
  unfold K9.slotIn
  rw [decide_eq_true hj, hm, hfr, Bool.true_and, Bool.true_and, Bool.true_and]
  cases h0 : A.F.gotF.getD j false with
  | true =>
    rw [decide_eq_true (show j < A.F.vp.size by rw [hS.1]; exact hj),
      decide_eq_true (show j < A.F.mf.size by rw [hS.2.1]; exact hj)]
    simp
  | false =>
    have hmem := mem_lateOf (F := A.F) (G := G₁) (by rw [hns]; exact hj) h0 hfil
    have hs : (K9.lateAt (K9.lateOf A.F G₁) j).isSome = true := by
      unfold K9.lateAt
      rw [Option.isSome_map]
      exact List.find?_isSome.2 ⟨_, hmem, by simp⟩
    rw [hs]
    rfl

/-- At a layers' link the free slot is the merge's end value's. -/
theorem mergeOf_lay {s : S} {a : LayOwn} {o : Own} (ha : s.here = .lay a) (ho : a.own = some o) :
    K9.mergeOf s = some o.wo.sFv := by
  simp only [K9.mergeOf, ha, ho, Option.map_some]

/-- At a layers' link the open segment's part is there. -/
theorem segAt_lay {s : S} {a : LayOwn} (ha : s.here = .lay a) :
    ∃ A, K9.segAt? s = some A ∧ A.F = a.F ∧ A.L = a.L := by
  have hL : s.link? = some a.L := by simp only [S.link?, ha]
  have hF : s.fork? = some a.F := by simp only [S.fork?, ha]
  have hT : s.tl? = some a.tl := by simp only [S.tl?, ha]
  unfold K9.segAt?
  rw [hL, hF, hT]
  exact ⟨_, rfl, rfl, rfl⟩

end OnBytes.Desc.First.K4.InT

#print axioms OnBytes.Desc.First.K4.InT.find_of_lookup
#print axioms OnBytes.Desc.First.K4.InT.forms_claimOf
#print axioms OnBytes.Desc.First.K4.InT.readerAt
#print axioms OnBytes.Desc.First.K4.InT.reader_front
#print axioms OnBytes.Desc.First.K4.InT.reader_back
#print axioms OnBytes.Desc.First.K4.InT.mem_lateOf
#print axioms OnBytes.Desc.First.K4.InT.lateOk_late
#print axioms OnBytes.Desc.First.K4.InT.slotIn_of
#print axioms OnBytes.Desc.First.K4.InT.mergeOf_lay
#print axioms OnBytes.Desc.First.K4.InT.segAt_lay
