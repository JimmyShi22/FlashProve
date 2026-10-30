-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05FormsMadeAt.lean: kind K5: THE TABLE's PUBLIC TEST formsInT (
Johnson/Desc/First/Batch/FormsIn.lean) AT ITS GENERIC READER "the reader is the run itself" (Johnson/Desc/First/Batch/ReaderOf.lean), AT K5's THREE
OWN RUNS "first", "keys", "second" (runsN, Att/SeatN.lean), HOLDS AT THE RECORD BEHIND THE HEARING's
LAY: what the table's item formsInT m 3 "own" stands for (its runsOf: the driver's (2, "first"),
(2, "keys"), (2, "second")).

Main names:
  `lateOf_self`: a run that hands the record back unturned has no late slot.
  `readerOf_runN`: the generic reader at a run of forms carried to claims (runN) that returns (l, s)
    at s, where every entry of every form passes ownRow: it gives l and no late slot.
  `formsInT_of`: so formsInT holds there if every form of l passes affInT with no late slot.
  `find_first`, `find_keys`, `find_second`: the three runs in runsN A, by name.
  `formsInT_own_behind`: **formsInT (Readers.ofStates states) own 2 name (behind s a h G) = true at
    name = "first" | "keys" | "second"**, where states 2 = runsN A.
Premises: those of k5_forms_there (Att/K05FormsMade.lean) at c := parCOf A, and "keys"' return.
Limits: as there. "join" and the lookup's "planes" are not spoken of.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05FormsMade
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (named Claim)
open VerifiableInference.Desc.K9 (affInT lateOk Read Readers segAt? formsInT mergeOf lateOf ownRow
  readerOf RunOf)

theorem lateOf_self (F : Fork) : lateOf F F = [] := by
  unfold lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  cases F.gotF.getD j false <;> rfl

/-- The generic reader at a run of forms that hands the record back. -/
theorem readerOf_runN {states : ℕ → List (RunOf First.S)} {b : ℕ} {name nm : String}
    {r : ℕ → First.S → Except String (List Aff × First.S)} {s : First.S} {l : List Aff} {G : Fork}
    (hf : ((states b).find? fun x => x.1 == name) = some (nm, runN r)) (hr : r 0 s = .ok (l, s))
    (hG : s.fork? = some G) (ho : ∀ f ∈ l, f.ents.all (ownRow G) = true) :
    readerOf states b name s = some { forms := l, late := [] } := by
  unfold readerOf
  rw [hf]
  have h1 : runN r 0 s = .ok (l.map claimOf, s) := by
    unfold runN
    rw [hr]
    rfl
  simp only [Option.bind_some, h1, hG]
  have h2 : ((l.map claimOf).all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow G)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hfl, rfl⟩ := List.mem_map.1 hc
    show (true && true && f.ents.all (ownRow G)) = true
    rw [ho f hfl]
    rfl
  rw [if_pos h2, lateOf_self, List.map_map]
  have h3 : ((fun c : Claim => c.form) ∘ claimOf) = id := rfl
  rw [h3, List.map_id]

/-- So the test holds, if every form passes affInT with no late slot. -/
theorem formsInT_of {states : ℕ → List (RunOf First.S)} {b : ℕ} {name : String} {s : First.S}
    {l : List Aff} {part : K9.Part} (own : List (ℕ × ℕ)) (hp : segAt? s = some part)
    (hm : mergeOf s = none) (hr : readerOf states b name s = some { forms := l, late := [] })
    (ha : ∀ f ∈ l, affInT own none [] part f = true) :
    formsInT (Readers.ofStates states) own b name s = true := by
  unfold formsInT
  have hr' : (Readers.ofStates states).forms b name s = some { forms := l, late := [] } := hr
  rw [hp, hr', hm]
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨rfl, List.all_eq_true.2 ha⟩

theorem find_first (A : Attention.Plan) : ((runsN A).find? fun x => x.1 == "first") =
    some ("first", runN fun _ s => named "K5.first" (firstK (seatCO (parCOf A)) (parCOf A) s)) := rfl

theorem find_keys (A : Attention.Plan) : ((runsN A).find? fun x => x.1 == "keys") =
    some ("keys", runN fun _ s => named "K5.keys" (keysK (seatCO (parCOf A)) (parCOf A) s)) := rfl

theorem find_second (A : Attention.Plan) : ((runsN A).find? fun x => x.1 == "second") =
    some ("second", runN fun _ s => named "K5.second" (secondK (seatCO (parCOf A)) (parCOf A) s)) := rfl

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard}
  {G : Fork} {i : Runs.In} {K : ℕ}

theorem all_ownRow {f : Aff} (hf : ∀ e ∈ f.ents.toList, e.row = 0 ∧ ∃ T, G.trees[e.tree]? = some T ∧ T.R = 1) :
    f.ents.all (ownRow G) = true := by
  rw [← Array.all_toList]
  refine List.all_eq_true.2 fun e he => ?_
  obtain ⟨h0, T, hT, hR⟩ := hf e he
  unfold ownRow
  rw [hT]
  show (T.R == 1 && e.row == 0) = true
  rw [hR, h0]
  rfl

/-- **What the table's item formsInT m 3 "own" stands for holds behind the lay.** -/
theorem formsInT_own_behind (states : ℕ → List (RunOf First.S)) (A : Attention.Plan)
    (hst : states 2 = runsN A) (own : List (ℕ × ℕ))
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : Sized a.F)
    (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s a h G) = some (i, K)) {l₁ l₂ : List Aff}
    {j : Runs.JoinsP} (h1 : Runs.firstRun i K = some (l₁, j)) (h2 : Runs.secondRun i K = some l₂)
    {kf : Array Aff} (hk : keysOfK (seatCO (parCOf A)) (parCOf A) (behind s a h G) = some kf)
    (gf : GeoFits (parCOf A).geo x) (U : U3There own s a (parCOf A)) :
    ∀ name ∈ ["first", "keys", "second"],
      formsInT (Readers.ofStates states) own 2 name (behind s a h G) = true := by
  have hT := k5_forms_there own hh hz hin h1 h2 gf U none
  have hG : (behind s a h G).fork? = some G := rfl
  have hm : mergeOf (behind s a h G) = none := rfl
  intro name hn
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · refine formsInT_of (l := l₁) own segAt_behind hm (readerOf_runN (by rw [hst]; exact find_first A)
      ?_ hG fun f hf => all_ownRow (hT f (List.mem_append_left _ hf)).2)
      fun f hf => (hT f (List.mem_append_left _ hf)).1
    show named "K5.first" (firstK _ _ _) = _
    unfold firstK
    simp [hin, h1, named]
  · refine formsInT_of (l := []) own segAt_behind hm (readerOf_runN (by rw [hst]; exact find_keys A)
      ?_ hG fun f hf => by cases hf) fun f hf => by cases hf
    show named "K5.keys" (keysK _ _ _) = _
    unfold keysK
    simp [hk, named]
  · refine formsInT_of (l := l₂) own segAt_behind hm (readerOf_runN (by rw [hst]; exact find_second A)
      ?_ hG fun f hf => all_ownRow (hT f (List.mem_append_right _ hf)).2)
      fun f hf => (hT f (List.mem_append_right _ hf)).1
    show named "K5.second" (secondK _ _ _) = _
    unfold secondK
    simp [hin, h2, named]

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readerOf_runN
#print axioms VerifiableInference.Desc.First.Att.P.formsInT_of
#print axioms VerifiableInference.Desc.First.Att.P.formsInT_own_behind
