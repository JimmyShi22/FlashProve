-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MergedAtLink.lean: at the merge's run of claims, the readers of a link of
the IOP as written in Lean are the run's own reader. Theorems with their proofs.

Why. `merged_at_member` (MaskRow.lean) takes the table's sentence on linear forms at the reader that
is the run itself (`Readers.ofStates`, Johnson/Desc/First/Batch/ReaderOf.lean). The composed filling
reads a link's runs through `readersOfLink` (Johnson/Desc/First/Batch/ReadersOfLink.lean), which has
two holes: one answers for the approximate range proof's run; the other answers where the run itself
does not, at the output head by laying the head's tables first (`k6Silent`,
Johnson/Desc/Kinds/Law/K6SilentCode.lean).

Main names:
  `readerOf_alike`: two runs of claims that accept alike (the same answers wherever either accepts)
    are read alike. `mergeStates run`: the list that states the merge's run of claims alone.
  `readerOf_merge_tables`: the merge's run of claims does not read the head's tables: its reader
    answers alike at a verifier's state and at that state with tables laid.
  `forms_link_merge`: so at that run neither hole answers in the run's place.
  `formsQ_link_merge`: the table's sentence at the link's readers gives the sentence at the run's
    own reader.

Limits. That the link's sub-protocol states, under the run's name, a run that accepts just where the
merge's does (hst, hr) is a premise: at the IOP as written in Lean the run stands under a guard, so
it is not the merge's run to the letter. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Desc.First.Batch.ReadersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (readerOf RunOf Readers readersOfLink statesOfLink holesAt)
open VerifiableInference.Desc.Sound (formsQ MsgQ)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

/-- **The merge's run of claims does not read the head's tables**: the reader of that run answers
alike at a verifier's state and at that state with tables laid. -/
theorem readerOf_merge_tables (states : ℕ → List (RunOf S)) (piece : ℕ) (run name : String)
    (hst : ((states piece).find? fun r => r.1 == run) = some (name, headMergeClaim))
    {s : S} {a : HeadOwn} (e : s.here = .head a) (t : _) :
    readerOf states piece run { s with here := .head { a with t := some t } } =
      readerOf states piece run s := by
  unfold readerOf
  rw [hst]
  simp only [Option.bind_some]
  unfold headMergeClaim S.fork?
  simp only [e]
  cases a.wo with
  | none => rfl
  | some wo =>
    simp only [VerifiableInference.Desc.named, bind, Except.bind]
    cases OnBytes.K.Kc.Fl.pscRow wo.p wo.fvp {} a.F [] with
    | none => rfl
    | some x => by_cases ho : a.opened = true <;> simp [ho, pure, Except.pure]

/-- **Two runs of claims that accept alike are read alike.** -/
theorem readerOf_alike (states states' : ℕ → List (RunOf S)) (piece : ℕ) (run name name' : String)
    (r r' : ℕ → S → Except String (List Claim × S))
    (hst : ((states piece).find? fun x => x.1 == run) = some (name, r))
    (hst' : ((states' piece).find? fun x => x.1 == run) = some (name', r'))
    (h : ∀ n t y, r n t = .ok y ↔ r' n t = .ok y) (s : S) :
    readerOf states piece run s = readerOf states' piece run s := by
  unfold readerOf
  rw [hst, hst']
  simp only [Option.bind_some]
  cases h1 : r 0 s with
  | ok z => rw [(h 0 s z).1 h1]
  | error e =>
    cases h2 : r' 0 s with
    | ok z => rw [(h 0 s z).2 h2] at h1; exact nomatch h1
    | error e' => rfl

/-- The list that states the merge's run of claims alone, at every number. -/
def mergeStates (run : String) : ℕ → List (RunOf S) := fun _ => [(run, headMergeClaim)]

theorem mergeStates_find (run : String) (piece : ℕ) :
    ((mergeStates run piece).find? fun x => x.1 == run) = some (run, headMergeClaim) := by
  simp [mergeStates]

/-- **At the merge's run of claims the readers of a link are the run's own reader**: neither of the
two holes answers there in its place. -/
theorem forms_link_merge (X : OnBytes.Model.Verify.Public) (mH m : ℕ) (l : Link S Claim)
    (piece : ℕ) (run name : String) (hrun : (run == "K8.equations") = false)
    (r : ℕ → S → Except String (List Claim × S))
    (hst : ((statesOfLink l piece).find? fun x => x.1 == run) = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y) (s : S) :
    (readersOfLink (holesAt X mH m l) l).forms piece run s =
      readerOf (mergeStates run) piece run s := by
  have eA : ∀ t, readerOf (statesOfLink l) piece run t = readerOf (mergeStates run) piece run t :=
    readerOf_alike _ _ piece run name run r headMergeClaim hst (mergeStates_find run piece) hr
  show (if (run == "K8.equations") = true then _ else
    match readerOf (statesOfLink l) piece run s with
    | some R => some R
    | Option.none => (holesAt X mH m l).silent piece run s) = _
  rw [if_neg (by rw [hrun]; simp), eA s]
  cases hq : readerOf (mergeStates run) piece run s with
  | some R => rfl
  | none =>
    show (holesAt X mH m l).silent piece run s = none
    unfold holesAt
    by_cases hm : (m == mH) = true
    · simp only [hm, if_true]
      unfold VerifiableInference.Desc.Kinds.Head.Law.k6Silent
        VerifiableInference.Desc.Kinds.Head.Law.withTables
      cases hh : s.here with
      | head a =>
        simp only
        cases VerifiableInference.Desc.Kinds.Head.Law.tablesAt (K9.phAt X m) s with
        | none => rfl
        | some t =>
          simp only [Option.map_some, Option.bind_some]
          rw [eA, readerOf_merge_tables (mergeStates run) piece run run (mergeStates_find run piece)
            hh t, hq]
      | _ => rfl
    · simp only [hm, Bool.false_eq_true, if_false]

/-- **So the table's sentence on linear forms at the link's readers is the one at the run's own
reader.** -/
theorem formsQ_link_merge (X : OnBytes.Model.Verify.Public) (mH m : ℕ) (l : Link S Claim)
    (own : List (ℕ × ℕ)) (piece : ℕ) (run name : String)
    (hrun : (run == "K8.equations") = false) (r : ℕ → S → Except String (List Claim × S))
    (hst : ((statesOfLink l piece).find? fun x => x.1 == run) = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y)
    (s : S) (rd : ℕ × ℕ → MsgQ)
    (h : formsQ (readersOfLink (holesAt X mH m l) l) own piece run s rd) :
    formsQ (Readers.ofStates (mergeStates run)) own piece run s rd := by
  obtain ⟨a, R, h1, h2, h3⟩ := h
  rw [forms_link_merge X mH m l piece run name hrun r hst hr s] at h2
  exact ⟨a, R, h1, h2, h3⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.readerOf_alike
#print axioms VerifiableInference.Desc.First.MergeLaw.forms_link_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.formsQ_link_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.readerOf_merge_tables
