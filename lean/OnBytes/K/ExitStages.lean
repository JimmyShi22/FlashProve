-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ExitStages.lean: the tests that the stages key and leaf of verify-on-bytes make on the
arguments and the public files, beside their files' checks. For proofs only; the program does
not import this file.

  `keyStage_iff`, `leafStage_iff`: the two stages, unfolded one level deep, whole, both ways: the
    planner's accounting of the file's plans at the bits asked, the file's check, the test on the
    accounting's note on work, and what is returned.
  `lastLine_passed`: a stage's ending is "passed" only at profile 4, at no fewer bits than the
    threshold, and if the list of missed conditions that it is handed is empty. These two stages
    hand in three conditions (`Model.Verify.oneTimeForm_nil`, OnBytes/Model/VerifyLawsRecord.lean).
  `StagesPassed C bits`: the facts together.
  `wholeCall_stages`: a whole call that passes has them, at the values that the call itself
    computes, and its three stages have returned and ended as "passed".
What is not stated here: the stage request's own tests, which stay folded in its "passed"
(OnBytes/K/ExitRequest.lean unfolds them); the tests of the end of the call (`cpStagesRun`) beyond
"every stage has passed"; the call's first tests (`readCall`).
What the facts do not say. An accounting that returns is the planner's own: every round of the
planner's plan holds at the setting's target, each round by itself, counting the work that the plan
asks of that round, on the planner's own bounds, which no theorem shows true; it is no sum over
rounds. No clause ties the plans that are accounted to the parameter bytes under which the files'
checks run. The field `bar` is true of every C at 128 bits.
The test on the note on work is one bit.



-/
import OnBytes.Model.VerifyLawsWhole
import OnBytes.Model.VerifyLawsRecord

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages
open OnBytes.Params (exc_bind)

/-- A stage's ending is "passed" only if the profile is not low, the bits asked are not below the
threshold and no condition of the standard parameter form is missed. -/
theorem lastLine_passed {lowProfile belowBar : Bool} {form : List String} {lidb nminH : Nat}
    (h : lastLine lowProfile belowBar form lidb nminH = .passed) :
    lowProfile = false ∧ belowBar = false ∧ form = [] := by
  unfold lastLine at h
  split at h
  · cases h
  · split at h
    · rename_i hg
      unfold goodEnding at hg
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_false'] at hg
      exact ⟨hg.1.1, hg.1.2, List.isEmpty_iff.1 hg.2⟩
    · cases h

/-- The stage for the key file, unfolded whole, both ways. -/
theorem keyStage_iff (C : Common) (n : Nat) (key : ByteArray) (r : Found) :
    keyStage C n key = .ok r ↔
      ∃ ac table, C.acct C.chains.made.key n "key" = .ok ac ∧
        Key.check C.chains.key key = .ok table ∧
        workHeldH (Params.needsWork C.chains.made.key) ac.work = .ok () ∧
        r = (lastLine (!C.X.p4) (askedBelowBar n) (C.oneTimeForm) lidbSealed 0,
          some ac.acct, ac.work) := by
  constructor
  · intro h
    unfold keyStage at h
    obtain ⟨ac, ha, h⟩ := exc_bind h
    split at h
    · cases h
    · rename_i table hf
      obtain ⟨u, hw, h⟩ := exc_bind h
      cases h
      exact ⟨ac, table, named_ok ha, hf, named_ok hw, rfl⟩
  · rintro ⟨ac, table, h1, h2, h3, rfl⟩
    have n1 : named (C.acct C.chains.made.key n "key") = .ok ac := by
      rw [h1]
      rfl
    have n3 : named (workHeldH (Params.needsWork C.chains.made.key) ac.work) = .ok () := by
      rw [h3]
      rfl
    unfold keyStage
    simp only [n1, n3, h2, bind, Except.bind, pure, Except.pure]

/-- The stage for an entry file, unfolded whole, both ways. -/
theorem leafStage_iff (C : Common) (n : Nat) (e : ByteArray) (r : Found) :
    leafStage C n e = .ok r ↔
      ∃ ac further, C.acct [C.chains.made.entry] n "leaf" = .ok ac ∧
        Entry.check C.chains.made.entryLink C.first e = .ok further ∧
        workHeldH (Params.needsWork [C.chains.made.entry]) ac.work = .ok () ∧
        r = (lastLine (!C.X.p4) (askedBelowBar n) (C.oneTimeForm) lidbSealed 0,
          some ac.acct, ac.work) := by
  constructor
  · intro h
    unfold leafStage at h
    obtain ⟨ac, ha, h⟩ := exc_bind h
    split at h
    · cases h
    · rename_i further hf
      obtain ⟨u, hw, h⟩ := exc_bind h
      cases h
      exact ⟨ac, further, named_ok ha, hf, named_ok hw, rfl⟩
  · rintro ⟨ac, further, h1, h2, h3, rfl⟩
    have n1 : named (C.acct [C.chains.made.entry] n "leaf") = .ok ac := by
      rw [h1]
      rfl
    have n3 : named (workHeldH (Params.needsWork [C.chains.made.entry]) ac.work) = .ok () := by
      rw [h3]
      rfl
    unfold leafStage
    simp only [n1, n3, h2, bind, Except.bind, pure, Except.pure]

/-- What the stages key and leaf have tested of the arguments and the public files where both end as
"passed": the profile; the threshold; the three conditions of the standard parameter form that they
test; the planner's accounting of the key's plans and of the entry's plan at the bits asked; and that each accounting has a note on work
exactly where its plans say that a round needs its work. What these facts do not say: the head of
this file. -/
structure StagesPassed (C : Common) (bits : Nat) : Prop where
  profile : C.X.p4 = true
  bar : askedBelowBar bits = false
  reading : C.X.P.frame.reading = 1
  twoCodes : C.chains.twoCodes = true
  oneAnswer : C.X.recordOneAnswer = true
  key : ∃ ac, C.acct C.chains.made.key bits "key" = .ok ac ∧
    workHeldH (Params.needsWork C.chains.made.key) ac.work = .ok ()
  leaf : ∃ ac, C.acct [C.chains.made.entry] bits "leaf" = .ok ac ∧
    workHeldH (Params.needsWork [C.chains.made.entry]) ac.work = .ok ()

/-- From the two stages' "passed". -/
theorem stagesPassed_of {C : Common} {bits : Nat} {key ent : ByteArray}
    {ak al : Option Acct} {wk wl : Option WorkNote}
    (hk : keyStage C bits key = .ok (.passed, ak, wk))
    (hl : leafStage C bits ent = .ok (.passed, al, wl)) : StagesPassed C bits := by
  obtain ⟨ack, _, k1, _, k3, k4⟩ := (keyStage_iff C bits key _).1 hk
  obtain ⟨acl, _, l1, _, l3, l4⟩ := (leafStage_iff C bits ent _).1 hl
  have ek0 : lastLine (!C.X.p4) (askedBelowBar bits) (C.oneTimeForm) lidbSealed
      0 = .passed := (congrArg Prod.fst k4).symm
  have el0 : lastLine (!C.X.p4) (askedBelowBar bits) (C.oneTimeForm) lidbSealed
      0 = .passed := (congrArg Prod.fst l4).symm
  have ek := lastLine_passed ek0
  have el := lastLine_passed el0
  obtain ⟨f1, f2, f3⟩ := oneTimeForm_nil.1 ek.2.2
  exact ⟨by simpa using ek.1, ek.2.1, f1, f2, f3, ⟨ack, k1, k3⟩, ⟨acl, l1, l3⟩⟩

/-- A whole call that passes: at the files r that its first tests return, the entry's bytes and the
common beginning C of its stages, the three stages have returned and ended as "passed". -/
theorem wholeCall_stages {o : Options} {f : Files} {entry : FileIn} {r : Read} {ent : ByteArray}
    {C : Common} (h : (wholeCall o { f with entry := entry }).passing = true)
    (hr : readCall o f = .ok r) (he : entry = some ent) (hC : commonOfCall r = .ok C) :
    (∃ a w, keyStage C o.bits r.key = .ok (.passed, a, w)) ∧
    (∃ a w, leafStage C o.bits ent = .ok (.passed, a, w)) ∧
    (∃ a w, requestStage C o r ent = .ok (.passed, a, w)) ∧ StagesPassed C o.bits := by
  subst he
  unfold wholeCall at h
  rw [readCall_entry, hr] at h
  simp only [stagesOf, hC] at h
  obtain ⟨hall, _⟩ := cpStagesRun_passed h
  have h1 := hall _ (List.mem_cons_self)
  have h2 := hall _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨a1, w1, e1⟩ := stageOut_passed (name := .key) (idHex := C.idHex) h1
  obtain ⟨a2, w2, e2⟩ := stageOut_passed (name := .leaf) (idHex := C.idHex) h2
  obtain ⟨a3, w3, e3⟩ := stageOut_passed h3
  exact ⟨⟨a1, w1, e1⟩, ⟨a2, w2, e2⟩, ⟨a3, w3, e3⟩, stagesPassed_of e1 e2⟩

end OnBytes.K

#print axioms OnBytes.K.keyStage_iff
#print axioms OnBytes.K.leafStage_iff
#print axioms OnBytes.K.wholeCall_stages
