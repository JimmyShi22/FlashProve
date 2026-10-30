-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ExitRequest.lean: what the "passed" of the stage request of verify-on-bytes says beyond
the yes of the check of the proof file. For proofs only; that Lean text does not import this file.

  `servedForm_nil`: no condition of the standard parameter form is missed exactly if all twenty-one
    fields of `Served` are true.
  `requestStage_passed`: where the stage request returns and ends as "passed": the request's and the
    reply's lengths are multiples of four; the account of the proof's plan holds the bits asked, and
    it has a note on work exactly where the plan says that a round needs its work; all twenty-one
    conditions hold, at the statement and the covered positions that the stage itself reads off the
    request; the statement's item is the one that the sub-proofs use; and the record that the stage
    hands on is the account of all three files' plans together.

-/
import OnBytes.K.ExitStages

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages
open OnBytes.Params (exc_bind)

/-- No condition is missed exactly if every field is true. -/
theorem servedForm_nil (s : Served) :
    servedForm s = [] ↔
      (s.attention = true ∧ s.experts = true ∧ s.fiveLimbs = true ∧ s.clamps = true ∧
        s.promptSource = true ∧ s.placementTable = true ∧ s.tableDigests = true ∧
        s.noRangeWords = true ∧ s.threeBytes = true ∧ s.ringDegree = true ∧ s.oneShift = true ∧
        s.onePlacement = true ∧ s.softmaxTable = true ∧ s.rotaryTable = true ∧
        s.normShifts = true ∧ s.readingAsPrinted = true ∧ s.twoCodes = true ∧
        s.recordOneAnswer = true ∧ s.nextToken = true ∧ s.exactMatch = true ∧
        s.policyNamed = true) := by
  unfold servedForm
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Bool.not_eq_true', Bool.not_eq_false]

/-- The stage request's "passed". In words: the head of this file. -/
theorem requestStage_passed {C : Common} {o : Options} {r : Read} {entry : ByteArray}
    {ac : Option Acct} {w : Option WorkNote}
    (h : requestStage C o r entry = .ok (.passed, ac, w)) :
    ∃ so cov a item,
      (r.request.size % 4 != 0 || r.y.size % 4 != 0) = false ∧
      Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      C.acct C.chains.made.proof o.bits "request" = .ok a ∧
      workHeldH (Params.needsWork C.chains.made.proof) a.work = .ok () ∧
      servedForm (servedOf C o r.layout.isSome so cov) = [] ∧
      Proof.requestItem r.pol r.KL r.request = some item ∧ statementHeld C.X item = .ok () ∧
      ac = acctWhole C.chains.made.sized.set
        (some (C.chains.made.key ++ [C.chains.made.entry] ++ C.chains.made.proof)) ∧
      w = a.work := by
  unfold requestStage at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  have hx := named_ok hx
  split at h
  · cases h
  · obtain ⟨_, hw, h⟩ := exc_bind h
    have hw := named_ok hw
    have h0 : (lastLine (!C.X.p4) (askedBelowBar o.bits) x.form C.X.P.settings.lidb
        C.X.P.settings.nminH, x.whole, x.work) = (StageEnd.passed, ac, w) := Except.ok.inj h
    have e1 : lastLine (!C.X.p4) (askedBelowBar o.bits) x.form C.X.P.settings.lidb
        C.X.P.settings.nminH = .passed := congrArg Prod.fst h0
    have e2 : x.whole = ac := congrArg (fun t => t.2.1) h0
    have e3 : x.work = w := congrArg (fun t => t.2.2) h0
    have hform := (lastLine_passed e1).2.2
    unfold requestRun at hx
    obtain ⟨_, g0, hx⟩ := exc_bind hx
    obtain ⟨so, g1, hx⟩ := exc_bind hx
    obtain ⟨cov, g2, hx⟩ := exc_bind hx
    obtain ⟨further, _, hx⟩ := exc_bind hx
    obtain ⟨a, g4, hx⟩ := exc_bind hx
    cases hi : Proof.requestItem r.pol r.KL r.request with
    | none =>
      rw [hi] at hx
      cases hx
    | some item =>
      rw [hi] at hx
      obtain ⟨_, hp, hx⟩ := exc_bind hx
      cases hp
      obtain ⟨_, g5, hx⟩ := exc_bind hx
      obtain ⟨links, _, hx⟩ := exc_bind hx
      cases hx
      have g0' : (r.request.size % 4 != 0 || r.y.size % 4 != 0) = false := by
        unfold refuseIf at g0
        split at g0
        · cases g0
        · rename_i hb
          simpa using hb
      exact ⟨so, cov, a, item, g0', g1, g2, g4, hw, hform, rfl, g5, e2.symm, e3.symm⟩

end OnBytes.K

#print axioms OnBytes.K.servedForm_nil
#print axioms OnBytes.K.requestStage_passed
