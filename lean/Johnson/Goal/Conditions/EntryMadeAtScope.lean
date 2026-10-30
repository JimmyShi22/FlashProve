-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryMadeAtScope.lean: WHAT THE PLANNER MAKES FOR THE ENTRY FILE's CHAIN, AT EVERY THREE PUBLIC FILES IN SCOPE, IS THE LIBRARY's TYPED VALUES: the chain's codes, its plan (42 entries and six settings), the link's sizes.
So the laws «at written sizes or codes» of the entry file speak of what the run makes: BY THEOREM, no print and no comparison at the run.
  entry_made_at_scope    InScope Z → planned Z.pol Z.KL (some Z.lay) = .ok p → made.sized.entryCodes = recordCodes ∧ made.entry.plan = recordPlan ∧ made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ ∧ made.entry.holds = true
  planned_of_madeOf      what madeOf returns holds what the planner returns
  entry_made_of_madeOf   the same at m := what madeOf makes of the three files
BY THE LAWS: inScope_reads (Johnson/Goal/Scope/ScopeLines.lean) · planned_madeKey (OnBytes/K/KeySalt.lean) · record_entry_made (OnBytes/Model/FitRecord.lean).
THE FULL SIZE ALONE: InScope pins the full size's files. EMPTY WHERE the planner refuses. Nothing on soundness.
-/
import Johnson.Goal.Scope.ScopeLines
import OnBytes.K.KeySalt
import OnBytes.Model.FitRecord
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Params

theorem entry_made_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (h : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.entryCodes = recordCodes ∧ p.chains.made.entry.plan = recordPlan ∧
      p.chains.made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ ∧ p.chains.made.entry.holds = true := by
  obtain ⟨b, hb⟩ : ∃ b, Params.readLines Z.pol = .ok (Params.recordLines, b) := Johnson.G.ScopeLines.inScope_reads hZ
  obtain ⟨l, rest, shapes, hl, hm⟩ := Model.Verify.planned_madeKey h
  rw [hb] at hl
  injection hl with hl
  injection hl with h1 _
  subst h1
  obtain ⟨e1, e2, e3, e4⟩ := record_entry_made hm
  exact ⟨e2, e3, e1, e4⟩

theorem planned_of_madeOf {pol lay KL : ByteArray} {m : Johnson.G.OfPlan.Made} (h : Johnson.G.OfPlan.madeOf pol lay KL = .ok m) :
    Model.Verify.planned pol KL (some lay) = .ok m.p := by
  unfold Johnson.G.OfPlan.madeOf at h
  cases hp : Model.Verify.planned pol KL (some lay) with
  | error e => rw [hp] at h; exact nomatch h
  | ok p =>
    rw [hp] at h
    cases hs : Johnson.G.sendsOf pol lay KL with
    | error e => simp only [hs, bind, Except.bind] at h; exact nomatch h
    | ok l =>
      simp only [hs, bind, Except.bind] at h
      split at h
      · injection h with h
        subst h
        rfl
      · exact nomatch h

theorem entry_made_of_madeOf {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {m : Johnson.G.OfPlan.Made}
    (h : Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL = .ok m) :
    m.p.chains.made.sized.entryCodes = recordCodes ∧ m.p.chains.made.entry.plan = recordPlan ∧
      m.p.chains.made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ ∧ m.p.chains.made.entry.holds = true :=
  entry_made_at_scope hZ (planned_of_madeOf h)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.entry_made_at_scope
#print axioms VerifiableInference.OnPublicFiles.entry_made_of_madeOf
