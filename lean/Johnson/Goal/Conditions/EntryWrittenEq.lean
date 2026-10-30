-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryWrittenEq.lean: THE EQUATION THAT CARRIES LAWS AND RIDES FROM THE ELDER ROOT (linkOfFilesV: through the planner) TO THE ROOT AT THE WRITTEN VALUES (Johnson/Desc/Link/LinkWritten.lean): AT EVERY THREE PUBLIC FILES IN SCOPE AT WHICH THE
ELDER ROOT SAYS ok, THE TWO ROOTS RETURN ONE LINK, AND THE TWO VALUES FOR THE SLOT ARE ONE.
  root_parts        what an ok of the elder root says (by unfolding its text)
  linkAt_of_root    InScope Z → linkOfFilesV Z.pol Z.lay Z.KL = .ok L → linkAt frP recordPlan = .ok L
  linkWritten_eq    … → linkWritten Z.pol = .ok L
  decWritten_eq     … → linkDecisionAtParameterFile Z.pol = decOfRoot Z.pol Z.lay Z.KL
BY: p15Of_of_lines (the planner's parameters are frP) · entry_made_at_scope (the made plan is recordPlan) · the tests on the plan, clause by name (CoreSays: fileOk · roundsDeclaredByBlocks == plans).
  decWritten_cases  AT EVERY PARAMETER FILE: linkDecisionAtParameterFile says no to all, or it IS the run of linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) at the keys written of the two records: THE FORM AT WHICH THE LAWS ON THE LINK ARE TYPED (any plan, any Bool)
WHERE linkOfFilesV REFUSES IN SCOPE THE EQUATION SAYS NOTHING: there decOfRoot says no to all and linkDecisionAtParameterFile may decide: BUT BY decWritten_cases IT DECIDES BY THE TYPED DESCRIPTION, OF WHICH THE LAWS SPEAK WITHOUT linkOfFilesV. OBJECT: Desc.K15.decOfRoot (linkOfFilesV's decision, of the three public files) · Desc.K15.linkDecisionAtParameterFile (the entry file's decision: `FlashProve.linkDecisionAtFiles`, Johnson/Goal/Description/LinkDec.lean) · USER: EntryWrittenLaw.lean (decWritten_cases, linkAt_F) · LETTERS: none.
Nothing on soundness.
-/
import Johnson.Goal.Conditions.LinkTypedAtLines
import Johnson.Goal.Conditions.EntryMadeAtScope
import Johnson.Desc.Link.LinkWritten
import Johnson.Desc.Link.CoreSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params VerifiableInference.Desc

theorem root_parts (pol lay KL : ByteArray) (L : Link3) (h : linkOfFilesV pol lay KL = .ok L) :
    ∃ p plan, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧ L.F = linkDescV p.chains plan ∧ L.F.planWord = none ∧
      L.F.dsOf "entry file" = .ok L.ds ∧ L.xs = L.F.xsTyped := by
  unfold linkOfFilesV at h
  split at h
  · cases h
  · cases h
  · rename_i p plan hp hplan
    dsimp only at h
    split at h
    · cases h
    · cases h
    · rename_i ds hw hds
      cases h
      exact ⟨p, plan, hp, rfl, hw, hds, rfl⟩

theorem linkAt_of_root {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {L : Link3} (h : linkOfFilesV Z.pol Z.lay Z.KL = .ok L) :
    linkAt frP recordPlan = .ok L := by
  obtain ⟨p, plan, hp, hF, hw, hds, hxs⟩ := root_parts _ _ _ L h
  obtain ⟨b, hb⟩ := scope_reads hZ
  have hP : p15Of p.chains = frP := p15Of_of_lines hp hb
  obtain ⟨_, hE, _, _⟩ := VerifiableInference.OnPublicFiles.entry_made_at_scope hZ hp
  have hok := OneChainFileDescription.planWord_none L.F hw
  have hfile : (VerifiableInference.Desc.entryOk p.chains.made && tiesOk p.chains plan) = true := by
    have := OneChainFileDescription.planOk_fileOk L.F hok
    rw [hF] at this
    exact this
  have hdecl : linkDeclaredRounds frP = plan := by
    have := OneChainFileDescription.planOk_decl L.F hok
    rw [hF] at this
    have e : (linkDescV p.chains plan).asFile.roundsDeclaredByBlocks.1 = (linkDescV p.chains plan).asFile.plans.1 := by simpa using this
    have e' : linkDeclaredRounds (p15Of p.chains) = plan := e
    rw [hP] at e'
    exact e'
  have hties : tiesOk p.chains plan = true := (Bool.and_eq_true _ _ ▸ hfile : _ ∧ _).2
  have hokAt : linkRoundsMatchPlan frP recordPlan = true := by
    unfold tiesOk at hties
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hties
    unfold linkRoundsMatchPlan
    rw [hdecl, ← hE]
    exact decide_eq_true hties.1.1.1
  have hFF : linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) = L.F := by
    rw [hF, hokAt, hdecl]
    unfold linkDescV
    rw [hP, hfile]
  unfold linkAt
  simp only [hFF, hw, hds]
  obtain ⟨F, ds, xs⟩ := L
  simp only at hxs
  rw [hxs]

theorem linkWritten_eq {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {L : Link3} (h : linkOfFilesV Z.pol Z.lay Z.KL = .ok L) :
    linkWritten Z.pol = .ok L := by
  obtain ⟨b, hb⟩ := scope_reads hZ
  unfold linkWritten
  rw [hb]
  simp only [if_true]
  exact linkAt_of_root hZ h

theorem decWritten_eq {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {L : Link3} (h : linkOfFilesV Z.pol Z.lay Z.KL = .ok L) :
    linkDecisionAtParameterFile Z.pol = decOfRoot Z.pol Z.lay Z.KL := by
  obtain ⟨b, hb⟩ := scope_reads hZ
  unfold linkDecisionAtParameterFile decOfRoot
  rw [hb, h]
  simp only [if_true, linkAt_of_root hZ h]

/-- What an ok of linkAt holds: the description at the typed parameters. -/
theorem linkAt_F {P : P15} {plan : Fmt.Plan} {L : Link3} (h : linkAt P plan = .ok L) : L.F = linkDescriptionAt P (linkDeclaredRounds P) (linkRoundsMatchPlan P plan) := by
  unfold linkAt at h
  dsimp only at h
  split at h
  · cases h
  · cases h
  · cases h
    rfl

section
open OnBytes.Flat OnBytes.Slice TypedOracleCompiler.Slice _root_.Run

/-- **AT EVERY PARAMETER FILE, IN SCOPE OR NOT, WHATEVER THE ELDER ROOT SAYS: the written value for the slot says no to all, or it is the run of linkDescriptionAt frP ‹a plan› ‹a Bool› at the keys written of the two records**: the form at which the laws on
the link are typed (decDescFullV frP plan ok (recX rr), Johnson/Desc/K15/HsemAtV.lean:153, for ANY plan and ANY Bool): the two agree by the definition of decDescFullV, at every plan and Bool; at the written value decWritten_is (Johnson/Goal/Conditions/EntryWrittenLaw.lean) states it, by the kernel, or that linkDecisionAtParameterFile says no to all.
(Where this and lean/THEOREM.md differ, the page holds.) -/
theorem decWritten_cases (pol : ByteArray) : linkDecisionAtParameterFile pol = (fun _ _ => false) ∨
    linkDecisionAtParameterFile pol = fun rr V => (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) (recX rr)) V := by
  unfold linkDecisionAtParameterFile
  split
  · split
    · split
      · rename_i L hL
        right
        rw [linkAt_F hL]
      · left; rfl
    · left; rfl
  · left; rfl

end

end Desc.K15

#print axioms Desc.K15.decWritten_cases
#print axioms Desc.K15.linkAt_of_root
#print axioms Desc.K15.linkWritten_eq
#print axioms Desc.K15.decWritten_eq
