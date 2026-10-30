-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.CallsDef
import Johnson.Desc.K12.Law.RowsForOn
import Johnson.Desc.Means.Walk
import Johnson.Desc.GroundKeeps
/-
Johnson/Desc/K12/Law/CallsWalkG.lean: A RUN OF THE GROUND's CALLS (Johnson/Desc/K12/Law/CallsDef.lean) IS A WALK (Johnson/Desc/Means/Walk.lean: quiet steps and beginnings of tests) FROM ITS FIRST STATEMENT TO ITS LAST, WHERE THE CODES' LENGTHS ARE IN ORDER. So «tidy in front» gives «tidy behind», and no claim is lost. The law on the sample's rows is no premise. It stands over the plain ground, Means and the sending's laws alone: it reads no block. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  call_codes     a step leaves the codes
  call_walk      Codes.lengthsOk at d.st.codes ⇒ a step is a walk from d.st to d'.st: at a step that admits the rows lie on the message by rowsFor_on | sampleFit_of (Johnson/Desc/K12/Law/RowsForOn.lean)
  calls_walk     Codes.lengthsOk at d.st.codes · a run from d to d' ⇒ Walk ρ d.st d'.st ∧ d'.st.codes = d.st.codes
  calls_tidy     … · Means.Tidy d.st ⇒ Means.Tidy d'.st
WHAT IT DOES NOT SAY: that the codes' lengths are in order (a test with code on public data) · that any statement in front is tidy.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {K : Type} [CommRing K] (ρ : Model.Reading K) {ft : Nat}

theorem call_codes (d d' : DS) (h : Call ft d d') : d'.st.codes = d.st.codes := by
  cases h with
  | newGroup h => exact (groundKeeps_grows.newGroup _ _ _ _ _ h).1
  | recv h => exact (groundKeeps_grows.recv _ _ _ _ _ h).1
  | admit _ _ _ _ h => exact (groundKeeps_grows.admit _ _ _ _ h).1
  | join h => exact (groundKeeps_grows.join _ _ _ _ _ h).1
  | addRow h => exact (groundKeeps_grows.addRow _ _ _ _ h).1
  | closeLedger h => exact (groundKeeps_grows.closeLedger _ _ _ h).1
  | spend h => exact (groundKeeps_grows.spendAsMask _ _ _ h).1
  | begin h =>
    obtain ⟨G, _, _, e⟩ := beginRunP_inv h
    rw [e]
    exact Slice.closeLedgers_codes _ _
  | count t => rfl
  | cols l => rfl

theorem call_walk (d d' : DS) (hl : d.st.codes.lengthsOk = true) (h : Call ft d d') :
    Walk ρ d.st d'.st := by
  cases h with
  | newGroup h => exact (quiet_newGroupP ρ h).walk
  | recv h => exact (quiet_recvP ρ h).walk
  | admit hs hfit hlong hr h =>
    refine (quiet_admitP ρ h ?_).walk
    have h' := h
    unfold admitP at h'
    split at h'
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
      obtain ⟨x, hx, pl, hpl, _⟩ := h'
      rw [hx] at hs
      obtain rfl := Option.some.inj hs
      have hpl' : Send.pad d.st.codes x.shape = some pl := hpl
      exact rowsFor_on d.st _ x hx _ (sampleFit_of d.st x _ pl hl hfit hlong hpl') _ _ _ _ _
        (fun r hr' => by simp at hr') hr
    · cases h'
  | join h => exact (quiet_joinP ρ h).walk
  | addRow h => exact (quiet_addRowP ρ h).walk
  | closeLedger h => exact (quiet_closeLedgerP ρ h).walk
  | spend h => exact (quiet_spendAsMaskP ρ h).walk
  | begin h => exact Walk.of_beginRunP ρ h
  | count t => exact Walk.nil _
  | cols l => exact Walk.nil _


theorem calls_walk {d d' : DS} (h : Calls ft d d') (hl : d.st.codes.lengthsOk = true) :
    Walk ρ d.st d'.st ∧ d'.st.codes = d.st.codes := by
  induction h with
  | nil d => exact ⟨Walk.nil _, rfl⟩
  | cons s _ ih =>
    have hc := call_codes _ _ s
    obtain ⟨w, e⟩ := ih (by rw [hc]; exact hl)
    exact ⟨(call_walk ρ _ _ hl s).trans w, e.trans hc⟩

include ρ in
theorem calls_tidy {d d' : DS} (h : Calls ft d d') (hl : d.st.codes.lengthsOk = true)
    (hT : Tidy d.st) : Tidy d'.st :=
  (calls_walk ρ h hl).1.tidy hT

end H2K.Out

#print axioms H2K.Out.calls_walk
#print axioms H2K.Out.calls_tidy
