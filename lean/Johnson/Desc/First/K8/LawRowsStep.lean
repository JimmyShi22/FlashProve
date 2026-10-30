-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRowsStep.lean: THE SMALLNESS TEST, ITS FIRST HALF: WHAT A YES OF THE BLOCK
AS THE FOLD CALLS IT MEANS AT THE CARRIED RECORD, WITH THE FRAME'S OWN TEST ON THE ROUND HELD.

WHY THIS FILE. `HearMeansAtRecord` (Johnson/Desc/First/K8/LawRowsMeans.lean) speaks of the block's
DECISION. The fold over a chain's blocks calls `Block.step` (Johnson/Desc/Block.lean), which asks
the frame's test on the rounds (`roundsFit`) in front of the decision. The head of LawRowsMeans.lean
hands that to `HearLaw`; but `HearLaw` ranges over the images of typed transcripts alone, all of
which are well shaped: a frame that asked nothing of the rounds would leave it true. The tie between
step and decision is proved (`step_eq`, `step_ok`, Johnson/Desc/First/K8/Law.lean) and stood in no
row. Here it is bound:
  `HearStepMeansAtRecord`: a closed proposition: AT THE CARRIED RECORD, AT ALL LISTS OF ROUNDS AND
    ALL COLUMNS: the step says yes, hands on st' and takes n columns IF AND ONLY IF there is one
    round r, THE FRAME'S TEST ON THE ROUND PASSES (it shows no item; it drew no element and no
    position, and columns x tau matrix entries, each -1, 0 or 1), `MeansAtS p st r st'` holds, and
    n = 0.
  `K08LawHearingAtStep` := `K08LawHearingAtRecord` ∧ `HearStepMeansAtRecord`, with a theorem of just
    that type.
Statement and proof.
Limits. IT IS THE YES OF THE STEP OF `approximateRangeProofDrawKind atS p`: that a description seats that block at a place,
and that a verifier runs that description, is said nowhere here. What the record's fields MEAN is
not said. `S.tl?` and `S.putTl` are functions of Johnson/Desc/First/State.lean and stand on both
sides. The step says yes at a record that bears a mark, too.

-/
import Johnson.Desc.First.K8.LawRowsMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- **The step at the carried record, both ways, in the record's own fields.** -/
theorem step_atS_iff {Cl : Type} (p : Par) (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView)
    (cols : List Col) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols = .ok (st', n) ↔
      ∃ r, rs = [r] ∧ roundsFit [round p] [r] = true ∧ MeansAtS p st r st' ∧ n = 0 := by
  constructor
  · intro h
    obtain ⟨hn, r, rfl, hfit, _⟩ := step_ok atS p ft st st' rs cols n h
    rw [step_eq atS p ft st r cols hfit] at h
    cases hd : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide st [noDigest r] [] with
    | error e => rw [hd] at h; simp [Except.map] at h
    | ok s1 =>
      rw [hd] at h
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨r, rfl, hfit, (decide_atS_iff p st s1 (noDigest r) []).1 hd, hn⟩
  · rintro ⟨r, rfl, hfit, hm, rfl⟩
    rw [step_eq atS p ft st r cols hfit,
      (decide_atS_iff (Cl := Cl) p st st' (noDigest r) []).2 hm]
    rfl

/-- At the carried record a yes of the step means just this. -/
def HearStepMeansAtRecord : Prop :=
  ∀ (Cl : Type) (p : Par) (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List Col),
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols = .ok (st', n) ↔
      ∃ r, rs = [r] ∧ roundsFit [round p] [r] = true ∧ MeansAtS p st r st' ∧ n = 0

theorem hearStepMeansAtRecord : HearStepMeansAtRecord :=
  fun _ p ft st st' n rs cols => step_atS_iff p ft st st' n rs cols

/-- **The row on what a yes means, at the step as the fold calls it.** -/
def K08LawHearingAtStep : Prop := K08LawHearingAtRecord ∧ HearStepMeansAtRecord

theorem k08LawHearingAtStep : K08LawHearingAtStep :=
  ⟨k08LawHearingAtRecord, hearStepMeansAtRecord⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.step_atS_iff
#print axioms VerifiableInference.Desc.First.K8.hearStepMeansAtRecord
#print axioms VerifiableInference.Desc.First.K8.k08LawHearingAtStep
