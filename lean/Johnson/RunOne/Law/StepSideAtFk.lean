-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/StepSideAtFk.lean: THE FOUR
STEPS OF Johnson/RunOne/Law/StepSide4.lean AT THE KEY FILE's OWN DESCRIPTION, IN THE FORM OF THE
FIELDS g4 | g5 | g10 | g11 of the structure Gaps
(Johnson/Top/Fire/Code/KeyASideAtFk.lean): at whatever block stands at the place k of the first
chain's flat list.

Main names:
  H₀ X, H₁ X: the state holds what the kind K3's own block of lookup 0 | 1 has left (HeardOk).
  g4 | g10: StepInv b (ASide … k) (ASide … (k + 1) ∧ H): THE BLOCK EARNS H.
  g5 | g11: StepInv b (ASide … k ∧ H) (ASide … (k + 1)): THE LAYER SPENDS IT.
  lk_of_list: where the lookups are [x₀, x₁]: lookup 0 | 1 as these files name it is x₀ | x₁.

Premises: the plan's ranges are admitted (Wf.admitted); the lookup is there.
Limits. Nothing on the claims. Nothing on soundness.

-/
import Johnson.RunOne.Law.StepSide4
import Johnson.RunOne.KeyRowsAtFk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.StepSideAtFk
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Source Where lookupSeat lookupPlace lookupsOf)
open Johnson.RunOne.Sound (FK fk_K3_at fk_layer_at)
open Johnson.RunOne.KeyRows1 (ASide)
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.StepSide4
open LPFD (StepInv)

/-- The state holds what the kind's own block of lookup 0 has left. -/
def H₀ (X : Source) (s : FirstState) : Prop :=
  HeardOk lookupSeat (lookupPlace X.set 0 (lk (oneAt X) 0)) s

/-- The state holds what the kind's own block of lookup 1 has left. -/
def H₁ (X : Source) (s : FirstState) : Prop :=
  HeardOk lookupSeat (lookupPlace X.set 1 (lk (oneAt X) 1)) s

/-- Where the lookups are [x₀, x₁]. -/
theorem lk_of_list (one : OneTime) (x₀ x₁ : VerifiableInference.Desc.Key.Lookup)
    (h : lookupsOf one = [x₀, x₁]) : lk one 0 = x₀ ∧ lk one 1 = x₁ := by
  have hn : one.ranges.lookups.length = 2 := by
    have e : (lookupsOf one).length = one.ranges.lookups.length := List.length_map _
    rw [← e, h]
    rfl
  have e0 := look_at one 0 (by omega)
  have e1 := look_at one 1 (by omega)
  rw [h] at e0 e1
  exact ⟨(Option.some.inj e0).symm, (Option.some.inj e1).symm⟩

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
  (at_ : Where)

/-- **g4.** -/
theorem g4 (hW : Wf.admitted (oneAt X).codes (oneAt X).ranges (Wf.matrixOf (oneAt X).lin) = true)
    (hl : 0 < (oneAt X).ranges.lookups.length) :
    ∀ b, (Fk X N P).first.blocksInOrder[4]? = some b →
      StepInv b (ASide (oneAt X) at_ 4) (fun s => ASide (oneAt X) at_ 5 s ∧ H₀ X s) := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_K3_at X N P 0 _ (look_at (oneAt X) 0 hl)).symm.trans hb)
  intro s s' rs gs hf hy hA
  have h := step_4 (oneAt X) X.set at_ hW hl s s' rs gs hf hy
    ⟨hA, jside_else _ _ 4 (by decide) (by decide) s⟩
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rwa [jside_5] at h2

/-- **g5.** -/
theorem g5 (hW : Wf.admitted (oneAt X).codes (oneAt X).ranges (Wf.matrixOf (oneAt X).lin) = true)
    (hl : 0 < (oneAt X).ranges.lookups.length) :
    ∀ b, (Fk X N P).first.blocksInOrder[5]? = some b →
      StepInv b (fun s => ASide (oneAt X) at_ 5 s ∧ H₀ X s) (ASide (oneAt X) at_ 6) := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_layer_at X N P 0 _ (look_at (oneAt X) 0 hl)).symm.trans hb)
  intro s s' rs gs hf hy hA
  exact (step_5 (oneAt X) X.set at_ hW hl s s' rs gs hf hy
    ⟨hA.1, by rw [jside_5]; exact hA.2⟩).1

/-- **g10.** -/
theorem g10 (hW : Wf.admitted (oneAt X).codes (oneAt X).ranges (Wf.matrixOf (oneAt X).lin) = true)
    (hl : 1 < (oneAt X).ranges.lookups.length) :
    ∀ b, (Fk X N P).first.blocksInOrder[10]? = some b →
      StepInv b (ASide (oneAt X) at_ 10) (fun s => ASide (oneAt X) at_ 11 s ∧ H₁ X s) := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_K3_at X N P 1 _ (look_at (oneAt X) 1 hl)).symm.trans hb)
  intro s s' rs gs hf hy hA
  have h := step_10 (oneAt X) X.set at_ hW hl s s' rs gs hf hy
    ⟨hA, jside_else _ _ 10 (by decide) (by decide) s⟩
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rwa [jside_11] at h2

/-- **g11.** -/
theorem g11 (hW : Wf.admitted (oneAt X).codes (oneAt X).ranges (Wf.matrixOf (oneAt X).lin) = true)
    (hl : 1 < (oneAt X).ranges.lookups.length) :
    ∀ b, (Fk X N P).first.blocksInOrder[11]? = some b →
      StepInv b (fun s => ASide (oneAt X) at_ 11 s ∧ H₁ X s) (ASide (oneAt X) at_ 12) := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_layer_at X N P 1 _ (look_at (oneAt X) 1 hl)).symm.trans hb)
  intro s s' rs gs hf hy hA
  exact (step_11 (oneAt X) X.set at_ hW hl s s' rs gs hf hy
    ⟨hA.1, by rw [jside_11]; exact hA.2⟩).1

end Johnson.RunOne.Law.StepSideAtFk

#print axioms Johnson.RunOne.Law.StepSideAtFk.lk_of_list
#print axioms Johnson.RunOne.Law.StepSideAtFk.g4
#print axioms Johnson.RunOne.Law.StepSideAtFk.g5
#print axioms Johnson.RunOne.Law.StepSideAtFk.g10
#print axioms Johnson.RunOne.Law.StepSideAtFk.g11
