-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/Public.lean: THE PUBLIC PREMISES OF `SwitchRowsHold` ALONE GIVE AN
`AtSwitch` (Inner/Words.lean): there are honest new messages: those at a fold that left zeros. So a
lemma that is typed under `AtSwitch` and speaks of rows' coefficients alone holds under the public
premises. Statements and proofs.

  `leftZero`, `rowsAtZero`   what a fold leaves, all 0; the new messages' rows at it
  `honest_zero`     these rows are honest
  `atPublic`        the public premises give an `AtSwitch`

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open Johnson.Prover.Send (Rows)

/-- What a fold leaves, all 0. -/
def leftZero : Left :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩⟩

/-- The new messages' rows at it: over the extension field the main rows themselves; else 0. -/
def rowsAtZero (Z : Sizes) (k : Nat) : Rows :=
  ⟨mainRows Z leftZero (fun _ _ _ => zeroG) k, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ _ => 0⟩

/-- These rows are honest, where the carrying message's rows are over the extension field. -/
theorem honest_zero (Z : Sizes) (h3 : Z.target.shape.mainDeg = 3) :
    HonestMain Z leftZero (rowsAtZero Z) := by
  intro k hk s b j _ _ _
  unfold Rows.main
  by_cases hd : (s.mainDeg == 3) = true
  · rw [if_pos hd]
    rfl
  · rw [if_neg hd]
    have hk0 : k ≠ 0 := by
      intro e
      apply hd
      show ((if k = 0 then Z.target.shape else Z.kept.getD (k - 1) {}).mainDeg == 3) = true
      rw [if_pos e, h3]
      rfl
    have hb : (k == 0) = false := by simpa using hk0
    show algebraMap _ _ (0 : Cb.Gl.F) = _
    unfold mainRows
    rw [hb, map_zero]
    simp only [Bool.false_eq_true, if_false, if_pos hk]
    rfl

/-- **The public premises give an `AtSwitch`.** -/
theorem atPublic {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} (check : switchTargetCheck S old T = true) (restMain : T.rest.part = .main)
    (fits : OldFits S old) (keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (seated : SeatedAt S old T g anew) (lengths : S.codes.lengthsOk = true) :
    AtSwitch S old T g anew leftZero (rowsAtZero (sizesAt S old T)) :=
  ⟨check, restMain, fits, keptPos, seated, lengths,
    honest_zero _ ((_root_.Tw.K2.targetOk_means S old T).1
      ((_root_.Tw.K2.targetOk_eq S old T).trans check)).degree⟩

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.atPublic
