-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Start.lean: the last chain's first record holds the very statement that the
start is handed. One theorem.

Main name: `start₃E_st`: an equation at the border: every group, mark, open row, message and sample
row of the first chain's last statement stands in the last chain's first statement.

Limits. Nothing on what these mean. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.TakenSources

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice

namespace VerifiableInference.Desc.Third.Law

/-! ## The border: the start -/

/-- **The third chain begins at the very statement that the start is handed as the first chain's
last.** -/
theorem start₃E_st (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) : s₀.st = st₁ := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i t ht
        have e : t = s₀ := Except.ok.inj h
        subst e
        -- the start lays f.st; firstOutFrom lays st₁ into f
        have e₁ : t.st = f.st := by
          unfold start₃ at ht
          split at ht
          · have e := Option.some.inj ht
            subst e
            rfl
          · cases ht
        have e₂ : f.st = st₁ := by
          unfold firstOutFrom at hf
          split at hf
          · try dsimp only at hf
            repeat' (split at hf)
            all_goals first | (cases hf; rfl) | (cases hf)
          · cases hf
        exact e₁.trans e₂

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.start₃E_st
