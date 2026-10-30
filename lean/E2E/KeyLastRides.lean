-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastRides.lean: `RidesPast` at all four members of the key file's last thread at this work's letters, from one premise.

  `rides_all`.

What stays open. `hY`: a pin read at the strings of E says the same at those of E with this chain's new tables. The last chain's
strings keep every tree taken over (`srcAt`, `Env.add`); that a pin reads those alone is the meaning's matter.
What is shown: the member 0 reads no state at the three pins; the members 1 and 3 leave the state; the own test shuts all.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastOwes
import E2E.KeyLastMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL ItemL lastPlaces startLast)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces descriptionFromSource thirdPar)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) Wt)
  (m₁ : Local W₀ Rc Xi Unit → KItem → Xi × FirstState → Strs → Wt → Prop)
  (ML : MeaningL S₃ Wt)
  (ends : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → (Xi × FirstState) × St)
  (wit : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)

/-- **Riders at all four members.** -/
theorem rides_all
    (hY : ∀ v (i : ItemL) a (E : Env) (ps : List Played) u,
      i = .pinI ∨ i = .pinV ∨ i = .pinO →
      (quietT Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd w).means v i a
        ((quietT Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd w).strs E) u →
      (quietT Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd w).means v i a
        ((quietT Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd w).strs (E.add ps)) u)
    (b : Nat) (hb : b < 4) : RidesPast (quietT Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd w) b := by
  match b, hb with
  | 0, _ =>
    intro k s m E s' ps i v _ _ hi hs ho hu
    have hs' : (i : ItemL) ∉ (LastRows.rows 0).shuts := hs
    have ho' : (i : ItemL) ∉ (LastRows.rows 0).owes := ho
    have key : ∀ j : ItemL, j ∉ (LastRows.rows 0).shuts → j ∉ (LastRows.rows 0).owes →
        j = .pinI ∨ j = .pinV ∨ j = .pinO := by
      intro j
      cases j <;> decide
    rcases key i hs' ho' with rfl | rfl | rfl
    · exact hY _ .pinI _ E ps v (Or.inl rfl) hu
    · exact hY _ .pinV _ E ps v (Or.inr (Or.inl rfl)) hu
    · exact hY _ .pinO _ E ps v (Or.inr (Or.inr rfl)) hu
  | 1, _ =>
    intro k s m E s' ps i v _ hk hi _ _ hu
    have hq : keptOwn ⟨3, none, 1, .frame⟩ s s' := by
      have e := hk ⟨3, none, 1, .frame⟩ rfl
      exact e
    rcases hq with hq | hq
    · cases hq
    · subst hq
      have hi' : (i : ItemL) ∈ fwdOpen startLast LastRows.rows 1 := hi
      have key : ∀ j : ItemL, j ∈ fwdOpen startLast LastRows.rows 1 →
          j = .rows ∨ j = .pinI ∨ j = .pinV ∨ j = .pinO := by
        intro j
        cases j <;> decide
      rcases key i hi' with e | e
      · subst e
        exact hu
      · exact hY _ i _ E ps v e hu
  | 2, _ => exact ridesPast_own _
  | 3, _ =>
    intro k s m E s' ps i v _ _ hi _ _ _
    have hi' : (i : ItemL) ∈ fwdOpen startLast LastRows.rows 3 := hi
    have e : fwdOpen startLast LastRows.rows 3 = [] := by decide
    rw [e] at hi'
    cases hi'
  | _ + 4, h => exact absurd h (by omega)

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.rides_all
