-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastOwes.lean: `Behind` at the key file's last thread at the values that this thread lays: the letter
for riders is true of all, and the letter for what is kept says that only the own test moves the state.

  `keptOwn`: that letter.
  `behind_all`: `Behind` at all four members, in scope.

What stays open. `RidesPast` at 0, 1, 3 (the pins' strings) is not here.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastOwn
import E2E.KeyLastQuiet

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
open AtPublicFiles.KeyLastThread (lettersLastKey)
open AtPublicFiles.KeyLastQuiet (behind_first behind_sources behind_end)
open AtPublicFiles.KeyLastOwn (behind_own)
open AtPublicFiles.AtFiles (KeySourced)

/-- Only the own test moves the state. -/
def keptOwn (q : Place) (s s' : S₃) : Prop := q = ⟨3, none, 2, .K12⟩ ∨ s' = s

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Wt : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) Wt)
  (m₁ : Local W₀ Rc Xi Unit → KItem → Xi × FirstState → Strs → Wt → Prop)
  (ML : MeaningL S₃ Wt)
  (ends : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → (Xi × FirstState) × St)
  (wit : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)

/-- The thread at the two letters. -/
abbrev quietT :=
  (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun _ _ _ => True) keptOwn w).thread

/-- **`Behind` at all four members.** -/
theorem behind_all (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (b : Nat) (hb : b < 4) :
    Behind (quietT Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd w) b := by
  have hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, keptOwn q s s :=
    fun _ _ _ => Or.inr rfl
  have h0 := behind_first Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun _ _ _ => True) keptOwn w
    fun _ _ _ _ _ _ _ => trivial
  have h1 := behind_sources Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hK
    fun _ _ _ _ _ _ _ => trivial
  have h2 := behind_own Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hs scope
    (fun _ _ _ _ _ _ => Or.inl rfl) fun _ _ _ _ _ _ _ => trivial
  have h3 := behind_end Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hK
    fun _ _ _ _ _ _ _ => trivial
  match b, hb with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | _ + 4, h => exact absurd h (by omega)

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.behind_all
