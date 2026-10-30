-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/DoorAndClause.lean: THE DOOR WITH ONE MORE CLAUSE ON THE SECOND
CHAIN. The companion Said of the second chain's thread may be widened by a clause on the run. The
rules that read Said as a premise take the wider one as it stands. The door has to give it.

  doorBehindS_and   where the door gives S₃, and the clause holds at each state at which the door
    enters, the door gives both

What this is. A lemma on our own definitions. It is none of the library's goals.

Limits. That a clause holds at the door's states is a premise.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Ky Tr X₀ X : Type} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ C : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **The door with one more clause.** -/
theorem doorBehindS_and (hd : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R)
    (hC : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → C 0 k { R.start₃ H m₁ m₂ with opened := o }) :
    DoorBehindS F H T₁ T₂ T₃ S₁ S₂ (fun b k m => S₃ b k m ∧ C b k m) x k R := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs p₁ p₂
  have d := hd e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs p₁ p₂
  exact ⟨d.1, d.2, hC e₁ m₁ E₁ e₂ m₂ E₂ _ u₁ u₂⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.doorBehindS_and
