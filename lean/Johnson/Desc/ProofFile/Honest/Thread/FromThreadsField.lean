-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FromThreadsField.lean: `FromThreads` AT THE LETTER `SaidField`.
`FromThreadsOk.lean` lays `FromThreads` at `SaidOk`, where `next`, `said` and the letter's share of
`door` cost nothing. Here the three letters say what the field `opened` holds: the first and the
shared chain with nothing in front, the last chain at a letter `B₃` for its base. `said` still costs
nothing. `next` is a premise, paid by `saidNext_field_of_owes`. `door` needs one premise more: that
`B₃` holds of the columns that the two earlier chains hand to the last.

  `said₁_field`, `said₂_field`   the letter at the two starts
  `door_field`   `DoorBehindS` at the letters, from `DoorBehind` and the premise on `B₃`
  `fromThreads_field`   `FromThreads` at the letters

What these are. Conditional lemmas on our own definitions. None is one of the library's goals.

Limits.
  * All limits of Honest/Thread/FromThreads.lean and Honest/Thread/SaidField.lean stand.
  * `B₃` is a letter. At `fun _ _ _ => True` the premise `hB` costs nothing, and the last chain's
    letter says only that some base exists, which a test of that chain that reads the columns in
    front cannot use. Which `B₃` serves is not said here.
  * `R` is a letter: nothing here says `ready … = .ok R`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SaidField
import Johnson.Desc.ProofFile.Honest.Thread.FromThreadsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  {B₃ : Coins Bk → Mid (Local W₀ Rc Xi Tr) X → List OpenedColumn → Prop}

/-- The letter at the first chain's start, as `ChainProgress.start` lays it. -/
theorem said₁_field (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) :
    SaidField T₁ BaseNil 0 k { R.start₁ H with opened := some [] } :=
  saidField_start T₁ rfl

/-- The letter at the shared chain's start. -/
theorem said₂_field (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) :
    SaidField T₂ BaseNil 0 k { R.start₂ H with opened := some [] } :=
  saidField_start T₂ rfl

/-- **The door at the letters.** `hB`: `B₃` holds of the columns that the two ends hand on. -/
theorem door_field (a₃ : DoorBehind F H T₁ T₂ T₃ x k R)
    (hB : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      ThrS T₁ (SaidField T₁ BaseNil) F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidField T₂ BaseNil) F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      B₃ k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (o₁ ++ o₂)) :
    DoorBehindS F H T₁ T₂ T₃ (SaidField T₁ BaseNil) (SaidField T₂ BaseNil) (SaidField T₃ B₃)
      x k R :=
  fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs g₁ g₂ =>
    ⟨a₃ e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁.1 u₂.1 hs, said₃_ok H k R (o₁ ++ o₂) u₁.2.1 u₂.2.1, o₁ ++ o₂,
      hB e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs g₁ g₂, fun E _ => T₃.field_start (o₁ ++ o₂) _ E⟩

/-- **`FromThreads` at the letters.** A conditional lemma on this folder's own definitions. It is
none of the library's goals. `said₁`, `said₂` are paid here; `next₁`, `next₂`, `next₃` are premises
(`saidNext_field_of_owes`); `door` comes of `door_field`, `doorYes` and `finYes` of their elder
forms. -/
theorem fromThreads_field (sits : Sits F H T₁ T₂ T₃)
    (o₁ : OwesS T₁ (SaidField T₁ BaseNil)) (o₂ : OwesS T₂ (SaidField T₂ BaseNil))
    (o₃ : OwesS T₃ (SaidField T₃ B₃))
    (n₁ : ∀ b, SaidNext T₁ (SaidField T₁ BaseNil) b)
    (n₂ : ∀ b, SaidNext T₂ (SaidField T₂ BaseNil) b)
    (n₃ : ∀ b, SaidNext T₃ (SaidField T₃ B₃) b)
    (y₁ : YesS T₁ (SaidField T₁ BaseNil) (fallsBy f₁ F.first.blocksInOrder))
    (y₂ : YesS T₂ (SaidField T₂ BaseNil) (fallsBy f₂ F.shared.blocksInOrder))
    (y₃ : YesS T₃ (SaidField T₃ B₃) (fallsBy f₃ F.second.blocksInOrder))
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R)
    (hB : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      ThrS T₁ (SaidField T₁ BaseNil) F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidField T₂ BaseNil) F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      B₃ k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (o₁ ++ o₂))
    (door : DoorYes F T₁ T₂ x k) (fin : FinYes F T₁ T₂ T₃ x k) :
    FromThreads F H T₁ T₂ T₃ (SaidField T₁ BaseNil) (SaidField T₂ BaseNil) (SaidField T₃ B₃)
      f₁ f₂ f₃ w₀ rc x k R where
  sits := sits
  owes₁ := o₁
  owes₂ := o₂
  owes₃ := o₃
  next₁ := n₁
  next₂ := n₂
  next₃ := n₃
  yes₁ := y₁
  yes₂ := y₂
  yes₃ := y₃
  enters₁ := a₁
  enters₂ := a₂
  said₁ := said₁_field T₁ H k R
  said₂ := said₂_field T₂ H k R
  door := door_field a₃ hB
  doorYes := doorYesS_of door
  finYes := finYesS_of fin

end ProofFile.Honest

#print axioms ProofFile.Honest.said₁_field
#print axioms ProofFile.Honest.said₂_field
#print axioms ProofFile.Honest.door_field
#print axioms ProofFile.Honest.fromThreads_field
