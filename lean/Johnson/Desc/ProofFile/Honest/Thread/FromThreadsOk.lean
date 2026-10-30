-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FromThreadsOk.lean: `FromThreads` AT THE LETTER `SaidOk`: FIVE
OF ITS SEVENTEEN FIELDS ARE PAID THERE, AT EVERY THREAD, AND THE LETTER's SHARE OF THREE MORE FALLS.
`FromThreads` (Honest/Thread/FromThreads.lean) asks seventeen things of three threads, each with a
letter for what is said. Here all three letters are `SaidOk` (Honest/Thread/SaidOk.lean: every word
that the rounds seen show is below the prime). That letter reads the rounds seen alone, and not the
field `opened`. So: it is carried over every sub-protocol (`saidNext_ok`: the fields `next`); it
holds at the two starts, which have seen nothing (`said₁`, `said₂`); and behind the door it holds
because the second chain's start has seen what the two ends have seen. What is left are TWELVE
hypotheses, the last three of them in their source forms, which name no letter. Calls alone.

  `said₁_ok`, `said₂_ok`: the letter at the two starts
  `said₃_ok`: the letter behind the door
  `door_ok`: `DoorBehindS` at the letter, from `DoorBehind`
  `fromThreads_ok`: `FromThreads` at the letter, from the twelve

WHAT THESE ARE. CONDITIONAL LEMMAS ON OUR OWN DEFINITIONS. NONE IS ONE OF THE LIBRARY's GOALS; they
bear no milestone's name. No kind is named. The twelve are shown here of no description, no prover
and no thread.

Limits.
  * All limits of Honest/Thread/FromThreads.lean stand.
  * ONE LETTER. A law that spends more than `SaidOk` does not pay `owes` or `yes` here: its letter
    would have to be carried and met at the starts as well. `SaidOk` says nothing of the field
    `opened`: a letter that says what that field holds (`Thread.Field`,
    Honest/Thread/ThrField.lean) is such a letter, and this file pays neither its `next` nor its
    `said` nor its `door`.
  * `R` is a letter: nothing here says `ready … = .ok R`.
  * The debts `owes` and `yes` are asked from the pair with `SaidOk`. Whoever has them in the plain
    forms `Owes` and `Yes` has them here: `owesS_of`, `yesS_of` (Honest/Thread/PaysS.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FromThreads
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

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

/-- The letter at the first chain's start, as `ChainProgress.start` lays it: nothing has been seen. -/
theorem said₁_ok (H : Prover W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) :
    SaidOk 0 k { R.start₁ H with opened := some [] } :=
  saidOk_nil rfl

/-- The letter at the shared chain's start. -/
theorem said₂_ok (H : Prover W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) :
    SaidOk 0 k { R.start₂ H with opened := some [] } :=
  saidOk_nil rfl

/-- The letter at the second chain's start: it has seen what the two ends have seen. -/
theorem said₃_ok (H : Prover W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) {n₁ n₂ : Nat} {m₁ : Mid (Local W₀ Rc Xi Tr) X}
    {m₂ : Mid (Common W₀ Rc Ky) X₀} (c : List OpenedColumn) (h₁ : SaidOk n₁ k m₁) (h₂ : SaidOk n₂ k m₂) :
    SaidOk 0 k { R.start₃ H m₁ m₂ with opened := some c } :=
  saidOk_append (m' := m₁) (m'' := m₂) rfl h₁ h₂

/-- **The door at the letter, from the elder form.** -/
theorem door_ok (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) :
    DoorBehindS F H T₁ T₂ T₃ SaidOk SaidOk SaidOk x k R :=
  doorBehindS_of a₃ fun _ _ o₁ o₂ h₁ h₂ _ _ => said₃_ok H k R (o₁ ++ o₂) h₁ h₂

/-- **`FromThreads` at `SaidOk`, from twelve hypotheses.** A conditional lemma on this folder's own
definitions. It is none of the library's goals and proves none of them. `next₁`, `next₂`, `next₃`,
`said₁`, `said₂` are paid here; `door`, `doorYes`, `finYes` come of their elder forms. -/
theorem fromThreads_ok (sits : Sits F H T₁ T₂ T₃)
    (o₁ : OwesS T₁ SaidOk) (o₂ : OwesS T₂ SaidOk) (o₃ : OwesS T₃ SaidOk)
    (y₁ : YesS T₁ SaidOk (fallsBy f₁ F.first.blocksInOrder)) (y₂ : YesS T₂ SaidOk (fallsBy f₂ F.shared.blocksInOrder))
    (y₃ : YesS T₃ SaidOk (fallsBy f₃ F.second.blocksInOrder))
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) (door : DoorYes F T₁ T₂ x k)
    (fin : FinYes F T₁ T₂ T₃ x k) :
    FromThreads F H T₁ T₂ T₃ SaidOk SaidOk SaidOk f₁ f₂ f₃ w₀ rc x k R where
  sits := sits
  owes₁ := o₁
  owes₂ := o₂
  owes₃ := o₃
  next₁ := saidNext_ok T₁
  next₂ := saidNext_ok T₂
  next₃ := saidNext_ok T₃
  yes₁ := y₁
  yes₂ := y₂
  yes₃ := y₃
  enters₁ := a₁
  enters₂ := a₂
  said₁ := said₁_ok H k R
  said₂ := said₂_ok H k R
  door := door_ok a₃
  doorYes := doorYesS_of door
  finYes := finYesS_of fin

end ProofFile.Honest

#print axioms ProofFile.Honest.said₁_ok
#print axioms ProofFile.Honest.said₂_ok
#print axioms ProofFile.Honest.said₃_ok
#print axioms ProofFile.Honest.door_ok
#print axioms ProofFile.Honest.fromThreads_ok
