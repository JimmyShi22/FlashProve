-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverMarksJoin.lean: two fields of `FirstAsks`
(Honest/Law/CoverAsks.lean) at a list of marks that is several owners' lists in a row. Each owner of
sub-protocols lays its own list of marks and proves the field `hM` (a bound for each mark) at its
own list. Here `hM` at two lists in a row follows from `hM` at each. The number stated for a mark
may be read in different ways by different owners, so `hM` is also carried from one function of
numbers to another that agrees with it on the list. The field `hq0` (the number laid for a mark of
`fitMarks` is 0) holds at two ways of reading a mark's number. The field `hseat` at two lists in a
row is `List.forall_mem_append`. It is general in the chain and in the lists.

  1  `hM_append`   the field `hM` at two lists in a row
  2  `hM_congr`   `hM` at another function of numbers that agrees on the list
  3  `hq0_val`, `hq0_num`   `hq0` where a mark's number is its stated share's value, and where it is
     the share's numerator times a factor

Limits.
  * No list of marks is laid here, and no bound is proved.
  * The condition `PM` is one function for both lists.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld
import Johnson.Desc.ProofFile.Honest.Law.Due

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

variable {S Cl : Type}

/-- The field `hM` at two lists in a row. -/
theorem hM_append (C : CK) {pre₁ : List (Block S Cl)} {hm₁ hm₂ : List Mark}
    {PM : Block S Cl → List Fmt.Drawn → Prop} {qM : Block S Cl → Mark → ℝ≥0∞}
    (h₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm₁.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (h₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm₂.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (hm₁ ++ hm₂).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk) := by
  intro A b b' B e mk hmk dsb hd
  rw [List.filter_append] at hmk
  rcases List.mem_append.1 hmk with h | h
  · exact h₁ A b b' B e mk h dsb hd
  · exact h₂ A b b' B e mk h dsb hd

/-- The field `hM` at another function of numbers that agrees with the first on the list. -/
theorem hM_congr (C : CK) {pre₁ : List (Block S Cl)} {hm : List Mark}
    {PM : Block S Cl → List Fmt.Drawn → Prop} {qM q' : Block S Cl → Mark → ℝ≥0∞}
    (hq : ∀ b, ∀ mk ∈ hm, qM b mk = q' b mk)
    (h : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (q' b mk)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk) := by
  intro A b b' B e mk hmk dsb hd
  rw [hq b mk (List.mem_filter.1 hmk).1]
  exact h A b b' B e mk hmk dsb hd

/-- The field `hq0` where a mark's number is its stated share's value. -/
theorem hq0_val (pre₁ : List (Block S Cl)) :
    ∀ b ∈ pre₁, (fun (_ : Block S Cl) (mk : Mark) => mk.share.val) b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0 := by
  intro b _
  show (⟨0, 1⟩ : Odds).val = 0
  simp [Odds.val]

/-- The field `hq0` where a mark's number is its stated share's numerator times a factor. -/
theorem hq0_num (pre₁ : List (Block S Cl)) (kap : ℝ≥0∞) :
    ∀ b ∈ pre₁, (fun (_ : Block S Cl) (mk : Mark) => (mk.share.num : ℝ≥0∞) * kap) b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0 := by
  intro b _
  show (((⟨0, 1⟩ : Odds).num : Nat) : ℝ≥0∞) * kap = 0
  simp

end ProofFile.Honest

#print axioms ProofFile.Honest.hM_append
#print axioms ProofFile.Honest.hM_congr
#print axioms ProofFile.Honest.hq0_val
#print axioms ProofFile.Honest.hq0_num
