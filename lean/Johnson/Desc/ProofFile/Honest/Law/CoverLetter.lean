-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverLetter.lean: the first chain's data as a letter.
`falls_first` (Honest/Law/CoverEnd.lean) and `localDebts_own` (Honest/Law/CoverOwn.lean) are to be
applied one after the other. A statement that writes all hypotheses of the second out at the first
chain's own data `at₁` (Honest/Law/CoverFile.lean) has been too slow for Lean to check. Here the
data are a letter `Xc`, and a hypothesis `hXc` says that `Xc` is `fun _ => at₁ ...`. These lemmas
prove, for such a letter, the hypotheses of `localDebts_own` that hold of every first chain
(`letter_starts` at `runC`'s own `[]`: whoever hands it in as `hX` lays `[]` for `front`), and
restate `falls_first` at the letter.

  1  `letter_starts`, `letter_stored`, `letter_tree`   what the walk starts from; the stored
     columns' words; the number of the first tree
  2  `pre_nodup`   no two gated sub-protocols stand at one place
  3  `falls_letter`   `falls_first`, with the first chain's bounds stated at the letter

Limits.
  * `falls_asks` (Honest/Law/CoverAsks.lean) applies `falls_letter` to the conclusion of
    `debts_letter` (Honest/Law/CoverDebts.lean).
  * Nothing is proved here of any description.
  * No number follows from the lemmas.
  * Among the hypotheses that the prose above does not name: `FileDescription.placesOk` (the library's
    executable test): `pre_nodup`; `ready … = .ok` (`ready` returns at these coins): `falls_letter`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverEnd
import Johnson.Desc.ProofFile.Honest.Law.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type}

/-! ## 1 The letter's three facts -/

/-- Every start of the walk comes from `ChainProgress.start` at the description's own first state, with no
column opened (`[]`). -/
theorem letter_starts (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (R : Ready W₀ Rc Xi Ky Tr X₀ X)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F P w₀ rc x R) :
    ∀ base a, (Xc base).start = some a → ∃ m₀ : Option (Mid (Local W₀ Rc Xi Tr) X),
      m₀.isSome = true ∧
        ChainProgress.start (Xc base).lay F.first.blocksInOrder m₀ (some (F.start₁ (F.pub x))) [] = .ok a := by
  subst hXc
  intro _ a h
  exact ⟨some (R.start₁ P), rfl, toOption_some h⟩

/-- The words of the stored columns are below the prime. -/
theorem letter_stored (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (R : Ready W₀ Rc Xi Ky Tr X₀ X)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F P w₀ rc x R) :
    ∀ base i y u, (Xc base).lay.stored i y = some u → ∀ a ∈ u, a < fieldPrimeWord := by
  subst hXc
  intro _
  exact storedWords_lt P w₀ rc

/-- The first tree has the number 0. -/
theorem letter_tree (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (R : Ready W₀ Rc Xi Ky Tr X₀ X)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F P w₀ rc x R) : ∀ base, (Xc base).lay.firstTree = 0 := by
  subst hXc
  intro _
  exact at₁_tree F P w₀ rc x R

/-! ## 2 The places -/

/-- No two sub-protocols before the chain's last one stand at one place. -/
theorem pre_nodup {F : FileDescription Xi} (hpl : F.placesOk = true) {pre₁ : List (Block F.S₁ F.Cl)}
    {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁]) :
    (pre₁.map (·.place)).Nodup := by
  have h := (places_nodup hpl).1
  rw [cut, List.map_append] at h
  exact h.of_append_left

/-! ## 3 The bound at the letter -/

/-- `falls_first`, with `d₁` stated at the letter. -/
theorem falls_letter (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi}
    {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (ms₁ ms₂ ms₃ : List Mark)
    (p₁ p₂ p₃ : Nat → ℝ≥0∞) {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit F (G.prover H) D pre₁ e₁) (hne : pre₁ ≠ [])
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = [])
    (s₁ : fellBy F.first.blocksInOrder G.falls₁ (at₁ F (G.prover H) w₀ rc x R) 0 [] = false)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F (G.prover H) w₀ rc x R)
    (d₁ : LocalDebts C F.first.blocksInOrder G.falls₁ ms₁ 0 Xc p₁ [noDraw] (silentQ ms₁ 0 pre₁) pre₁ 0 0
      D.ds₁)
    (hmk₂ : ∀ A b B, F.shared.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₂.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms₂ b.place fr (drawnT C _ ρ) = none)
    (hmk₃ : ∀ A b B, F.second.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₃.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms₃ b.place fr (drawnT C _ ρ) = none) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R ms₁ p₁ pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R ms₂ p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R ms₃ p₃).map (·.p)).sum) := by
  subst hXc
  exact falls_first C D tF tJ t3 G H w₀ rc x k R ms₁ ms₂ ms₃ p₁ p₂ p₃ hR Sf hne hf₂ hf₃ s₁ d₁
    hmk₂ hmk₃

end ProofFile.Honest

#print axioms ProofFile.Honest.letter_starts
#print axioms ProofFile.Honest.letter_stored
#print axioms ProofFile.Honest.letter_tree
#print axioms ProofFile.Honest.pre_nodup
#print axioms ProofFile.Honest.falls_letter
