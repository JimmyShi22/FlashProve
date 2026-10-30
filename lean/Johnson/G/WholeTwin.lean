-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/WholeTwin.lean: a twin of `OnBytes.Three.Whole.of` that Lean's kernel can evaluate at long
lists of rounds, with the proof that the two are equal.

`OnBytes.Three.sentBefore` counts, for each round, the trees that the chain has sent before it, by a
fold that pushes onto an array. Lean's kernel evaluates an array's push as an append to a list, and
at some thousands of rounds it runs out of stack. The twin counts by recursion over the list.
Definitions and proofs.
Main names:
  `sentFrom a R`: the counts, from a on. `sentBefore_eq : sentBefore R = sentFrom 0 R`.
  `rdsTwin`, `rdsFromL_eq`: a chain's rounds' data over `sentFrom`.
  `wholeTwin R₁ R₂ R₃`, `whole_eq : Three.Whole.of R₁ R₂ R₃ = wholeTwin R₁ R₂ R₃`.
Limits: general in the lists; no value is treated. Nothing on soundness.

-/
import OnBytes.Three.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Three
open OnBytes.Params (Rounds)

/-- For each round the number of trees sent before it, counted from a. -/
def sentFrom : Nat → Rounds → List Nat
  | _, [] => []
  | a, r :: R => a :: sentFrom (a + r.1.items.countP (· == .root)) R

theorem sentFold (R : Rounds) : ∀ (a : Nat) (A : Array Nat),
    (R.foldl (fun (x : Nat × Array Nat) r =>
      (x.1 + r.1.items.countP (· == .root), x.2.push x.1)) (a, A)).2.toList =
      A.toList ++ sentFrom a R := by
  induction R with
  | nil => intro a A; simp [sentFrom]
  | cons r R ih =>
    intro a A
    rw [List.foldl_cons, ih]
    simp [sentFrom]

theorem sentBefore_eq (R : Rounds) : sentBefore R = sentFrom 0 R := by
  unfold sentBefore
  rw [sentFold]
  simp

/-- The rounds' data of one chain, over the twin. -/
def rdsTwin (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat) (R : Rounds) :
    List RDL :=
  List.zipWith (rdOf all t₁ t₂ here base first) R (sentFrom 0 R)

theorem rdsFromL_eq (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (R : Rounds) : rdsFromL all t₁ t₂ here base first R = rdsTwin all t₁ t₂ here base first R := by
  unfold rdsFromL rdsTwin
  rw [sentBefore_eq]

/-- The twin of `Three.Whole.of`. -/
def wholeTwin (R₁ R₂ R₃ : Rounds) : Whole :=
  let t₁ := rootsIn R₁
  let t₂ := rootsIn R₂
  let all := opensOf t₁ t₂ 0 R₁ ++ (opensOf t₁ t₂ 1 R₂ ++ opensOf t₁ t₂ 2 R₃)
  let ds₁ := rdsTwin all t₁ t₂ 0 0 0 R₁
  let ds₂ := rdsTwin all t₁ t₂ 1 t₁ 0 R₂
  let ds₃ := rdsTwin all t₁ t₂ 2 (t₁ + t₂) (first₃ t₁) R₃
  ⟨ds₁, ds₂, ds₃,
    treesOfChain all 0 0 ds₁ ++ (treesOfChain all 1 t₁ ds₂ ++ treesOfChain all 2 (t₁ + t₂) ds₃),
    t₁, t₂, rootsIn R₃, all⟩

theorem whole_eq (R₁ R₂ R₃ : Rounds) : Whole.of R₁ R₂ R₃ = wholeTwin R₁ R₂ R₃ := by
  unfold Whole.of wholeTwin
  simp only [rdsFromL_eq]

end Johnson.G

#print axioms Johnson.G.sentBefore_eq
#print axioms Johnson.G.whole_eq
