-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyReady.lean: theorems about the two toy examples of
Honest/Law/ToyRow.lean and Honest/Law/ToyFall.lean: at every input of the examples' relation and at
all coins `ready` (Honest/Frame.lean) returns, and the three lists of rounds that it prepares have
the skeletons (Honest/Law/ToySk.lean) that are written out here as closed lists; these pass that
file's two tests. The theorems are about these files' own made-up objects alone. None is one of the
library's goals.

  1  `skBare`, `skHalf`, `Ky₁` … `Kv₃`   the skeletons, computed from the descriptions' own
     sub-protocols
  2  `ready_row`, `ready_rowV`   `ready` returns

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

Limits.
  * A toy example.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyFall
import Johnson.Desc.ProofFile.Honest.Law.ToySk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.BlockToy (St look send₃ sealB)

/-! ## 1 The skeletons -/

/-- The rounds of a sub-protocol at which no prover's side is defined. -/
def skBare (b : Block St Nat) : List Sk :=
  (b.rounds.zip b.oracles).map fun r => (r.1, r.2, false, 0)

/-- The rounds of a sub-protocol at which a prover's side is defined. `ns`: round by round its
part's number. -/
def skHalf (b : Block St Nat) (ns : List Nat) : List Sk :=
  ((b.rounds.zip b.oracles).zip ns).map fun r => (r.1.1, r.1.2, true, r.2)

def Ky₁ : List Sk := skBare sealB
def Ky₂ : List Sk := skHalf (look [(3, 1)] true ()) [0, 1] ++ skBare storeY
def Ky₃ : List Sk := skHalf send₃ [0] ++ skHalf tellB [0, 0] ++ skHalf askQ [0]

def Kv₁ : List Sk := skBare sealB
def Kv₂ : List Sk := []
def Kv₃ : List Sk :=
  skHalf vbA [0] ++ skHalf vbB [0] ++ skHalf vbS [0] ++ skHalf vbD [0] ++ skHalf vbM [0] ++
    skHalf vbW [0] ++ skHalf vbL [0] ++ skHalf vbE [0]

-- the two tests of Honest/Law/ToySk.lean, at the six lists
#guard skFits Ky₁ && skFits Ky₂ && skFits Ky₃ && skFits Kv₁ && skFits Kv₂ && skFits Kv₃
#guard inTimeFrom [] Ky₁ && inTimeFrom [] Ky₂ && inTimeFrom [] Ky₃
#guard inTimeFrom [] Kv₁ && inTimeFrom [] Kv₂ && inTimeFrom [] Kv₃
-- a list that fails the second: the teller's rounds without the round that sends the tree
#guard !inTimeFrom [] (skHalf tellB [0, 0])

theorem fits_Ky : skFits Ky₁ = true ∧ skFits Ky₂ = true ∧ skFits Ky₃ = true :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
theorem fits_Kv : skFits Kv₁ = true ∧ skFits Kv₂ = true ∧ skFits Kv₃ = true :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
theorem inTime_Ky :
    inTimeFrom [] Ky₁ = true ∧ inTimeFrom [] Ky₂ = true ∧ inTimeFrom [] Ky₃ = true :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
theorem inTime_Kv :
    inTimeFrom [] Kv₁ = true ∧ inTimeFrom [] Kv₂ = true ∧ inTimeFrom [] Kv₃ = true :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-! ## 2 `ready` returns -/

/-- **At the first toy example**: at every input of `RelY` and at all coins. -/
theorem ready_row (w₀ : Wit₀) (rc : UInt64) (x : Nat) (k : Coins By) (h : RelY w₀ rc x) :
    ∃ R, ready Fy By (Gy.prover Py) w₀ rc x k = .ok R ∧ R.first.map sk = Ky₁ ∧
      R.shared.map sk = Ky₂ ∧ R.second.map sk = Ky₃ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.2
  have hin : (Gy.prover Py).inRange w₀ = true := bne_iff_ne.2 h.1
  have hT : readyTests Fy By (Gy.prover Py) w₀ = .ok () := by
    unfold readyTests
    rw [hin]
    with_unfolding_all rfl
  unfold ready
  rw [hT]
  exact ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl⟩

/-- **At the second toy example**: the same. -/
theorem ready_rowV (w₀ : Wit₀) (rc : UInt64) (x : Nat) (k : Coins Bv) (h : RelY w₀ rc x) :
    ∃ R, ready Fv Bv Pv w₀ rc x k = .ok R ∧ R.first.map sk = Kv₁ ∧ R.shared.map sk = Kv₂ ∧
      R.second.map sk = Kv₃ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.2
  have hin : Pv.inRange w₀ = true := bne_iff_ne.2 h.1
  have hT : readyTests Fv Bv Pv w₀ = .ok () := by
    unfold readyTests
    rw [hin]
    with_unfolding_all rfl
  unfold ready
  rw [hT]
  exact ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl⟩

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.fits_Ky
#print axioms ProofFile.Honest.Toy.fits_Kv
#print axioms ProofFile.Honest.Toy.inTime_Ky
#print axioms ProofFile.Honest.Toy.inTime_Kv
#print axioms ProofFile.Honest.Toy.ready_row
#print axioms ProofFile.Honest.Toy.ready_rowV
