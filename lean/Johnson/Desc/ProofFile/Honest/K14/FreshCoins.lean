-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshCoins.lean: coins of the frame's type Cs (Honest/Frame.lean),
all of the extension field, N0 + (n + 1) + r of them, cut in four: the first N0 · the next n · one
more · the last r. No part occurs here. Honest/K14/FreshRows.lean (takes_omega, sp_mask_coin,
sp_tail_coin) shows that the part at "send o_omega" takes its coins in this order, where the shape
splits and meets SpShape: o_omega's coins; the n entries of o_sp's mask row that are no pad; the pad
of o_sp's out-of-domain (OOD) sample; that row's random tail.

  coinsFour       the bijection: coins to ((the last r, the one, the n), the first N0)
  coin_word, coin_read   the coin number j as the program's element, as a part reads it off the list
                  of its coins; and that element read in the field: the coin
  eAt_four        what the frame's eAt returns at the number N0 + kappa: entry kappa of the n
  cut_four, words_four   two lists of coins with the same first N0 have the same cut of the first
                  N0, and a part reads the same elements off both below N0

What is not claimed. Nothing on how coins are sampled. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.ProofFile.Honest.Sum
import OnBytes.Slice.BlkRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE)
open OnBytes.Slice (rdE rdE_val readE_ofTriple toE_ofE ofE)

/-- **The coins as a product**: ((the last r, the one in front of them, the n in front of that), the
first N0). -/
def coinsFour (N0 n r : Nat) {d : Due} (hf : d.f = 0) (he : d.e = N0 + (n + 1) + r) :
    Cs d ≃ ((Fin r → Cb.Gl.E) × Cb.Gl.E × (Fin n → Cb.Gl.E)) × (Fin N0 → Cb.Gl.E) where
  toFun c :=
    ((fun q => c.e ⟨N0 + (n + 1) + q.1, by have := q.2; omega⟩, c.e ⟨N0 + n, by omega⟩,
      fun i => c.e ⟨N0 + i.1, by have := i.2; omega⟩), fun i => c.e ⟨i.1, by have := i.2; omega⟩)
  invFun x :=
    ⟨fun i => absurd i.2 (by omega), fun j =>
      if h₁ : j.1 < N0 then x.2 ⟨j.1, h₁⟩
      else if h₂ : j.1 < N0 + n then x.1.2.2 ⟨j.1 - N0, by omega⟩
      else if _h₃ : j.1 < N0 + (n + 1) then x.1.2.1
      else x.1.1 ⟨j.1 - (N0 + (n + 1)), by have := j.2; omega⟩⟩
  left_inv c := Cs.ext' (fun i => absurd i.2 (by omega)) fun j => by
    dsimp only
    split_ifs with h₁ h₂ h₃
    · rfl
    · exact congrArg c.e (Fin.ext (by show N0 + (j.1 - N0) = j.1; omega))
    · exact congrArg c.e (Fin.ext (by show N0 + n = j.1; omega))
    · exact congrArg c.e (Fin.ext (by
        show N0 + (n + 1) + (j.1 - (N0 + (n + 1))) = j.1
        omega))
  right_inv x := by
    refine Prod.ext (Prod.ext (funext fun q => ?_) (Prod.ext ?_ (funext fun i => ?_)))
      (funext fun i => ?_)
    · dsimp only
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      exact congrArg x.1.1 (Fin.ext (by show N0 + (n + 1) + q.1 - (N0 + (n + 1)) = q.1; omega))
    · dsimp only
      rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    · have := i.2
      dsimp only
      rw [dif_neg (by omega), dif_pos (by omega)]
      exact congrArg x.1.2.2 (Fin.ext (by show N0 + i.1 - N0 = i.1; omega))
    · dsimp only
      rw [dif_pos i.2]

/-- The coin number j, as a part reads it off the list of its coins. -/
theorem coin_word {d : Due} (c : Cs d) (j : Nat) (h : j < d.e) :
    (coinsE c).toArray.getD j zeroE = E.ofTriple (ofE (c.e ⟨j, h⟩)) := by
  unfold coinsE
  simp [Array.getD_eq_getD_getElem?, h]

/-- The element that a part reads off the list of its coins at the number j, read in the field, is
the coin number j. -/
theorem coin_read {d : Due} (c : Cs d) (j : Nat) (h : j < d.e) :
    rdE.val ((coinsE c).toArray.getD j zeroE) = c.e ⟨j, h⟩ := by
  rw [coin_word c j h, rdE_val, readE_ofTriple, toE_ofE]

/-- The coin number N0 + kappa, as the frame's eAt returns it: entry kappa of the n. -/
theorem eAt_four (N0 n r : Nat) {d : Due} (hf : d.f = 0) (he : d.e = N0 + (n + 1) + r) (c : Cs d)
    (kappa : Fin n) : c.eAt (N0 + kappa.1) = .ok ((coinsFour N0 n r hf he c).1.2.2 kappa) := by
  unfold Cs.eAt
  rw [dif_pos (by have := kappa.2; omega)]
  rfl

/-- Coins with the same first N0 have the same cut of the first N0. -/
theorem cut_four (N0 n r : Nat) {d : Due} (hf : d.f = 0) (he : d.e = N0 + (n + 1) + r)
    (c c' : Cs d) (h : (coinsFour N0 n r hf he c).2 = (coinsFour N0 n r hf he c').2) :
    c.cut ⟨0, 0⟩ ⟨0, N0⟩ = c'.cut ⟨0, 0⟩ ⟨0, N0⟩ := by
  have hc : (⟨0, 0⟩ : Due).f + (⟨0, N0⟩ : Due).f ≤ d.f ∧
      (⟨0, 0⟩ : Due).e + (⟨0, N0⟩ : Due).e ≤ d.e :=
    ⟨Nat.zero_le _, by show 0 + N0 ≤ d.e; omega⟩
  unfold Cs.cut
  rw [dif_pos hc, dif_pos hc]
  refine congrArg some (Cs.ext' (fun i => i.elim0) fun i => ?_)
  have h1 : c.e ⟨i.1, by have := i.2; show i.1 < d.e; have h2 : i.1 < N0 := i.2; omega⟩ =
      c'.e ⟨i.1, by have h2 : i.1 < N0 := i.2; omega⟩ := congrFun h ⟨i.1, i.2⟩
  have e1 : ∀ hlt : 0 + i.1 < d.e, (⟨0 + i.1, hlt⟩ : Fin d.e) =
      ⟨i.1, by have h2 : i.1 < N0 := i.2; omega⟩ := fun _ => Fin.ext (Nat.zero_add _)
  show c.e ⟨0 + i.1, _⟩ = c'.e ⟨0 + i.1, _⟩
  rw [e1]
  exact h1

/-- Coins with the same first N0: a part reads the same elements off both lists below N0. -/
theorem words_four (N0 n r : Nat) {d : Due} (hf : d.f = 0) (he : d.e = N0 + (n + 1) + r)
    (c c' : Cs d) (h : (coinsFour N0 n r hf he c).2 = (coinsFour N0 n r hf he c').2) :
    ∀ i, i < N0 → (coinsE c).toArray.getD i zeroE = (coinsE c').toArray.getD i zeroE :=
  fun i hi => by
    rw [coin_word c i (by omega), coin_word c' i (by omega)]
    exact congrArg (fun x => E.ofTriple (ofE x)) (congrFun h ⟨i, hi⟩)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.eAt_four
#print axioms ProofFile.Honest.K14.cut_four
#print axioms ProofFile.Honest.K14.words_four
#print axioms ProofFile.Honest.K14.coinsFour
#print axioms ProofFile.Honest.K14.coin_word
#print axioms ProofFile.Honest.K14.coin_read
