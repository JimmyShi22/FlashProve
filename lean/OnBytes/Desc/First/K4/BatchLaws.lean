-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/BatchLaws.lean: a batching round of the layers' own rounds returns the powers
of ONE drawn element.

The text of K4 (OnBytes/Desc/First/K4/Hear.lean) batches rows three times (the nine sums of a norm;
the row products; the stacked panels) through the engine's `batch`, which Plain.lean fills with the
plain function `Fl.batch` (OnBytes/K/Kc/Flat.lean). Its docstring says that it returns the
powers of the drawn element. Here that is a theorem.

  `batch_powers`: where `Fl.batch rows` returns gp, there is one element x with
      gp = Model.powers x rows; the ledger is as it was.
  `powers_val`: read in a ring, member s of Model.powers x n is the reading of x to the power s, for
      s below n.
  `batch_val`: the two together.

Limits. Nothing on how x is drawn, and nothing on soundness. If Fl.batch's text turns, this law is
owed anew.
-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.K.Kc

theorem batch_powers {rows : Nat} {F F' : Fork} {t t' : Tape} {gp : Array E}
    (h : Fl.batch rows F t = some (gp, F', t')) : ∃ x, gp = Model.powers x rows ∧ F' = F := by
  unfold Fl.batch Fl.onTape at h
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.mp h
  unfold Fl.batchOn at hy
  by_cases hr : (rows != 0) = true
  · rw [if_pos hr] at hy
    obtain ⟨z, _, ez⟩ := Option.map_eq_some_iff.mp hy
    refine ⟨z.1, ?_, ?_⟩
    · have e1 : y.1 = gp := congrArg (fun q : Array E × Fork × Tape => q.1) e
      rw [← e1, ← ez]
    · exact (congrArg (fun q : Array E × Fork × Tape => q.2.1) e).symm
  · rw [if_neg hr] at hy
    cases hy

variable {K : Type} [CommRing K] (ρ : Reading K)

theorem powersLoop_val (x : E) : ∀ (n : Nat) (c : E) (a : Array E) (s : Nat), s < a.size + n →
    ρ.val ((powersLoop x n c a).getD s zeroE) =
      if s < a.size then ρ.val (a.getD s zeroE) else ρ.val c * ρ.val x ^ (s - a.size)
  | 0, c, a, s, hs => by
    rw [if_pos (by omega)]
    rfl
  | n + 1, c, a, s, hs => by
    have ih := powersLoop_val x n (mulE c x) (a.push c) s (by rw [Array.size_push]; omega)
    have e : powersLoop x (n + 1) c a = powersLoop x n (mulE c x) (a.push c) := rfl
    rw [e, ih, Array.size_push]
    by_cases h1 : s < a.size
    · rw [if_pos (by omega), if_pos h1]
      simp [Array.getD, Array.getElem_push, h1, Nat.lt_succ_of_lt h1]
    · by_cases h2 : s = a.size
      · subst h2
        rw [if_pos (by omega), if_neg h1]
        simp [Array.getD]
      · rw [if_neg (by omega), if_neg h1, ρ.mul]
        have e2 : s - a.size = (s - (a.size + 1)) + 1 := by omega
        rw [e2, pow_succ]
        ring

theorem powers_val (x : E) {n s : Nat} (hs : s < n) :
    ρ.val ((Model.powers x n).getD s zeroE) = ρ.val x ^ s := by
  unfold Model.powers
  rw [powersLoop_val ρ x n oneE _ s (by simpa using hs)]
  simp [ρ.one]

theorem batch_val {rows : Nat} {F F' : Fork} {t t' : Tape} {gp : Array E}
    (h : Fl.batch rows F t = some (gp, F', t')) :
    ∃ x, ∀ s, s < rows → ρ.val (gp.getD s zeroE) = ρ.val x ^ s := by
  obtain ⟨x, e, _⟩ := batch_powers h
  exact ⟨x, fun s hs => by rw [e, powers_val ρ x hs]⟩

#print axioms batch_powers
#print axioms powers_val
#print axioms batch_val

end OnBytes.Desc.First.K4
