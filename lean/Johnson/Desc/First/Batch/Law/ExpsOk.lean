-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ExpsOk.lean
(kind K9's soundness lemma): THEOREM: THE TEST ON THE
EXPONENTS (hok of k9_row_moves: the exponents of chi in the moves' terms differ from each other and
are at most d) PAID DOWN TO A DISCIPLINE OF EACH MOVE AND TWO NUMBERS OF THE PLAN.
THE WEIGHTS (Johnson/Desc/Claim.lean): claim number c gets chi^c; a tie or a read of the smallness
test takes a number like any claim, but its weight, and the powers inside its runs, are chi^(n + e),
n the plan's number of claims, e the number of one of its equations.
  InWin n len plan t tie e   the exponent e lies in the move's OWN WINDOW of numbers
                  [n, n + len), or in its WINDOW OF EQUATIONS [plan + t, plan + t + tie).
  DiscFrom        THE DISCIPLINE along a row of moves, each with its number "tie" of equations: if n
                  claims and t equations stand before: the move's exponents differ from each other
                  and lie in its two windows; the next move's windows begin where these end.
  disc_terms      under the discipline, if all the moves' claims are at most the plan's number: the
                  exponents of the whole row differ from each other and lie in the joined windows.
  termsOk_of_disc **TermsOk (termsOf p y ms 0) (plan + ties - 1)**: ties: all equations together.
So d := plan + ties - 1. THE DOOR's OWN TEST "K9.rows-counted" asks that the rows which the draw's
entry counts are the claims added and the indices that the smallness test's equations take
(Law/Door.lean: door_parts: owed = some (nClaim + laid)): so at a run that the door accepts
d = rows - 1, IF ties is what the smallness test's record says is laid: not shown here: ONE LEMMA
IS OWED that ties door_parts' "nClaim + laid" to "plan + ties": it is the number that Law/AtCap.lean
prices (d ≤ 2^60). (At no move and plan = ties = 0 the bound reads 0 - 1 = 0: idle.)
WHO PAYS THE DISCIPLINE: each run's kind's files. For a run of plain claims tie = 0 and the
exponents are the claims' own numbers.

-/
import Johnson.Desc.First.Batch.Law.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model

variable {T P K : Type}

/-- The exponent lies in the window of numbers or in the window of equations. -/
def InWin (n len plan t tie e : ℕ) : Prop :=
  (n ≤ e ∧ e < n + len) ∨ (plan + t ≤ e ∧ e < plan + t + tie)

/-- The discipline along a row of moves. -/
def DiscFrom (p : P) (y : Bound K) (plan : ℕ) : List (Termed T P K × ℕ) → ℕ → ℕ → Prop
  | [], _, _ => True
  | m :: l, n, t =>
    ((m.1.tm n p y).map (·.1)).Nodup ∧
      (∀ x ∈ m.1.tm n p y, InWin n (m.1.len p) plan t m.2 x.1) ∧
      DiscFrom p y plan l (n + m.1.len p) (t + m.2)

/-- All claims of a row of moves; all its equations. -/
def lenAll (p : P) : List (Termed T P K × ℕ) → ℕ
  | [] => 0
  | m :: l => m.1.len p + lenAll p l

def tieAll : List (Termed T P K × ℕ) → ℕ
  | [] => 0
  | m :: l => m.2 + tieAll l

theorem disc_terms (p : P) (y : Bound K) (plan : ℕ) :
    ∀ (ms : List (Termed T P K × ℕ)) (n t : ℕ), DiscFrom p y plan ms n t →
      n + lenAll p ms ≤ plan →
      ((termsOf p y (ms.map (·.1)) n).map (·.1)).Nodup ∧
        ∀ x ∈ termsOf p y (ms.map (·.1)) n, InWin n (lenAll p ms) plan t (tieAll ms) x.1
  | [], _, _, _, _ => ⟨List.nodup_nil, fun _ h => (nomatch h)⟩
  | m :: l, n, t, h, hp => by
    obtain ⟨h1, h2, h3⟩ := h
    have hp' : n + m.1.len p + lenAll p l ≤ plan := by
      have : lenAll p (m :: l) = m.1.len p + lenAll p l := rfl
      omega
    obtain ⟨i1, i2⟩ := disc_terms p y plan l (n + m.1.len p) (t + m.2) h3 hp'
    have e : termsOf p y ((m :: l).map (·.1)) n =
        m.1.tm n p y ++ termsOf p y (l.map (·.1)) (n + m.1.len p) := rfl
    have eL : lenAll p (m :: l) = m.1.len p + lenAll p l := rfl
    have eT : tieAll (m :: l) = m.2 + tieAll l := rfl
    rw [e, List.map_append]
    refine ⟨List.nodup_append.2 ⟨h1, i1, ?_⟩, ?_⟩
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
      have wx := h2 x hx
      have wz := i2 z hz
      unfold InWin at wx wz
      omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · have wx := h2 x hx
        unfold InWin at wx ⊢
        omega
      · have wz := i2 x hx
        unfold InWin at wz ⊢
        omega

/-- **The test on the exponents, from the discipline and the plan's number of claims.** -/
theorem termsOk_of_disc [Field K] (p : P) (y : Bound K) (plan : ℕ)
    (ms : List (Termed T P K × ℕ)) (h : DiscFrom p y plan ms 0 0) (hp : lenAll p ms ≤ plan) :
    Desc.TermsOk K (termsOf p y (ms.map (·.1)) 0) (plan + tieAll ms - 1) := by
  obtain ⟨h1, h2⟩ := disc_terms p y plan ms 0 0 h (by omega)
  refine ⟨h1, fun x hx => ?_⟩
  have w := h2 x hx
  unfold InWin at w
  omega

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.disc_terms
#print axioms VerifiableInference.Desc.K9L.termsOk_of_disc
