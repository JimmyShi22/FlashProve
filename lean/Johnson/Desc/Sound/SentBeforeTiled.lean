-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SentBeforeTiled.lean: **SentBefore (Johnson/Desc/Sound/LedgerRides.lean: the four comparisons of numbers for a message at a block) FROM ONE COMPARISON AND "THE STRETCHES TILE THE CHAIN".** Statements and proofs; counting alone.
  hiAt_get      at the place of a piece of the row, hiAt is that piece's base.
  hiAt_step     along a tiled row hiAt does not fall from a place to the next.   hiAt_le: nor from a place to any later one.
  **sentBefore_of**   Tiled f l · N.lo ≤ the tenant's tree · the tenant's tree lies below hiAt j f l at SOME place j ≤ k · x is the row's piece number k ⟹ SentBefore N f l k x m.
  sentBefore_base     the same with "below the base of the row's piece number j".
What for: nine_paid's | ten_paid's sb and word_seat's window (SeamWordSeats.lean) from the three comparisons tU | tO | tS ("the tenant's tree lies below the base of the piece behind its sending").
Limits. These three comparisons stay premises. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.LedgerRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Shared

section
variable {S Cl W : Type} {C : CK} {F : Frame}

/-- At the place of a piece of the row, hiAt is that piece's base. -/
theorem hiAt_get : ∀ (k : ℕ) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (x : Piece C F S Cl W), (p :: l)[k]? = some x → hiAt k p l = x.base
  | 0, p, _, x, h => by
    obtain rfl : p = x := by simpa using h
    rfl
  | k + 1, p, [], x, h => by simp at h
  | k + 1, p, q :: l, x, h => by
    show hiAt k q l = x.base
    exact hiAt_get k q l x (by simpa using h)

/-- Along a tiled row hiAt does not fall from a place to the next. -/
theorem hiAt_step : ∀ (k : ℕ) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)), Tiled p l →
    hiAt k p l ≤ hiAt (k + 1) p l
  | 0, p, [], _ => Nat.le_add_right _ _
  | 0, p, q :: l, h => by
    show p.base ≤ q.base
    rw [h.2.2.2.1]
    exact Nat.le_add_right _ _
  | k + 1, p, [], _ => Nat.le_refl _
  | k + 1, p, q :: l, h => hiAt_step k q l h.2.2.2.2

theorem hiAt_le (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (h : Tiled p l) (j : ℕ) :
    ∀ k, j ≤ k → hiAt j p l ≤ hiAt k p l := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ k _ ih => exact Nat.le_trans ih (hiAt_step k p l h)

end

section
variable {P₁ S₂ Cl Cells Tok : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (f : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
  (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))

/-- **The four comparisons from one.** -/
theorem sentBefore_of (hT : Tiled f l) (m : Msg2) (hlo : N.lo ≤ (N.tenant m).1) (j k : ℕ)
    (hjk : j ≤ k) (hj : (N.tenant m).1 < hiAt j f l)
    (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (hx : (f :: l)[k]? = some x) :
    SentBefore N f l k x m :=
  ⟨hlo, Nat.lt_of_lt_of_le hj (hiAt_le f l hT j k hjk),
    Nat.lt_of_lt_of_le hj (hiAt_le f l hT j (k + 1) (by omega)),
    by rw [← hiAt_get k f l x hx]; exact Nat.lt_of_lt_of_le hj (hiAt_le f l hT j k hjk)⟩

/-- The same, from "below the base of the row's piece number j". -/
theorem sentBefore_base (hT : Tiled f l) (m : Msg2) (hlo : N.lo ≤ (N.tenant m).1) (j k : ℕ)
    (hjk : j ≤ k) (y : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (hy : (f :: l)[j]? = some y)
    (hj : (N.tenant m).1 < y.base)
    (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (hx : (f :: l)[k]? = some x) :
    SentBefore N f l k x m :=
  sentBefore_of N f l hT m hlo j k hjk (by rw [hiAt_get j f l y hy]; exact hj) x hx

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.hiAt_get
#print axioms VerifiableInference.Desc.Sound.hiAt_le
#print axioms VerifiableInference.Desc.Sound.sentBefore_of
#print axioms VerifiableInference.Desc.Sound.sentBefore_base
