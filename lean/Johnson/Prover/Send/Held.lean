-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Send/Held.lean: the held words of Johnson/Prover/Send/Core.lean, BY INDEX. Statements
and proofs; each is an unfolding.

  held_old       at a number that is not the place's: the words as they were
  held_new       at the number first + k, k below the number of the place's messages: message k's
                 tables
  word_main, word_mask   entry (row r, place j), r a real row, stands at r + j * 2 ^ (clog rows)
  word_main_beyond, word_mask_beyond   0 at an index whose row is beyond the real ones
  clog_eq        K1's clog is the program's ceilLog2
  padded_new     so at a statement that has the place's shapes at the new numbers, the words are 0
                 on the rows beyond the real ones THERE (the clause of Padded,
                 Johnson/Desc/Means/Says.lean, at these numbers)

held reads w, first, P and V alone: no round, no record.
Not shown here: anything on a decision, a row or a column. Nothing on what any entry discloses or
does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Core
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc

theorem held_old (w : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows) (o : ℕ) (part : Part)
    (i : ℕ) (h : ¬ (first ≤ o ∧ o < first + P.sent.size)) :
    held w first P V o part i = w o part i :=
  if_neg h

theorem held_new (w : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows) (k : ℕ)
    (hk : k < P.sent.size) (part : Part) (i : ℕ) :
    held w first P V (first + k) part i = (V k).word (shapeAt P k) part i := by
  unfold held
  rw [if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩, Nat.add_sub_cancel_left]

theorem clog_eq (n : ℕ) : K1.clog n = ceilLog2 n := rfl

theorem split_index (r j n : ℕ) (hr : r < n) :
    (r + j * 2 ^ K1.clog n) % 2 ^ K1.clog n = r ∧ (r + j * 2 ^ K1.clog n) / 2 ^ K1.clog n = j := by
  have h2 : r < 2 ^ K1.clog n := lt_of_lt_of_le hr (le_two_pow_ceilLog2 n)
  have hp : 0 < 2 ^ K1.clog n := Nat.pos_of_ne_zero (by positivity)
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  · rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h2, Nat.zero_add]

theorem word_main (R : Rows) (s : OracleShape) (r j : ℕ) (hr : r < s.mainRows) :
    R.word s .main (r + j * 2 ^ K1.clog s.mainRows) = R.main (s.mainDeg == 3) r j := by
  show (if _ then _ else _) = _
  rw [(split_index r j s.mainRows hr).1, (split_index r j s.mainRows hr).2, if_pos hr]

theorem word_mask (R : Rows) (s : OracleShape) (r j : ℕ) (hr : r < s.maskRows) :
    R.word s .mask (r + j * 2 ^ K1.clog s.maskRows) = R.mask r j := by
  show (if _ then _ else _) = _
  rw [(split_index r j s.maskRows hr).1, (split_index r j s.maskRows hr).2, if_pos hr]

theorem word_main_beyond (R : Rows) (s : OracleShape) (i : ℕ)
    (h : s.mainRows ≤ i % 2 ^ K1.clog s.mainRows) : R.word s .main i = 0 :=
  if_neg (Nat.not_lt.2 h)

theorem word_mask_beyond (R : Rows) (s : OracleShape) (i : ℕ)
    (h : s.maskRows ≤ i % 2 ^ K1.clog s.maskRows) : R.word s .mask i = 0 :=
  if_neg (Nat.not_lt.2 h)

/-- Padded's clause at the new numbers. -/
theorem padded_new (w : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows) (S : Statement) (k : ℕ)
    (hk : k < P.sent.size) (x : OnBytes.Oracle) (hx : S.oracles[first + k]? = some x)
    (hs : x.shape = shapeAt P k) (part : Part) (i : ℕ)
    (h : realRows S (first + k) part ≤ i % 2 ^ S.rowBits (first + k) part) :
    held w first P V (first + k) part i = 0 := by
  rw [held_new w first P V k hk]
  unfold realRows at h
  unfold Statement.rowBits at h
  rw [hx] at h
  simp only [hs] at h
  cases part
  · exact word_main_beyond _ _ _ h
  · exact word_mask_beyond _ _ _ h

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.held_old
#print axioms Johnson.Prover.Send.held_new
#print axioms Johnson.Prover.Send.clog_eq
#print axioms Johnson.Prover.Send.split_index
#print axioms Johnson.Prover.Send.word_main
#print axioms Johnson.Prover.Send.word_mask
#print axioms Johnson.Prover.Send.word_main_beyond
#print axioms Johnson.Prover.Send.word_mask_beyond
#print axioms Johnson.Prover.Send.padded_new
