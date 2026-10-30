-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/DrawPort.lean: the entry of the drawn matrix that the Lean verifier reads, out
of the words that the chain gives, is the value of the typed challenge's coefficient.

The format makes the list of columns * tau matrix entries from words of the chain (Fmt.tritsOf,
Fmt/Rules6.lean). The verifier keeps that list as an array and reads it at the index
(first + c) * tau + u, with 0 where the array ends (foldColumn, OnBytes/Model/Tail.lean).
OnBytes/Tie/Pv/Tail/Draw.lean has the bijection between the typed challenge Dr s and lists of
coefficients by that index. Here both are put together. Definitions, statements and proofs.

Main names:
  `bitsAt ws n`: the n coefficients that the words ws hold: number j is made of bits 2 (j % 32) and
    2 (j % 32) + 1 of word j / 32.
    `bitsAt_eq`: they are the pairs of bits as Run/DrawPage.lean reads them (Run.bitsOf).
  `drawnOf s ws`: the typed challenge that the words stand for.
  `entry_of_words`: if there are words enough, the format's list, as an array, read at the
    verifier's index with the fallback 0, is the value of drawnOf's coefficient at (μ, u, c).
  `drawnOf_apply`: that coefficient is the one that the words hold at the verifier's index.

Limits: nothing here speaks of a run of the verifier. That the array which a sub-proof keeps is the
format's list of the round's words is not proved here. The road is: drawMatrixF
(OnBytes/Model/Tail.lean), SubM.trits (OnBytes/Model/Hide.lean), trTrits and closeAs
(OnBytes/Model/Rounds.lean), Blk.close (OnBytes/Iop/Ground.lean); its last step, that the record of
what a round drew holds the list of Fmt.drawTrits, has not been read for this file. Nothing is said
on the law of the words: that every typed challenge comes from equally many lists of
(columns * tau + 31) / 32 words is owed by whoever joins the round to the chain.
-/
import Run.DrawPage
import OnBytes.Tie.Pv.Tail.Draw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Cb.Pv.Tail

/-- The n coefficients that a list of words holds, 32 to a word. -/
def bitsAt (ws : List UInt64) (n : ℕ) : Fin n → Prob.Coef := fun j =>
  ((ws.getD (j.val / 32) 0).toNat.testBit (2 * (j.val % 32)),
    (ws.getD (j.val / 32) 0).toNat.testBit (2 * (j.val % 32) + 1))

/-- They are the pairs of bits as the page on draws reads them. -/
theorem bitsAt_eq (ws : List UInt64) (n : ℕ) (j : Fin n) :
    bitsAt ws n j = Run.bitsOf n (fun i => ws.getD i.val 0) j := rfl

/-- The typed challenge that the words stand for. -/
def drawnOf (s : Size) (ws : List UInt64) : Dr s :=
  (flatPort s).symm (bitsAt ws (s.columns * s.tau))

/-- The coefficient of (μ, u, c) is the one at the verifier's index. -/
theorem drawnOf_apply (s : Size) (ws : List UInt64) (μ : Fin s.NM) (c : Fin (s.k μ))
    (u : Fin s.tau) :
    drawnOf s ws μ u c = bitsAt ws (s.columns * s.tau) (portIndex s μ c u) := by
  rw [← flatPort_apply s (drawnOf s ws) μ c u]
  show flatPort s ((flatPort s).symm _) _ = _
  rw [Equiv.apply_symm_apply]

/-- The entry that the verifier reads, out of the words. -/
theorem entry_of_words (s : Size) (ws : List UInt64)
    (hl : (s.columns * s.tau + 31) / 32 ≤ ws.length) (μ : Fin s.NM) (c : Fin (s.k μ))
    (u : Fin s.tau) :
    (Fmt.tritsOf ws (s.columns * s.tau)).toArray.getD ((firstCol s μ + c.val) * s.tau + u.val) 0 =
      (drawnOf s ws μ u c).val := by
  rw [← portIndex_val, drawnOf_apply]
  have hj := (portIndex s μ c u).isLt
  have h := tritsOf_get ws (s.columns * s.tau) (portIndex s μ c u).val hj (by omega)
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, h, Option.getD_some]
  rfl

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.bitsAt_eq
#print axioms OnBytes.Tie.Pv.Tail.drawnOf_apply
#print axioms OnBytes.Tie.Pv.Tail.entry_of_words
