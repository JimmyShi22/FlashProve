-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FrozenReads.lean: the kind "the code switch" (K2): WHAT
`frozenLeft` (Johnson/Desc/ProofFile/Honest/K2/Closing.lean) KEEPS, FIELD BY FIELD, MESSAGES AND
TAILS, BELOW THE SIZES AT WHICH IT WAS FROZEN. Six lemmas; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

  `frozenRead_main`, `frozenRead_mainTail`  the main row
  `frozenRead_mask`, `frozenRead_maskTail`  the two mask rows
  `frozenRead_kept`, `frozenRead_keptTail`  a kept member's rows, at its real rows
How. By the text of `frozenLeft`: an array made over a range, read below its size.
Limits. Nothing beyond the sizes (there `frozenLeft` holds 0).
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K2.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes
open VerifiableInference.Desc.K2.Honest (Left)

variable (c z : Code) (kept : List OracleShape) (W : Left)

/-- The main row's message, below the code's message length. -/
theorem frozenRead_main (j : Nat) (hj : j < c.ell) : (frozenLeft c z kept W).main j = W.main j := by
  unfold frozenLeft
  simp [Array.getD, hj]

/-- The main row's tail, below the code's number of tail entries. -/
theorem frozenRead_mainTail (q : Nat) (hq : q < c.r) :
    (frozenLeft c z kept W).mainTail q = W.mainTail q := by
  unfold frozenLeft
  simp [Array.getD, hq]

/-- The two mask rows' messages. -/
theorem frozenRead_mask (r i : Nat) (hr : r < 2) (hi : i < z.ell) :
    (frozenLeft c z kept W).mask r i = W.mask r i := by
  unfold frozenLeft
  simp [Array.getD, hr, hi]

/-- The two mask rows' tails. -/
theorem frozenRead_maskTail (r q : Nat) (hr : r < 2) (hq : q < z.r) :
    (frozenLeft c z kept W).maskTail r q = W.maskTail r q := by
  unfold frozenLeft
  simp [Array.getD, hr, hq]

/-- A kept member's rows' messages, at its real rows. -/
theorem frozenRead_kept (a b j : Nat) (ha : a < kept.length) (hb : b < (kept.getD a {}).mainRows)
    (hj : j < c.ell) : ((frozenLeft c z kept W).kept a).main b j = (W.kept a).main b j := by
  rw [List.getD_eq_getElem _ _ ha] at hb
  unfold frozenLeft
  simp [Array.getD, ha, hb, hj]

/-- A kept member's rows' tails, at its real rows. -/
theorem frozenRead_keptTail (a b q : Nat) (ha : a < kept.length)
    (hb : b < (kept.getD a {}).mainRows) (hq : q < c.r) :
    ((frozenLeft c z kept W).kept a).tail b q = (W.kept a).tail b q := by
  rw [List.getD_eq_getElem _ _ ha] at hb
  unfold frozenLeft
  simp [Array.getD, ha, hb, hq]

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.frozenRead_main
#print axioms ProofFile.Honest.K2.frozenRead_mainTail
#print axioms ProofFile.Honest.K2.frozenRead_mask
#print axioms ProofFile.Honest.K2.frozenRead_maskTail
#print axioms ProofFile.Honest.K2.frozenRead_kept
#print axioms ProofFile.Honest.K2.frozenRead_keptTail
