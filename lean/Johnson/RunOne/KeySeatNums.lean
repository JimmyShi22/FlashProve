-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatNums.lean: THEOREMS BY THE KERNEL's EVALUATION, EACH A TEST THAT CAN FAIL. At the full size's codes of the key's chains and the shapes of its first two sampled messages (the index masks; the lookups' own message): the two premises on numbers that a reading of a committed word as the library's word asks of a shape: hm: no main row, or the main rows' code is as long as the tree · the degree of a main row is 1 or 3.
OBJECT: csKey · shIdx · shMul (Johnson/Top/H/KeyRows.lean). USER: none yet (meant: the premise hm of other files' filling at one tenant, and SeatFits' fifth and seventh clauses). With the numbers themselves, so that a reader sees which half of hm holds.
Nothing on soundness.

-/
import Johnson.RunOne.KeyMemberFull

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params Johnson.Pack
open Johnson.Top.H (csKey shIdx shMul)

theorem hmIdx : shIdx.mainRows = 0 ∨ (cMain csKey shIdx).a = aOf csKey shIdx := by decide +kernel
theorem hmMul : shMul.mainRows = 0 ∨ (cMain csKey shMul).a = aOf csKey shMul := by decide +kernel
theorem degIdx : shIdx.mainDeg = 1 ∨ shIdx.mainDeg = 3 := by decide +kernel
theorem degMul : shMul.mainDeg = 1 ∨ shMul.mainDeg = 3 := by decide +kernel

/-- The numbers: main rows · mask rows · the degree · the mask code's log-length · the tree's. At the index masks hm holds by its FIRST half (no main row). -/
theorem numsIdx : (shIdx.mainRows, shIdx.maskRows, shIdx.mainDeg, (cMask csKey shIdx).a, aOf csKey shIdx) = (0, 1, 1, 13, 13) := by decide +kernel
/-- With the main code's log-length. At the lookups' own message hm holds by its SECOND half: the main rows' code is as long as the tree. -/
theorem numsMul : (shMul.mainRows, shMul.maskRows, shMul.mainDeg, (cMain csKey shMul).a, (cMask csKey shMul).a, aOf csKey shMul) = (2, 9, 1, 22, 16, 22) := by decide +kernel
/-- The control: hm is no empty clause: at the same shape under a shorter main code (number 13: 2 ^ 19) beside a mask code of 2 ^ 20 (number 14) it fails. -/
theorem hm_not : ¬ (({ shMul with code := 13, maskCode := 14 } : OracleShape).mainRows = 0 ∨ (cMain csKey { shMul with code := 13, maskCode := 14 }).a = aOf csKey { shMul with code := 13, maskCode := 14 }) := by decide +kernel

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.hmIdx
#print axioms Johnson.RunOne.KeyLetters.hmMul
#print axioms Johnson.RunOne.KeyLetters.degIdx
#print axioms Johnson.RunOne.KeyLetters.degMul
#print axioms Johnson.RunOne.KeyLetters.numsIdx
#print axioms Johnson.RunOne.KeyLetters.numsMul
#print axioms Johnson.RunOne.KeyLetters.hm_not
