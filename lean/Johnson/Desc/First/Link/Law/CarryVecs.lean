-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CarryVecs.lean: THE CARRIED CLAIM's VECTOR, AS THE CLOSING's FILES
WRITE IT (`outVec`, Johnson/Desc/First/Close/Law/Border.lean) AND AS THE CODE SWITCH's FILES
WRITE IT (`vecOf`, Johnson/Top/H0/K2Hands/ClaimJoin.lean), ARE ONE, where the closing's names of
the kept slots are the switch's frame's. A theorem.

  `outVec_eq_vecOf`: **N.orc q = (pl q).old · N.idx q x = row q + 2 ^ (pl q).rowBits * x ⊢
    outVec N out = vecOf R.s R.Kp out row pl**, general in the group R and the claim out. On the
    main row and on the two mask rows the two are one text; on a kept slot both sum, over the
    claim's kept forms on that slot's oracle message, the form's entry at that index.
Limits. That the closing's names N, which stand in front of all statements, are a running frame's
kept places' is not said. Nothing on the words. Nothing on soundness.
-/
import Johnson.Desc.First.Close.Law.Border
import Johnson.Top.H0.K2Hands.ClaimJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Johnson.Top.H
open VerifiableInference.Desc.First.Close (SlotNames outVec)
open VerifiableInference.Desc.First.K2Hands (vecOf oldVec)

theorem outVec_eq_vecOf {S : Sig GE} (R : RowsK S) (N : SlotNames R) (out : SingleRows)
    (row : R.Kp → ℕ) (pl : R.Kp → KeptPlace) (hO : ∀ q, N.orc q = (pl q).old)
    (hI : ∀ q x, N.idx q x = row q + 2 ^ (pl q).rowBits * x.val) :
    outVec N out = vecOf R.s R.Kp out row pl := by
  funext j
  rcases j with ⟨o, x⟩ | x | x
  · cases o with
    | none => rfl
    | some q =>
      show (out.kept.toList.map fun kf =>
          if kf.oracle = N.orc q then readE (kf.c.entry (N.idx q x)) else 0).sum =
        (out.kept.toList.map fun f =>
          if (pl q).old = f.oracle then formAt f.c (row q + 2 ^ (pl q).rowBits * x.val) else 0).sum
      rw [hO, hI]
      congr 1
      refine List.map_congr_left fun f _ => ?_
      by_cases h : f.oracle = (pl q).old
      · rw [if_pos h, if_pos h.symm]
        rfl
      · rw [if_neg h, if_neg fun e => h e.symm]
  · rfl
  · rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.outVec_eq_vecOf
