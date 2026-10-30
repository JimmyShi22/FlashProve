-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/MuCoded.lean: the scalar at "SPLIT": the one that is made with code
(Johnson/Desc/K14/Honest/Coded.lean: muAtE), read into the library's field, is the scalar of the
honest tables (Johnson/Desc/K14/Honest/ChainHolds.lean: muRun).

Main names:
  mu_coded            **the equation.** Asked: the shared point has its planned number of
                      coordinates; the rows held are the coded rows, read, at the places that hold
                      the matrix, and at no other; the entry number 0 of o_sp's mask row, as held,
                      is the coded random value, read

How. The readings of the coded vectors (Johnson/Desc/K14/Honest/CodedReads.lean) and of the rows'
weights (Johnson/Desc/K14/Honest/RowsHold.lean: wOf_eq). The sums run over the matrix's places
alone.

What is not claimed. That a prover sends that scalar. Nothing on the verifier's decision, on
soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.ChainHolds
import Johnson.Desc.K14.Honest.CodedReads
import Johnson.Desc.K14.Honest.RowsHold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (rdE)

/-- **The scalar made with code reads as the scalar of the honest tables.** hpt: the shared point
has its planned number of coordinates. hRw: the rows held are the coded rows, read, AT THE PLACES
THAT HOLD THE MATRIX: no other place is read. hk: the entry number 0 of o_sp's mask row, as it is
held, is the coded random value, read. -/
theorem mu_coded (P : P14) (d0 : St) (r1 r7 : Fmt.RoundView) (H : Inputs) (RwE : Nat → Nat → E) (kE : E)
    (hpt : (drawn r1).length = P.par.S.kCol)
    (hRw : ∀ r < P.par.S.fold.index.rows, ∀ k < P.par.S.matrixRows * 2 ^ P.par.S.kLo,
      H.Rw r k = rdE.val (RwE r k))
    (hk : kappaOf H.cSp P.par.S.sharedSplit.maskRows 0 = rdE.val kE) :
    rdE.val (muAtE P.par.S (drawn r1) (drawn r7) RwE kE) = muRun P d0 r1 r7 H := by
  have hg : (gamma P.par.S
      (locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1)).length =
      P.par.S.fold.index.v := by
    show ((drawn r1).drop P.par.S.kLo).length = _
    rw [List.length_drop, hpt]
    unfold LinShape.kCol
    omega
  have hw := wOf_eq rdE P.par.S _ hg
  rw [val_muAtE]
  unfold muRun muSent muHon
  rw [hk]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  congr 1
  show rdE.val (omegaAtE P.par.S (drawn r1) RwE j) = _
  rw [val_omegaAtE]
  unfold omegaHon
  rw [if_pos hj', if_pos hj']
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  congr 1
  show rdE.val (uAtE P.par.S (drawn r1) RwE (t + 2 ^ P.par.S.kLo * j)) = _
  rw [val_uAtE]
  unfold uHon
  have hlt : t + 2 ^ P.par.S.kLo * j < P.par.S.matrixRows * 2 ^ P.par.S.kLo := by
    calc t + 2 ^ P.par.S.kLo * j < 2 ^ P.par.S.kLo + 2 ^ P.par.S.kLo * j := by omega
      _ = (j + 1) * 2 ^ P.par.S.kLo := by ring
      _ ≤ P.par.S.matrixRows * 2 ^ P.par.S.kLo := Nat.mul_le_mul_right _ hj'
  by_cases hc : t + 2 ^ P.par.S.kLo * j < P.par.S.fold.entries
  · rw [if_pos hc, if_pos hc]
    unfold foldRows
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    rw [hRw r hr' _ hlt]
    congr 1
    exact (hw r hr').symm
  · rw [if_neg hc, if_neg hc]

end Desc.K14.Honest

#print axioms Desc.K14.Honest.mu_coded
