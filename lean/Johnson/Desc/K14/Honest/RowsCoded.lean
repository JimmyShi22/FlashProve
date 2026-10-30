-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/RowsCoded.lean: the two vectors that the two sendings of the batch's shared
rounds carry, made with code (uAtE, omegaAtE: Johnson/Desc/K14/Honest/Coded.lean), READ as the
honest tables' vectors at a run's first round (Johnson/Desc/K14/Honest/ChainHolds.lean: rowsU,
rowsO).

  u_coded         the folded row: at every place
  omega_coded     omega_col: at every place

What is assumed. hpt: the shared point has its planned number of coordinates. hRw: the rows held are
the coded rows, read, at every real row and every place.
What is not claimed. Nothing on a verifier's decision, on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.ChainHolds
import Johnson.Desc.K14.Honest.CodedReads
import Johnson.Desc.K14.Honest.RowsHold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (rdE)

/-- **The folded row made with code reads as the honest tables' folded row.** -/
theorem u_coded (P : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) (RwE : Nat → Nat → E)
    (hpt : (drawn r1).length = P.par.S.kCol)
    (hRw : ∀ r < P.par.S.fold.index.rows, ∀ k, H.Rw r k = rdE.val (RwE r k)) (n : Nat) :
    rdE.val (uAtE P.par.S (drawn r1) RwE n) = uHon P.par.S.fold (wRun P d0 r1) H.Rw n := by
  have hg : (gamma P.par.S
      (locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1)).length =
      P.par.S.fold.index.v := by
    show ((drawn r1).drop P.par.S.kLo).length = _
    rw [List.length_drop, hpt]
    unfold LinShape.kCol
    omega
  have hw := wOf_eq rdE P.par.S _ hg
  rw [val_uAtE]
  unfold uHon
  by_cases hc : n < P.par.S.fold.entries
  · rw [if_pos hc, if_pos hc]
    unfold foldRows
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    rw [hRw r hr' n]
    congr 1
    exact (hw r hr').symm
  · rw [if_neg hc, if_neg hc]

/-- **omega_col made with code reads as the honest tables' omega_col.** -/
theorem omega_coded (P : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) (RwE : Nat → Nat → E)
    (hpt : (drawn r1).length = P.par.S.kCol)
    (hRw : ∀ r < P.par.S.fold.index.rows, ∀ k, H.Rw r k = rdE.val (RwE r k)) (j : Nat) :
    rdE.val (omegaAtE P.par.S (drawn r1) RwE j) =
      omegaHon P.par.S (psiLoRun P r1) (uHon P.par.S.fold (wRun P d0 r1) H.Rw) j := by
  rw [val_omegaAtE]
  have e : (fun k => rdE.val (uAtE P.par.S (drawn r1) RwE k)) =
      uHon P.par.S.fold (wRun P d0 r1) H.Rw := funext fun k => u_coded P d0 r1 H RwE hpt hRw k
  rw [e]
  rfl

end Desc.K14.Honest

#print axioms Desc.K14.Honest.u_coded
#print axioms Desc.K14.Honest.omega_coded
