-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontOfCarried.lean: the code switch's law: frontB2_of_fold's premise on the
carried rows (RowsLike, FrontOfFold.lean) FROM THE CLOSING's OWN LAW ON ITS OUTPUT (CarriedOk,
Johnson/Desc/First/Close/Law/CarriedRows.lean), the kept members' numbers,
the walk's fact on the two codes and the number of masks, and closed facts. A law file; no running
text imports it.

  rowsLike_of_kept      ITS PREMISES, EACH WITH ITS PAYER:
    C    CarriedOk P G S' out                     closing_carried | closeFrame_carried, off the
                                                  closing's yes
    hk   (switchKept out).toList = olds           the walk's fact on what the next switching keeps,
                                                  in numbers (kept_next |
                                                  kept_one end in this form, at the walk's frame's
                                                  carried rows)
    hcs  S'.codes = cs                            the fold's fact «codes», behind the closing
    hM   the shapes at olds in S' are the listed M's   the fold's fact «msgShapes», behind the
                                                  closing
    h1 h2 h3   out's two codes and number of masks are the written rows'   the walk's fact on
                                                  every copy of the frame
    k1   CLOSED: the written rows' count of kept rows is the sum of M's main rows at olds
    k2   CLOSED: the frame's main code has the exponent of the message length of cs's code number
         P.code
    k3   CLOSED: cs's mask code number P.maskCode is no longer than the frame's
  rowsLike_of_carried   the same with hk said of the group: G's members whose flag says "kept" are
                        olds (by CarriedOk's first field).
Limits. Nothing is paid here. S' is the statement right behind the closing. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontOfFold
import Johnson.Desc.First.Close.Law.CarriedRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.Close (Plan CarriedOk)

/-- **The carried rows are like the written rows.** -/
theorem rowsLike_of_kept {P : Plan} {G : Group} {S' : Statement} {out R₀ : SingleRows}
    {W₀ : SwitchFrame} {olds : List ℕ} {cs : Codes} {M : List OracleShape}
    (C : CarriedOk P G S' out)
    (hk : (switchKept out).toList = olds) (hcs : S'.codes = cs)
    (hM : ∀ o ∈ olds, (S'.oracles[o]?).map (·.shape) = M[o]?)
    (h1 : out.code = R₀.code) (h2 : out.maskCode = R₀.maskCode) (h3 : out.masks = R₀.masks)
    (k1 : R₀.keptRows = (olds.map fun o => ((M[o]?).map (·.mainRows)).getD 0).sum)
    (k2 : W₀.code.logEll = (cs.base.getD P.code default).logEll)
    (k3 : (cs.mask.getD P.maskCode default).ell ≤ W₀.zk.ell) : RowsLike out R₀ W₀ olds := by
  refine ⟨h1, h2, h3, ?_, hk, fun v hv => ?_, ?_, ?_⟩
  · rw [C.keptRows, hk, k1]
    refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
    rw [← hM o ho, Option.map_map]
    rfl
  · rw [C.vars v hv, hcs, k2]
  · rw [C.d0, hcs]
    exact k3
  · rw [C.d1, hcs]
    exact k3

/-- The same, with the kept members said of the group in front of the closing. -/
theorem rowsLike_of_carried {P : Plan} {G : Group} {S' : Statement} {out R₀ : SingleRows}
    {W₀ : SwitchFrame} {olds : List ℕ} {cs : Codes} {M : List OracleShape}
    (C : CarriedOk P G S' out)
    (hk : (((G.members.zip G.kept).filter (·.2)).map (·.1)).toList = olds) (hcs : S'.codes = cs)
    (hM : ∀ o ∈ olds, (S'.oracles[o]?).map (·.shape) = M[o]?)
    (h1 : out.code = R₀.code) (h2 : out.maskCode = R₀.maskCode) (h3 : out.masks = R₀.masks)
    (k1 : R₀.keptRows = (olds.map fun o => ((M[o]?).map (·.mainRows)).getD 0).sum)
    (k2 : W₀.code.logEll = (cs.base.getD P.code default).logEll)
    (k3 : (cs.mask.getD P.maskCode default).ell ≤ W₀.zk.ell) : RowsLike out R₀ W₀ olds :=
  rowsLike_of_kept C (by rw [C.kept]; exact hk) hcs hM h1 h2 h3 k1 k2 k3

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.rowsLike_of_kept
#print axioms VerifiableInference.Desc.First.K2Hands.rowsLike_of_carried
