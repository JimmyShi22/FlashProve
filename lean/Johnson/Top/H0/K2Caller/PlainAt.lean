-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PlainAt.lean: the code switch at the plain letters (`Letters.plain`,
Member.lean): THE STAGE IN FRONT HAS NO OPEN OLD MESSAGE. So what the law's premises ask of such
messages is asked of nothing.

Main names:
  `SwRow.OK.kept_mem`: a kept place is a member's (from the test r.ok's clause on the kept places).
  `plain_empty`: the index of the stage's open old messages is empty: at these letters what stays
    open is what is kept, and a kept member is held in the folded word.
Limits. A choice of letters: the law then speaks of the folded word, the kept slots and the new
messages alone; other messages that are open at a real place are no matter of this block's law.
Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.GoodAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

/-- A kept place is a member's. -/
theorem SwRow.OK.kept_mem {r : SwRow} (H : r.OK) (i : Fin r.lo.length) (k : i.val ∈ r.kept) :
    r.mem i := by
  have h := H.kept i.val k
  rw [List.getElem?_eq_getElem i.isLt] at h
  simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- **At the plain letters the stage in front has no open old message**: what stays open is kept,
    and
every kept place is a member's, which is held in the folded word. -/
instance plain_empty :
    IsEmpty (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).S.O :=
  ⟨fun i => i.2 ⟨H.kept_mem i.1.1 i.1.2, i.1.2⟩⟩

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.plain_empty
