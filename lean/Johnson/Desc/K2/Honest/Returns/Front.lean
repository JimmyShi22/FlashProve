-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Front.lean: THE FRONT OF A CODE SWITCH RETURNS (`firstFront` at a
segment's place, `finishFront` behind the last segment: Johnson/Top/H0/Tw/K2/First.lean) wherever
premises on the frame and the codes hold; what it returns is a term, and the new group that it opens
is written out. Statements and proofs, over the library's `firstFront_iff` and `finishFront_iff`
(Johnson/Top/H0/Tw/K2C/Asks.lean).

  `newGroupG_returns`   a new group is opened: both codes are in their lists, and the mask code is
                    not longer than the main code
  `group_new`, `codes_new`, `oracles_new`   the statement behind: under the next number a group of
                    these two codes without a member, without an open row, whose test has not begun;
                    the codes and the messages as before
  `firstFront_returns`, `finishFront_returns`   the two fronts

Limits. The head's front is not here. `group_new` stands at the statement IN FRONT OF THE SENDING:
that the sending keeps the group, and that the target's code is the group's (which hangs on how the
frame's groups are made), is not shown: so none of the step's premises on the group
(Returns/BehindAt.lean) is reached here. Nothing on any property.

-/
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.Ground (newGroupP newGroupL groupL withGroup ok has)
open _root_.Tw.K2 (newGroupG firstFront finishFront dOf firstFront_iff finishFront_iff)

/-- **A new group is opened.** -/
theorem newGroupG_returns (S : Statement) (code maskCode : Nat) (c z : Code)
    (hc : S.codes.base[code]? = some c) (hz : S.codes.mask[maskCode]? = some z)
    (hle : z.logN ≤ c.logN) :
    newGroupG S code maskCode = .ok (withGroup S code maskCode, S.groups.size) := by
  have hok : ok (newGroupL (dOf S).st code maskCode) = true := by
    show ok (newGroupL S code maskCode) = true
    unfold ok newGroupL groupL has
    simp [hc, hz, hle]
  unfold newGroupG newGroupP
  rw [if_pos hok]
  rfl

/-- The new group: no member, no open row, its test not begun. -/
theorem group_new (S : Statement) (code maskCode : Nat) :
    (withGroup S code maskCode).groups[S.groups.size]? =
      some { code := code, maskCode := maskCode } := by
  unfold withGroup
  simp

theorem codes_new (S : Statement) (code maskCode : Nat) :
    (withGroup S code maskCode).codes = S.codes := rfl

theorem oracles_new (S : Statement) (code maskCode : Nat) :
    (withGroup S code maskCode).oracles = S.oracles := rfl

/-- **The front at a segment's place returns.** -/
theorem firstFront_returns (S : Statement) (f : ReqFrame) (L : Params.ReqLink) (G : ReqGroup)
    (c z : Code) (h1 : f.next = .first) (h0 : f.link ≠ 0) (h2 : f.shape.link[f.link]? = some L)
    (h3 : f.groups[f.link]? = some G) (hc : S.codes.base[f.shape.code]? = some c)
    (hz : S.codes.mask[f.shape.maskCode]? = some z) (hle : z.logN ≤ c.logN) :
    firstFront S f = .ok ⟨withGroup S f.shape.code f.shape.maskCode,
      { f with group := S.groups.size, moment := 1, own := #[] }, f.atMoment 0,
      ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape f.link {})], G.target,
      L.plain⟩ :=
  (firstFront_iff S f _).2 ⟨L, G, _, _,
    ⟨h1, h0, h2, h3, newGroupG_returns S _ _ c z hc hz hle, rfl⟩⟩

/-- **The front behind the last segment returns.** -/
theorem finishFront_returns (S : Statement) (f : ReqFrame) (G : ReqGroup) (c z : Code)
    (h1 : f.next = .first) (h0 : f.link = f.shape.link.length) (h3 : f.groups[f.link]? = some G)
    (hc : S.codes.base[f.shape.code]? = some c) (hz : S.codes.mask[f.shape.maskCode]? = some z)
    (hle : z.logN ≤ c.logN) :
    finishFront S f = .ok ⟨withGroup S f.shape.code f.shape.maskCode,
      { f with group := S.groups.size, moment := 1, own := #[] }, [],
      #[foldMaskNotice (f.foldShape f.link {})], G.target, 0⟩ :=
  (finishFront_iff S f _).2 ⟨G, _, _, ⟨h1, h0, h3, newGroupG_returns S _ _ c z hc hz hle, rfl⟩⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.firstFront_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finishFront_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.group_new
