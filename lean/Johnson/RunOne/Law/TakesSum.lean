-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TakesSum.lean: THE PROMISE
IN FRONT OF THE FIRST LINK, WITH ITS TWO INEQUALITIES AS ONE TEST ON PUBLIC NUMBERS: promL_fresh
(HandedIn.lean) from RoomFor (Johnson/Desc/First/Look/KeyLaw/Takes.lean).

Main names:
  sumTo_shift, sumTo_list: sumTo over a list's members, by number, is the list's sum.
  sum_cntO, sum_cntK: what the plan's lookups take together, in the promise's terms and in the
    test's.
  promL_room: PromL 0 from plain facts on the record and RoomFor.

Object: none of a description's own text: promL_room speaks of a record s of the first chain's type
under premises on s. That the record behind the second sending of (FK X N P).first.blocksInOrder meets them
is shown by no term.
User: none yet.
Letters: one, m, idxN, lo, lk, Ex, s.

Limits. Those of promL_fresh, but for the two inequalities and the two mask rows.

-/
import Johnson.RunOne.Law.HandedIn
import Johnson.RunOne.Law.LinkAtPlan
import Johnson.Desc.First.Look.KeyLaw.Takes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TakesSum
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.FitsKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.HandedIn
open Johnson.RunOne.Law.LinkAtPlan

theorem sumTo_shift (f : ℕ → ℕ) : ∀ n, sumTo f (n + 1) = f 0 + sumTo (fun i => f (i + 1)) n
  | 0 => by
    show 0 + f 0 = f 0 + 0
    omega
  | n + 1 => by
    show sumTo f (n + 1) + f (n + 1) = f 0 + (sumTo (fun i => f (i + 1)) n + f (n + 1))
    rw [sumTo_shift f n]
    omega

/-- sumTo over a list's members, by number, is the list's sum. -/
theorem sumTo_list {α : Type} (g : α → ℕ) (d : α) : ∀ ls : List α,
    sumTo (fun i => g (ls.getD i d)) ls.length = (ls.map g).sum
  | [] => rfl
  | a :: ls => by
    rw [List.length_cons, sumTo_shift, List.map_cons, List.sum_cons]
    show g a + sumTo (fun i => g (ls.getD i d)) ls.length = _
    rw [sumTo_list g d ls]

theorem sum_cntO (one : OneTime) (m : Wf.Matrix) :
    sumTo (cntO one.ranges.messageId m (Lof one)) one.ranges.lookups.length =
      takesO one.ranges.messageId m one.ranges.lookups :=
  sumTo_list (fun l => (faceOfLkp (Wf.lookupOf one.ranges.messageId m l)).slots -
    2 * (faceOfLkp (Wf.lookupOf one.ranges.messageId m l)).parts.length) default _

theorem sum_cntK (one : OneTime) (m : Wf.Matrix) :
    sumTo (cntK one.ranges.messageId m (Lof one)) one.ranges.lookups.length =
      takesK one.ranges.messageId m one.ranges.lookups :=
  sumTo_list (fun l => 2 * (faceOfLkp (Wf.lookupOf one.ranges.messageId m l)).parts.length)
    default _

/-- **The promise in front of the first link, from plain facts on the record and RoomFor.** -/
theorem promL_room {one : OneTime} {m : Wf.Matrix} {idxN : ℕ} {lo lk : Ledger} {Ex : FirstState →
    Prop}
    {s : FirstState} (hR : RoomFor one.ranges m one.codes one.indexMasks.shape) (h1 : s.idx = idxN)
    (h2 : ledAt s.d.st one.ranges.messageId = some lo) (h3 : ledAt s.d.st idxN = some lk)
    (hT : TablesFit s.d.st one.ranges one.codes) (hi : idxN < s.d.st.oracles.size)
    (o0 : lo.next = 0) (o1 : lo.rows = max one.ranges.message.shape.maskRows 1)
    (o2 : lo.logRows = ceilLog2 one.ranges.message.shape.maskRows) (k0 : lk.next = 0)
    (k1 : lk.rows = max one.indexMasks.shape.maskRows 1)
    (k2 : lk.logRows = ceilLog2 one.indexMasks.shape.maskRows)
    (tO : Means.tableSize s.d.st one.ranges.messageId .mask =
      2 ^ ((one.codes.mask.getD one.ranges.message.shape.maskCode default).logEll +
        ceilLog2 one.ranges.message.shape.maskRows))
    (tK : Means.tableSize s.d.st idxN .mask =
      2 ^ ((one.codes.mask.getD one.indexMasks.shape.maskCode default).logEll +
        ceilLog2 one.indexMasks.shape.maskRows))
    (hE : Ex s) :
    PromL one one.ranges.messageId m (Lof one) idxN one.ranges.lookups.length lo lk Ex 0 s :=
  promL_fresh h1 h2 h3 hT hi hR.1 o0 o1 o2 hR.2.1 k0 k1 k2 tO tK
    (by rw [sum_cntO]; exact hR.2.2.1) (by rw [sum_cntK]; exact hR.2.2.2) hE

end Johnson.RunOne.Law.TakesSum

#print axioms Johnson.RunOne.Law.TakesSum.sumTo_list
#print axioms Johnson.RunOne.Law.TakesSum.sum_cntO
#print axioms Johnson.RunOne.Law.TakesSum.sum_cntK
#print axioms Johnson.RunOne.Law.TakesSum.promL_room
