-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadViewsSeats.lean: the two cheap public tests planK6AtZ and padsAtZ
(Johnson/Desc/Kinds/HeadDoorAtZ.lean) ACCEPT wherever Z's codes, shape and layout are the written
ones AND THE SEATS THAT ARE MADE OF Z ARE THE WRITTEN SEATS (psFull, seatsAllFull:
Johnson/P5T/PlanSeatsFull.lean). Theorems; three evaluations by Lean's kernel.


Why. Law/HeadViewsWritten.lean asks five equations of Z, the fifth on a table of counts of roots
that no test compares. It is stated, in the goals' scope, that planSeats Z Z.D.1 = psFull and
planSeatsAll Z Z.D = seatsAllFull. lettersAt Z reads Z through these two lists alone. So these two
equations serve in the place of the equations on the sendings and on the roots.

  SeatsWritten Z   five equations: Z.first.codes, Z.first.shape, Z.first.layout as in Written;
          planSeats Z Z.D.1 = psFull; planSeatsAll Z Z.D = seatsAllFull.
  lettersS         the five arguments at the two written lists.

What is proved.
  letters_seats    under the last two equations lettersAt Z = lettersS.
  viewS_closed, numS_closed, padsS_closed   BY LEAN's KERNEL: the first test's View at lettersS,
          with 8192 in ns's place, is viewFull's with 8192 there; the number of the head's first
          oracle message is 145; the second test's View is padsFull.
  **padsAtZ_of_seats**     SeatsWritten Z and XPart Z.p.X imply padsAtZ Z = true.
  **planK6AtZ_of_seats**   ProofFile.pureRoad.pub o pol lay KL = .ok Z, SeatsWritten Z and XPart Z.p.X
          imply planK6AtZ Z = true.

No existential quantifier in these statements.
Not proved here. SeatsWritten Z. XPart Z.p.X (Goal/Meaning/HeadXPartScope.lean: in the goals' scope,
at publicOf's X). Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadViewsWritten
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqLayout)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open P5T (planSeats planSeatsAll numbersOf psFull seatsAllFull)

/-- The five arguments at the two written lists of seats. -/
def lettersS : DoorLetters :=
  { arr := arrFast seatsAllFull
    num := numFast seatsAllFull
    group := (numbersOf psFull).group
    sent0 := (numbersOf psFull).sent 24 0
    mems := memsOf psFull }

/-- Five equations on Z. -/
structure SeatsWritten (Z : ProofFile.Pub) : Prop where
  codes : Z.first.codes = proofSizedFull.codes
  shape : Z.first.shape = proofSizedFull.request
  layout : Z.first.layout = layoutFull
  seats : planSeats Z Z.D.1 = psFull
  seatsAll : planSeatsAll Z Z.D = seatsAllFull

theorem letters_seats {Z : ProofFile.Pub} (h1 : planSeats Z Z.D.1 = psFull)
    (h2 : planSeatsAll Z Z.D = seatsAllFull) : lettersAt Z = lettersS := by
  unfold lettersAt lettersS
  rw [h1, h2]

/-- Lean's kernel evaluates it. -/
theorem viewS_closed :
    viewPlain proofSizedFull.codes layoutFull 8 4 8192 (labW 24) lettersS.num lettersS.arr
      (lettersS.group 24) lettersS.sent0 lettersS.mems = { viewFull with ns := 8192 } := by
  decide +kernel

/-- Lean's kernel evaluates it. -/
theorem numS_closed : lettersS.num 24 0 = 145 := by
  decide +kernel

/-- Lean's kernel evaluates it. -/
theorem padsS_closed :
    padsViewOf proofSizedFull.codes layoutFull labW lettersS.num lettersS.arr lettersS.group
      lettersS.mems 8 (fun _ => 1) 4 = padsFull := by
  decide +kernel

/-- **The second test accepts.** -/
theorem padsAtZ_of_seats {Z : ProofFile.Pub} (W : SeatsWritten Z) (hx : XPart Z.p.X) :
    padsAtZ Z = true := by
  unfold padsAtZ padsRow
  rw [padsDoor_eq, letters_seats W.seats W.seatsAll, W.codes, W.layout, hx.ixi, hx.nhf]
  have e1 : pairsOf 8 (nasOf Z.p.X) 4 = pairsOf 8 (fun _ => 1) 4 :=
    pairsOf_nas 8 4 _ _ hx.nas
  have e2 : padsViewOf proofSizedFull.codes layoutFull (labsOf Z.p.X) lettersS.num lettersS.arr
      lettersS.group lettersS.mems 8 (nasOf Z.p.X) 4 = padsFull := by
    rw [← padsS_closed]
    have e3 : padsViewOf proofSizedFull.codes layoutFull (labsOf Z.p.X) lettersS.num lettersS.arr
        lettersS.group lettersS.mems 8 (nasOf Z.p.X) 4 =
        padsViewOf proofSizedFull.codes layoutFull (labsOf Z.p.X) lettersS.num lettersS.arr
          lettersS.group lettersS.mems 8 (fun _ => 1) 4 := by
      unfold padsViewOf
      rw [e1]
    rw [e3]
    refine padsViewOf_labs _ _ _ _ _ _ _ _ _ _ _ fun x hxm => ?_
    rcases pairs_kinds hxm with ⟨g, h0, hg, a1, a2⟩ | ⟨g, hg, a1, a2⟩ | ⟨a1, a2⟩
    · rw [a1, a2, hx.layers g h0 hg, labW_layers g hg h0]
    · rw [a1, a2, hx.att g hg, labW_att g hg]
    · rw [a1, a2, hx.head 7 (by decide), labW_head 7 (by decide)]
  rw [e2]
  exact padsFull_yes

/-- **The first test accepts.** -/
theorem planK6AtZ_of_seats {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (W : SeatsWritten Z) (hx : XPart Z.p.X) :
    planK6AtZ Z = true := by
  have hns : Z.p.X.H.ns ≤ 8192 := by
    obtain ⟨zk, hz, hle⟩ := head_ns_le h
    rw [W.codes, W.shape] at hz
    have e := ell_closed
    rw [hz] at e
    have : zk.ell = 8192 := Option.some.inj e
    omega
  unfold planK6AtZ planK6Row planK6Door
  rw [letters_seats W.seats W.seatsAll, W.codes, W.layout, hx.nm, hx.nhf, numS_closed]
  have e : viewPlain proofSizedFull.codes layoutFull 8 4 8192 (labsOf Z.p.X 24) lettersS.num
      lettersS.arr (lettersS.group 24) lettersS.sent0 lettersS.mems =
      { viewFull with ns := 8192 } := by
    rw [← viewS_closed]
    refine viewPlain_labs _ _ _ _ _ _ _ _ _ _ _ _ fun a ha => ?_
    rw [hx.head a ha, labW_head a ha]
  have b : planK6V { viewPlain proofSizedFull.codes layoutFull 8 4 Z.p.X.H.ns (labsOf Z.p.X 24)
      lettersS.num lettersS.arr (lettersS.group 24) lettersS.sent0 lettersS.mems with
      ns := 8192 } 145 0 = true := by
    have : { viewPlain proofSizedFull.codes layoutFull 8 4 Z.p.X.H.ns (labsOf Z.p.X 24)
        lettersS.num lettersS.arr (lettersS.group 24) lettersS.sent0 lettersS.mems with
        ns := 8192 } = viewPlain proofSizedFull.codes layoutFull 8 4 8192 (labsOf Z.p.X 24)
          lettersS.num lettersS.arr (lettersS.group 24) lettersS.sent0 lettersS.mems := rfl
    rw [this, e]
    exact viewFull_bound
  exact planK6V_mono b hns

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.letters_seats
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewS_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.numS_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsS_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsAtZ_of_seats
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6AtZ_of_seats
