-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Head/PlanList.lean: the entries that the planner adds for the output head's own
rounds, as closed lists.

The planner's routines planHeadOwn and planHeadEnd (OnBytes/Params/SubRounds.lean) add the rounds of
the head's sub-proof behind its lookup and behind its smallness test. This file writes the entries
of these rounds out as functions of the record x : HeadRounds and of the work w of a round, cut into
named stretches, and proves of the planner's own routines that they add just these entries: the
whole entry, its name and its eleven numbers, for every record and every setting.

The stretches of planHeadOwn: hPoint (the point P_V) · hBatSums (the sums of limb products and the
element that batches them) · hSquares (a sumcheck and the point of a line) · hBatProducts (the row
products and their batching element) · hProducts, hStream, hLogits (three token sumchecks, each with
its claimed sum in the message of the hiding polynomial's sum). Those of planHeadEnd: hBatWeights
(the merge's element, one row) · hMerge (the merge's sumcheck) · hBatAll (the last batching).

Main theorems: headOwn_adds, headEnd_adds.

Under: a state of a request's scope with no open byte, root or answer; that the routine ends well;
for headOwn_adds, that there is at least one row value (else the planner leaves out the round in
the further variable).

Not claimed. A plan knows bytes and draws alone: nothing here on start forms, on the order of the
variables, on which coefficient is not sent, on the order of the scalars inside a message, or on
what an end value is. Nothing on the errors. Nothing on the place of these rounds in a chain's plan.

-/
import OnBytes.Tie.Pv.Lay.PlanList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Head

open OnBytes OnBytes.Params OnBytes.Tie.Pv.Lay

def hPoint (w : Nat) (x : HeadRounds) : List Fmt.Entry := [eDraw "ZERO" w 0 x.lt]
def hBatSums (w : Nat) (x : HeadRounds) : List Fmt.Entry := [eBat w (24 * x.sums) x.sums]
def hSquares (w : Nat) (x : HeadRounds) : List Fmt.Entry := lLayer w (x.lPd + x.lt)
def hBatProducts (w : Nat) (x : HeadRounds) : List Fmt.Entry :=
  [eBat w (24 * x.products) x.products]
def hProducts (w : Nat) (x : HeadRounds) : List Fmt.Entry := lPsc w 24 x.lt 2 x.rowValues
def hStream (w : Nat) (x : HeadRounds) : List Fmt.Entry := lPsc w 24 x.lt 2 2
def hLogits (w : Nat) (x : HeadRounds) : List Fmt.Entry := lPsc w 24 (x.lt + x.lPd) 2 2
def hBatWeights (w : Nat) : List Fmt.Entry := [eBat w 0 1]
def hMerge (w : Nat) (x : HeadRounds) : List Fmt.Entry := lPsc w 0 x.lkW 1 1
def hBatAll (w : Nat) (x : HeadRounds) : List Fmt.Entry := [eBat w 0 x.rows]

/-- The entries of the head's own rounds behind its lookup. -/
def headOwnList (w : Nat) (x : HeadRounds) : List Fmt.Entry :=
  hPoint w x ++ hBatSums w x ++ hSquares w x ++ hBatProducts w x ++ hProducts w x ++
    hStream w x ++ hLogits w x

/-- The entries of the head's rounds behind its smallness test. -/
def headEndList (w : Nat) (x : HeadRounds) : List Fmt.Entry :=
  hBatWeights w ++ hMerge w x ++ hBatAll w x

/-- A claimed sum and the sumcheck that starts from it, with at least one end value. -/
theorem adds_tokenSum (s : Setting) (lt shown dy more : Nat) (h : 0 < shown) :
    Adds s 0 0 (planTokenSum lt shown dy more)
      (lPsc (s.workOf .field .request) 24 (lt + more) dy shown) := by
  have e : planTokenSum lt shown dy more = (planScalars 1 >>= fun _ =>
      planPsc { degree := List.replicate (lt + more) 3, degreeY := dy, values := shown }) := by
    unfold planTokenSum
    rw [decide_eq_true h]
  rw [e]
  exact (Adds.bind (adds_scalars s 0 1) (adds_psc s (0 + 24 * 1) (lt + more) dy shown)).cast
    rfl rfl (by simp)

theorem headOwn_adds (s : Setting) (x : HeadRounds) (h : 0 < x.rowValues) :
    Adds s 0 0 (planHeadOwn x) (headOwnList (s.workOf .field .request) x) := by
  have g := Adds.bind (adds_zero s x.lt) (Adds.bind (adds_scalars s 0 x.sums)
    (Adds.bind (adds_bat s (0 + 24 * x.sums) x.sums)
    (Adds.bind (adds_psc s 0 (x.lPd + x.lt) 2 2) (Adds.bind (adds_line s)
    (Adds.bind (adds_scalars s 0 x.products)
    (Adds.bind (adds_bat s (0 + 24 * x.products) x.products)
    (Adds.bind (adds_tokenSum s x.lt x.rowValues 2 0 h)
    (Adds.bind (adds_tokenSum s x.lt 2 2 0 (Nat.succ_pos 1))
      (adds_tokenSum s x.lt 2 2 x.lPd (Nat.succ_pos 1))))))))))
  exact g.cast rfl rfl (by
    simp [headOwnList, hPoint, hBatSums, hSquares, hBatProducts, hProducts, hStream, hLogits,
      lLayer])

theorem headEnd_adds (s : Setting) (x : HeadRounds) :
    Adds s 0 0 (planHeadEnd x) (headEndList (s.workOf .field .request) x) := by
  have g := Adds.bind (adds_bat s 0 1) (Adds.bind (adds_psc s 0 x.lkW 1 1) (adds_bat s 0 x.rows))
  exact g.cast rfl rfl (by simp [headEndList, hBatWeights, hMerge, hBatAll])

end OnBytes.Tie.Pv.Head

#print axioms OnBytes.Tie.Pv.Head.headOwn_adds
#print axioms OnBytes.Tie.Pv.Head.headEnd_adds
