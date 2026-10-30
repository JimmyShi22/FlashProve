-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadWeightsMeet.lean: THE OUTPUT MATRIX'S WEIGHTS, READ TWICE OFF THE
WITNESS, ARE ONE, WHERE THE WITNESS'S CELLS HOLD AN INDEX: the law of the sub-protocol at the output
head reads them as whOf w.cells (Law/WhOf.lean: the output matrix of the index that the cells hold);
the caller of the proved lookup sub-protocol reads them as the lift of two bytes of the committed
table's message (Johnson/Desc/First/Look/K3CallerHead.lean: headCells' field Wh).

Why. In the composed meaning the committed table as an oracle message, its
reader of a cell and the witness's message are fixed terms
(Johnson/Desc/First/Look/K3LettersAt.lean: k3StoredAt: oWc, wOfC, msgWc): so the agreement, which
the head's bill took as a premise, is a theorem.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  wOfE_stored: the caller's entry (a, b) of the committed matrix IS the cast of the index's matrix's
      entry, at EVERY a and b: inside the cells' shape by what "holds" says; outside both are 0.
  weights_stored: SO: intW (Hof (the caller's entries) k v) = whOf w.cells k v, for k below 5120 and
      v below 202048.

How. Hof_weightsOf (the layout reads H as these two bytes), head_wh_cast
(the lift of a cast of size at most 2 ^ 12), indexOf_eq
(Johnson/Goal/Meaning/NextToken.lean: a matrix holds at most one index, whatever its shape),
whOf_abs.
Every letter under "there is": none.
What it does not say. THAT THE WITNESS'S CELLS HOLD AN INDEX: a premise (in that meaning's three
items at the head it is the guard). Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WhOf
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.Desc.First.Look.K3HeadGoodIn
import Johnson.Goal.Meaning.NextToken

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes
open VerifiableInference.OnPublicFiles (layMs)
open VerifiableInference.OnPublicFiles.Flat (GE Holds InRange)
open VerifiableInference.Desc.First.Look (Sent sigListCalls wOfE msgLay lyW finOf)
open VerifiableInference.Desc.Sound (MsgT)

variable {rows cols : Nat} {Tok : Type} (x : First.Look.Place) (tl : OnBytes.Model.HTailF2)
  (D : Sent) (rad : OracleShape → Nat) (arr : Nat → Nat → Nat)
  (seatT : Fin (sigListCalls D rad x.link).length → Nat × Nat)

/-- **The caller's entries of the committed matrix are the index's, at every place.** -/
theorem wOfE_stored (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (i : Cm.Idx)
    (h : Holds w.cells i) (a b : Nat) :
    wOfE (msgLay x tl D rad (First.Look.Stored.oWc rows cols) First.Look.Stored.wOfC rows cols
      (layMs x D rad (First.Look.Stored.oWc rows cols) seatT arr First.Look.Stored.msgWc w)) a b =
      ((i.mat a b : ℤ) : Cb.Gl.E) := by
  unfold wOfE lyW finOf
  by_cases ha : a < rows
  · by_cases hb : b < cols
    · rw [dif_pos ha, dif_pos hb]
      show First.Look.Stored.wOfC (First.Look.Stored.msgWc w) a b = _
      unfold First.Look.Stored.wOfC
      rw [dif_pos ⟨ha, hb⟩]
      exact h.1 ⟨a, ha⟩ ⟨b, hb⟩
    · rw [dif_pos ha, dif_neg hb, h.2 a b (fun e => hb e.2)]
      simp [msgLay]
  · rw [dif_neg ha, h.2 a b (fun e => ha e.1)]
    simp [msgLay]

/-- **The two readings of the output matrix's weights are one.** -/
theorem weights_stored [Sizes] [Policy] [Request] (adr : HeadAdr)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hR : InRange w.cells) (k v : Nat)
    (hk : k < 5120) (hv : v < 202048) :
    intW (Inst.Model.Head.Hof (wOfE (msgLay x tl D rad (First.Look.Stored.oWc rows cols)
        First.Look.Stored.wOfC rows cols
      (layMs x D rad (First.Look.Stored.oWc rows cols) seatT arr First.Look.Stored.msgWc w))) k v) =
      whOf w.cells k v := by
  obtain ⟨i, hi⟩ := hR
  have e1 : whOf w.cells k v = Inst.Model.Head.Hof i.mat k v := by
    unfold whOf
    rw [VerifiableInference.Meaning.indexOf_eq hi]
    exact Inst.Model.Head.Hof_weightsOf i.mat hk hv
  have hb : |Inst.Model.Head.Hof i.mat k v| ≤ 2 ^ 12 := by
    rw [← e1]
    exact whOf_abs w.cells k v
  rw [e1]
  exact head_wh_cast (adr := adr) _ i.mat (wOfE_stored x tl D rad arr seatT w i hi _ _)
    (wOfE_stored x tl D rad arr seatT w i hi _ _) hb

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.wOfE_stored
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.weights_stored
