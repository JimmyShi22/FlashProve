-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/PlanNums.lean: WHAT THE MERGE's LAW ASKS OF THE PLAN's NUMBERS HOLDS OF
EVERY PUBLIC RECORD THAT THE PLANNER RETURNS. General: no file is read, no number evaluated.

`merge_table_plan` (OfPlan.lean) takes, of the block's numbers P: that the layout P.lay is a return
of the program's `wsLayOf`; that 2 lk + 3 ≤ P.nMsg, lk the layout's number of column bits; and, of
the slot sv of the claim's value, sv < P.nMsg. A written description's lot lays P.lay :=
X.layers.wsLay and P.nMsg := X.H.nMsg, X the public record. Here the first two are shown of every X
that `Verify.publicOf` (OnBytes/Model/VerifyPublic.lean) returns, and of every X that its copy with
the second hash function as an argument returns (`publicOfO`,
Johnson/Desc/Ok/PlanWritten/PublicAt.lean). Of the third: what a yes of the merge's decision gives.

Main names:
  `pubOf_wsLay`: `Layer.Pub.of` keeps the weights' layout.
  `planH2_slots`: the head's plan has room: 2 lkW + 3 ≤ nMsg: `Head.planH2` lays nMsg := `slotsH`,
    whose last summand is the merge's own count `wsForkSlots lkW`.
  `public_merge`, `publicO_merge`: both facts; the layout's lk is lkW by `wsLayOf_units`
    (Johnson/Road/FormsKeysWLay.lean), and one lkW goes to both calls.
  `svAt`: the slot of the claim's value, read off a record that stands at the head.
  `sv_lt_of_yes`: where `headMergeDecide` says yes the record stands at the head, holds such a slot,
    `svAt` reads it, and, if the ledger in front is sized, it is below THE LEDGER's number of slots.
Limits. `sv_lt_of_yes` bounds the slot by a.F.ns, the ledger's number in the record in front, NOT by
P.nMsg: that the two are one number is not shown here (at a yes the ledger's «next» behind is
P.nMsg: `decide_inv`, Says.lean). That a lot's numbers are X's is by unfolding the lot's own text,
not here. Tools on the planner's text: nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.MergeLaw.OfPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePub
import Johnson.Road.FormsKeysWLay
import OnBytes.Tie.Pv.Psc.PscRoom
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model Fo.BatRows Fo.Pub

/-- Layer.Pub.of keeps the weights' layout. -/
theorem pubOf_wsLay {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.wsLay = wsLay := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

/-- **The head's plan has room for the merge's slots.** -/
theorem planH2_slots {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : Nat} {H : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok H) : 2 * lkW + 3 ≤ H.nMsg := by
  unfold Head.planH2 at e
  repeat' first
    | (obtain ⟨_, _, e⟩ := bindE_ok e)
    | (split at e)
  all_goals
    cases e
    simp only [Head.slotsH, wsForkSlots, sumcheckSlots, roundValues]
    omega

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **What the merge's law asks of the plan's numbers holds of every public record that the planner
returns.** -/
theorem public_merge (h : Verify.publicOf pol KL layout = .ok X) :
    (∃ s p3 lkW, wsLayOf s p3 lkW = .ok X.layers.wsLay) ∧
      2 * X.layers.wsLay.lk + 3 ≤ X.H.nMsg := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, kW, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, kL, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have hw : layers.wsLay = wsLay := pubOf_wsLay k4
  dsimp only
  rw [hw]
  refine ⟨⟨_, _, _, kW⟩, ?_⟩
  rw [(OnBytes.Road.wsLayOf_units kW).1]
  exact planH2_slots k8

/-- The same of the planner's text with the second hash function as an argument. -/
theorem publicO_merge (o : Nat → ByteArray → ByteArray)
    (h : VerifiableInference.PlanWritten.publicOfO o pol KL layout = .ok X) :
    (∃ s p3 lkW, wsLayOf s p3 lkW = .ok X.layers.wsLay) ∧
      2 * X.layers.wsLay.lk + 3 ≤ X.H.nMsg := by
  unfold VerifiableInference.PlanWritten.publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, kW, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, kL, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have hw : layers.wsLay = wsLay := pubOf_wsLay k4
  dsimp only
  rw [hw]
  refine ⟨⟨_, _, _, kW⟩, ?_⟩
  rw [(OnBytes.Road.wsLayOf_units kW).1]
  exact planH2_slots k8

end

/-- The slot of the claim's value, read off a record that stands at the head. -/
def svAt (s : S) : ℕ :=
  match s.here with
  | .head a => (a.x.map (·.sV)).getD 0
  | _ => 0

/-- **Where the merge's decision says yes, the slot of the claim's value is below the ledger's
    number
of slots.** -/
theorem sv_lt_of_yes {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : Johnson.Desc.First.ForkMerge.headMergeDecide P s rs = .ok s') :
    ∃ a x0, s.here = .head a ∧ a.x = some x0 ∧ svAt s = x0.sV ∧
      (OnBytes.PscRun.Sized a.F → x0.sV < a.F.ns) := by
  obtain ⟨a, a', tp, F, claim, x, wo, e1, e2, e3, e4, e5, e6, e7, -⟩ := decide_inv h
  refine ⟨a, x, e1, e4, ?_, fun hz => ?_⟩
  · unfold svAt
    rw [e1]
    show (a.x.map (·.sV)).getD 0 = x.sV
    rw [e4]
    rfl
  · obtain ⟨xx, mu, eps, c, beta, v, T, r1, rY, rV, qs, -, -, -, hp, -⟩ := mergeHear_inv e7
    exact OnBytes.PscRun.filled_lt hz.2.2 (filled_of_public hp)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.planH2_slots
#print axioms VerifiableInference.Desc.First.MergeLaw.public_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.publicO_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.sv_lt_of_yes
