-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/HeldAtBatch.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): FROM THE TEST `k5Live` ON WHAT THE OWN ROUNDS OF AN
ATTENTION SEGMENT DREW (Johnson/Desc/K5/Honest/Law/LiveCount.lean) TO THE PROPOSITION `HeldLive`
(LiveState.lean beside it) AT THE STATE IN FRONT OF THE SEGMENT's BATCHING. On the verifier's chain
alone.

Why. `HeldLive` is the clause on states under which the runs of claims of this kind name each slot
of the kind's own window with a coefficient that does not read 0. Here `HeldLive` is shown, under
premises, for the state in front of the batching.

How. `HeldLive` reads of a state what it holds of the segment's own rounds, and nothing else: so it
rides along the library's `CarK5` (its first half). `CarK5` over the four members between:
Johnson/Desc/K5/Honest/Law/CarAtHead.lean, which calls the library's laws on each kind.

Main names:
  `heldLive_of_car`: the proposition rides along `CarK5`. Frame-free; no head.
  `held_at_batch`: **the whole.**

Limits. The head is a hypothesis. The yes of the five members (d4 .. d8) is a premise: no run is
shown. e4, hz (the ledger in front of the first has arrays of its length) and hc (c holds what the
rounds drew) are the caller's. The number k of `HeldLive` is the next slot of the ledger in front of
the first: A FIELD OF THE STATE: that it is the plan's number is not shown here. A yes of the test
is seen by evaluation alone, at three small places (Johnson/Desc/K5/Honest/Law/LiveCountToy.lean),
not at this size. That the batching stands next behind the fifth: `batch_place`
(Johnson/Desc/K5/Honest/Law/BatchPlace.lean), on the written list of places. At the function
`OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.CarAtHead
import Johnson.Desc.K5.Honest.Law.LiveToBatch
import Johnson.Desc.K5.Honest.Law.LiveState
import Johnson.Desc.K5.Honest.Law.LiveCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (Heard hear behind)
open K5Law (CarK5)
open P5J (AtMgA TS)

/-- **The proposition rides along the library's relation.** Conditional: hI; hc. -/
theorem heldLive_of_car {x : OnBytes.Params.AttentionRounds} {k : ℕ} {u u' : S}
    (hI : HeldLive x k u) (hc : CarK5 u u') : HeldLive x k u' := by
  obtain ⟨h5, F, G, rs, rest, lead, a, b⟩ := hI
  exact ⟨h5, F, G, rs, rest, lead, hc.1 h5 a, b⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **FROM THE TEST ON WHAT THE SEGMENT's OWN ROUNDS DREW TO `HeldLive` AT THE STATE IN FRONT OF THE
BATCHING.** Conditional: the head; hg; ea; f4 … f8: which five members; d4 … d8: their yes, each at
its own rounds; e4, hz: the open segment in front of the first, and its ledger's arrays have their
length; hc: c holds what the rounds of the first drew; hL: the test. -/
theorem held_at_batch {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) {att : AttOwn} (e4 : s4.here = .att att)
    (hz : OnBytes.Model.Road.Sized att.F) (c : Chal) (hc : Reads c rs4)
    (hL : k5Live a.own c = true) : HeldLive a.own att.F.next s9 := by
  obtain ⟨att', hd, G, e4', hh, rfl⟩ := heard_of_k5 h hg ea f4 d4
  obtain rfl : att' = att := Here.att.inj (e4'.symm.trans e4)
  exact heldLive_of_car
    ⟨hd, att'.F, G, rs4, [], 0, rfl, hh, hz, rfl, heardLive_of_draws c hh hc hL⟩
    (car_to_batch h hg ea f5 f6 f7 f8 d5 d6 d7 d8)

end H2K5.Honest

#print axioms H2K5.Honest.heldLive_of_car
#print axioms H2K5.Honest.held_at_batch
