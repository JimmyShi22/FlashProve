-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/KeepsAtK8.lean: at each of the 25 numbers of the proof file's
first chain at which the draw of the smallness test stands, the sub-protocol's place has the kind
K8, and every accepting step of it gives the clause `K8KeepsM`. It serves the column `hK` of the
gathering (`owesS_head_cells`, Honest/Thread/GatherHeadCells.lean). The clause is stated by its own
name, with the kind beside it, so that the lemmas do not depend on how the clauses of all kinds are
gathered into one family. The authors of K8's lemmas prove the clause from the accepting step of any
sub-protocol that is seated over the draw's own (`keepsM_of_step`,
Johnson/Desc/K8/Honest/KeepsMark.lean). That the chain's sub-protocol at the number is so seated is
their `draw_layers` and `draw_head` (Johnson/Desc/K8/Honest/ReadsReach.lean) at the feed-forward
segments and the output head's. At an attention segment it is the library's `IM.k8_of_attention`
(Johnson/IMR/K8Seat.lean) with their `seats_of_alone` (ReadsReach.lean). The kind comes from
`head_place_hear` (Honest/Thread/HeadPlaceAt.lean). No definition.

  1  `k8_keeps_lay`, `k8_keeps_att`, `k8_keeps_head`   at the twelve feed-forward segments, the
     twelve attention segments and the output head's segment

Limits.
  * The authors of K8's lemmas state the attention segments' seat as `draw_att`
    (Honest/K8/ReadyAtHeadAtt.lean), in a file that depends on many files of a third group of
    authors. `k8_keeps_att` does not import it and makes the calls of its proof that bear on the
    seat.
  * No hypothesis beside the library's `AtMgA` and the range of the segment's number. That a
    `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (Honest/Thread/FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.K8.Honest.KeepsMark
import Johnson.Desc.K8.Honest.ReadsReach
import Johnson.IMR.K8Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First.K8.Honest (K8KeepsM keepsM_of_step draw_layers draw_head
  seats_of_alone)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h

/-- At the draw of feed-forward segment `2 * g`. -/
theorem k8_keeps_lay {g : Nat} (hg : g < 12) :
    ∀ blk, cF.blocksInOrder[14 * (2 * g) + 4 + 2]? = some blk →
      blk.place.kind = KindName.K8 ∧ ∀ s s', StepYes 0 blk s s' → K8KeepsM s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, Xl, -, hb', hs, -⟩ := draw_layers h.scope h.reads O hg
  rw [show 28 * g + 6 = 14 * (2 * g) + 4 + 2 by omega] at hb'
  obtain rfl : b = blk := Option.some.inj (hb'.symm.trans hb)
  have hp := head_place_hear h (l := 2 * g) (i := 4) (k := .K8) (by omega)
    (head_kind_lay hg (by unfold VerifiableInference.Desc.First.kindsBeforeBatching; rfl)) hb
  exact ⟨by rw [hp], fun _ _ hy => keepsM_of_step hs hy⟩

/-- At the draw of attention segment `2 * g + 1`. -/
theorem k8_keeps_att {g : Nat} (hg : g < 12) :
    ∀ blk, cF.blocksInOrder[14 * (2 * g + 1) + 4 + 2]? = some blk →
      blk.place.kind = KindName.K8 ∧ ∀ s s', StepYes 0 blk s s' → K8KeepsM s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, Xl, a, e1, e2, -, la, -⟩ := IM.k8_of_attention h.scope h.reads O g hg
  have hb' := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) 4] at hb'
  obtain rfl : b = blk := Option.some.inj (hb'.symm.trans hb)
  have hp := head_place_hear h (l := 2 * g + 1) (i := 4) (k := .K8) (by omega)
    (head_kind_att hg rfl) hb
  exact ⟨by rw [hp], fun _ _ hy => keepsM_of_step (seats_of_alone la) hy⟩

/-- At the draw of the output head's segment, number 343. -/
theorem k8_keeps_head :
    ∀ blk, cF.blocksInOrder[14 * 24 + 5 + 2]? = some blk →
      blk.place.kind = KindName.K8 ∧ ∀ s s', StepYes 0 blk s s' → K8KeepsM s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, Xl, -, hb', hs⟩ := draw_head h.scope h.reads O
  have hb'' : cF.blocksInOrder[14 * 24 + 5 + 2]? = some b := hb'
  obtain rfl : b = blk := Option.some.inj (hb''.symm.trans hb)
  have hp := head_place_hear h (l := 24) (i := 5) (k := .K8) (by decide) rfl hb
  exact ⟨by rw [hp], fun _ _ hy => keepsM_of_step hs hy⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k8_keeps_lay
#print axioms ProofFile.Honest.FirstThread.k8_keeps_att
#print axioms ProofFile.Honest.FirstThread.k8_keeps_head
