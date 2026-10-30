-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/KeepsAtK4.lean: at each of the twelve numbers of the proof file's
first chain at which the feed-forward layers' own rounds stand, the sub-protocol's place has the
kind K4, and every accepting step of it gives the clause `K4KeepsM`: `K4Keeps`, and no mark of
failure after the step. It serves the column `hK` of the gathering (`owesS_head_cells`,
Honest/Thread/GatherHeadCells.lean). The clause is stated by its own name, with the kind beside it,
so that the lemma does not depend on how the clauses of all kinds are gathered into one family. The
library's `IM.k4_of` (Johnson/IMR/K4Seat.lean) says which sub-protocol stands at the number, and its
`IM.k4_yes` says that an accepting decision there is an accepting decision of the kind's own
sub-protocol with no mark after it. `k4_keeps` (Honest/K4/Law/Keeps.lean) of the authors of K4's
lemmas gives `K4Keeps` from that decision. The kind comes from `head_place_hear`
(Honest/Thread/HeadPlaceAt.lean). No definition.

  1  `k4_keeps_lay`   the lemma

Limits.
  * The authors of K4's lemmas prove the same clause at a thread's member (`k4_keepsM_of_laid`,
    Honest/K4/Law/SitsAt.lean). That lemma takes a thread's arguments and a fact on how the member
    is laid. This one takes neither and makes the same two calls.
  * No hypothesis beside the library's `AtMgA` and the range of the segment's number. That a
    `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (Honest/Thread/FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatScope
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h

/-- At K4's sub-protocol of feed-forward segment `2 * g`. -/
theorem k4_keeps_lay {g : Nat} (hg : g < 12) :
    ∀ blk, cF.blocksInOrder[14 * (2 * g) + 2 + 2]? = some blk →
      blk.place.kind = KindName.K4 ∧
        ∀ s s', StepYes 0 blk s s' → ProofFile.Honest.K4.K4KeepsM s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, -, hla, -⟩ := IM.k4_of h.scope h.reads O g hg
  have hb1 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g) (by omega) 2] at hb1
  obtain rfl : b = blk := Option.some.inj (hb1.symm.trans hb)
  have hp := head_place_hear h (l := 2 * g) (i := 2) (k := .K4) (by omega)
    (head_kind_lay hg (by unfold VerifiableInference.Desc.First.kindsBeforeBatching; rfl)) hb
  refine ⟨by rw [hp], fun s s' hy => ?_⟩
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨y1, y2, -⟩ := (IM.k4_yes hla s s' rs gs).1 hd
  exact ⟨ProofFile.Honest.K4.k4_keeps y1, y2⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k4_keeps_lay
