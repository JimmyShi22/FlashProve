-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsH.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for number 338: the next
token (K7), the first sub-protocol of the output head's segment. The library's `IM.k7_sits`
(Johnson/IMR/FirstSeats.lean) says which sub-protocol stands there. `k7KeepsAt_of_step`
(Honest/K7/KeepsAt.lean) gives the clause from its accepting step, and `k7Block_lot`
(Honest/K7/InScope.lean) one of its hypotheses. The argument `G` of `fHead` is `Bs.G₀`, where `Bs`
is what `ProofFile.baseOf` returns at the public part. The lemma has the form that `head_hK_of_families`
(SteppedYes.lean) takes. No definition.

  1  `fHead_keeps_k7`   the lemma

Limits.
  * That a `StepYes` exists at any state is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.K7.InScope
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At the next token, number 338. -/
theorem fHead_keeps_k7 {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ blk, cF.blocksInOrder[338]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF Bs.G₀ take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨sz, -⟩ := IM.ground_gets h.scope h.reads O.pub O.blank
  obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits h.scope h.reads O
  have hb1 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) 0] at hb1
  have hb2 : cF.blocksInOrder[338]? = some b := hb1
  obtain rfl : b = blk := Option.some.inj (hb2.symm.trans hb)
  have hb3 : cF.blocksInOrder[14 * 24 + 0 + 2]? = some b := hb
  have hpl : b.place = IM.k7Place :=
    head_place_hear h (l := 24) (i := 0) (k := .K7) (by decide) rfl hb3
  have hj' : IM.Joined Zp (Bs'.G₀.built.size - 1) b (IM.k7Block Bs'.G₀.W 24).retype
      IM.k7Place := by
    rw [sz]
    exact hj
  have hp : b.place = (P4.k7Core Bs'.G₀).place := by
    rw [hpl]
    unfold P4.k7Core
    rw [sz]
    rfl
  have K := k7KeepsAt_of_step (k7Block_lot h.scope h.reads O) hj' hp hy
  have hk : b.place.kind = .K7 := by rw [hpl]
  rw [hk]
  exact K

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k7
