-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsG.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for number 2: K1's opening
of segment 0 with the frame's step "opened" joined after it. The library's `IM.first_sits`
(Johnson/IMR/FirstSeats.lean) says that the sub-protocol there is such a join.
`keeps_joined_openedR` (OpenedKeepsR.lean) takes a clause of the first half to the joined form. The
clause of the first half comes from `k1_first_half`
(Johnson/Desc/ProofFile/Honest/K1/Law/KeepsMember.lean) of the authors of K1's lemmas. The lemma has
the form that `head_hK_of_families` (SteppedYes.lean) takes. No definition.

  1  `fHead_keeps_two`   the lemma

Limits.
  * No hypothesis beside the library's `AtMgA`. That a `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
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
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At number 2. -/
theorem fHead_keeps_two :
    ∀ blk, cF.blocksInOrder[2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hj⟩ :=
    IM.first_sits h.scope h.reads O 0 (by decide) .K1 rfl
  have hb1 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) 0] at hb1
  have hb2 : cF.blocksInOrder[2]? = some b := hb1
  obtain rfl : b = blk := Option.some.inj (hb2.symm.trans hb)
  have hb3 : cF.blocksInOrder[14 * 0 + 0 + 2]? = some b := hb
  rw [head_place_hear h (l := 0) (i := 0) (k := .K1) (by decide) rfl hb3]
  exact (fHead_K1_first Zp cF G take P11 p12 P13
    (p := { chain := 1, link := some 0, piece := 0 + 1, kind := .K1 }) rfl rfl s s').2
    (keeps_joined_openedR hj 0
      (fun s m => ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m)
      (fun _ _ y _ => ProofFile.Honest.K1.k1_first_half ⟨L, hL, hb'⟩ ep y) s s' hy)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_two
