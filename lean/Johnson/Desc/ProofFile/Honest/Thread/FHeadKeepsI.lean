-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsI.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for number 356: K1's
sending of W with a step of K13 after it. The library's `IM.back_of`, `IM.back_at_flat` and
`IM.links_flat_352` (Johnson/IMR/BackSeat.lean) say which sub-protocol stands there.
`IM.alone_noMark` (Johnson/IMR/MemberPath.lean) takes its acceptance to the acceptance of the two
steps in a row, with no mark of failure after them. `k1_send_half`
(Johnson/Desc/ProofFile/Honest/K1/Law/KeepsMember.lean) gives the clause of the first step and
`rowsB_rowsKeeps` (Johnson/Desc/K13/Honest/RowsKeeps.lean) that of the second. The argument `P13` of
`fHead` is the library's `K13.whereOf Zp`. The lemma has the form that `head_hK_of_families`
(SteppedYes.lean) takes. No definition.

  1  `head_P13`   the library's `h.𝔇.P13` is `K13.whereOf Zp`
  2  `fHead_keeps_w`   the lemma

Limits.
  * No hypothesis beside the library's `AtMgA`. That a `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.IMR.BackSeat
import Johnson.IMR.MemberPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)

/-- The library's parameter of K13 under `AtMgA` is the one at which it seats K13's
sub-protocols. -/
theorem head_P13 : h.𝔇.P13 = VerifiableInference.Desc.K13.whereOf Zp := rfl

include h

/-- At the sending of W, number 356. -/
theorem fHead_keeps_w :
    ∀ blk, cF.blocksInOrder[356]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind
        blk.place s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, b, b', w, e3, hbl, hw, eb, hla⟩ := IM.back_of O
  obtain ⟨hfr, h352⟩ := IM.links_flat_352 h.scope h.reads O
  have hf := IM.back_at_flat e3
  rw [hfr, h352] at hf
  have hf' : cF.blocksInOrder[356]? = some { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := hf
  obtain rfl := Option.some.inj (hf'.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  have d0 : b.decide s rs gs = .ok s' := d
  obtain ⟨d', hm⟩ := IM.alone_noMark hla d0
  have hL : VerifiableInference.Desc.K13.lot4 Zp ∈ ProofFile.onlineFirstChainBlockTables Zp := by
    unfold ProofFile.onlineFirstChainBlockTables
    simp
  have hp' : b'.place = { chain := 1, link := none, piece := 4, kind := .K1 } := by
    rw [eb]
    unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
    rfl
  obtain ⟨m, rs₂, gs₂, k1, k2⟩ := ProofFile.Honest.K1.k1_send_half ⟨_, hL, hbl⟩ hp' d'
  have hpl : b.place = { chain := 1, link := none, piece := 4, kind := .K1 } := by
    have e : b = IM.seatedAs ProofFile.sameReply b' b.name (IM.bAt 3 .K1) := hla
    rw [e]
    rfl
  show fHead Zp cF G take P11 p12 (VerifiableInference.Desc.K13.whereOf Zp) b.place.kind
    b.place s s'
  rw [hpl]
  exact (fHead_K1_send Zp cF G take P11 p12 (VerifiableInference.Desc.K13.whereOf Zp)
    (p := { chain := 1, link := none, piece := 4, kind := .K1 }) rfl rfl s s').2
    ⟨⟨m, k1, VerifiableInference.Desc.K13.Honest.rowsB_rowsKeeps k2⟩, hm⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_P13
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_w
