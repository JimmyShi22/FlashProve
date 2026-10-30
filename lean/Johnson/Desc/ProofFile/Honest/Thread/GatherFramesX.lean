-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFramesX.lean: the gathering `owesS_framesN`
(GatherFramesN.lean) at one value of its parameter `carryX`: `carryExact Zp (P5J.At.arr Zp)`
(Johnson/Desc/K2/Honest/Carry/Exact.lean, of other authors). There two of its hypotheses on the item
`carry m` are proved. No definition.

  `owesS_framesX`   `OwesS` (Honest/Thread/PaysS.lean) at the first chain's invariant at the full
     size, at `keeps` := `kpBy fHeadH` and `carryX` := `carryExact Zp (P5J.At.arr Zp)`

What is proved here of `owesS_framesN`'s hypotheses.
  * `hcarry` (`carry m` passes over the sub-protocols of the kind `frame` other than the 25 after
    the batching): `carry_frame_exact_paid` (CarryFramePaid.lean).
  * `hX` (`carryX m` reads of the verifier's state no more than the library's `doorZ Zp m`):
    `carryExact_door` (CarryShut.lean).

Left on the column `hR`: `hcar7` (`carry m` at the place of the kind K7) and `hwor` (`worth m k r`
at the place of the kind K11), each asked where the item is open and not closed.

Limits.
  * All other hypotheses are those of `owesS_framesN`: what the prover's sides play and exchange,
    and the riders, are proved here of no prover.
  * Nothing here shows that the invariant holds at any state of a run, or that `carryExact` holds at
    any state.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFramesN
import Johnson.Desc.ProofFile.Honest.Thread.CarryFramePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size**, at `keeps` := `fHeadH` and
`carryX` := `carryExact Zp (P5J.At.arr Zp)`. -/
theorem owesS_framesX (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread SaidOk (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread SaidOk (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread SaidOk 353) (hP354 : PlaysS L.thread SaidOk 354)
    (hP355 : PlaysS L.thread SaidOk 355) (hP356 : PlaysS L.thread SaidOk 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → ExchangeS L.thread SaidOk (14 * l + i + 2))
    (hXback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      ExchangeS L.thread SaidOk (14 * l + IM.nAt l + j))
    (hX353 : ExchangeS L.thread SaidOk 353) (hX354 : ExchangeS L.thread SaidOk 354)
    (hX355 : ExchangeS L.thread SaidOk 355) (hX356 : ExchangeS L.thread SaidOk 356)
    (hnx : LaysAtS L.thread SaidOk 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread SaidOk 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread SaidOk (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread SaidOk (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread SaidOk b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread SaidOk b (Item.worth m k ρ)) : OwesS L.thread SaidOk :=
  owesS_framesN h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd w hB hσ hb₀ noHalf hhalf
    hL rfl (carry_frame_exact_paid h H Q test item n₁ n₂ b₀ Vd _ _ w rfl)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt (carryExact_door Zp (P5J.At.arr Zp)) hcar7 hwor

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_framesX
