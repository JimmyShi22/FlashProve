-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFrames.lean: the hypothesis `OwesS` (PaysS.lean) of the
rule for a whole file, at the first chain's invariant at the full size, with more of its columns
brought down to smaller hypotheses than in `owesS_fHeadG` (FHeadGKeeps.lean). The condition `keeps`
is `fHeadG` (FHeadG.lean). What is said before the chain is `SaidOk` (SaidOk.lean), and the border
from which the reply is held is 339. The 77 sub-protocols of the kind `frame` ask nothing any more
in the columns `hP`, `hF`, `hX` and `hR`: `frame_all_front` and its four fellows
(Law/NoHouse/FrameAll.lean) and `frame_cellsS` (Law/NoHouse/FrameCells.lean) prove them at `fHead`,
and KeepsFree.lean, KeepsMono.lean and FormShare.lean carry them over to `fHeadG`. The column `h₀`
comes from `head_h0` (HeadReply.lean). The column `hF` comes from `head_hF_ok` (FormBehindAll.lean).
No definition.

  1  `all_but_frames`   a statement at the five families of the kind `frame` and at the other nine
     families holds at every number below 358
  2  `owesS_frames`   the lemma

What `owesS_frames` leaves as hypotheses.
  * `hP…`, `hX…`: `PlaysS` and `ExchangeS` at the 281 numbers that are not of the kind `frame`.
  * `hnx`, `hs`, `hstl`, `hatt`: the 38 of the 55 clauses of `csHead` that speak of its three
    arguments. `fHead_hl` (FHeadLays.lean) proves the other 17.
  * `hok`: the column `hR` at the places that are not of the kind `frame`.
  * On the prover `H`: `noHalf` (no part of it stands at a place of the kind `frame`) and `hhalf`
    (its part at K7's place is the kind's own).
  * On arguments of the invariant whose text is not laid yet: `hcarry` (on `carryX`), `htst` (on
    `test`), `hσ` (on `st`).
  * `hB`: it names what `ProofFile.baseOf` returns at the public part (HeadBase.lean: it does return).

Limits.
  * `OwesS` is the form of a hypothesis of the rule. Nothing here shows that a run accepts.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadGKeeps
import Johnson.Desc.ProofFile.Honest.Thread.HeadReply
import Johnson.Desc.ProofFile.Honest.Thread.FormBehindAll
import Johnson.Desc.ProofFile.Honest.Thread.KeepsFree
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameAll
import Johnson.Desc.ProofFile.Honest.Thread.FHeadLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- A statement at the five families of the kind `frame` and at the other nine families holds at
every number below 358. -/
theorem all_but_frames (P : Nat → Prop) (hfront : P 0) (hlaid : ∀ l, l < 25 → P (14 * l + 1))
    (hbehind : ∀ l, l < 25 → P (14 * l + IM.nAt l + 3))
    (hcleared : ∀ l, l < 25 → P (P1L20.clearIx l)) (hseal : P 357)
    (hhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → P (14 * l + i + 2))
    (hback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 → P (14 * l + IM.nAt l + j))
    (h353 : P 353) (h354 : P 354) (h355 : P 355) (h356 : P 356) : ∀ b, b < 358 → P b := by
  refine all_numbers P hfront hlaid hhear ?_ h353 h354 h355 h356 hseal
  intro l hl j j2 j7
  have hc : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hback l hl 2 (Or.inl rfl)
  · exact hbehind l hl
  · exact hback l hl 4 (Or.inr (Or.inl rfl))
  · exact hback l hl 5 (Or.inr (Or.inr (Or.inl rfl)))
  · exact hback l hl 6 (Or.inr (Or.inr (Or.inr rfl)))
  · have e : 14 * l + IM.nAt l + 7 = P1L20.clearIx l := by
      have e' := clearIx_is l
      omega
    rw [e]
    exact hcleared l hl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size**, with nothing left at the 77
sub-protocols of the kind `frame`. -/
theorem owesS_frames (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L L₀ : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadG Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hL₀ : L₀ = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp))) w)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      L₀.thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
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
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → p.kind ≠ KindName.frame → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread SaidOk b i) : OwesS L.thread SaidOk := by
  subst hL
  subst hL₀
  have a0 := frame_all_front h H Q test carryX item n₁ n₂ b₀ Vd ν st R
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry
  have aL := fun l (hl : l < 25) =>
    frame_all_laid h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
  have aB := fun l (hl : l < 25) =>
    frame_all_behind h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
      (htst l hl)
  have aC := fun l (hl : l < 25) =>
    frame_all_cleared h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
  have aS := frame_all_seal h H Q test carryX item n₁ n₂ b₀ Vd ν st R
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry
  have hlen : ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadG Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.bs.length → b < 358 := by
    intro b hb
    have hb' : b < cF.blocksInOrder.length := hb
    rw [head_len h] at hb'
    exact hb'
  have eC : ∀ l, 14 * l + IM.nAt l + 7 = P1L20.clearIx l := by
    intro l
    have e' := clearIx_is l
    omega
  refine owesS_fHeadG h H Q test carryX item n₁ n₂ b₀ Vd w hB hσ rfl ?_ ?_ ?_
    (fun b _ c hc he => fHead_hl h H Q test carryX item n₁ n₂ b₀ Vd ν st R _ w SaidOk hB
      hnx hs hstl hatt b c hc he) ?_ ?_
  · intro b hb
    exact all_but_frames _ (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk a0.1)
      (fun l hl => head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aL l hl).1)
      (fun l hl => head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aB l hl).1)
      (fun l hl => head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aC l hl).1)
      (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk aS.1)
      hPhear hPback hP353 hP354 hP355 hP356 b (hlen b hb)
  · exact formBehind_column.1 (head_hF_ok h H Q test carryX item n₁ n₂ b₀ Vd _ _ w
      (head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS a0.2.1))
      (fun l hl => head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS (aL l hl).2.1))
      (fun l hl => head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS (aB l hl).2.1))
      (fun l hl => by
        rw [eC l]
        exact head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
          (formBehindAtS_of_behindS (aC l hl).2.1))
      (head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk
        (formBehindAtS_of_behindS aS.2.1)))
  · exact head_h0 h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hb₀ SaidOk hhalf
  · intro b hb
    exact (exchangeS_iff _ _).1 (all_but_frames _
      (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk a0.2.2.1)
      (fun l hl =>
        head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aL l hl).2.2.1)
      (fun l hl =>
        head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aB l hl).2.2.1)
      (fun l hl =>
        head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aC l hl).2.2.1)
      (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk aS.2.2.1)
      hXhear hXback hX353 hX354 hX355 hX356 b (hlen b hb))
  · intro b p i hp hi h1 h2 hr
    by_cases hk : p.kind = KindName.frame
    · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) SaidOk
        (frame_cellsS h H Q test carryX item n₁ n₂ b₀ Vd _ _ w SaidOk rfl hcarry b p i hp hk
          hr)
    · exact hok b p i hp hk hi h1 h2 hr

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.all_but_frames
#print axioms ProofFile.Honest.FirstThread.owesS_frames
