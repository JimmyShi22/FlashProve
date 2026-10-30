-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFramesN.lean: the gathering `owesS_framesH`
(GatherFramesH.lean) with weaker hypotheses on the item `carry m`. No definition.

  `owesS_framesN`   `OwesS` (Honest/Thread/PaysS.lean) at the first chain's invariant at the full
     size, at `keeps` := `kpBy fHeadH`

What changes against `owesS_framesH`.
  * `hcarry`: there, the parameter `carryX` was asked to pass along `keeps` at all 77 sub-protocols
    of the kind `frame`. Here `carry m` is asked to pass (`RidesPastAt`) at those alone at which the
    lemmas on the frame use it: not at the 25 after the batching. The lemmas are the second forms
    `frame_all_frontN` to `frame_all_sealN` (Honest/Law/NoHouse/FrameAllN.lean) and `frame_cellsSN`
    (FrameCellsN.lean).
  * `hcar`: there, `carry m` was asked to pass over the places of the kinds K7 and K9. Here K9 is
    proved by `cell_carry_k9` (CarryShut.lean) from `hX`: `carryX m` reads of the verifier's state
    no more than the library's `doorZ Zp m` does. K7 stays a hypothesis (`hcar7`).

Where this comes from. The statement and the proof are those of `owesS_framesH` but for these two
hypotheses and the names of the lemmas called; the lines stand a third time here.

Limits.
  * `hcarry`, `hX`, `hcar7` and `hwor` (`worth m k r` at K11) are hypotheses. All other hypotheses
    are those of `owesS_framesH`: what the prover's sides play and exchange, and the riders, are
    proved here of no prover.
  * Nothing here shows that the invariant holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFramesH
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameAllN
import Johnson.Desc.ProofFile.Honest.Thread.CarryShut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.LinkJoin (hearN)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size**, at `keeps` := `fHeadH`: `carry m`
is asked at the sub-protocols of the kind `frame` only where it is used, at K9 through `hX`, and at
K7 as it was. -/
theorem owesS_framesN (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hL₀ : L₀ = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp))) w)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt L₀.thread b (Item.carry m))
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
    (hX : ∀ (m : Nat) (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF),
      doorZ Zp m s' = doorZ Zp m s → carryX m (z, s) y v → carryX m (z, s') y' v)
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread SaidOk b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread SaidOk b (Item.worth m k ρ)) : OwesS L.thread SaidOk := by
  subst hL
  subst hL₀
  have a0 := frame_all_frontN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry
  have aL := fun l (hl : l < 25) =>
    frame_all_laidN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
  have aB := fun l (hl : l < 25) =>
    frame_all_behindN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
      (htst l hl)
  have aC := fun l (hl : l < 25) =>
    frame_all_clearedN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
      (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry hl
  have aS := frame_all_sealN h H Q test carryX item n₁ n₂ b₀ Vd ν st R
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp)) w rfl rfl noHalf hb₀ hcarry
  have hlen : ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.bs.length → b < 358 := by
    intro b hb
    have hb' : b < cF.blocksInOrder.length := hb
    rw [head_len h] at hb'
    exact hb'
  have eC : ∀ l, 14 * l + IM.nAt l + 7 = P1L20.clearIx l := by
    intro l
    have e' := clearIx_is l
    omega
  refine owesS_fHeadH h H Q test carryX item n₁ n₂ b₀ Vd w hB hσ rfl ?_ ?_ ?_
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
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
          (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' hk))) SaidOk
        (frame_cellsSN h H Q test carryX item n₁ n₂ b₀ Vd _ _ w SaidOk rfl hcarry b p i hp hk
          hr)
    · exact head_hok h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk
        (fun b p m hp e hi h1 => e.elim (fun e7 => hcar7 b p m hp e7 hi h1) fun e9 =>
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk
            (cell_carry_k9 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk hX
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e9 hi h1))
        hwor
        (fun b p m k ρ hp e hi h1 =>
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk
            (cell_forms_k11 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ hB
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e hi h1))
        b p i hp hk hi h1 h2 hr

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_framesN
