-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFramesH.lean: the gathering of `OwesS`
(Honest/Thread/PaysS.lean) at the first chain's invariant at the full size, stated anew at `keeps`
:= `kpBy fHeadH` (FHeadH.lean) in the place of `kpBy fHeadG`. With the stronger `keeps` the item
`pile` passes over the sub-protocols of the kinds K2, K7 and K12, so that the hypothesis `hok` of
`owesS_frames` (GatherFrames.lean) comes down to two families of cells. No definition.

  1  `owesS_fHeadH`   `owesS_fHeadG` (FHeadGKeeps.lean) at `fHeadH`. What `fHeadH` asks beyond
     `fHeadG` after a sub-protocol's step is `head_hbook_paid` (PileKeptK2.lean)
  2  `owesS_framesH`   `owesS_frames` at `fHeadH`, with `hok` by `head_hok` (HokFold.lean) and, for
     the items `forms` at K11, `cell_forms_k11` (K11FormsCell.lean)

Where this comes from. Both statements and both proofs are those of `owesS_fHeadG` and
`owesS_frames` with `fHeadH` written for `fHeadG`; the lines stand a second time here. Why it
is stated anew: `keeps` stands on both sides in `OwesS`. A stronger `keeps` makes `RidesPastAtS` and
`StaysBy` easier to prove and `BehindS` harder, so the author has not tried to carry `OwesS` over.

Left as hypotheses of `owesS_framesH`, beside those of `owesS_frames` other than `hok`:
  * `hcar`: `carry m` passes over the places of the kinds K7 and K9 where it is open and not closed;
  * `hwor`: `worth m k r` passes over the place of the kind K11 where it is open and not closed.

Limits.
  * The hypotheses on what the prover's sides play and exchange (`hPhear` to `hX356`) and on the
    riders (`hnx`, `hs`, `hstl`, `hatt`) are those of `owesS_frames`: they are proved here of no
    prover.
  * Nothing here shows that the invariant holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFrames
import Johnson.Desc.ProofFile.Honest.Thread.PileKeptK2
import Johnson.Desc.ProofFile.Honest.Thread.HokFold
import Johnson.Desc.ProofFile.Honest.Thread.K11FormsCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size**, at `csHead` and `fHeadH`. -/
theorem owesS_fHeadH (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread SaidOk b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread SaidOk b c)
    (hX : ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes,
      ExchangeAtS L.thread SaidOk b i)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread SaidOk b i) : OwesS L.thread SaidOk := by
  subst hL
  exact owesS_head_form h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R)
    (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) w SaidOk rfl hP hF
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨fHeadG_hK h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          hA hd hS,
        head_hbook_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ w SaidOk hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩)
    h₀
    (fun b _ c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
        (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' hk)))
      (fHead_hst_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hσ b c hc h1 h2))
    hl hX
    (head_hR_of_cellsF h H Q test carryX item n₁ n₂ b₀ Vd _ _ w SaidOk hok)

/-- **`OwesS` at the first chain's invariant at the full size**, at `keeps` := `fHeadH`, with
nothing left at the 77 sub-protocols of the kind `frame`, and of the column `hR` two families of
cells. -/
theorem owesS_framesH (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
    (hcar : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 ∨ p.kind = KindName.K9 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread SaidOk b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread SaidOk b (Item.worth m k ρ)) : OwesS L.thread SaidOk := by
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
        (frame_cellsS h H Q test carryX item n₁ n₂ b₀ Vd _ _ w SaidOk rfl hcarry b p i hp hk
          hr)
    · exact head_hok h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk hcar hwor
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

#print axioms ProofFile.Honest.FirstThread.owesS_fHeadH
#print axioms ProofFile.Honest.FirstThread.owesS_framesH
