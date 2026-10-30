-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFramesS.lean: the gathering `owesS_framesX`
(GatherFramesX.lean) once more, general in the family `Said` (Honest/Thread/Said.lean): at every
`Said` that implies `SaidOk` (Honest/Thread/SaidOk.lean). No definition.

  `owesS_fHeadHS`       `owesS_fHeadH` (GatherFramesH.lean) at such a `Said`
  `owesS_framesNS`      `owesS_framesN` (GatherFramesN.lean) at such a `Said`
  `owesS_framesS`       `owesS_framesX` at such a `Said`
  `owesS_framesX_of_S`  the statement of `owesS_framesX`, sign for sign, by one call of
     `owesS_framesS` at `Said` := `SaidOk`: so the new lemma is no weaker than the old one

Why. In `PlaysS`, `BehindS`, `ExchangeS` and `RidesPastS` (Honest/Thread/PaysS.lean) the family
stands in one place: inside `ThrS`, among the hypotheses. So each of them, proved at `Said`, holds
at every family that implies `Said` (Honest/Thread/SaidMono.lean), and not the other way round. Some
authors prove `PlaysS` for their sub-protocols at a family other than `SaidOk`. Such a lemma does
not fit the hypotheses of `owesS_framesX`. It fits those of `owesS_framesS` at the conjunction of
the two families.

How. The proofs are those of the three older lemmas. Some of the lemmas that they call are stated at
`SaidOk` alone, and these calls stay at `SaidOk`. What the five families at the kind `frame`
(Honest/Law/NoHouse/FrameAllN.lean) give of `PlaysS` and `ExchangeS`, and the result of
`cell_forms_k11` (K11FormsCell.lean), are carried to `Said` by `playsS_mono`, `exchangeS_mono` and
`ridesPastAtS_mono`. `head_hF_ok` (FormBehindAll.lean) gives the column `hF` at `SaidOk`, and
`fHeadG_hK` (FHeadGKeeps.lean) takes it there: each is used at a state at which `ThrS` holds at
`Said`, which `thrS_mono` carries to `SaidOk`. All other lemmas that are called are general in the
family.

The hypothesis `hF` of `owesS_fHeadHS` is asked at `SaidOk`, not at `Said`: `fHeadG_hK` needs it
there. `owesS_framesNS` proves it there, as `owesS_framesN` does.

Limits.
  * The hypotheses are those of the older lemmas, asked at `Said`, and `hSaid`. What the prover's
    sides play and exchange, and the riders, are proved here of no prover.
  * `OwesS` alone. `SaidNext` (Honest/Thread/Said.lean) has the family in its conclusion too: a
    family that says more makes that hypothesis harder. Nothing on it is proved here.
  * Nothing here shows that the invariant holds at any state of a run, or that `carryExact` holds at
    any state.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFramesX
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.LinkJoin (hearN)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- `owesS_fHeadH` at a family that implies `SaidOk`. The column `hF` is asked at `SaidOk`. -/
theorem owesS_fHeadHS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread Said b c)
    (hX : ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes,
      ExchangeAtS L.thread Said b i)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread Said b i) : OwesS L.thread Said := by
  subst hL
  exact owesS_head_form h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R)
    (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) w Said rfl hP
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      hF b hb blk hblk k s m E ds y cols s' (thrS_mono _ hSaid hA) hd hS)
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨fHeadG_hK h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          (thrS_mono _ hSaid hA) hd hS,
        head_hbook_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩)
    h₀
    (fun b _ c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
        (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' hk)))
      (fHead_hst_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hσ b c hc h1 h2))
    hl hX
    (head_hR_of_cellsF h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hok)

/-- `owesS_framesN` at a family that implies `SaidOk`. -/
theorem owesS_framesNS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
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
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → ExchangeS L.thread Said (14 * l + i + 2))
    (hXback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      ExchangeS L.thread Said (14 * l + IM.nAt l + j))
    (hX353 : ExchangeS L.thread Said 353) (hX354 : ExchangeS L.thread Said 354)
    (hX355 : ExchangeS L.thread Said 355) (hX356 : ExchangeS L.thread Said 356)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hX : ∀ (m : Nat) (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF),
      doorZ Zp m s' = doorZ Zp m s → carryX m (z, s) y v → carryX m (z, s') y' v)
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.worth m k ρ)) : OwesS L.thread Said := by
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
  refine owesS_fHeadHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hB hσ rfl ?_ ?_ ?_
    (fun b _ c hc he => fHead_hl h H Q test carryX item n₁ n₂ b₀ Vd ν st R _ w Said hB
      hnx hs hstl hatt b c hc he) ?_ ?_
  · intro b hb
    exact all_but_frames _
      (playsS_mono _ hSaid (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk a0.1))
      (fun l hl => playsS_mono _ hSaid
        (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aL l hl).1))
      (fun l hl => playsS_mono _ hSaid
        (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aB l hl).1))
      (fun l hl => playsS_mono _ hSaid
        (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aC l hl).1))
      (playsS_mono _ hSaid (head_playsS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk aS.1))
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
  · exact head_h0 h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hb₀ Said hhalf
  · intro b hb
    exact (exchangeS_iff _ _).1 (all_but_frames _
      (exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk a0.2.2.1))
      (fun l hl => exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aL l hl).2.2.1))
      (fun l hl => exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aB l hl).2.2.1))
      (fun l hl => exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk (aC l hl).2.2.1))
      (exchangeS_mono _ hSaid
        (head_exchangeS_kp h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ SaidOk aS.2.2.1))
      hXhear hXback hX353 hX354 hX355 hX356 b (hlen b hb))
  · intro b p i hp hi h1 h2 hr
    by_cases hk : p.kind = KindName.frame
    · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
          (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' hk))) Said
        (frame_cellsSN h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said rfl hcarry b p i hp hk
          hr)
    · exact head_hok h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (fun b p m hp e hi h1 => e.elim (fun e7 => hcar7 b p m hp e7 hi h1) fun e9 =>
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
            (cell_carry_k9 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said hX
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e9 hi h1))
        hwor
        (fun b p m k ρ hp e hi h1 => ridesPastAtS_mono _ hSaid <|
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk
            (cell_forms_k11 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ hB
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e hi h1))
        b p i hp hk hi h1 h2 hr

/-- **`OwesS` at the first chain's invariant at the full size**, at `keeps` := `fHeadH`,
`carryX` := `carryExact Zp (P5J.At.arr Zp)` and every family that implies `SaidOk`. -/
theorem owesS_framesS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
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
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → ExchangeS L.thread Said (14 * l + i + 2))
    (hXback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      ExchangeS L.thread Said (14 * l + IM.nAt l + j))
    (hX353 : ExchangeS L.thread Said 353) (hX354 : ExchangeS L.thread Said 354)
    (hX355 : ExchangeS L.thread Said 355) (hX356 : ExchangeS L.thread Said 356)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hcar7 : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 →
      Item.carry m ∈ L.thread.opened b → Item.carry m ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ L.thread.opened b → Item.worth m k ρ ∉ (L.thread.row b).shuts →
      RidesPastAtS L.thread Said b (Item.worth m k ρ)) : OwesS L.thread Said :=
  owesS_framesNS h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀
    noHalf hhalf
    hL rfl (carry_frame_exact_paid h H Q test item n₁ n₂ b₀ Vd _ _ w rfl)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt (carryExact_door Zp (P5J.At.arr Zp)) hcar7 hwor

/-- The statement of `owesS_framesX`, by one call of `owesS_framesS`. -/
theorem owesS_framesX_of_S (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
  owesS_framesS h H Q test item n₁ n₂ b₀ Vd w SaidOk (fun _ _ _ e => e) hB hσ hb₀ noHalf hhalf hL
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt hcar7 hwor

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_fHeadHS
#print axioms ProofFile.Honest.FirstThread.owesS_framesNS
#print axioms ProofFile.Honest.FirstThread.owesS_framesS
#print axioms ProofFile.Honest.FirstThread.owesS_framesX_of_S
