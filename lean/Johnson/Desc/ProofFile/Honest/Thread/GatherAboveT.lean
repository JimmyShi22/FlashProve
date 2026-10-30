-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherAboveT.lean: the gathering `owesS_framesT`
(GatherFramesT.lean) once more, for every condition `keeps` := `kpBy f` that implies `kpBy fHeadH`
and holds after every accepted step; and at `fHeadI` (FHeadI.lean), where the column `hR` has no
hypothesis of its own left. No definition.

  1  `exchangeS_of_newF`, `behindS_aboveHS`, `owesS_aboveHT`, `owesS_aboveNT`, `owesS_aboveT`   the
     five lemmas `exchangeS_of_new`, `behindS_fHeadHS`, `owesS_fHeadHT`, `owesS_framesNT`,
     `owesS_framesT` of GatherFramesT.lean with `kpBy f` in the place of `kpBy fHeadH`, under `hle`
     (`kpBy f` implies `kpBy fHeadH`) and `hKf` (the column `hK` of the gathering at `f`)
  2  `owesS_framesT_of_above`   a control: the statement of `owesS_framesT`, by one call at
     `f := fHeadH`
  3  `owesS_framesI`   **the statement of `owesS_framesT` at `fHeadI`, without its two hypotheses
     `hcar7` and `hwor`.** They are proved by `cell_carry_k7_exact` (K7CarryCell.lean) and
     `cell_worth_k11` (K11WorthCell.lean)

The form of `hKf`. In `behindS_aboveHS` and `owesS_aboveHT` it is the column itself. In
`owesS_aboveNT` and `owesS_aboveT` it has the column `hF` (the forms after a step, at `SaidOk`) as a
hypothesis in front: these two lemmas prove `hF` inside, and `fHeadG_hK`, which pays a part of `hK`
at `fHeadH` and `fHeadI`, takes `hF`.

How it was made. The statements and proofs under 1 are those of GatherFramesT.lean, changed by a
program: the places with `kpBy fHeadH`; the binders `f`, `hle`, `hKf`; `hle` at the end of each
chain of implications; a lift by `head_ridesPastAtS_mono` (KeepsMono.lean) around each call of
`cellH_of_G`; the names of the lemmas called. So these proofs stand twice in the library.

Limits.
  * Those of GatherFramesT.lean. All other hypotheses of `owesS_framesI` are those of
    `owesS_framesT`: what the prover's sides play and exchange at the 281 sub-protocols of a kind
    other than `frame`, the four hypotheses on the riders, and the rest. They are proved here of no
    prover.
  * Sixteen of the 23 named hypotheses of `owesS_framesI` are shares of its own end: the six on
    `PlaysS` and the six on `ExchangeAtS` at the 281 sub-protocols, and the four on `LaysAtS`, which
    are clauses of the end of `BehindS` at 37 numbers (345, 14 l + 8 and 14 (2 g + 1) + 3). `hσ`
    says that one such clause stays past number 346. Of the four parts of `OwesS` only `RidesPastS`
    has no hypothesis of its own.
  * The end and these sixteen are implications from the invariant `ThrS`. Where `Vd`, `Said`, the
    argument of type `Script`, `Bk` or `H.first` are chosen so that no state meets `ThrS`, or so
    that `chainSteps` refuses, the end and these sixteen are true and say nothing.
    `file_owed_hands` (Honest/Thread/Hands.lean) asks at the same arguments that the invariant holds
    at the first border.
  * `OwesS` does not say that a side stands at a place, nor that a step accepts what was played.
  * Two arguments are idle: `srcAt` (Honest/Thread/Thr.lean) does not read `n₂` at the first chain,
    and `replyHalf` (Honest/K7.lean) does not read `Vh`.
  * The share of `ExchangeS` at the item `pinW` is proved here through `cell_pinW`
    (Honest/Thread/CellsByKindC.lean), which is `ridesPastAt_pinW` (Honest/Thread/HeadPinW.lean);
    its proof returns its hypothesis unchanged: at these parameters the decoder of the stored table
    is a constant, so the item says nothing about the stored table, nor about the committed weights:
    it is no step toward correctness of extraction.
  * Nothing here shows that the invariant holds at any state of a run, or that `carryExact` or an
    item `worth` holds at any state.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFramesT
import Johnson.Desc.ProofFile.Honest.Thread.GatherAboveH
import Johnson.Desc.ProofFile.Honest.Thread.HokFoldF
import Johnson.Desc.ProofFile.Honest.Thread.K7CarryCell
import Johnson.Desc.ProofFile.Honest.Thread.K11WorthCell

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
open P5J (AtMgA CellsM TS F0T parts4)

/-! ## 1 The exchange at a sub-protocol of a kind other than `frame` -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- `exchangeS_of_new` (GatherFramesT.lean) at every `keeps` that implies `kpBy fHeadH`. -/
theorem exchangeS_of_newF (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD) p s s') {b : Nat}
    (hh : ∃ p, P5J.At.ps[b]? = some p ∧ p.kind ≠ KindName.frame)
    (hB : ∀ c, c < 358 → BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said c)
    (hX : ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said b j) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said b := by
  obtain ⟨p, hp, hk⟩ := hh
  have up : ∀ {b : Nat} {i : Item},
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b i →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy f) w).thread Said b i :=
    fun hc => head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w (kpBy f) hle Said hc
  have hb : b < 358 := by
    have e := (List.getElem?_eq_some_iff.1 hp).1
    have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
    rw [← e', IM.places_len] at e
    exact e
  refine (exchangeS_iff _ _).2 fun (j : Item) hj => ?_
  by_cases ho : j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.opened b
  · cases j with
    | pin m t =>
      exact exchangeAtS_again _ Said ho (hB b hb)
        (up (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
          (cell_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk m t)))
    | pinI =>
      exact exchangeAtS_again _ Said ho (hB b hb)
        (up (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
          (cell_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk)))
    | pinW =>
      exact exchangeAtS_again _ Said ho (hB b hb)
        (up (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
          (cell_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b)))
    | constr m q =>
      by_cases hq : q ∈ parts4
      · exact exchangeAtS_again _ Said ho (hB b hb)
          (up (cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
            (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m hq)))
      · exact hX _ hj fun _ => ⟨(fun _ _ e => nomatch e), (fun e => nomatch e),
          (fun e => nomatch e), (fun _ _ hq' e => hq (by cases e; exact hq'))⟩
    | _ =>
      exact hX _ hj fun _ => ⟨(fun _ _ e => nomatch e), (fun e => nomatch e),
        (fun e => nomatch e), (fun _ _ _ e => nomatch e)⟩
  · exact hX j hj fun ho' => absurd ho' ho

end

/-! ## 2 The gathering -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- `behindS_fHeadHS` at every `keeps` that implies `kpBy fHeadH` and holds after every accepted
step. -/
theorem behindS_aboveHS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase}
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) p s s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy f) w)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (hKf : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      f blk.place.kind blk.place s s')
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread Said b c) :
    ∀ b, b < L.thread.bs.length → BehindS L.thread Said b := by
  subst hL
  intro b hb
  exact behindS_of_keeps_and _ Said
    (R₀ := fun c v s => b₀ ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R)
      (kpBy f) w)
    (fun blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨hF b hb blk hblk k s m E ds y cols s' (thrS_mono _ hSaid hA) hd hS,
        (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
          f w hblk rfl s s').2
          (hKf b hb blk hblk k s m E ds y cols s' hA hd hS)⟩)
    (h₀ b hb)
    (fun c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
        (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' (hle p s s' hk))))
      (fHead_hst_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hσ b c hc h1 h2))
    (hl b hb)

/-- `owesS_fHeadHT` at every such `keeps`. -/
theorem owesS_aboveHT (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase}
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) p s s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy f) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (hKf : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      f blk.place.kind blk.place s s')
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread Said b c)
    (hX : (∀ c, c < L.thread.bs.length → BehindS L.thread Said c) →
      ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes, ExchangeAtS L.thread Said b i)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread Said b i) : OwesS L.thread Said :=
  owesS_aboveHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hσ f hle hL hP hF hKf h₀ hl
    (hX (behindS_aboveHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hσ f hle hL hF hKf h₀
      hl))
    hok

/-- `owesS_framesNT` at every such `keeps`. `hKf` has the column `hF` as a hypothesis in front. -/
theorem owesS_aboveNT (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
    (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) p s s')
    {L L₀ : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy f) w)
    (hL₀ : L₀ = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp))) w)
    (hKf : (∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk →
        ∀ k s m E ds y cols s', ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
        L.thread.Stepped blk k s m E ds y cols s' → L.thread.Form (b + 1) k s' y.2) →
      ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      f blk.place.kind blk.place s s')
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
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
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
      (kpBy f) w).thread.bs.length → b < 358 := by
    intro b hb
    have hb' : b < cF.blocksInOrder.length := hb
    rw [head_len h] at hb'
    exact hb'
  have hlen' : ∀ b, b < 358 → b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy f) w).thread.bs.length := by
    intro b hb
    show b < cF.blocksInOrder.length
    rw [head_len h]
    exact hb
  have eC : ∀ l, 14 * l + IM.nAt l + 7 = P1L20.clearIx l := by
    intro l
    have e' := clearIx_is l
    omega
  refine owesS_aboveHT h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hσ f hle rfl ?_ ?hF
    (hKf ?hF) ?_
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
  · intro hBe b hb
    have hB' := fun c (hc : c < 358) => hBe c (hlen' c hc)
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
      (fun l hl i hi => exchangeS_of_newF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        f hle
        (house_hear hl hi) hB' (hXhear l hl i hi))
      (fun l hl c hc => exchangeS_of_newF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        f hle
        (house_back hl hc) hB' (hXback l hl c hc))
      (exchangeS_of_newF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        f hle
        (house_tail (by decide)) hB' hX353)
      (exchangeS_of_newF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        f hle
        (house_tail (by decide)) hB' hX354)
      (exchangeS_of_newF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        f hle
        (house_tail (by decide)) hB' hX355)
      (exchangeS_of_newF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        f hle
        (house_tail (by decide)) hB' hX356)
      b (hlen b hb))
  · intro b p i hp hi h1 h2 hr
    by_cases hk : p.kind = KindName.frame
    · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
          (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' (hle p s s' hk)))) Said
        (frame_cellsSN h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said rfl hcarry b p i hp hk
          hr)
    · exact head_hokF h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said f hle
        (fun b p m hp e hi h1 => e.elim (fun e7 => hcar7 b p m hp e7 hi h1) fun e9 =>
          head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ hle Said <|
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
            (cell_carry_k9 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said hX
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e9 hi h1))
        hwor
        (fun b p m k ρ hp e hi h1 => ridesPastAtS_mono _ hSaid <|
          head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _ hle SaidOk <|
          cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ _ SaidOk
            (cell_forms_k11 h H Q test carryX item n₁ n₂ b₀ Vd _ w _ _ _ _ hB
              (by
                have e' := (List.getElem?_eq_some_iff.1 hp).1
                have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
                rw [← eW, IM.places_len] at e'
                exact e') hp e hi h1))
        b p i hp hk hi h1 h2 hr

/-- `owesS_framesT` at every such `keeps`. -/
theorem owesS_aboveT (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
    (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) p s s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy f) w)
    (hKf : (∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk →
        ∀ k s m E ds y cols s', ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
        L.thread.Stepped blk k s m E ds y cols s' → L.thread.Form (b + 1) k s' y.2) →
      ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      f blk.place.kind blk.place s s')
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
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
  owesS_aboveNT h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀
    noHalf hhalf f hle
    hL rfl hKf (carry_frame_exact_paid h H Q test item n₁ n₂ b₀ Vd _ _ w rfl)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt (carryExact_door Zp (P5J.At.arr Zp)) hcar7 hwor

/-- A control: `owesS_framesT` (GatherFramesT.lean), statement for statement. -/
theorem owesS_framesT_of_above (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
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
      RidesPastAtS L.thread Said b (Item.worth m k ρ)) : OwesS L.thread Said := by
  subst hL
  exact owesS_aboveT h H Q test item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀ noHalf hhalf
    (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) (fun _ _ _ hk => hk) rfl
    (fun hF b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨fHeadG_hK h H Q test _ item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          (thrS_mono _ hSaid hA) hd hS,
        head_hbook_paid h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt hcar7 hwor

/-- **`OwesS` at `fHeadI`: `owesS_framesT` without `hcar7` and `hwor`.** -/
theorem owesS_framesI (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
      (kpBy (fHeadI Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g)) :
    OwesS L.thread Said := by
  subst hL
  exact owesS_aboveT h H Q test item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀ noHalf hhalf
    (fHeadI Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) (kpBy_fHeadI _ _ _ _ _ _) rfl
    (fun hF b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨⟨fHeadG_hK h H Q test _ item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          (thrS_mono _ hSaid hA) hd hS,
        head_hbook_paid h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩,
        head_hreply_paid h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt
    (fun b p m hp e hi h1 =>
      cell_carry_k7_exact h H Q test item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (by
          have e' := (List.getElem?_eq_some_iff.1 hp).1
          have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
          rw [← eW, IM.places_len] at e'
          exact e') hp e hi h1)
    (fun b p m k ρ hp e hi h1 =>
      cellI_of_H h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said <|
      cellH_of_G h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said <|
      cell_worth_k11 h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (by
          have e' := (List.getElem?_eq_some_iff.1 hp).1
          have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
          rw [← eW, IM.places_len] at e'
          exact e') hp e hi h1)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.exchangeS_of_newF
#print axioms ProofFile.Honest.FirstThread.behindS_aboveHS
#print axioms ProofFile.Honest.FirstThread.owesS_aboveHT
#print axioms ProofFile.Honest.FirstThread.owesS_aboveNT
#print axioms ProofFile.Honest.FirstThread.owesS_aboveT
#print axioms ProofFile.Honest.FirstThread.owesS_framesT_of_above
#print axioms ProofFile.Honest.FirstThread.owesS_framesI
