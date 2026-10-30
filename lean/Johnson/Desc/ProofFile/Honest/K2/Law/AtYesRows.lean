-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AtYesRows.lean: the kind "the code switch" (K2): TWO MORE OF
THE TWENTY-ONE FIELDS OF THE RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), EACH
IN ITS OWN TEXT: carriedNo · positionNo: what the table's numbers say of the rows of the classes
"carried" and "position" at a switch's link, at a yes of the kind's own decision, at a switch of the
plan, at a reached state, under the library's head and the opening. ON THE VERIFIER's STATE AT A
YES: numbers, shapes, counts of stored sample rows: no tests on the public files. That file is not
imported. No definition; nothing is evaluated here. Lemmas: calls; none of the library's goals.

  `poss_at_switch`  the table's count of positions at the switch's link is the plan's number
  `both_at_switch`  the two invariants on stored sample rows hold at the front's statement
  `one_stored_at_switch`   so each kept old message has just one stored sample row
  `rows_at_yes`     THE TWO FIELDS

By. Of other authors, in the library: `rows_debts` (Johnson/Top/H0/Tw/K2C/RowsDebts.lean): the two
equations, from five facts · `hone_of_both` (K2C/OneStored.lean) · `both_at_front`
(K2C/DebtsState.lean) · `possAt_found` (K2C/PossAtK2.lean) · `yesPositions` (K2C/Closed.lean) ·
`one_answer_of_test`, `keptTyped_at`, `way_tables` (Johnson/Top/H0/K2Caller/OneAnswer.lean,
KeptTypedFull.lean, FrontSide.lean) · `front_len` (Johnson/IMR/RootsWhole.lean) · `places_nodup`
(Johnson/IMR/BorderW.lean) · `AtMg.seats_written` (Johnson/HB/LLHARD/MaskSeatWritten.lean). Under
Johnson/P1K2R/: `both_at_open`, `closed_at` (FoldSide.lean) · `swBlock_link`, `swBlock_head`,
`swBlock_fin`, `find_by_place`, `findW_at`, `hps_scope`, `keptLen_at` (DebtsConst.lean). Beside the
library: `front_test_at_reach`, `front_pin_at_fold` (SizesAtYes.lean of this folder) ·
`request_at_head` (AtYesTarget.lean) · `placeLinksW` (AtYesMore.lean) · `link_bounds`
(AtYesFits.lean) · `SwitchArm` (BlockAtHead.lean). Near: `d_link_const`, `d_head_const`,
`d_finish_const` (DebtsConst.lean) have the two equations inside larger records, at the plan's
number of positions in the place of the count of those drawn, under a fence on the states, the
table's own test on the state, a laying of trees that returns, and one test more on the numbers
(`sentFitB`: Johnson/Top/H0/K2Ties/SentFitAt.lean has it at the head's numbers); none of the four is
wanted here.

Limits. No coin, input or run occurs in a statement; each stands behind a yes and reads the
verifier's state there. `AtYes`, the kind's own yes (hy) and hr (THE STATE IS REACHED OVER THE
MEMBERS UNDER `below`) ARE PREMISES. The head and the opening are premises. "One stored sample row a
kept message" holds because the parameter file says "answers 1", which the goals' scope holds fixed
(the head of RowsDebts.lean tells it). That the two texts are the record's is held by no theorem
here. It speaks at the head's own size and hash: the full size, the format's second hash function. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesFits
import Johnson.P1K2R.DebtsConst
import Johnson.P1K2R.FoldSide
import Johnson.Top.H0.Tw.K2C.RowsDebts
import Johnson.Top.H0.Tw.K2C.OneStored
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.K2Caller.OneAnswer
import Johnson.Top.H0.K2Caller.KeptTypedFull
import Johnson.Top.H0.K2Caller.FrontSide
import Johnson.IMR.RootsWhole
import Johnson.HB.LLHARD.MaskSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First (S possAt)
open VerifiableInference.Desc.First.K2 (P2 AtYes frontAt frameAt keptSamples targetRows decideWith
  SampleGoodS AnsweredStored both_at_front hone_of_both rows_debts possAt_found yesPositions)
open VerifiableInference.Desc.First.K2Caller (one_answer_of_test keptTyped_at way_tables)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {Pp : P1K2.Prep} {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
  {after : TS → TS → Except String TS} {z₀ : ProofFile.InstPub} {s s₁ t u : TS} {r₁ r₂ : Fmt.RoundView}
  {gs gs' : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
  {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}

/-- **The table's count of positions at the switch's link is the plan's number.** -/
theorem poss_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) (hA : SwitchArm Zp Bs.G₀ p st before after) :
    possAt cF.blocksInOrder P5J.At.links.length p.link = n.positions := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hpW)
  have h25 : P5J.At.links.length = 25 := rfl
  rw [h25]
  rcases hA with ⟨-, ep, h1, h24, -⟩ | ⟨-, ep, -⟩ | ⟨-, ep, -⟩
  · obtain ⟨b, hb, H⟩ := P1K2.swBlock_link h.scope h.reads O h.laid.planOk h1 h24
    rw [ep] at hn
    rw [← (H Pp n hP hn).2]
    exact possAt_found (P1K2.find_by_place (P1K2.hps_scope h.scope h.reads O) IM.places_nodup hb
      ((P1K2.findW_at h1 (by omega)).trans (by rw [P1K2.swNo_link (by omega)])))
  · have e24 : p.link = 24 := by
      rw [hlk, ep]
      rfl
    obtain ⟨b, hb, H⟩ := P1K2.swBlock_head h.scope h.reads O h.laid.planOk
    rw [ep] at hn
    rw [e24, ← (H Pp n hP hn).2]
    exact possAt_found (P1K2.find_by_place (P1K2.hps_scope h.scope h.reads O) IM.places_nodup hb
      ((P1K2.findW_at (g := 24) (by omega) (by omega)).trans (by rw [P1K2.swNo_24])))
  · have e25 : p.link = 25 := by
      rw [hlk, ep]
      rfl
    obtain ⟨b, hb, H⟩ := P1K2.swBlock_fin h.scope h.reads O h.laid.planOk
    rw [ep] at hn
    rw [e25, ← (H Pp n hP hn).2]
    exact possAt_found (P1K2.find_by_place (P1K2.hps_scope h.scope h.reads O) IM.places_nodup hb
      ((P1K2.findW_at (g := 25) (by omega) (by omega)).trans (by rw [P1K2.swNo_25])))

/-- **The two invariants on stored sample rows, at the front's statement.** -/
theorem both_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) :
    SampleGoodS x.st ∧ AnsweredStored x.st := by
  have hk : P5J.At.ps.findIdx (· == p.place) ≤ (Meaning.K2.frontOf cF).length := by
    rw [Meaning.Carry.front_len h.scope h.reads O]
    rcases hA with ⟨-, -, -, h24, ei, -⟩ | ⟨-, -, ei, -⟩ | ⟨-, -, ei, -⟩ <;> omega
  obtain ⟨hG, hAn⟩ := P1K2.both_at_open O h.laid.value h.laid.planOk hk hr
  have hway : ((k2P Zp p.place nm st n).stands ≠ .finish ∧ s₁ = s) ∨
      ((k2P Zp p.place nm st n).stands = .finish ∧ First.K2.finishFrontQ s = .ok s₁) := by
    rcases hA with ⟨rfl, -, -, -, -, rfl, -⟩ | ⟨rfl, -, -, rfl, -⟩ | ⟨rfl, -, -, rfl, -⟩
    · exact Or.inl ⟨fun c => (by cases c), (Except.ok.inj hb).symm⟩
    · exact Or.inl ⟨fun c => (by cases c), (Except.ok.inj hb).symm⟩
    · exact Or.inr ⟨rfl, hb⟩
  obtain ⟨w1, w2⟩ := way_tables hway
  exact both_at_front hx w1 w2 hG hAn

/-- **Each kept old message has just one stored sample row.** -/
theorem one_stored_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) {W₀ : SwitchFrame}
    (hW : frameAt x = some W₀) :
    ∀ k ∈ W₀.kept, (x.st.oracles.getD k.old default).sampleRows.size = 1 := by
  obtain ⟨w, W, hw, hWw, ht⟩ := front_test_at_reach h O hp hA hr hb nm hx
  obtain ⟨hG, hAn⟩ := both_at_switch h O hA hr hb nm hx
  exact hone_of_both hG hAn
    (one_answer_of_test ht (keptTyped_at hw) (P1K2.closed_at hw hWw).2 hW)

/-- **THE FIELDS carriedNo AND positionNo OF `MadeAsks`, IN ITS OWN TEXT.** hy: the kind's own
decision says yes at s₁, at the same two rounds. -/
theorem rows_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (hy : decideWith sendByL8 (k2P Zp p.place nm st n) s₁ [r₁, r₂] gs' = .ok u)
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    (∀ W₀, frameAt x = some W₀ →
      (P5J.At.N Zp cF).rowsAt p.link .carried = (0, 1 + keptSamples x W₀)) ∧
    ∀ W₀, frameAt x = some W₀ → (P5J.At.N Zp cF).rowsAt p.link .position =
      (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2)) := by
  obtain ⟨h1, h25⟩ := link_bounds h O hp hA
  obtain ⟨-, R, C, hf⟩ := (reach_raw hr).fold
  obtain ⟨-, f2, -, -⟩ := front_pin_at_fold h O hp hA hf hb nm A.front
  have hpos : possAt cF.blocksInOrder P5J.At.links.length p.link = r₂.drawn.poss.length :=
    (poss_at_switch h O hp hP hn hA).trans (yesPositions _ _ _ _ _ _ _ hy).symm
  have hkept : (P5T.numbersOf (P5J.At.pseats Zp)).keptOf = P5T.N0Full.keptOf :=
    congrArg (·.keptOf) (P5J.AtMg.seats_written h.toAtMg).2.2
  have hlen : ((P5T.numbersOf (P5J.At.pseats Zp)).keptOf (p.link - 1)).length = x.T.kept.size := by
    have q := P1K2.keptLen_at hkept (request_at_head h) (i := p.link - 1) (by omega)
    rw [show p.link - 1 + 1 = p.link by omega] at q
    rw [f2]
    exact q
  have key : ∀ W₀, frameAt x = some W₀ →
      (P5J.At.N Zp cF).rowsAt p.link .carried = (0, 1 + keptSamples x W₀) ∧
      (P5J.At.N Zp cF).rowsAt p.link .position =
        (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2)) :=
    fun W₀ hW => rows_debts (N₀ := P5T.numbersOf (P5J.At.pseats Zp)) (sh := P5J.At.shape Zp)
      (links := P5J.At.links) (bs := cF.blocksInOrder) (by omega) hW f2 hpos hlen
      (one_stored_at_switch h O hp hA hr hb nm A.front hW)
  exact ⟨fun W₀ hW => (key W₀ hW).1, fun W₀ hW => (key W₀ hW).2⟩

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.poss_at_switch
#print axioms ProofFile.Honest.K2.Law.both_at_switch
#print axioms ProofFile.Honest.K2.Law.one_stored_at_switch
#print axioms ProofFile.Honest.K2.Law.rows_at_yes
