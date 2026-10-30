-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SizesAtYes.lean: the kind "the code switch" (K2): AT A YES OF
THE KIND, AT A REACHED STATE, THE SIZES THAT THE LIBRARY READS OFF THE STATEMENT BEHIND THE JOINS
ARE THE PLACE's OWN: `sizesAt` S3 x.f.rows x.T = p.sizes; AND ONE MORE OF THE TWENTY-ONE FIELDS OF
THE RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), IN ITS OWN TEXT: fresh. WHY:
the record's four fields on values speak at `sizesAt` S3 x.f.rows x.T; the honest side's laws speak
at p.sizes. Under the library's head and the opening, at a switch of the plan, at a state REACHED
OVER THE MEMBERS UNDER `below` (the library's device: each member first tests that the words shown
lie below the prime). PUBLIC. That file is not imported. One definition, a public test; one closed
fact by evaluation in Lean's kernel, with a control; lemmas: calls.

  `front_test_at_reach`   the library's test on a switch's front (`frontB2`) says yes at the front
                    that the switch takes off the state, against the written row of the place's
                    link: the three sealed laws `link_pinned_reached`, `head_pinned_reached`,
                    `fin_pinned_reached`, joined over `SwitchArm`
  `placeSizesOk`, `placeSizesW`   A PUBLIC TEST: a written place's sizes are, field by field: the
                    written codes; the written request's two codes' numbers; the kept shapes at the
                    written row's front; the written request's target at the place's link; BY LEAN's
                    KERNEL; A CONTROL: among the places that have a row one link further, against
                    that row it says no somewhere (of the five clauses the kept shapes' alone reads
                    the row)
  `sizes_of_tables`   `sizesAt` reads of a statement its codes and its messages' shapes alone
  `front_pin_at_fold`   the front's codes, target and two codes' numbers, at the place's own link:
                    the sealed `front_pin_link`, `front_pin_head`, `front_pin_fin` joined
  `sizes_at_yes`    THE END
  `fresh_at_yes`    the field fresh

By, sealed, ours: the three named (Johnson/Desc/K2/Honest/Returns/PinReached.lean, PinArms.lean) ·
`keptShapes_pin` (TargetPin.lean) · `AlikeKept.sizes` (AlikeKept.lean) · `tests_at_head`
(UnderHead.lean). Of other authors: `pin_facts`, `facts_of_test`
(Johnson/Top/H0/K2Hands/FrameOne.lean, FrontFacts.lean) · `frontOf_iff`
(Johnson/Top/H0/Tw/K2C/DebtsState.lean) · `AtYes`. Ours, beside the seal: `SwitchArm` · a kin, the
weaker: `target_at_fold` (AtYesTarget.lean: the target at SOME link from 1 to 25, where
`front_pin_at_fold` says: at the place's own) · `placeLinksW` (AtYesMore.lean).

Limits. PUBLIC: no coin, input or run occurs. hr (THE STATE IS REACHED UNDER `below`) IS A PREMISE:
from a thread's stand it is had where what was said lies below the prime (`reach_below`,
Honest/Thread/SaidOk.lean): not called here. `AtYes` is a premise. The full size and the format's
second hash function alone. The head and the opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesMore
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicMoreAtHead
import Johnson.Desc.K2.Honest.Returns.PinArms
import Johnson.Desc.K2.Honest.Returns.TargetPin
import Johnson.Desc.K2.Honest.Returns.AlikeKept
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.Top.H0.K2Hands.FrontFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes SameTables FrontOf frontAt frontOf_iff targetAt
  frameAt n0At oldsAt)
open VerifiableInference.Desc.First.K2Hands (Pinned frontB2 pin_facts facts_of_test)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.K2.Honest (sizesAt)
open VerifiableInference.Desc.K2.Honest.Returns (link_pinned_reached head_pinned_reached
  fin_pinned_reached keptShapes_pin AlikeKept tests_at_head row_at)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt codesFull2)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 At the written constants -/

/-- **A PUBLIC TEST** at a place and a row's number: the place's sizes, field by field. -/
def placeSizesOk (p : SwitchPlace) (i : Nat) : Bool :=
  (tableFullLit[i]?).any fun r =>
    p.sizes.codes == codesFull2 && p.sizes.code == proofSizedFull.request.code &&
      p.sizes.maskCode == proofSizedFull.request.maskCode &&
      p.sizes.kept == (sizesAt (fxAt r).st (fxAt r).f.rows (fxAt r).T).kept &&
      p.sizes.target == targetAt proofSizedFull.request p.link

set_option maxRecDepth 1000000 in
/-- **At the written places, each against the row of its own link**; a control: among the places
that have a row one link further, against that row the test says no somewhere. -/
theorem placeSizesW : (placesW.all fun p => placeSizesOk p (p.link - 1)) = true ∧
    ((placesW.filter fun p => decide (p.link < 25)).all fun p => placeSizesOk p p.link) =
      false := by
  decide +kernel

/-- `sizesAt` reads of a statement its codes and its messages' shapes alone. -/
theorem sizes_of_tables {A B : Statement} (h : SameTables A B) (old : SingleRows)
    (T : SwitchTarget) : sizesAt B old T = sizesAt A old T := by
  unfold sizesAt
  rw [h.codes]
  congr 1
  refine List.map_congr_left fun o _ => ?_
  have e := h.shape o
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases hb : B.oracles[o]? with
  | none =>
    rw [hb] at e
    cases ha : A.oracles[o]? with
    | none => rfl
    | some a =>
      rw [ha] at e
      cases e
  | some b =>
    rw [hb] at e
    cases ha : A.oracles[o]? with
    | none =>
      rw [ha] at e
      cases e
    | some a =>
      rw [ha] at e
      exact Option.some.inj e

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **The library's test on a switch's front says yes**, against the written row of the arm's link.
i + 1: the arm's link. -/
theorem front_test_at_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
    {after : TS → TS → Except String TS} (hA : SwitchArm Zp Bs.G₀ p st before after)
    {z₀ : ProofFile.InstPub} {s s₁ : TS}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String) {x : _root_.Tw.K2.Front}
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) :
    ∃ (w : SwRow) (W : SwitchFrame), tableFullLit[p.link - 1]? = some w ∧
      frameAt (fxAt w) = some W ∧
      frontB2 (fxAt w) W p.link 0 (n0At p.link) (oldsAt p.link) x = true := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hpW)
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h.toAtMg O
  have hF := frontOf_iff.2 hx
  rcases hA with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    obtain ⟨m, hm⟩ : ∃ m, p.link = m + 1 := ⟨p.link - 1, by omega⟩
    rw [ei, hm] at hr
    rcases hF with ⟨-, hf⟩ | ⟨c, -⟩ | ⟨c, -⟩
    · obtain ⟨w, hw⟩ := row_at (m := m) (by omega)
      obtain ⟨W, hW, ht, -⟩ := link_pinned_reached h.scope h.reads O h.laid.value h.laid.planOk hy
        hcut hB (by omega) hr hf hw
      rw [hm]
      exact ⟨w, W, hw, hW, ht⟩
    · cases c
    · cases c
  · obtain rfl : s = s₁ := Except.ok.inj hb
    have e24 : p.link = 24 := by
      rw [hlk, ep]
      rfl
    rw [ei] at hr
    rcases hF with ⟨c, -⟩ | ⟨-, a, Q, here, group, rfl⟩ | ⟨c, -⟩
    · cases c
    · obtain ⟨w, hw⟩ := row_at (m := 23) (by decide)
      obtain ⟨W, hW, ht, -⟩ := head_pinned_reached h.scope h.reads O h.laid.value h.laid.planOk hy
        hcut hB hr here group hw
      rw [e24]
      exact ⟨w, W, hw, hW, ht⟩
    · cases c
  · have e25 : p.link = 25 := by
      rw [hlk, ep]
      rfl
    rw [ei] at hr
    rcases hF with ⟨c, -⟩ | ⟨c, -⟩ | ⟨-, a, Q, here, laid, rfl⟩
    · cases c
    · cases c
    · obtain ⟨w, hw⟩ := row_at (m := 24) (by decide)
      obtain ⟨W, hW, ht, -⟩ := fin_pinned_reached h.scope h.reads O h.laid.value h.laid.planOk hy
        hcut hB hr hb here laid hw
      rw [e25]
      exact ⟨w, W, hw, hW, ht⟩

/-- **The front's codes, target and two codes' numbers are the public part's, at the place's own
link.** -/
theorem front_pin_at_fold (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
    {after : TS → TS → Except String TS} (hA : SwitchArm Zp Bs.G₀ p st before after)
    {z₀ : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {s s₁ : TS}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (P5J.At.ps.findIdx (· == p.place))) (ProofFile.startS Zp z₀) R C =
      .ok (s, [], [])) (hb : before s = .ok s₁) (nm : String) {x : _root_.Tw.K2.Front}
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) :
    x.st.codes = Zp.first.codes ∧ x.T = targetAt Zp.first.shape p.link ∧
      x.f.rows.code = Zp.first.shape.code ∧ x.f.rows.maskCode = Zp.first.shape.maskCode := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hpW)
  rcases hA with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    rw [ei] at hf
    obtain ⟨a1, -, a3, -, -, -, a7, a8, -⟩ :=
      Meaning.K2.front_pin_link h.scope h.reads O h1 h24 hf rfl hx
    exact ⟨a1, a3, a7, a8⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    have e24 : p.link = 24 := by
      rw [hlk, ep]
      rfl
    rw [ei] at hf
    obtain ⟨a1, -, a3, -, -, a6, a7, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O hf rfl hx
    rw [e24]
    exact ⟨a1, a3, a6, a7⟩
  · have e25 : p.link = 25 := by
      rw [hlk, ep]
      rfl
    rw [ei] at hf
    obtain ⟨a1, -, a3, -, -, a6, a7, -⟩ :=
      Meaning.K2.front_pin_fin h.scope h.reads O hf hb rfl hx
    rw [e25]
    exact ⟨a1, a3, a6, a7⟩

section
variable {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
  {after : TS → TS → Except String TS} {z₀ : ProofFile.InstPub} {s s₁ t : TS} {r₁ r₂ : Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
  {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}

/-- **AT A YES, AT A REACHED STATE: THE SIZES READ OFF THE STATEMENT BEHIND THE JOINS ARE THE
PLACE's OWN.** -/
theorem sizes_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    sizesAt S3 x.f.rows x.T = p.sizes := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  obtain ⟨w, W, hw, hW, ht⟩ := front_test_at_reach h O hp hA hr hb nm A.front
  have ht' := ht
  simp only [frontB2, Bool.and_eq_true] at ht'
  have Pn : Pinned (fxAt w) x := pin_facts ht'.1.1
  have K : AlikeKept x.f.rows x.st z.st :=
    ⟨A.sent.codes, fun o ho => A.sent.old o (Pn.below o ho)⟩
  rw [sizes_of_tables A.same, K.sizes]
  have tk := List.all_eq_true.1 placeSizesW.1 p hpW
  unfold placeSizesOk at tk
  rw [hw] at tk
  have tk' : (p.sizes.codes == codesFull2 && p.sizes.code == proofSizedFull.request.code &&
      p.sizes.maskCode == proofSizedFull.request.maskCode &&
      p.sizes.kept == (sizesAt (fxAt w).st (fxAt w).f.rows (fxAt w).T).kept &&
      p.sizes.target == targetAt proofSizedFull.request p.link) = true := tk
  simp only [Bool.and_eq_true, beq_iff_eq] at tk'
  obtain ⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩ := tk'
  obtain ⟨-, R, C, hf⟩ := (reach_raw hr).fold
  obtain ⟨f1, f2, f3, f4⟩ := front_pin_at_fold h O hp hA hf hb nm A.front
  have e4 := keptShapes_pin Pn
  have hcs : Zp.first.codes = p.sizes.codes := (codes_switch h O hp).symm
  have hsh := request_at_head h
  have g1 : (sizesAt x.st x.f.rows x.T).codes = p.sizes.codes := f1.trans hcs
  have g2 : (sizesAt x.st x.f.rows x.T).code = p.sizes.code := by
    rw [k2, ← hsh]
    exact f3
  have g3 : (sizesAt x.st x.f.rows x.T).maskCode = p.sizes.maskCode := by
    rw [k3, ← hsh]
    exact f4
  have g4 : (sizesAt x.st x.f.rows x.T).kept = p.sizes.kept := e4.trans k4.symm
  have g5 : (sizesAt x.st x.f.rows x.T).target = p.sizes.target := by
    rw [k5, ← hsh]
    exact f2
  cases hq : sizesAt x.st x.f.rows x.T with
  | mk c1 c2 c3 c4 c5 =>
    rw [hq] at g1 g2 g3 g4 g5
    cases hz : p.sizes with
    | mk d1 d2 d3 d4 d5 =>
      rw [hz] at g1 g2 g3 g4 g5
      obtain rfl : c1 = d1 := g1
      obtain rfl : c2 = d2 := g2
      obtain rfl : c3 = d3 := g3
      obtain rfl : c4 = d4 := g4
      obtain rfl : c5 = d5 := g5
      rfl

/-- **THE FIELD fresh OF `MadeAsks`, IN ITS OWN TEXT**: the group had no open row in front. -/
theorem fresh_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) : G.rows = #[] := by
  obtain ⟨w, W, -, -, ht⟩ := front_test_at_reach h O hp hA hr hb nm A.front
  have FF := facts_of_test ht
  obtain ⟨G', hG', h0⟩ := FF.fresh
  have e := A.before
  rw [FF.group, hG'] at e
  have e' : G'.rows = G.rows := Option.some.inj e
  rw [← e']
  exact Array.eq_empty_of_size_eq_zero h0

end

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.placeSizesOk
#print axioms ProofFile.Honest.K2.Law.placeSizesW
#print axioms ProofFile.Honest.K2.Law.sizes_of_tables
#print axioms ProofFile.Honest.K2.Law.front_test_at_reach
#print axioms ProofFile.Honest.K2.Law.front_pin_at_fold
#print axioms ProofFile.Honest.K2.Law.sizes_at_yes
#print axioms ProofFile.Honest.K2.Law.fresh_at_yes
