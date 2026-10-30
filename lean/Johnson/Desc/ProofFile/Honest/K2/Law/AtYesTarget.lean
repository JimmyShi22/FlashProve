-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AtYesTarget.lean: the kind "the code switch" (K2): THE TARGET
OF THE FRONT THAT THE SWITCH TAKES OFF A FOLD's STATE IS THE WRITTEN PLAN's, AND TWO MORE OF THE
TWENTY-ONE FIELDS OF THE RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), IN THE
RECORD's OWN TEXT: keptPos · restMain. Under the library's head and the opening, at a switch of the
plan, at a state that the verifier's own fold over the members in front returns. BOTH ARE PUBLIC. IT
DOES NOT SAY THAT THE RECORD IS MET. That file is not imported: the fields' texts are copied. One
definition, a public test; one closed fact by evaluation in Lean's kernel, with a control; lemmas.

  `targetPlainOk`, `targetsW`   A PUBLIC TEST on a target: each message that takes a kept member has
                    a main row, and the rest lies in main rows; BY LEAN's KERNEL at the written
                    request's targets at the links 1 to 25; A CONTROL on the second clause alone:
                    with the rest bent into the mask rows the test says no at each
  `targetPlain_gives`   what the test gives: the two fields' own forms
  `request_at_head`   the public part's request is the written one
  `target_at_fold`  the front's target is `targetAt` of the written request at a link from 1 to 25
  `two_at_yes`      THE END: keptPos · restMain

By, sealed, of other authors: `front_pin_link`, `front_pin_head` (Johnson/IMR/FrontPin.lean) ·
`front_pin_fin` (Johnson/IMR/FinPin.lean) · `at_written` (Johnson/Top/H0/K2Ties/WrittenAt.lean) ·
`KeptPos` (Johnson/Top/H0/K2Hands/AtYes.lean) · `AtYes` (Johnson/Top/H0/K2Hears/Whole.lean). Ours:
`SwitchArm` (Honest/K2/Law/BlockAtHead.lean).

Limits. PUBLIC: no coin, input or run occurs. THAT THERE IS A FRONT IS A PREMISE. WHICH LINK's
target it is, is said by the arm (the place's own link · 24 · 25), not against p.link at the two
last arms. The full size and the format's second hash function alone. The head and the opening are premises.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead
import Johnson.IMR.FrontPin
import Johnson.IMR.FinPin
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H0.K2Hears.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes KeptPos frontAt targetAt)
open VerifiableInference.Desc.First.K2Ties (at_written)
open VerifiableInference.PlanWritten (proofSizedFull pinnedAt_of_row)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST** on a target: each message that takes a kept member has a main row; the rest
lies in main rows. -/
def targetPlainOk (T : SwitchTarget) : Bool :=
  (T.kept.all fun k => decide (0 < k.shape.mainRows)) && T.rest.part == .main

set_option maxRecDepth 1000000 in
/-- **At the written request's targets at the links 1 to 25**; a control: with the rest bent into
the mask rows the test says no at each. -/
theorem targetsW :
    ((List.range 25).all fun i => targetPlainOk (targetAt proofSizedFull.request (i + 1))) = true ∧
      ((List.range 25).any fun i => targetPlainOk
        { targetAt proofSizedFull.request (i + 1) with
          rest := { (targetAt proofSizedFull.request (i + 1)).rest with part := .mask } }) =
        false := by
  decide +kernel

/-- What the test gives. -/
theorem targetPlain_gives {T : SwitchTarget} (h : targetPlainOk T = true) :
    KeptPos T ∧ T.rest.part = .main := by
  unfold targetPlainOk at h
  rw [Bool.and_eq_true] at h
  exact ⟨fun i hi => of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 h.1 _
    (Array.getElem_mem hi)), beq_iff_eq.1 h.2⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- The public part's request is the written one. -/
theorem request_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    Zp.first.shape = proofSizedFull.request :=
  (at_written h.scope h.laid (pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true]))).shape

/-- **The front's target is the written request's, at some link from 1 to 25.** -/
theorem target_at_fold (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
    {after : TS → TS → Except String TS} (hA : SwitchArm Zp Bs.G₀ p st before after)
    {z₀ : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {s s₁ : TS}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (P5J.At.ps.findIdx (· == p.place))) (ProofFile.startS Zp z₀) R C =
      .ok (s, [], [])) (hb : before s = .ok s₁) (nm : String) {x : _root_.Tw.K2.Front}
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) :
    ∃ i, i < 25 ∧ x.T = targetAt proofSizedFull.request (i + 1) := by
  rw [← request_at_head h]
  rcases hA with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, -, ei, rfl, -⟩ | ⟨rfl, -, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    rw [ei] at hf
    refine ⟨p.link - 1, by omega, ?_⟩
    rw [show p.link - 1 + 1 = p.link by omega]
    exact (Meaning.K2.front_pin_link h.scope h.reads O h1 h24 hf rfl hx).2.2.1
  · obtain rfl : s = s₁ := Except.ok.inj hb
    rw [ei] at hf
    exact ⟨23, by decide, (Meaning.K2.front_pin_head h.scope h.reads O hf rfl hx).2.2.1⟩
  · rw [ei] at hf
    exact ⟨24, by decide, (Meaning.K2.front_pin_fin h.scope h.reads O hf hb rfl hx).2.2.1⟩

/-- **TWO FIELDS OF `MadeAsks`, IN ITS OWN TEXT**: keptPos · restMain. -/
theorem two_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
    {after : TS → TS → Except String TS} (hA : SwitchArm Zp Bs.G₀ p st before after)
    {z₀ : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {s s₁ t : TS}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (P5J.At.ps.findIdx (· == p.place))) (ProofFile.startS Zp z₀) R C =
      .ok (s, [], [])) (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    KeptPos x.T ∧ x.T.rest.part = .main := by
  obtain ⟨i, hi, e⟩ := target_at_fold h O hA hf hb nm A.front
  rw [e]
  exact targetPlain_gives (List.all_eq_true.1 targetsW.1 i (List.mem_range.2 hi))

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.targetPlainOk
#print axioms ProofFile.Honest.K2.Law.targetsW
#print axioms ProofFile.Honest.K2.Law.targetPlain_gives
#print axioms ProofFile.Honest.K2.Law.request_at_head
#print axioms ProofFile.Honest.K2.Law.target_at_fold
#print axioms ProofFile.Honest.K2.Law.two_at_yes
