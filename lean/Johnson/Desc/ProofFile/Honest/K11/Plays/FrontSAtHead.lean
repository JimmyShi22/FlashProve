-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FrontSAtHead.lean: the proofs of `FrontOfReady` and
`FrontSAtHead` (Honest/K11/Plays/FrontSAtHeadStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The first, clause by clause out of the twelve of `MergeReady`. The part: the three readers of
the open link return where the head's link is open. `LedgerReady`: the sizes · the start form names
the one slot x.sV (`slotsIn_wsForkStart`, Johnson/Road/K4/Slots/FillsMore.lean), which is filled,
and so below the number of slots (`filled_lt`, OnBytes/Tie/Pv/Psc/PscRoom.lean) · the shape's own
slots and its end value's are 2 lk + 3 (`mergeShapeSlots`, here; `ownSlots_one_add`,
Johnson/Desc/Part/MaskedSumLedger.lean): within the number of slots, since the end value's slot, the
last of them, is below it · free by the premise. The unit: `claimFits_iff` and `claimFits_eq`
(Johnson/Top/H0/MergeLaw/Fits.lean) · `ofLay_unit` and `ofLay_in`
(Johnson/Top/H0/K11Caller/AtLay.lean). The second: `mergeReady_at_head` (ReadyWhole.lean of this
folder) · `sevenReady_at_head` (ReadyAtHead.lean) for "free above" · the layout: `sized_fact`
(Johnson/Desc/Sound/K11Tests/WeightsFactsInScope.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontSAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyWhole
import Johnson.Road.K4.Slots.FillsMore
import Johnson.Desc.Part.MaskedSumLedger
import Johnson.Top.H0.MergeLaw.Fits
import Johnson.Top.H0.K11Caller.AtLay
import Johnson.Desc.Sound.K11Tests.WeightsFactsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open OnBytes (oneE)
open OnBytes.PscRun (Filled filled_lt)
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Part.MaskedSum (Call.all Call.endsN ownSlots ownSlots_one_add Var.d)
open VerifiableInference.Desc.First.MergeLaw (claimFits_iff claimFits_eq)
open VerifiableInference.Desc.First.K11Caller (ofLay_unit ofLay_in)
open Johnson.Desc.First.ForkMerge.Returns (mergeEndSlot)

/-- The merge's shape takes 2 lk + 3 slots: its own and its one end value's. -/
theorem mergeShapeSlots (lk : ℕ) :
    ownSlots (headMergeShape lk).all + (headMergeShape lk).endsN = 2 * lk + 3 := by
  rw [ownSlots_one_add]
  simp only [headMergeShape, Call.all, Call.endsN, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Var.d, smul_eq_mul]
  omega

/-- **The seven, from "ready" and "free above".** -/
theorem frontOfReady : FrontOfReady := by
  intro P s sh p3 lkW hlay hready hfree
  obtain ⟨_, a, claim, x, ha, hop, _, hcl, hx, hfit, hsz, hfil, hlt, _, _⟩ := hready
  have hfr := hfree a ha
  have hL : s.link? = some a.L := by simp [S.link?, ha, hop]
  have hF : s.fork? = some a.F := by simp [S.fork?, ha, hop]
  have hT : s.tl? = some a.tl := by simp [S.tl?, ha, hop]
  obtain ⟨b9, hb9⟩ : ∃ b9, segAt? s = some b9 := by
    unfold segAt?
    rw [hL, hF, hT]
    exact ⟨_, rfl⟩
  obtain ⟨un, hun, _, _⟩ := (claimFits_iff P.lay claim).1 hfit
  have hshape : OnBytes.Model.wsClaimShape P.lay claim = .ok () := by
    have e := claimFits_eq P.lay claim
    rw [hfit] at e
    cases hs : OnBytes.Model.wsClaimShape P.lay claim with
    | ok u => rfl
    | error m =>
      rw [hs] at e
      cases e
  refine ⟨a, claim, x, b9, ha, hcl, hx, hb9, ⟨hsz, ?_, ?_, ?_⟩, hfil, un, hun, hshape,
    ofLay_unit hlay _ un hun, ofLay_in hlay _ un hun⟩
  · exact OnBytes.Desc.First.K4.Slots.slotsIn_wsForkStart
      (S := fun j => j < a.F.ns ∧ Filled a.F j) #[x.sV] #[oneE] (by
        intro j hj
        obtain rfl : j = x.sV := by simpa using hj
        exact ⟨filled_lt hsz.2.2 hfil, hfil⟩)
  · have e := mergeShapeSlots P.lay.lk
    unfold mergeEndSlot at hlt
    omega
  · intro j hj _
    exact hfr j hj

/-- **The seven at the thread.** -/
theorem frontS_at_head : FrontSAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT
  obtain ⟨Bs', _, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hmade)
  obtain ⟨shW, _, hw⟩ := LT28.K11Tests.sized_fact h.scope h.reads O.public
  obtain ⟨_, a, _, _, ha, _, _, _, _, _, _, o4⟩ := sevenReady_at_head Z D r Zp Np cF x h Bk W₀ Rc
    Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs' hmade hT
  exact frontOfReady (_root_.K11.parOf Zp Bs'.G₀) s shW true _ hw
    (mergeReady_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
      Kp w k s m E Bs' hmade hT)
    (fun a' ha' => by
      obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
      exact o4)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.mergeShapeSlots
#print axioms ProofFile.Honest.K11.frontOfReady
#print axioms ProofFile.Honest.K11.frontS_at_head
