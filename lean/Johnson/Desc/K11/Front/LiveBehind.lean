-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/LiveBehind.lean: the proofs of `SvBelowRaw`, `NextAtRaw` and
`MergeLiveBehindRaw` (Johnson/Desc/K11/Front/LiveBehindStatement.lean), to the letter. Lemmas; none
of the library's goals.

How. The first: the lines of `filledRaw` (Filled.lean of this folder), with two other ends of
`sv_at_yes` (Johnson/Desc/Kinds/Law/SvLaid.lean) spent: behind the output head's yes x.sV + 1 is the
ledger's next free number; `KeptW` hands x on and a later ledger, whose next number is no smaller
(`Later.next`, OnBytes/Tie/Pv/Psc/PscLater.lean). The second: `countRaw` (Count.lean of this folder)
at lk = 18 (`m0lk_in_scope`, Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean) and 3570 slots
(`slots_in_scope`, SlotsInScope.lean of that folder). The third: the member at its seat is the
kind's block under the guard on marks (`headMergeSeated`, Johnson/Desc/K11/Returns/Seat.lean;
`IM.guardMark_yes`, Johnson/IMR/SeatForm.lean): so its yes is the kind's decision's;
`headMergeLiveBehind` (Johnson/Desc/K11/Live/Behind.lean) at the first; the two numbers by the
second.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Front.LiveBehindStatement
import Johnson.Desc.K11.Front.Filled
import Johnson.Desc.K11.Front.Count
import Johnson.Desc.K11.Live.Behind
import Johnson.Desc.K11.Returns.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Front
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.First.MergeLaw (hlay_at)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (sv_at_yes)
open Johnson.Desc.First.ForkMerge.Live (headMergeLiveBehind)
open Johnson.Desc.First.ForkMerge.Returns (headMergeSeated)

/-- **The slot of the claim's value lies below the ledger's next free number.** -/
theorem svBelowRaw : SvBelowRaw := by
  intro Z D r Zp Np cF xP z sF a x h hr ha hax
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  obtain ⟨s, s', rv, gs, hd, hW, hk⟩ := backToHeadRaw Z D r Zp Np cF xP Bs z sF h O.made hr
  obtain ⟨o1, x1, ho1, hx1, hn1, hsv, _, _⟩ := sv_at_yes _ _ _ _ s s' rv gs hW hd
  obtain ⟨a0, F1, X0, Q, -, hop, -, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ hd
  have eL : (seatAt Bs.G₀.W.hS
      (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)).ledger s' = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  rw [eL] at hn1
  obtain ⟨p, p', hp, hp', ex, _, _, _, _, _, hL⟩ := hk
  obtain rfl : p' = a := Here.head.inj (hp'.symm.trans ha)
  obtain rfl : o1 = p := Here.head.inj (ho1.symm.trans hp)
  have eF : o1.F = F1 := by
    rw [e] at ho1
    exact (congrArg (·.F) (Here.head.inj ho1)).symm
  obtain rfl : x1 = x := Option.some.inj (hx1.symm.trans (ex.symm.trans hax))
  rw [eF] at hL
  have := hL.next
  omega

/-- **The two numbers.** -/
theorem nextAtRaw : NextAtRaw := by
  intro Z D r Zp Np cF xP Bs z sF a h hB hr ha
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made hB).2.2.1
  have l1 : (K11.parOf Zp Bs.G₀).lay.lk = 18 := by
    rw [← hlay_at hG]
    exact (LT28.K11Tests.m0lk_in_scope h.scope h.pubOne).2
  have l2 := LT28.K11Tests.slots_in_scope h.scope h.reads h.pubOne hG
  have l3 := countRaw Z D r Zp Np cF xP Bs z sF a h hB hr ha
  rw [l1, l2] at l3
  exact ⟨by omega, l1⟩

/-- **The condition behind the member's yes, at the written numbers.** -/
theorem mergeLiveBehindRaw : MergeLiveBehindRaw := by
  intro Z D r Zp Np cF xP Bs z sF s' a x name pl rs gs h hB hr hd ha hax hne
  rw [headMergeSeated (K11.parOf Zp Bs.G₀) name pl] at hd
  obtain ⟨h1, -⟩ := (IM.guardMark_yes (headClaimMergeKind (K11.parOf Zp Bs.G₀)) sF s' rs gs).1 hd
  obtain ⟨n1, n2⟩ := nextAtRaw Z D r Zp Np cF xP Bs z sF a h hB hr ha
  have hl := headMergeLiveBehind (K11.parOf Zp Bs.G₀) sF s' rs a x h1 ha hax
    (svBelowRaw Z D r Zp Np cF xP z sF a x h hr ha hax) hne
  rw [n1, n2] at hl
  exact hl

end Johnson.Desc.First.ForkMerge.Front

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Front.svBelowRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.nextAtRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.mergeLiveBehindRaw
