-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimBare.lean: the proofs of `FrontOfMergeRaw`,
`HeadClaimAskedRaw` and `HeadClaimIsAtBare` (Honest/K11/ClaimBareStatement.lean), to the letter.
Lemmas; none of the library's goals.

How. The first: the library's own walk back over five sub-protocols, 346 to 341 (`P4.waK6_at_346`,
Johnson/P4R/WaK6At346.lean), line for line, at the sub-protocols' own steps: one step back is
`P4.reach_last` with `P4.step_yes` (Johnson/P4R/Back341N.lean) in the stead of `P4.peel`; its lemmas
on the five places (`yes_341`, `kept_342`, `kept_343`, `kept_344`, `digits_345`) and `wellLaid_341`
(Johnson/P4R/FreeAt341N.lean) take the sub-protocols' own decisions and that "reached". The second:
`headClaimOfRun` (ClaimOfQuiet.lean of this folder) and `askedSmallOfReply` (ClaimAsked.lean); the
request's words at such a state without a mark: `Meaning.K2.req_at_open`
(Johnson/LTPileR/AtGate.lean) and `Meaning.K2.reqOk_of_noMark` (Johnson/IMR/AtReach.lean). The
third: `reach_of_fold` (Johnson/Top/H0/Walk/Reach.lean) at the bare list.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimBareStatement
import Johnson.Desc.ProofFile.Honest.K11.ClaimAsked
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.P4R.WaK6At346
import Johnson.LTPileR.AtGate

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (KeptW sized_of_wellLaid blockAt_later)
open VerifiableInference.Desc.K13.Honest (HeadClaimIs)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)

/-- **In front of the merge, at what the sub-protocols' own steps reach.** -/
theorem frontOfMergeRaw : FrontOfMergeRaw := by
  intro Z D r Zp Np cF xP Bs z sF h hB hr
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨s345, B5, h345, hB5, y5⟩ := P4.reach_last hr
  obtain ⟨s344, B4, h344, hB4, y4⟩ := P4.reach_last h345
  obtain ⟨s343, B3, h343, hB3, y3⟩ := P4.reach_last h344
  obtain ⟨s342, B2, h342, hB2, y2⟩ := P4.reach_last h343
  obtain ⟨s341, B1, h341, hB1, y1⟩ := P4.reach_last h342
  obtain ⟨r5, g5, d5⟩ := P4.step_yes y5
  obtain ⟨r4, g4, d4⟩ := P4.step_yes y4
  obtain ⟨r3, g3, d3⟩ := P4.step_yes y3
  obtain ⟨r2, g2, d2⟩ := P4.step_yes y2
  obtain ⟨r1, g1, d1⟩ := P4.step_yes y1
  have c1 := P4.yes_341 h.scope h.reads O hB1 d1
  have c2 := P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) h341 Bs'.G₀.W.hS
    (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)
  obtain ⟨a, F1, X0, Q, -, hop, -, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ c1
  have ho2 : s342.here = .head { a with F := F1, x := some X0, squaresP := some Q } := by rw [e]
  have eL : (seatAt Bs'.G₀.W.hS
      (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)).ledger s342 = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  have hz2 : Sized ({ a with F := F1, x := some X0, squaresP := some Q } : HeadOwn).F := by
    have hL := blockAt_later _ _ _ _ s341 s342 r1 g1 c1
    rw [eL] at hL
    exact hL.sized (sized_of_wellLaid c2)
  have k2 := P4.kept_342 h.scope h.reads O hB2 d2 ho2
  obtain ⟨o3, ho3, hz3⟩ := k2.next ho2 hz2
  have k3 := P4.kept_343 h.scope h.reads O hB3 d3 ho3
  obtain ⟨o4, ho4, hz4⟩ := k3.next ho3 hz3
  have k4 := P4.kept_344 h.scope h.reads O hB4 d4 ho4
  obtain ⟨o5, ho5, hz5⟩ := k4.next ho4 hz4
  obtain ⟨k5, cov, tb, c5, c6⟩ := P4.digits_345 h.scope h.reads O h.laid.planOk hB5 d5 ho5 hz5
  exact ⟨s341, s342, r1, g1, cov, tb, c1, ((k2.trans k3).trans k4).trans k5, c5, c6⟩

/-- **At border 346, where the heard reply is the asked one.** -/
theorem headClaimAskedRaw : HeadClaimAskedRaw := by
  intro H Z D r Zp Np cF xP Bs x heard s o claim h hB hr hf hrep ho hoc hties
  obtain ⟨s1, s2, rv, gs, cov, t, hd, hk, hcov, hcl⟩ :=
    frontOfMergeRaw Z D r Zp Np cF xP Bs x.pub s h hB hr
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨a, F1, X0, Q, _, _, _, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ hd
  obtain ⟨p, p', hp, hp', ex, _⟩ := hk
  rw [e] at hp
  obtain rfl := Here.head.inj hp
  obtain rfl : p' = o := Here.head.inj (hp'.symm.trans ho)
  have hox : p'.x = some X0 := ex
  have hq := Meaning.K2.reqOk_of_noMark h.scope h.reads O hr hf
  have hstart : (startS Zp x.pub).req = OnBytes.Model.Verify.words32 x.pub.request := by
    unfold startS
    dsimp only
    rw [if_pos hq]
    rfl
  have hreq : s.req = OnBytes.Model.Verify.words32 x.pub.request :=
    Meaning.K2.req_at_open O (P5J.flat_ok h.toAtMg) 0 346 (x.pub, s) hr hf
  obtain ⟨k1, k2, k3, k4⟩ := hties p' X0 ho hox
  exact headClaimOfRun H Zp Bs'.G₀ x heard s cov X0 t claim hcov (hcl p' X0 claim ho hox hoc)
    (hreq.trans hstart.symm) (askedSmallOfReply x s _ _ cov hrep hcov) k1 k2 k3 k4

/-- **The law on the head's claim, at the list that runs, from the four ties.** -/
theorem headClaimIsAtBare : HeadClaimIsAtBare := by
  intro H Z D r Zp Np cF xP Bs link claims h hB hcl hties x rs cols sj c o claim hfold hf hrep ho
    hoc
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF xP h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (x.pub, sj) :=
    reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 346 hb sj rs _ cols c hfold
  have e := headClaimAskedRaw H Z D r Zp Np cF xP Bs x _ sj o claim h hB hr hf hrep ho hoc
    (hties x rs cols sj c hfold hf hrep)
  rw [hcl, e]

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.frontOfMergeRaw
#print axioms ProofFile.Honest.K11.headClaimAskedRaw
#print axioms ProofFile.Honest.K11.headClaimIsAtBare
