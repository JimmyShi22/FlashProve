-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/Filled.lean: the proofs of `BackToHeadRaw` and `FilledRaw`
(Johnson/Desc/K11/Front/FilledStatement.lean), to the letter. Lemmas; none of the library's goals.

How. The first: the library's own walk back from 346 to 341 (`P4.waK6_at_346`,
Johnson/P4R/WaK6At346.lean), line for line, at the sub-protocols' own steps (`P4.reach_last`,
`P4.step_yes`, Johnson/P4R/Back341N.lean, for `P4.peel`): as `frontOfMergeRaw`
(Johnson/Desc/ProofFile/Honest/K11/ClaimBare.lean, a file that is not in this library) goes, with
"the ledger in front is well laid" kept and the two clauses on the claim left out. The second:
`sv_at_yes` (Johnson/Desc/Kinds/Law/SvLaid.lean) behind that yes; the ledger behind it is the own
part's (`Came.decide_record`, Johnson/Desc/Kinds/Law/RowPromise.lean); x rides and the ledger at 346
is a later one (`KeptW`), and a later ledger keeps what is filled.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Front.FilledStatement
import Johnson.P4R.WaK6At346
import Johnson.Desc.Kinds.Law.SvLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (KeptW sized_of_wellLaid blockAt_later sv_at_yes)

/-- **Back to the output head's yes.** -/
theorem backToHeadRaw : BackToHeadRaw := by
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
  obtain ⟨k5, _⟩ := P4.digits_345 h.scope h.reads O h.laid.planOk hB5 d5 ho5 hz5
  exact ⟨s341, s342, r1, g1, c1, c2, ((k2.trans k3).trans k4).trans k5⟩

/-- **The slot of the claim's value is filled.** -/
theorem filledRaw : FilledRaw := by
  intro Z D r Zp Np cF xP z sF a x h hr ha hax
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  obtain ⟨s, s', rv, gs, hd, hW, hk⟩ := backToHeadRaw Z D r Zp Np cF xP Bs z sF h O.made hr
  obtain ⟨o1, x1, ho1, hx1, _, _, hfil, _⟩ := sv_at_yes _ _ _ _ s s' rv gs hW hd
  obtain ⟨a0, F1, X0, Q, -, hop, -, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ hd
  have eL : (seatAt Bs.G₀.W.hS
      (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)).ledger s' = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  rw [eL] at hfil
  obtain ⟨p, p', hp, hp', ex, _, _, _, _, _, hL⟩ := hk
  obtain rfl : p' = a := Here.head.inj (hp'.symm.trans ha)
  obtain rfl : o1 = p := Here.head.inj (ho1.symm.trans hp)
  have eF : o1.F = F1 := by
    rw [e] at ho1
    exact (congrArg (·.F) (Here.head.inj ho1)).symm
  obtain rfl : x1 = x := Option.some.inj (hx1.symm.trans (ex.symm.trans hax))
  rw [eF] at hL
  exact (hL.keep _ hfil).1

end Johnson.Desc.First.ForkMerge.Front

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Front.backToHeadRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.filledRaw
