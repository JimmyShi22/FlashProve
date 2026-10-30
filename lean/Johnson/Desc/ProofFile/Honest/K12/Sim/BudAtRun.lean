-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudAtRun.lean: the side's bound `testBud` (Sim/Row.lean) at
one run's own challenges and positions, at the first member of the proximity test on G_omega,
WHETHER OR NOT THE RUN HAS CALLED THE PART. The frame's `Lettered.owedAt`
(Johnson/Desc/ProofFile/Honest/Rule.lean) asks `bud` of every part, called or not;
Sim/MeetsAtRun.lean and Sim/StandsOfFilling.lean have it at a called part alone. It imports Mathlib.

A conditional. Nothing here shows that `ready` or `runC` returns at a prover whose shared list holds
these two parts, at a book that lends them: so nothing here shows that the premises can be met
together.

  `asks_at_run`   general in the description, the side and the member: the run's challenges and
                 positions at a part of the shared chain, in their closed forms. No premise says
                 that the part was called
  `bud_filled_O`   under the library's head (`P5J.AtMg`, Johnson/P5J/AtMg.lean), at whatever side
                 `testSide` takes off the description's own shared list, at a prover whose shared
                 list holds the two parts at the side's place: `testBud Js 0` at `r.run.drawnAt` and
                 `r.run.askedAt` (Johnson/Desc/ProofFile/Honest/Side.lean)
  `owed_bud_O`   the same in the letters of `Lettered.owedAt`'s first conjunct, at a list of parts
                 at that place whose row is `testPairs J Js` and whose bud is `testBud Js`, at its
                 members of number 0

Premises, sorted. Public: `ρ.due`. On the filling and the book: `ready` has returned R; the first
entry of the prover's shared list at the side's place has the parts `[firstPart J, restPart J]`. On
the run: `runC` has returned r.

By what. `stretch_back`, `at_shared`, `drawnAt_of`, `askedAt_of`, `runC_asks`, `steps_pairs`, which
go with the frame and ask no "called"; `stands_first` (Sim/StandsOfFilling.lean); `bud_first_O`
(Sim/BudOwnAtHead.lean); `side_is_testSide` (Sim/BudOwnIsDebt.lean).

Limits. The first member alone: the second member's bound is not treated. One request. At the test
on G_u the bound asks nothing at this member (`testBud_first`, Sim/MeetsAtHead.lean). All limits of
Sim/BudOwnAtHead.lean and Sim/StandsOfFilling.lean stand. Nothing on completeness, soundness or
hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.StandsOfFilling
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwnIsDebt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest.K12.AtProof (fourOf)

/-- **The run's challenges and positions at a part, called or not.** hpl: public. hR, S: on the
filling and the book. hrun: on the run. -/
theorem asks_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i n : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i) :
    r.run.drawnAt ⟨σ.block.place, u.number⟩ = (ρ.shared.drop n).take u.rounds.length ∧
      r.run.askedAt ⟨σ.block.place, u.number⟩ =
        asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hstr := S.str
  have hown := S.own
  have hfit := S.fits
  rw [← hn] at hstr hown hfit
  obtain ⟨ha, -, -, -⟩ := stretch_back hstr S.pos hfit
  have hA := at_shared hrun hR o₁ o₂ o₃ hp ha
  have e1 : ((R.shared.drop n).take u.rounds.length).map (·.oracles.length) =
      u.rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) hown
    rw [List.map_map] at g
    exact g
  have e2 : (R.shared.take n).map (·.oracles.length) =
      ((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length) := by
    rw [← steps_pairs s2, ← List.map_take, List.map_map]
    rfl
  refine ⟨drawnAt_of hA hstr, ?_⟩
  rw [askedAt_of hA hstr (treeAsks F ρ 1) (runC_asks hrun hR o₁ o₂ o₃ 1), e1, e2]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **The bound at the run's own letters, called or not.** hρ: public. hR, hg, hparts: on the
filling and the book. hrun: on the run. -/
theorem bud_filled_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hJ : Js.p = pO) (fs : List (Fall St))
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J])
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r) :
    testBud Js 0 (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
  obtain ⟨f1, f2⟩ := seated_at_O h hO Js J hp hJ fs σ hσ
  have hm : firstMember J Js ∈ σ.members := by
    rw [f2]
    exact List.mem_cons_self
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ'
  have hblk : σ.block ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hb
  have hrow : σ.row = testPairs J Js := by rw [← e]
  have hpos : firstLen J.p.nums.stages ≠ 0 := by
    rw [hp, nums_head_O h hO]
    decide
  obtain ⟨pre, t, S⟩ : ∃ pre t : List (Block St ProofFile.Cl),
      StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (firstMember J Js) pre t 0 :=
    stands_first h.laid.planOk hR J Js σ hblk hrow f1 hm hpos g hg hparts
  have hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hb' := bud_first_O h hO Js J hp hJ fs σ hσ pre t _ hcut rfl ρ hρ
  obtain ⟨e1, e2⟩ := asks_at_run h.laid.planOk hR hrun σ (firstMember J Js) pre t 0 _ S rfl
  have e1' : r.run.drawnAt ⟨σ.block.place, 0⟩ = _ := e1
  have e2' : r.run.askedAt ⟨σ.block.place, 0⟩ = _ := e2
  rw [e1', e2']
  exact hb'

/-- **The first conjunct of `Lettered.owedAt`, at the members of number 0.** -/
theorem owed_bud_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hJ : Js.p = pO) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = testBud Js)
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == L.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J])
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r) :
    ∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 0 →
      L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩) := by
  intro σ hσ u _ h0
  have hσ' : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ :=
    (side_is_testSide L J Js hpl hrow _).symm.trans hσ
  have hsp : σ.block.place = L.place := side_place hσ
  rw [← hsp] at hg ⊢
  rw [hbud, h0]
  exact bud_filled_O h hO Js J hp hJ [] σ hσ' hρ hR g hg hparts hrun

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.asks_at_run
#print axioms ProofFile.Honest.K12.Light.bud_filled_O
#print axioms ProofFile.Honest.K12.Light.owed_bud_O
