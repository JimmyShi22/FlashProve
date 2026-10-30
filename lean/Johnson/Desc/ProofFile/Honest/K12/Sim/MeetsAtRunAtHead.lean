-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/MeetsAtRunAtHead.lean: `meets_at_run` (Sim/MeetsAtRun.lean)
under the library's head (`P5J.AtMg`, Johnson/P5J/AtMg.lean), at the first member of the two
proximity tests of the proof file's shared chain, at whatever side `testSide` (Sim/Row.lean) takes
off the description's own shared list: its premises on public data are paid. It imports Mathlib.

A conditional. Nothing here shows that `ready` or `runC` returns at a prover whose shared list holds
these two parts, at a book that lends them: so nothing here shows that the premises can be met
together.

Nor does a premise say that the part which the prover plays at the member's address is this
member's part: `StandsAt` reads of the prepared rounds their addresses, declared rounds and oracle
messages alone, and "the run has called the part" reads what was played at the address. So the run
may be that of any prover with a part of that cut there. The stand m is the one in front of the
part, and the statement holds at it all the same: it is wider than "a run in which this member
plays", and does not say that.

  `draws_stretch_at`   general in the description and the place: the member's own stretch of a list
                 of challenges that passes `Draws.due` has the declared form
  `meets_run_O`  the test on G_omega, whose first fold sends its own table
  `meets_run_U`  the test on G_u, where the first fold's fresh table has come earlier

What is concluded: there is a stand m that `midSharedAtW` returns at the member's address; and at
every carried values the record `MeetsAt` (Sim/MeetsOwnAtHead.lean) at m, at the front
`r.run.beforeAt` with the stored tables' columns that the run reads, at `r.run.drawnAt` and at
`r.run.askedAt`: so, among its fields, the side's bound `testBud` at the run's own challenges and
positions.

The premises that stay, sorted.
- Public, on the challenges: `ρ.due`.
- On the filling and the book: `ready` has returned R; `StandsAt`
  (Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean): where the member's rounds stand among the
  shared chain's prepared rounds.
- On the run: `runC` has returned r; the run has called the part.

Paid here: `F.planOk` (a field of the head); the stretch's form (`draws_stretch_at`); `testBud` at
the positions that the declared rounds read (`bud_first_O`, Sim/BudOwnAtHead.lean; at G_u it asks
nothing: `testBud_first`, Sim/MeetsAtHead.lean); `MeetsEvery` (`meets_every_O`,
`meets_every_earlier`, Sim/MeetsEveryFront.lean).

Limits. All limits of Sim/MeetsAtRun.lean, Sim/MeetsEveryFront.lean and Sim/BudOwnAtHead.lean stand;
among them: "at every job at the place" says nothing on whether any job there is the prover's, nor
does it settle the state on entry; the carried values are any; the equation samples the part's own
values anew; the first member alone; one request. Nothing on completeness, soundness or hiding.
The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
through that state is not said here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St)
open ProofFile.Honest.K12.AtProof (fourOf)

/-- The member's own stretch of a due list has the declared form. -/
theorem draws_stretch_at {Xi V W X Pb : Type} {F : FileDescription Xi} (hpl : F.planOk = true)
    (Js : SimJob Pb) (J : TestJob W X)
    (hk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true) (b : Block F.S₂ F.Cl)
    (pre t : List (Block F.S₂ F.Cl)) (hcut : F.shared.blocksInOrder = pre ++ b :: t)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles) (ρ : Draws)
    (hρ : ρ.due F = true) :
    drawsFit ((firstMember (V := V) J Js).rounds.map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := V) J Js).rounds.length) = true := by
  have hl : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length ≤
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles.length := by
    have hs := shaped_len b (planOk_shaped hpl b
      (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self))
    rw [hr, hor] at hs
    exact Nat.le_of_eq hs.symm
  have hz : b.rounds = (H2K.JointK.laidOf J.p).map (·.1) := by
    rw [hr, ← zip_laid J.p hk, List.map_fst_zip hl]
  have hsplit : b.rounds = ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) ++
      ((H2K.JointK.laidOf J.p).drop (firstLen J.p.nums.stages)).map (·.1) := by
    rw [hz, ← List.map_append, List.take_append_drop]
  have h4 := draws_front pre t b hcut _ _ hsplit ρ hρ
  rw [List.length_map] at h4
  exact h4

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **The test on G_omega, at one run's stand and own front, challenges and positions.** hρ: public.
hR, S: on the filling and the book. hrun, hc: on the run. -/
theorem meets_run_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hfr : J.fresh.isNone = true) (hJ : Js.p = pO) (ho : Js.own = true)
    (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r) (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (firstMember J Js) pre t 0)
    (hc : r.called ⟨σ.block.place, 0⟩ = true) :
    ∃ m, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 0⟩ = .ok (some m) ∧
      ∀ ca, MeetsAt .shared σ 1 0 (testOn .shared J Js) (testBud Js) (firstMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 0⟩)
        (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
  have hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hb := bud_first_O h hO Js J hp hJ fs σ hσ pre t _ hcut rfl ρ hρ
  have hq : σ.block.rounds = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds ∧
      σ.block.oracles = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles := by
    obtain ⟨b, hf, _, hr, hor⟩ := find_gomega h hO
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    rw [hp, hf] at hσ'
    obtain rfl := Option.some.inj hσ'
    exact ⟨hr, hor⟩
  have hd := draws_stretch_O (V := Empty) h hO Js J hp σ.block pre t hcut hq.1 hq.2 ρ hρ
  exact meets_at_run h.laid.planOk hR hrun J Js σ pre t S hc hd hb fun ca m =>
    meets_every_O h hO Js J hp hfr hJ ho .shared σ 1 0 ca m

/-- **The test on G_u, at one run's stand and own front, challenges and positions.** hρ: public. hR,
S: on the filling and the book. hrun, hc: on the run. -/
theorem meets_run_U (h : P5J.AtMg o Z D r₀ Zp Np cF)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (hJ : Js.p = (fourOf Np).U)
    (ho : Js.own = false) (fs : List (Fall St))
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r) (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (firstMember J Js) pre t 0)
    (hc : r.called ⟨σ.block.place, 0⟩ = true) :
    ∃ m, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 0⟩ = .ok (some m) ∧
      ∀ ca, MeetsAt .shared σ 1 0 (testOn .shared J Js) (testBud Js) (firstMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 0⟩)
        (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
  have hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t := S.cut
  have F := facts_head_U h
  rw [← hp] at F
  have hq : σ.block.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ∧
      σ.block.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles := by
    obtain ⟨b, hf, _, hr, hor⟩ := find_gu h
    rw [← hp] at hf hr hor
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    rw [hf] at hσ'
    obtain rfl := Option.some.inj hσ'
    exact ⟨hr, hor⟩
  have hd := draws_stretch_at (V := Empty) h.laid.planOk Js J F.plan σ.block pre t hcut hq.1 hq.2
    ρ hρ
  exact meets_at_run h.laid.planOk hR hrun J Js σ pre t S hc hd (testBud_first Js ho _ _)
    fun ca m => meets_every_earlier J Js F hfr (hJ.trans hp.symm) ho .shared σ 1 0 ca m

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.draws_stretch_at
#print axioms ProofFile.Honest.K12.Light.meets_run_O
#print axioms ProofFile.Honest.K12.Light.meets_run_U
