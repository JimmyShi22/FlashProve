-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/StandsOfFilling.lean: the premise `StandsAt`
(Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean) of Sim/MeetsAtRun.lean and
Sim/MeetsAtRunAtHead.lean, paid from a plainer one: the prover's shared list holds, at the side's
place, just the two parts of the proximity test. With it the three statements speak of a run in
which this member's own part stands at the member's address. It imports Mathlib.

A conditional. Nothing here shows that `ready` or `runC` returns at a prover whose shared list holds
these two parts, at a book that lends them: so nothing here shows that the premises can be met
together.

  `stands_first`   general in the description: where `ready` has returned, the description passes
                 its tests on the plan, the side's sub-protocol is one of the shared list, its row
                 is `testPairs J Js`, it passes `Side.fits`, the first member is among its members
                 and has a round, and the first entry of the prover's shared list at the side's
                 place has the parts `[firstPart J, restPart J]`: there is a cut of the shared list
                 at which `StandsAt` holds of the first member
  `meets_filled_O`, `meets_filled_U`   `meets_run_O` and `meets_run_U` with that premise in the
                 place of `StandsAt`

The premises of the two tops, sorted.
- Public, on the challenges: `ρ.due`.
- On the filling and the book: `ready` has returned R; the prover's shared list holds the two parts
  at the place.
- On the run: `runC` has returned r; the run has called the part.

By what. `steps_stand` (Johnson/Desc/ProofFile/Honest/Law/Rule/Stands.lean), as the proof of
`parts_stand_chain` (Law/StandsFile.lean) calls it; `places_nodup` (Law/Cuts.lean); `ready_ok`
(Law/Run.lean); `seated_at_O` (Sim/MeetsOwnAtHead.lean), `first_any_head_U`
(Sim/FirstAnyAtHeadU.lean); `first_moves`, `len_movesFrom`.

Limits. All limits of Sim/MeetsAtRunAtHead.lean stand, but the one on whose part is played at the
address. The job is any at the place: nothing says that it is the prover's of the protocol, nor
does anything settle the state on entry. Nothing on completeness, soundness or hiding.
The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
through that state is not said here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsAtRunAtHead
import Johnson.Desc.ProofFile.Honest.Law.Rule.Stands
import Johnson.Desc.ProofFile.Honest.Law.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest.K12.AtProof (fourOf)

/-- **Where the first member's rounds stand, from what the prover's shared list holds.** -/
theorem stands_first {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Ky)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hblk : σ.block ∈ F.shared.blocksInOrder)
    (hrow : σ.row = testPairs J Js) (hfit : σ.fits = true)
    (hmem : firstMember J Js ∈ σ.members) (hpos : firstLen J.p.nums.stages ≠ 0)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J]) :
    ∃ pre t, StandsAt F.shared.blocksInOrder R.shared σ (firstMember J Js) pre t 0 := by
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok hR
  obtain ⟨-, n2, -⟩ := places_nodup ((F.planOk_ok).1 hpl).places
  have l1 : (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length =
      firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have hsum : (σ.row.map (·.1.moves.length)).sum =
      (σ.block.rounds.zip σ.block.oracles).length := by
    unfold Side.fits at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    have h1 : σ.half.rounds = σ.block.rounds.length := hfit.1.2
    rw [List.length_zip, hfit.2, Nat.min_self, ← h1]
    unfold Side.half Placed.rounds
    rw [hrow]
    show (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length +
        ((restPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length + 0) =
      0 + (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length +
        (restPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length
    omega
  have hp' : g.parts = σ.row.map (·.1) := by
    rw [hparts, hrow]
    rfl
  obtain ⟨pre, t, n, hcut, hle, hp0, hstr, hown, hn⟩ :=
    steps_stand s2 n2 σ hblk hg hp' hsum (firstMember J Js) hmem (by
      show (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length ≠ 0
      rw [l1]
      exact hpos)
  have hn0 : n = 0 := hn
  subst hn0
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **The test on G_omega, at a run of a prover whose shared list holds the two parts.** hρ: public.
hR, hg, hparts: on the filling and the book. hrun, hc: on the run. -/
theorem meets_filled_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hfr : J.fresh.isNone = true) (hJ : Js.p = pO) (ho : Js.own = true)
    (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J])
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 0⟩ = true) :
    ∃ m, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 0⟩ = .ok (some m) ∧
      ∀ ca, MeetsAt .shared σ 1 0 (testOn .shared J Js) (testBud Js) (firstMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 0⟩)
        (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
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
  obtain ⟨pre, t, S⟩ := stands_first h.laid.planOk hR J Js σ hblk hrow f1 hm hpos g hg hparts
  exact meets_run_O h hO Js J hp hfr hJ ho fs σ hσ hρ hR hrun pre t S hc

/-- **The test on G_u, at a run of a prover whose shared list holds the two parts.** hρ: public. hR,
hg, hparts: on the filling and the book. hrun, hc: on the run. -/
theorem meets_filled_U (h : P5J.AtMg o Z D r₀ Zp Np cF)
    {W₀ Rc Ky Tr X₀ Y : Type} (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (hJ : Js.p = (fourOf Np).U)
    (ho : Js.own = false) (fs : List (Fall St))
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = [firstPart J, restPart J])
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 0⟩ = true) :
    ∃ m, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 0⟩ = .ok (some m) ∧
      ∀ ca, MeetsAt .shared σ 1 0 (testOn .shared J Js) (testBud Js) (firstMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 0⟩)
        (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
  obtain ⟨f1, -, -, hm, -⟩ := (first_any_head_U (V := Empty) h J Js hp hfr hJ ho).2.2 fs σ hσ
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ'
  have hblk : σ.block ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hb
  have hrow : σ.row = testPairs J Js := by rw [← e]
  have hpos : firstLen J.p.nums.stages ≠ 0 := by
    rw [hp, nums_head_U h]
    decide
  obtain ⟨pre, t, S⟩ := stands_first h.laid.planOk hR J Js σ hblk hrow f1 hm hpos g hg hparts
  exact meets_run_U h Js J hp hfr hJ ho fs σ hσ hρ hR hrun pre t S hc

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.stands_first
#print axioms ProofFile.Honest.K12.Light.meets_filled_O
#print axioms ProofFile.Honest.K12.Light.meets_filled_U
