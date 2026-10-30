-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/MeetsAtRun.lean: the first member of a proximity test on the
shared chain, at one run of the frame's `runC` (Johnson/Desc/ProofFile/Honest/Walk.lean): the record
`MeetsAt` (Sim/MeetsOwnAtHead.lean: the six hypotheses of the sentence `ExactMember` in its order,
"something", the equation) as a conclusion, at that run's stand and own front, challenges and
positions. General in the description and in the arm. It imports Mathlib.

A conditional. Nothing here shows that `ready` or `runC` returns at a prover whose shared list holds
these two parts, at a book that lends them: so nothing here shows that the premises can be met
together.

Nor does a premise say that the part which the prover plays at the member's address is this
member's part: `StandsAt` reads of the prepared rounds their addresses, declared rounds and oracle
messages alone, and "the run has called the part" reads what was played at the address. So the run
may be that of any prover with a part of that cut there. The stand m is the one in front of the
part, and the statement holds at it all the same: it is wider than "a run in which this member
plays", and does not say that.

  `meets_at_run`   there is a stand m that `midSharedAtW` (Johnson/Desc/ProofFile/Honest/MidW.lean)
                 returns at the member's address, and at every carried values: `MeetsAt` at m, at
                 the front `r.run.beforeAt` with the stored tables' columns that the run reads, at
                 `r.run.drawnAt` and at `r.run.askedAt` (Johnson/Desc/ProofFile/Honest/Side.lean)

Its premises, sorted.
- Public, on the description: `F.planOk`.
- On the filling and the book: `ready` has returned R; and `StandsAt`
  (Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean), a definition that goes with the frame: the
  member's rounds are one stretch of the shared chain's prepared rounds, behind the rounds of the
  sub-protocols in front, and that stretch bears the member's declared rounds and oracle messages.
- On the run: `runC` has returned r; and the run has called the part.
- Three on public data, which a caller pays: the member's own stretch of the challenges has the
  declared form; `testBud` holds at that stretch and at the positions that the declared rounds read;
  `MeetsEvery` (Sim/MeetsEveryFront.lean) at every carried values and stand.

By what. The first half of the proof of `owed_part_shared` (Law/OwedParts.lean), step for step, with
`mid_shared` (Law/RunMidFile.lean) where that proof calls a law on invariants: `stretch_back`,
`at_shared`, `drawnAt_of`, `askedAt_of`, `runC_asks` (Law/RunAtFile.lean), `before_shared`
(Law/RunBefore.lean), `shown_is`, `runOk_of` (Law/Rule/Reads.lean), `seen_by`, `roundsOff_by`
(Law/Rule/Faith.lean), `steps_shaped` (Law/Along.lean), `steps_pairs` (Law/StratRun.lean),
`ready_ok` (Law/Run.lean), all under Johnson/Desc/ProofFile/Honest/.

Limits.
- The carried values are any, not those that the book lends: more than a run has. That the book
  lends the part its carried values (`carriedAt`, Johnson/Desc/ProofFile/Honest/Frame.lean) is
  neither a premise nor concluded here.
- The equation samples the part's own values anew: it says nothing on the values of the run r.
- Of the hypothesis of the frame's field `exact` on `m.opened` (`ExactMemberAt`,
  Johnson/Desc/ProofFile/Honest/Small/Field.lean) nothing is concluded here: `MeetsAt` has no field
  for it.
- The first member alone. One request.
- All limits of Sim/MeetsEveryFront.lean on the job and the state on entry stand.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsEveryFront
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)

/-- **At one run's stand and own front, challenges and positions.** hpl: public. hR, S: on the
filling and the book. hrun, hc: on the run. hd, hb, hE: on public data; a caller pays them. -/
theorem meets_at_run {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Ky)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ (firstMember J Js) pre t 0)
    (hc : r.called ⟨σ.block.place, 0⟩ = true)
    (hd : drawsFit ((firstMember (V := Empty) J Js).rounds.map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := Empty) J Js).rounds.length) = true)
    (hb : testBud Js 0 ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := Empty) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 1) ((firstMember (V := Empty) J Js).rounds.map (·.2.length))
        (((rowsOfChain F.shared.blocksInOrder).take (pre.flatMap (·.rounds)).length).map
          (·.2.length)).sum))
    (hE : ∀ ca m, MeetsEvery .shared σ 1 0 J Js ca m) :
    ∃ m, midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 0⟩ = .ok (some m) ∧
      ∀ ca, MeetsAt .shared σ 1 0 (testOn .shared J Js) (testBud Js) (firstMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 0⟩)
        (r.run.drawnAt ⟨σ.block.place, 0⟩) (r.run.askedAt ⟨σ.block.place, 0⟩) := by
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  have hstr : InStretch R.shared ⟨σ.block.place, 0⟩ (pre.flatMap (·.rounds)).length
      (firstMember (V := Empty) J Js).rounds.length := S.str
  have hown : ((R.shared.drop (pre.flatMap (·.rounds)).length).take
      (firstMember (V := Empty) J Js).rounds.length).map (fun s => (s.decl, s.oracles)) =
      (firstMember (V := Empty) J Js).rounds := S.own
  have hfit : (pre.flatMap (·.rounds)).length + (firstMember (V := Empty) J Js).rounds.length ≤
      R.shared.length := S.fits
  obtain ⟨ha, htw, -, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_shared hrun hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of hrun).1
  obtain ⟨m, hm, hseen⟩ := mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  refine ⟨m, hm, fun ca => ?_⟩
  have hbf := before_shared hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 1)
    (shown_is hRO 1 (by decide)) (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  rw [htw] at hbf hseen
  have e1 : ((R.shared.drop (pre.flatMap (·.rounds)).length).take
      (firstMember (V := Empty) J Js).rounds.length).map (·.oracles.length) =
      (firstMember (V := Empty) J Js).rounds.map (·.2.length) := by
    have g := congrArg (List.map (·.2.length)) hown
    rw [List.map_map] at g
    exact g
  have e2 : (R.shared.take (pre.flatMap (·.rounds)).length).map (·.oracles.length) =
      ((rowsOfChain F.shared.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
    rw [← steps_pairs s2, ← List.map_take, List.map_map]
    rfl
  rw [drawnAt_of hA hstr,
    askedAt_of hA hstr (treeAsks F ρ 1) (runC_asks hrun hR o₁ o₂ o₃ 1), e1, e2, hbf]
  exact hE ca m _ _ _ (by rw [hseen, seen_by, roundsOff_by]) hd hb

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.meets_at_run
