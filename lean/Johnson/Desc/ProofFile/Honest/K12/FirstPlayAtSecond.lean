-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FirstPlayAtSecond.lean

Conditionals: nothing here shows that ready or runC returns, or that the part is called.

What it proves. FirstPlayAtRun.lean's two statements at the last chain ("the second chain" of the
format and of the frame; the frame's number 2): the Steps of one block of the chain, out of what
ready returns; and, at a run of the frame's walking prover, at a proximity test whose half the
prover's list for the last chain holds: the stand in front of the test's second part is the end of
the frame's own play of the first part's Steps.

Names.
  block_steps_at_second   the Steps of one block.
  first_play_at_second    the play of the first part, at a run.

By what. The proofs of block_steps_at_first and first_play_at_first (FirstPlayAtFirst.lean), with
the last chain's names; played_at_second (Sim/PlayedAtSecond.lean) in the place of the unfolding of
midAtW; the frame's start_live, walk_live (ProofFile/Honest/WalkLive.lean) for the verifier's start.

Limits.
- At a state on entry that is the job's own letter rec₀, not shown to be the verifier's.
- It says nothing of what the first part sends.
- In this chain the second stop may read the input: the Steps are laid at some R.own.
- A stand of this chain has seen the two earlier chains' rounds too (mid_second): so the last
  conjunct is "m.seen = m₀.seen ++ roundsOf y.1", not a cut of m.seen at the chain's own count. What
  m₀ has seen is not concluded.
- Third texts of two proofs, made by program.
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- Of the walk (runC). They move no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtSecond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest

/-- **The Steps of one block of the last chain, out of what ready returns**: block_steps_at_ready
(FirstPlayAtRun.lean) at the last chain. -/
theorem block_steps_at_second {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₃ F.Cl)) (b : Block F.S₃ F.Cl) (t : List (Block F.S₃ F.Cl))
    (hcut : F.second.blocksInOrder = pre ++ b :: t) (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.second.find? fun g => g.place == b.place) = some g) :
    ∃ (c : RowCoins g.parts) (l₁ l₂ : List (Step (Local W₀ Rc Xi Tr) Y)),
      lendRow Bk (Bk.rowsOf 2) (k.look 2) b.place g.parts 0 = .ok c ∧
      R.second = l₁ ++ (g.steps b (Face.own.sees R.own) c ++ l₂) ∧
      l₁.length = (pre.flatMap (·.rounds)).length ∧ b.oracles.length = b.rounds.length := by
  obtain ⟨-, tr, -, -, -, -, -, s3⟩ := ready_ok hR
  rw [hcut, chainSteps_append] at s3
  obtain ⟨l₁, h1, h2⟩ := exBind_ok s3
  obtain ⟨l', h3, e'⟩ := exMap_ok h2
  obtain ⟨ho, l₂, -, hcase⟩ := chainSteps_cons_ok h3
  rcases hcase with ⟨hn, -⟩ | ⟨g', c, hg', -, -, hl, e⟩
  · rw [hg] at hn
    cases hn
  · obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
    refine ⟨c, l₁, l₂, hl, by rw [← e', e], ?_, ho⟩
    rw [chainSteps_length pre l₁ h1, List.length_flatMap]

/-- **The play of a proximity test's first part, at a run, in the last chain**: first_play_at_run
(FirstPlayAtRun.lean) there. The second stop may read the input in this chain: the Steps are laid at
some R.own (the frame's Face.own.sees). m₀ stands under "there is": that it is the stand which
midAtW returns at the first part's own address is not said; what it has seen is not concluded here,
but that m has seen that and then the first part's own rounds. -/
theorem first_play_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl))
    (S : StandsAt F.second.blocksInOrder R.second σ u pre t (firstLen J.p.nums.stages))
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m₀ m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (y : List Played × ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      lendRow Bk (Bk.rowsOf 2) (k.look 2) σ.block.place
        [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J] 0 = .ok c ∧
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      play ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
          ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1)
        ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) [] m₀ =
        .ok y ∧
      y.2 = m ∧ m₀.st.input = R.own ∧
      m.seen = m₀.seen ++ roundsOf y.1 := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl1, ho⟩ :=
    block_steps_at_second hR pre σ.block t S.cut (proverSideOfProximityTest J) hg
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, -⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨-, -, lS⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  have hρ : ρ.second.length = R.second.length := lS.1
  have hfits := S.fits
  have hle := S.le
  -- the stand is a walk's own state
  obtain ⟨m₁, m₂, m, a₁, z₁, a₂, z₂, a₃, Yw, -, -, -, -, -, -, -, -, ha₃, hY, -, hYm, hm⟩ :=
    played_at_second hpl hR hrun σ u pre t _ _ S rfl hc
  obtain ⟨m₀', v₀, -, ev⟩ := start_live ha₃ (walk_live _ _ _ a₃ Yw m hY hYm)
  rw [ev, S.cut] at ha₃
  -- the first part's Steps stand behind pre's
  have hJl : firstLen J.p.nums.stages ≤ J.laid.length := by
    rw [← hlaid, List.length_zip, ho, Nat.min_self]
    omega
  have hA : ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
      ⟨σ.block.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1).length = firstLen J.p.nums.stages
          := by
    rw [steps_len, first_moves_len, List.length_take, Nat.min_eq_left hJl, Nat.min_self]
  have hsteps : R.second = l₁ ++ ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr)
      Y).steps
      σ.block.name ⟨σ.block.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1 ++
      (rowSteps σ.block.name σ.block.place (some R.own) [(restPart J : Part (Local W₀ Rc Xi Tr)
          (Local W₀ Rc Xi Tr) Y)] 1
        (J.laid.drop (firstLen J.p.nums.stages)) c.2 ++ l₂)) := by
    rw [hsh]
    have e : (proverSideOfProximityTest J : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block
        (Face.own.sees R.own) c =
        (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
            ⟨σ.block.place, 0⟩
          ((σ.block.rounds.zip σ.block.oracles).take
            (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length)
                (some R.own) c.1 ++
        rowSteps σ.block.name σ.block.place (some R.own)
          [(restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)] 1
          ((σ.block.rounds.zip σ.block.oracles).drop
            (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length) c.2 := rfl
    rw [e, hlaid, first_moves_len, List.append_assoc]
  have htakeS : R.second.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) = l₁ ++
      (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
          ⟨σ.block.place, 0⟩
        (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1 := by
    rw [hsteps, ← List.append_assoc, List.take_left']
    rw [List.length_append, hl1, hA]
  have htakeD : ρ.second.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) =
      ρ.second.take (pre.flatMap (·.rounds)).length ++
        (ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages) :=
    List.take_add
  rw [htakeS, htakeD] at hY
  have hLo : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (P.storedWords w₀ rc) (fun ch k => if ch == 0 then ((tablesOf z₁.laid)[k]?).bind id
        else if ch == 1 then ((tablesOf z₂.laid)[k]?).bind id else none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) z₁.laid z₂.laid ps).2).symm
  obtain ⟨zb, mb, ps, w1, hmb, hp, -⟩ := play_in_block
    ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ hLo pre
    σ.block t (R.start₃ P m₁ m₂) v₀ ha₃ hl1
    (by rw [List.length_take, hl1, Nat.min_eq_left (by omega)])
    (by
      rw [hA]
      have := S.pos
      omega)
    (fun s hs => steps_part0 _ _ s3 s (by
      rw [hsteps]
      exact List.mem_append_right _ (List.mem_append_left _ hs)))
    hY hYm
  obtain ⟨i0, -, -⟩ := walk_mid ha₃ w1 hmb
  refine ⟨c, mb, m, (ps, m), hl, hm, hp, rfl, ?_, (play_mid _ _ _ _ _ hp).2.2⟩
  rw [i0]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.block_steps_at_second
#print axioms ProofFile.Honest.K12.Light.first_play_at_second
