-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FirstPlayAtFirst.lean

What it proves. FirstPlayAtRun.lean's two statements at the first chain: (1) out of what ready
returns: the Steps of one block of the first chain are its half's own Steps at the values that the
book has lent, and the lending has returned: both at one c (block_steps_at_first); (2) at the stand
in front of a proximity test's second part, where that part is called: that stand is where the
frame's own play of the first part's Steps ends (first_play_at_first). General in the description,
the book, the prover and the job.

Names.
  block_steps_at_first   (1).
  first_play_at_first    (2).

By what. called_at_first (CalledAtFirst.lean); steps_len, first_moves_len, play_in_block
(FirstPlayAtRun.lean); the frame's laws that FirstPlayAtRun.lean's head names, at the first chain's
letters.

Limits.
- The two proofs are second texts of FirstPlayAtRun.lean's, with the first chain's names. In this
  chain the second stop may read the input: the Steps are laid at some R.own.
- It says nothing of what the first part sends, and nothing of what is lent but that the lending
  returns. m₀ stands under "there is": of it the input and what it has seen are said.
- hg, hlaid are premises: on the filling; public at the place.
- Of the walk (runC); nothing on whether ready or runC returns, or whether the part is called.
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledAtFirst
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest

/-- **The Steps of one block of the first chain, out of what ready returns**: block_steps_at_ready
(FirstPlayAtRun.lean) at the first chain. -/
theorem block_steps_at_first {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == b.place) = some g) :
    ∃ (c : RowCoins g.parts) (l₁ l₂ : List (Step (Local W₀ Rc Xi Tr) Y)),
      lendRow Bk (Bk.rowsOf 0) (k.look 0) b.place g.parts 0 = .ok c ∧
      R.first = l₁ ++ (g.steps b (Face.own.sees R.own) c ++ l₂) ∧
      l₁.length = (pre.flatMap (·.rounds)).length ∧ b.oracles.length = b.rounds.length := by
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  rw [hcut, chainSteps_append] at s1
  obtain ⟨l₁, h1, h2⟩ := exBind_ok s1
  obtain ⟨l', h3, e'⟩ := exMap_ok h2
  obtain ⟨ho, l₂, -, hcase⟩ := chainSteps_cons_ok h3
  rcases hcase with ⟨hn, -⟩ | ⟨g', c, hg', -, -, hl, e⟩
  · rw [hg] at hn
    cases hn
  · obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
    refine ⟨c, l₁, l₂, hl, by rw [← e', e], ?_, ho⟩
    rw [chainSteps_length pre l₁ h1, List.length_flatMap]

/-- **The play of a proximity test's first part, at a run, in the first chain**: first_play_at_run
(FirstPlayAtRun.lean) there. The second stop may read the input in this chain: the Steps are laid at
some R.own (the frame's Face.own.sees). -/
theorem first_play_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl))
    (S : StandsAt F.first.blocksInOrder R.first σ u pre t (firstLen J.p.nums.stages))
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m₀ m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (y : List Played × ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      lendRow Bk (Bk.rowsOf 0) (k.look 0) σ.block.place
        [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J] 0 = .ok c ∧
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      play ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
          ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1)
        ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) [] m₀ =
        .ok y ∧
      y.2 = m ∧ m₀.st.input = R.own ∧
      m₀.seen = m.seen.take (pre.flatMap (·.rounds)).length := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl1, ho⟩ :=
    block_steps_at_first hR pre σ.block t S.cut (proverSideOfProximityTest J) hg
  obtain ⟨m, -, -, -, -, -, hm, -, -, -, hlen, -, -, -⟩ := called_at_first hpl hR σ u pre t _ S hrun
      hc
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, -⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  have hρ : ρ.first.length = R.first.length := lS.1
  have hfits := S.fits
  have hle := S.le
  -- the stand is a walk's own state
  have h0 := hm
  unfold midAtW at h0
  obtain ⟨R', hR', h0⟩ := exBind_ok h0
  rw [hR] at hR'
  cases hR'
  obtain ⟨a₁, ha₁, h1⟩ := exBind_ok h0
  split at h1
  case isFalse hno => exact absurd ha hno
  unfold midInW at h1
  split at h1
  · cases h1
  obtain ⟨Yp, hY, hYm⟩ := exMap_ok h1
  rw [hN] at hY
  -- the first part's Steps stand behind pre's
  have hJl : firstLen J.p.nums.stages ≤ J.laid.length := by
    rw [← hlaid, List.length_zip, ho, Nat.min_self]
    omega
  have hA : ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
      ⟨σ.block.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1).length = firstLen J.p.nums.stages
          := by
    rw [steps_len, first_moves_len, List.length_take, Nat.min_eq_left hJl, Nat.min_self]
  have hsteps : R.first = l₁ ++ ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr)
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
  have htakeS : R.first.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) = l₁ ++
      (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
          ⟨σ.block.place, 0⟩
        (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1 := by
    rw [hsteps, ← List.append_assoc, List.take_left']
    rw [List.length_append, hl1, hA]
  have htakeD : ρ.first.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) =
      ρ.first.take (pre.flatMap (·.rounds)).length ++
        (ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages) :=
    List.take_add
  rw [htakeS, htakeD] at hY
  rw [S.cut] at ha₁
  have hLo : ∀ ps, treeOwn ps = (envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
  obtain ⟨zb, mb, ps, w1, hmb, hp, -⟩ := play_in_block ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ hLo pre
    σ.block t (R.start₁ P) (F.start₁ (F.pub x)) ha₁ hl1
    (by rw [List.length_take, hl1, Nat.min_eq_left (by omega)])
    (by
      rw [hA]
      have := S.pos
      omega)
    (fun s hs => steps_part0 _ _ s1 s (by
      rw [hsteps]
      exact List.mem_append_right _ (List.mem_append_left _ hs)))
    hY hYm
  obtain ⟨i0, -, sn0⟩ := walk_mid ha₁ w1 hmb
  have snz : m.seen = mb.seen ++ roundsOf ps := (play_mid _ _ _ _ _ hp).2.2
  have hlen0 : zb.laid.length = (pre.flatMap (·.rounds)).length := by
    rw [walk_laid_length _ _ _ a₁ zb w1, start_laid ha₁, List.length_nil, Nat.zero_add, hl1]
  have hs0 : mb.seen = roundsOf zb.laid := by
    rw [sn0]
    rfl
  refine ⟨c, mb, m, (ps, m), hl, hm, hp, rfl, ?_, ?_⟩
  · rw [i0]
    rfl
  · rw [snz, List.take_left']
    rw [hs0, roundsOf_length, hlen0]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.block_steps_at_first
#print axioms ProofFile.Honest.K12.Light.first_play_at_first
