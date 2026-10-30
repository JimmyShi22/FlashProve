-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FirstPlayAtRun.lean

What it proves. How the frame's own play of a proximity test's first part is had at a run of the
frame's walking prover (runC). (1) Out of what ready returns: the Steps of one block of the shared
chain are its half's own Steps at the values that the book has lent, and the lending has returned:
both at one c (block_steps_at_ready). (2) At the stand in front of the test's second part (the state
that midSharedAtW returns, ProofFile/Honest/MidW.lean), where that part is called: that stand is
where the play of the first part's Steps ends, at the lent values and at the shared challenges' own
stretch, from a stand that has the run's input and has seen what the blocks in front have shown
(first_play_at_run). General in the description, the book, the prover and the job.

What for. The laws on the first part's play (Sim/PlayedFirst.lean, Sim/OnFromPlay.lean,
Sim/OnFromLent.lean) are at every stand m₀ and conclude that the play returns; play is a function:
so with (2) what they say of the play's end is said of the run's stand.

Names.
  block_steps_at_ready   (1).
  steps_len, first_moves_len   the number of a part's Steps; of the first part's moves.
  play_in_block          general in the chain: inside one block, short of its last round, a walk is
      the frame's play from the walk's own state in front of the block.
  first_play_at_run      (2).

By what. called_at_run (CalledAtRun.lean); movesFrom_length (TwoTypesLaw.lean). Of the frame's laws
(ProofFile/Honest/Law/): ready_ok (Run.lean); chainSteps_append (Cut.lean); chainSteps_cons_ok
(Rule/Member.lean); chainSteps_length (Rule/ChainFile.lean); exBind_ok, exMap_ok (Play.lean);
play_mid, steps_shaped (Along.lean); runC_laidAs (RunAtFile.lean); stretch_back (OwedParts.lean);
walk_append_ok, lays_live (Rule/WalkLaw.lean); walk_in, walk_mid (WalkMid.lean); steps_part0
(RunMid.lean); envOf_tree (Cut.lean). Beside that folder: walk_live (WalkLive.lean);
walk_laid_length, start_laid (WalkHeard.lean). live_fold (CalledFold.lean).

Limits.
- At a state on entry that is the job's own letter rec₀, not shown to be the verifier's.
- It says nothing of what the first part sends, and nothing of what is lent but that the lending
  returns.
- m₀ stands under "there is": that it is the stand which midSharedAtW returns at the first part's
  own address is not said. Of m₀ the input and what it has seen are said; what it has heard, what
  the parts pass on and its field opened are not.
- hg, hlaid are premises: on the filling; public at the place.
- Of the walk (runC); nothing on whether ready or runC returns, or whether the part is called.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- It moves no count. Steps of the frame's: no property of a prover or a protocol. Nothing on
  completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledAtRun
import Johnson.Desc.ProofFile.Honest.K12.TwoTypesLaw
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest

/-- **The Steps of one block of the shared chain, out of what ready returns.** Where ready has
returned R, the shared chain's flat list is cut as pre ++ b :: t, and the prover has the half g at
b's place: the book has lent g's parts their values, c; and R's shared Steps are: as many as pre
declares rounds; then g's own Steps at b, at that same c; then others. Besides: b states oracle
messages for as many rounds as it declares. -/
theorem block_steps_at_ready {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == b.place) = some g) :
    ∃ (c : RowCoins g.parts) (l₁ l₂ : List (Step (Common W₀ Rc Ky) X₀)),
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) b.place g.parts 0 = .ok c ∧
      R.shared = l₁ ++ (g.steps b (Face.shared.sees R.common) c ++ l₂) ∧
      l₁.length = (pre.flatMap (·.rounds)).length ∧ b.oracles.length = b.rounds.length := by
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok hR
  rw [hcut, chainSteps_append] at s2
  obtain ⟨l₁, h1, h2⟩ := exBind_ok s2
  obtain ⟨l', h3, e'⟩ := exMap_ok h2
  obtain ⟨ho, l₂, -, hcase⟩ := chainSteps_cons_ok h3
  rcases hcase with ⟨hn, -⟩ | ⟨g', c, hg', -, -, hl, e⟩
  · rw [hg] at hn
    cases hn
  · obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
    refine ⟨c, l₁, l₂, hl, by rw [← e', e], ?_, ho⟩
    rw [chainSteps_length pre l₁ h1, List.length_flatMap]

/-- A part's Steps are as many as the shorter of its rounds and its moves. -/
theorem steps_len {V W X : Type} (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    (p.steps name a rs v c).length = min rs.length p.moves.length := by
  unfold Part.steps
  rw [List.length_map, List.length_zipIdx, List.length_zip]

/-- The first part has as many moves as firstLen counts. -/
theorem first_moves_len {V W X : Type} (J : TestJob W X) :
    (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
  unfold firstPart
  split <;> exact movesFrom_length _ _ _ _

/-- **Inside one block, short of its last round, a chain's walk is the frame's own play from the
walk's state in front of the block.** General in the chain. l₁: as many Steps as the blocks pre
declare rounds; A: Steps behind them, fewer than b declares rounds. Where the walk over l₁ ++ A has
returned z and the prover's run is going on there, at m: the walk over l₁ alone has returned zb, the
run is going on there, at mb; play over A from mb returns m; and what z has produced is what zb has
produced and then that play's rounds.
Why: between two rounds of one block nothing is asked, so the field opened stands still (the frame's
walk_in, Law/WalkMid.lean; lays_live, Law/Rule/WalkLaw.lean). hp0: a Step without a move stands
under the part 0, as chainSteps prepares them. hL: the Lay's tree is envOf's. Of the walk; pre, v₀
and front₀ are free. -/
theorem play_in_block {S Cl W Y : Type} (L : Lay)
    {taken : ℕ → ℕ → Option (VerifiableInference.Desc.Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (m₀ : ProofFile.Honest.Mid W Y) (v₀ : S)
    {a z : ChainProgress S Cl W Y} {front₀ : List VerifiableInference.Desc.OpenedColumn} {l₁ A : List (Step W Y)}
    {d₁ dA : List Fmt.Drawn} {m : ProofFile.Honest.Mid W Y}
    (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some v₀) front₀ = .ok a)
    (hl₁ : l₁.length = (pre.flatMap (·.rounds)).length) (hd₁ : d₁.length = l₁.length)
    (hA : A.length < b.rounds.length)
    (hp0 : ∀ s ∈ A, s.move.isSome = false → s.addr.part = 0)
    (hz : walk L (l₁ ++ A) (d₁ ++ dA) a = .ok z) (hm : z.mid = some m) :
    ∃ (zb : ChainProgress S Cl W Y) (mb : ProofFile.Honest.Mid W Y) (ps : List Played),
      walk L l₁ d₁ a = .ok zb ∧ zb.mid = some mb ∧ play A dA [] mb = .ok (ps, m) ∧
        z.laid = zb.laid ++ ps := by
  obtain ⟨zb, h1, h2⟩ := walk_append_ok A dA l₁ d₁ a z hd₁ hz
  have live : zb.mid.isSome = true := walk_live L A dA zb z m h2 hm
  obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.1 live
  obtain ⟨s, -, hown, htodo, -, -⟩ := live_fold L hL pre b t (Nat.lt_of_le_of_lt (Nat.zero_le _) hA)
    m₀ v₀ ha h1 hl₁ live
  obtain ⟨y, hy, e⟩ := walk_in A dA zb z htodo
    (by rw [hown, List.length_nil, Nat.zero_add]; exact hA) h2
  rw [hmb] at hy
  obtain ⟨m', e', hp⟩ := lays_live A dA mb y hp0 hy
  have g : z.mid = y.2 := by
    rw [e]
    rfl
  rw [hm, e'] at g
  obtain rfl : m = m' := Option.some.inj g
  refine ⟨zb, mb, y.1, h1, hmb, hp, ?_⟩
  rw [e]
  rfl

/-- **The play of a proximity test's first part, at a run of the frame's walking prover.** J: a
test's job; the prover's half at the side's block is the test's pair (hg); the block's declared
rounds with their oracle messages are the job's (hlaid). At the stand m in front of the second part
(S at i := the first part's number of rounds), where that part is called: the book has lent the pair
its values, c; and m is where the frame's own play of the first part's Steps, at c's first component
and at the shared challenges' stretch behind the first N, ends, from a stand m₀ that has the run's
input and has seen what m has seen of the blocks in front.
Public: hpl, hlaid. On the filling and the book: hR, S, hg. On the run: hrun, hc.
It says nothing of what the first part sends. Of the walk (runC); nothing on whether runC returns or
calls the part. -/
theorem first_play_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Common W₀ Rc Ky) X₀) (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t (firstLen J.p.nums.stages))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (c : RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀), restPart J])
      (m₀ m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (y : List Played × ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) σ.block.place
        [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀), restPart J] 0 = .ok c ∧
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      play ((firstPart J : Part Empty (Common W₀ Rc Ky) X₀).steps σ.block.name ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) none c.1)
        ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) [] m₀ =
        .ok y ∧
      y.2 = m ∧ m₀.st.input = ⟨w₀, rc, P.key x⟩ ∧
      m₀.seen = m.seen.take (pre.flatMap (·.rounds)).length := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl1, ho⟩ :=
    block_steps_at_ready hR pre σ.block t S.cut (proverSideOfProximityTest J) hg
  obtain ⟨m, -, -, -, -, hm, -, -, hlen, -, -, -⟩ := called_at_run hpl hR σ u pre t _ S hrun hc
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, hcom, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, -⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨-, lS, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  have hρ : ρ.shared.length = R.shared.length := lS.1
  have hfits := S.fits
  have hle := S.le
  -- the stand is a walk's own state
  have h0 := hm
  unfold midSharedAtW at h0
  obtain ⟨R', hR', h0⟩ := exBind_ok h0
  rw [hR] at hR'
  cases hR'
  obtain ⟨a₂, ha₂, h1⟩ := exBind_ok h0
  unfold midInW at h1
  split at h1
  · cases h1
  obtain ⟨Y, hY, hYm⟩ := exMap_ok h1
  rw [hN] at hY
  -- the first part's Steps stand behind pre's
  have hJl : firstLen J.p.nums.stages ≤ J.laid.length := by
    rw [← hlaid, List.length_zip, ho, Nat.min_self]
    omega
  have hA : ((firstPart J : Part Empty (Common W₀ Rc Ky) X₀).steps σ.block.name ⟨σ.block.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) none c.1).length = firstLen J.p.nums.stages := by
    rw [steps_len, first_moves_len, List.length_take, Nat.min_eq_left hJl, Nat.min_self]
  have hsteps : R.shared = l₁ ++ ((firstPart J : Part Empty (Common W₀ Rc Ky) X₀).steps
      σ.block.name ⟨σ.block.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) none c.1 ++
      (rowSteps σ.block.name σ.block.place none [(restPart J : Part Empty (Common W₀ Rc Ky) X₀)] 1
        (J.laid.drop (firstLen J.p.nums.stages)) c.2 ++ l₂)) := by
    rw [hsh]
    have e : (proverSideOfProximityTest J : Placed Empty (Common W₀ Rc Ky) X₀).steps σ.block
        (Face.shared.sees R.common) c =
        (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).steps σ.block.name ⟨σ.block.place, 0⟩
          ((σ.block.rounds.zip σ.block.oracles).take
            (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length) none c.1 ++
        rowSteps σ.block.name σ.block.place none
          [(restPart J : Part Empty (Common W₀ Rc Ky) X₀)] 1
          ((σ.block.rounds.zip σ.block.oracles).drop
            (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length) c.2 := rfl
    rw [e, hlaid, first_moves_len, List.append_assoc]
  have htakeS : R.shared.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) = l₁ ++
      (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).steps σ.block.name ⟨σ.block.place, 0⟩
        (J.laid.take (firstLen J.p.nums.stages)) none c.1 := by
    rw [hsteps, ← List.append_assoc, List.take_left']
    rw [List.length_append, hl1, hA]
  have htakeD : ρ.shared.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) =
      ρ.shared.take (pre.flatMap (·.rounds)).length ++
        (ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages) :=
    List.take_add
  rw [htakeS, htakeD] at hY
  rw [S.cut] at ha₂
  have hLo : ∀ ps, treeOwn ps = (envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
  obtain ⟨zb, mb, ps, w1, hmb, hp, -⟩ := play_in_block ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ hLo pre
    σ.block t (R.start₂ P) (F.start₂ (F.pub x)) ha₂ hl1
    (by rw [List.length_take, hl1, Nat.min_eq_left (by omega)])
    (by
      rw [hA]
      have := S.pos
      omega)
    (fun s hs => steps_part0 _ _ s2 s (by
      rw [hsteps]
      exact List.mem_append_right _ (List.mem_append_left _ hs)))
    hY hYm
  obtain ⟨i0, -, sn0⟩ := walk_mid ha₂ w1 hmb
  have snz : m.seen = mb.seen ++ roundsOf ps := (play_mid _ _ _ _ _ hp).2.2
  have hlen0 : zb.laid.length = (pre.flatMap (·.rounds)).length := by
    rw [walk_laid_length _ _ _ a₂ zb w1, start_laid ha₂, List.length_nil, Nat.zero_add, hl1]
  have hs0 : mb.seen = roundsOf zb.laid := by
    rw [sn0]
    rfl
  refine ⟨c, mb, m, (ps, m), hl, hm, hp, rfl, ?_, ?_⟩
  · rw [i0]
    exact hcom
  · rw [snz, List.take_left']
    rw [hs0, roundsOf_length, hlen0]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.block_steps_at_ready
#print axioms ProofFile.Honest.K12.Light.steps_len
#print axioms ProofFile.Honest.K12.Light.first_moves_len
#print axioms ProofFile.Honest.K12.Light.play_in_block
#print axioms ProofFile.Honest.K12.Light.first_play_at_run
