-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlayedStretch.lean

What the shared chain's walk (`walk`, Johnson/Desc/ProofFile/Honest/Walk.lean) has produced at one
sub-protocol, in front of a later round: that sub-protocol's half, played alone (the frame's `play`,
Honest/Frame.lean) from the state that the walk over the rounds in front of it holds. One theorem.
General in the description, the book, the prover and the half: no kind of sub-protocol is named.

  `played_stretch`: the statement.

What for. The authors of the honest side of the linear claim's shared rounds state what their rows
play in the form "`play` of the half's own Steps at b, at coins c, from a stand m, returns these
rounds" (`send_plays`, Honest/K14/SendingsPlay.lean; `split_plays`, Honest/K14/PartsPlay.lean).
`played_at_run` (Sim/PlayedAtRun.lean) says that what a run of the walking prover has produced in
front of a called part is what the chain's walk over the first so many prepared rounds produces.
This file stands between the two.

Beside it in this folder. `played_round`, `tell_move` (Sim/RoundInFront.lean): round by round;
`sender_in_front` (Sim/SenderInFront.lean): the tables of a sending's first round;
`first_play_at_run` (FirstPlayAtRun.lean): a test's first part. This one has a whole half's stretch
at once.

By what. `live_fold` (CalledFold.lean). Of the frame's authors' laws (Honest/Law/): `walk_cut`
(WalkMid.lean); `walk_append_ok`, `member_ok`, `lays_live`, `walk_nil_ok` (Rule/WalkLaw.lean);
`walk_len` (RunAtFile.lean); `settle_laid` (WalkOn.lean); `steps_part0` (RunMid.lean);
`chainSteps_append`, `envOf_tree` (Cut.lean); `chainSteps_cons_ok` (Rule/Member.lean);
`chainSteps_length` (Rule/ChainFile.lean); `ready_ok` (Run.lean); beside that folder `walk_live`
(Honest/WalkLive.lean), `walk_laid_length`, `start_laid` (Honest/WalkHeard.lean). The proof's first
lines are a second text of `block_steps_at_ready`'s (FirstPlayAtRun.lean), which does not state that
the half has as many Steps as b declares rounds.

Limits. The shared chain alone. Of the walk: of a `play` from the chain's start nothing is said. No
stored run to fall back on. The challenges of the stretch stand as a cut of the run's list: a caller
that wants them as a written list opens it. Nothing says that `ready` or the walk returns, or that a
filling holds any half. Steps of the frame's: no property of a prover or a protocol. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.RoundInFront
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtRun
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription)
open ProofFile.Honest

/-- **What the shared chain's walk has produced at one sub-protocol in front: that sub-protocol's
half, played alone from the state that the walk over the rounds in front of it holds.** Where
`ready` has returned R, the shared chain's flat list is cut as pre ++ b :: t, the prover has the
half g at b's place, and the shared chain's walk, from the start that `runC` lays, has returned z
over the first n prepared rounds with the prover's run still going on: the book has lent g's parts
their values c; and if n reaches behind g's Steps at b: the walk over the rounds in front of b has
returned zb, which has produced the first so many of z's rounds, with the run going on at a state
mb; g's own Steps at b, at that c, played alone from mb at b's stretch of the challenges, return;
and what they produce is b's stretch of what z has produced. General in the description, the book,
the prover and the half: no kind of sub-protocol is named. Inside one sub-protocol nothing is asked,
so there a walk is the frame's `play`; over several it is not: the asking between them lengthens the
field `opened`. -/
theorem played_stretch {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (g : Placed Empty (Common W₀ Rc Ky) X₀)
    (hg : (P.shared.find? fun g => g.place == b.place) = some g) (n : ℕ)
    (a₂ z : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
    (ha : ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
      (some (F.start₂ (F.pub x))) [] = .ok a₂)
    (hz : walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take n) (ρ.shared.take n) a₂ = .ok z)
    (hm : z.mid = some m) :
    ∃ c : RowCoins g.parts,
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) b.place g.parts 0 = .ok c ∧
      ((pre.flatMap (·.rounds)).length + (g.steps b (Face.shared.sees R.common) c).length ≤ n →
        ∃ (zb : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (mb : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
          (y : List Played × ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
          walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take (pre.flatMap (·.rounds)).length)
            (ρ.shared.take (pre.flatMap (·.rounds)).length) a₂ = .ok zb ∧
          zb.laid = z.laid.take (pre.flatMap (·.rounds)).length ∧ zb.mid = some mb ∧
          play (g.steps b (Face.shared.sees R.common) c)
            ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
              (g.steps b (Face.shared.sees R.common) c).length) [] mb = .ok y ∧
          y.1 = (z.laid.drop (pre.flatMap (·.rounds)).length).take
            (g.steps b (Face.shared.sees R.common) c).length) := by
  -- the Steps of b, out of what ready returns (the text of block_steps_at_ready, with two lengths)
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok hR
  have s2' := s2
  rw [hcut, chainSteps_append] at s2'
  obtain ⟨l₁, c1, c2⟩ := exBind_ok s2'
  obtain ⟨l', c3, el⟩ := exMap_ok c2
  obtain ⟨-, l₂, c4, hcase⟩ := chainSteps_cons_ok c3
  rcases hcase with ⟨hno, -⟩ | ⟨g', c, hg', -, -, hl, e⟩
  · rw [hg] at hno
    cases hno
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  refine ⟨c, hl, ?_⟩
  have eR : R.shared = l₁ ++ (g.steps b (Face.shared.sees R.common) c ++ l₂) := by rw [← el, e]
  have hlen' : l₁.length = (pre.flatMap (·.rounds)).length := by
    rw [chainSteps_length pre l₁ c1, List.length_flatMap]
  have hlen := hlen'
  have hG : (g.steps b (Face.shared.sees R.common) c).length = b.rounds.length := by
    have q3 := chainSteps_length (b :: t) l' c3
    have q4 := chainSteps_length t l₂ c4
    rw [e, List.length_append, q4, List.map_cons, List.sum_cons] at q3
    omega
  have hp0 : ∀ s ∈ g.steps b (Face.shared.sees R.common) c,
      s.move.isSome = false → s.addr.part = 0 :=
    fun s hs => steps_part0 _ _ s2 s (by
      rw [eR]
      exact List.mem_append_right _ (List.mem_append_left _ hs))
  have ha' := ha
  rw [hcut] at ha'
  have hLo : ∀ ps, treeOwn ps = (envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
  generalize g.steps b (Face.shared.sees R.common) c = G at eR hG hp0 ⊢
  generalize (pre.flatMap (·.rounds)).length = N at hlen ⊢
  intro hn
  -- the walk, cut behind b's Steps, and that piece cut in front of them
  have hL : (l₁ ++ G).length = N + G.length := by rw [List.length_append, hlen]
  have hle : N + G.length ≤ (R.shared.take n).length := by
    rw [List.length_take, eR, ← List.append_assoc, List.length_append, hL]
    omega
  obtain ⟨z₂, v1, v2, k1, -⟩ := walk_cut (start_laid ha) hz (N + G.length) hle
  have t1 : (R.shared.take n).take (N + G.length) = l₁ ++ G := by
    have t0 : (R.shared.take n).take (N + G.length) = R.shared.take (N + G.length) := by
      rw [List.take_take]
      congr 1
      omega
    rw [t0, eR, ← List.append_assoc, List.take_left' hL]
  have t2 : (ρ.shared.take n).take (N + G.length) =
      ρ.shared.take N ++ (ρ.shared.drop N).take G.length := by
    have t0 : (ρ.shared.take n).take (N + G.length) = ρ.shared.take (N + G.length) := by
      rw [List.take_take]
      congr 1
      omega
    rw [t0, List.take_add]
  rw [t1, t2] at v1
  have hw := walk_len _ _ _ a₂ z hz
  obtain ⟨zb, w1, w2⟩ := walk_append_ok G _ l₁ _ a₂ z₂ (by
    rw [List.length_take, hlen]
    rw [List.length_take] at hw
    omega) v1
  obtain ⟨m₂, hm₂⟩ := Option.isSome_iff_exists.1 (walk_live _ _ _ z₂ z m v2 hm)
  have live : zb.mid.isSome = true := walk_live _ _ _ zb z₂ m₂ w2 hm₂
  obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.1 live
  have hzl : zb.laid.length = N := by
    rw [walk_laid_length _ _ _ a₂ zb w1, start_laid ha, List.length_nil, Nat.zero_add, hlen]
  -- b's Steps, walked from zb, are the frame's play from mb
  obtain ⟨y, hy, hyl⟩ : ∃ y : List Played × ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀,
      play G ((ρ.shared.drop N).take G.length) [] mb = .ok y ∧ z₂.laid = zb.laid ++ y.1 := by
    by_cases hne : G = []
    · subst hne
      rw [List.length_nil, List.take_zero] at w2 ⊢
      obtain rfl := walk_nil_ok w2
      refine ⟨([], mb), ?_, (List.append_nil _).symm⟩
      rw [play]
    · have hb : 0 < b.rounds.length := by
        rw [← hG]
        exact Nat.pos_of_ne_zero fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
      obtain ⟨s, -, hown, htodo, -, -⟩ := live_fold ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ hLo pre b t
        hb (R.start₂ P) (F.start₂ (F.pub x)) ha' w1 hlen' live
      obtain ⟨yy, hyy, hs⟩ := member_ok G _ zb z₂ htodo
        (by rw [hown, List.length_nil, Nat.zero_add, hG]) hne w2
      rw [hmb] at hyy
      obtain ⟨m', -, hp⟩ := lays_live G _ mb yy hp0 hyy
      refine ⟨(yy.1, m'), hp, ?_⟩
      rw [settle_laid _ _ _ z₂ hs]
      rfl
  refine ⟨zb, mb, y, ?_, ?_, hmb, hy, ?_⟩
  · have a : R.shared.take N = l₁ := by
      rw [eR]
      exact List.take_left' hlen
    rw [a]
    exact w1
  · have q : (z.laid.take (N + G.length)).take N = zb.laid := by
      rw [← k1, hyl]
      exact List.take_left' hzl
    rw [← q, List.take_take]
    congr 1
    omega
  · have q : (z.laid.take (N + G.length)).drop N = y.1 := by
      rw [← k1, hyl]
      exact List.drop_left' hzl
    rw [← q, List.drop_take]
    congr 1
    omega

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.played_stretch
