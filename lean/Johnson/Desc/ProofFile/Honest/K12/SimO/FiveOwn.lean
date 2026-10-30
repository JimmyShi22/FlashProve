-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at a proximity test whose first fold sends its own fresh table: five clauses at a run, behind the guard.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/FiveOwn.lean: the clauses le, leS, heardFit, heard, fold of `OnFreeOwn` (SimO/Free.lean) at a run of the frame's walking prover, at the stand in front of the test's second part, where the first fold sends its own fresh table and the prover lays the pair behind the guard (`needsField`). Twin of FiveAtRun.lean, which serves a table that came earlier, and a bare pair.

  `lendPart_own`            a part's own coins are the cut of its address's coins from 0 on
  `agree_own`               the two parts' readers agree where the second part carries the first part's own coins: premises on the book's entries
  `five_of_lent_own`        the five where the play of the first part ends
  `first_play_guarded`      the play of the bare first part ends at the stand, at a prover that lays the pair behind the guard: the field holds columns there, so the guard lets all through
  `five_own_at_run`         **the five at a run**

Limits. Conditional on the run: nothing here shows that ready or runC returns, or that the part is called. `hrows`, `ho`, `hst`, `hm` are premises on the job's text and on the book: no real book is evaluated here. At a state on entry that is the job's own letter. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Door
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard
import Johnson.Desc.ProofFile.Honest.K12.FiveAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC midSharedAtW
  Before Placed Part lendRow lendPart lend carryE spentE Ahead Addr Step play needsField_length
  exBind_ok exMap_ok lendRow_cons_ok lendPart_ok)

variable {V W X : Type}

theorem lendPart_own {Bk : ProverCoinCounts} {rows : List (Addr × ProofFile.Honest.Due)}
    {look : Addr → (d : ProofFile.Honest.Due) × ProofFile.Honest.Cs d} {a : Addr} {p : Part V W X} {c : p.Coins}
    (h : lendPart Bk rows look a p = .ok c) : (look a).2.cut ⟨0, 0⟩ p.takes = some c.1 := by
  unfold lendPart at h
  simp only at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i own hcut
  obtain ⟨sp, hsp, h⟩ := exBind_ok h
  obtain ⟨ca, hca, e⟩ := exMap_ok h
  subst e
  exact hcut

/-- **The two readers agree** where the second part carries the first part's own coins. -/
theorem agree_own (p : P12) (ms : List (Addr × ℕ × ProofFile.Honest.Due)) (r : W → Front X → T12)
    (ro : W → Front X → (ℕ → Stretch) → PS)
    (tr : W → Front X → (ℕ → Stretch) → PS → List Tree) (Bk : ProverCoinCounts)
    (look : Addr → (d : ProofFile.Honest.Due) × ProofFile.Honest.Cs d)
    (c₁ : (firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X).Coins)
    (c₂ : (restPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X).Coins)
    (own : (look ⟨p.place, 0⟩).2.cut ⟨0, 0⟩ (firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X).takes = some c₁.1)
    (k₁ : lend look (firstPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X).carries (carryE Bk ⟨p.place, 0⟩) = .ok c₁.2.2)
    (k₂ : lend look (restPart ⟨p, ms, none, r, ro, tr⟩ : Part V W X).carries (carryE Bk ⟨p.place, 0 + 1⟩) = .ok c₂.2.2)
    (w : W) (fr : Front X) (e₂ : Ahead) (hf : (carryE Bk ⟨p.place, 0 + 1⟩)[ms.length]? = some e₂)
    (ho : e₂.owner = ⟨p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hm : ∀ t, t < ms.length → ∃ a a', (carryE Bk ⟨p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr mem) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr mem')) :
    Agree ⟨p, ms, none, r, ro, tr⟩ w fr (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)
      (firstRd ⟨p, ms, none, r, ro, tr⟩ c₁) (restCoins ⟨p, ms, none, r, ro, tr⟩ c₂) := by
  obtain ⟨q2, x2, k2', z2⟩ := lend_stretch look _ _ _ k₂ ms.length e₂ hf
  have n2 : e₂.count = ⟨0, dueFresh (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)⟩ := by
    have e : ((memberRuns (⟨p, ms, none, r, ro, tr⟩ : TestJob W X) ⟨p.place, 1⟩ ++
        [freshRun ⟨p, ms, none, r, ro, tr⟩])[ms.length]?).map (·.2) = some e₂.count := q2
    rw [List.getElem?_append_right (by simp [memberRuns])] at e
    simp only [memberRuns, List.length_map, Nat.sub_self, List.getElem?_cons_zero,
      Option.map_some] at e
    exact (Option.some.inj e).symm
  have hs : ProofFile.Honest.K12.stretches _ c₂.2.2 ms.length = stretchOf c₁.1 := by
    rw [z2]
    exact stretch_tie look e₂
      { e₂ with owner := ⟨p.place, 0⟩, start := ⟨0, 0⟩, count := ⟨0, dueFresh (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)⟩ }
      x2 c₁.1 k2' own ho hst n2
  refine ⟨?_, ?_, fun _ => ?_⟩
  · show hideAt _ (stretchOf c₁.1).e = hideAt _ (ProofFile.Honest.K12.stretches _ c₂.2.2 ms.length).e
    rw [hs]
  · have e : ∀ K : TestCoins, μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩))
        (TestJob.first ⟨p, ms, none, r, ro, tr⟩ w fr K) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)) (ro w fr K.mem) := fun K => by
      funext x
      cases x <;> rfl
    rw [e, e]
    refine hrows _ _ fun t ht => ?_
    obtain ⟨a, a', ha, ha', o1, o2, o3⟩ := hm t ht
    obtain ⟨-, x1, k3, z1⟩ := lend_stretch look _ _ _ k₁ t a ha
    obtain ⟨-, y2, k4, z3⟩ := lend_stretch look _ _ _ k₂ t a' ha'
    show ProofFile.Honest.K12.stretches _ c₁.2.2 t = ProofFile.Honest.K12.stretches _ c₂.2.2 t
    rw [z1, z3]
    exact stretch_tie look a a' x1 y2 k3 k4 o1 o2 o3
  · show tailsIn _ (stretchOf c₁.1).e = tailsIn _ (ProofFile.Honest.K12.stretches _ c₂.2.2 ms.length).e
    rw [hs]

theorem five_of_lent_own (J : TestJob W X) (hfr : J.fresh = none) (Bk : ProverCoinCounts)
    (look : Addr → (d : ProofFile.Honest.Due) × ProofFile.Honest.Cs d)
    (c₁ : (firstPart J : Part V W X).Coins) (c₂ : (restPart J : Part V W X).Coins)
    (own : (look ⟨J.p.place, 0⟩).2.cut ⟨0, 0⟩ (firstPart J : Part V W X).takes = some c₁.1)
    (k₁ : lend look (firstPart J : Part V W X).carries (carryE Bk ⟨J.p.place, 0⟩) = .ok c₁.2.2)
    (k₂ : lend look (restPart J : Part V W X).carries (carryE Bk ⟨J.p.place, 0 + 1⟩) = .ok c₂.2.2)
    (e₂ : Ahead) (hf : (carryE Bk ⟨J.p.place, 0 + 1⟩)[J.members.length]? = some e₂)
    (ho : e₂.owner = ⟨J.p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < J.members.length → ∃ a a', (carryE Bk ⟨J.p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨J.p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count) (name : String) (ad : Addr) (v : Option V)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : ProofFile.Honest.Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ m₀.st.input (frontBy m₀ 0) mem) =
        μOf (sgOf s) (J.rows₀ m₀.st.input (frontBy m₀ 0) mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds = true)
    (front : Before) :
    ∃ y, play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
        c₁) ds [] m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen →
        firstLen J.p.nums.stages ≤ y.2.st.heard.length ∧
        firstLen J.p.nums.stages ≤ y.2.seen.length ∧
        drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
          (y.2.st.lately (firstLen J.p.nums.stages)) = true ∧
        (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
          y.2.st.lately (firstLen J.p.nums.stages) ∧
        (lastSeen front (firstLen J.p.nums.stages)).tail =
          aFold (coinsOf J.p.nums.stages (carriedCoins J (stretches _ c₂.2.2)).hide fun _ => 0) 0
            J.s₀ 1
            (rowsAt J (stretches _ c₂.2.2) y.2)
            (rowOf (J.recB y.2.st.input (restFront J y.2) (heardIn J y.2 0))) (heardIn J y.2)) := by
  obtain ⟨p, ms, fresh, r, ro, tr⟩ := J
  obtain rfl : fresh = none := hfr
  have hs0 : (⟨p, ms, none, r, ro, tr⟩ : TestJob W X).s₀ = s := by
    have := T.stages
    show p.nums.stages.headD default = s
    rw [show p.nums.stages = s :: next :: rest from this]
    rfl
  have Ag := agree_own p ms r ro tr Bk look c₁ c₂ own k₁ k₂ m₀.st.input (frontBy m₀ 0) e₂ hf ho hst hmem
    (by rw [hs0]; exact hrows)
  rw [hs0] at Ag
  exact five_of_play _ _ name ad v s next rest m₀ D ds T hk c₁ hfit
    (agree_carried _ _ _ _ _ c₂ Ag) front

/-- **The play of the bare first part ends at the stand**, at a prover that lays the pair behind the guard. -/
theorem first_play_guarded {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Common W₀ Rc Ky) X₀) (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t (firstLen J.p.nums.stages))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (c : ProofFile.Honest.RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField, (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField])
      (m₀ m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (y : List Played × ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) σ.block.place
        [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField, (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField] 0 = .ok c ∧
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      play ((firstPart J : Part Empty (Common W₀ Rc Ky) X₀).steps σ.block.name ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) none c.1)
        ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) [] m₀ =
        .ok y ∧
      y.2 = m ∧ m₀.st.input = ⟨w₀, rc, P.key x⟩ ∧
      m₀.seen = m.seen.take (pre.flatMap (·.rounds)).length ∧
      y.1 = (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).drop
        (pre.flatMap (·.rounds)).length := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl1, ho⟩ :=
    block_steps_at_ready hR pre σ.block t S.cut (proverSideOfProximityTest J : Placed Empty _ _).needsField hg
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
  obtain ⟨a₂', y', m', ha', hy', hl', -, -⟩ := played_at_run hpl hR hrun σ u pre t _ _ S rfl hc
  have eA : a₂' = a₂ := Except.ok.inj (ha'.symm.trans ha₂)
  rw [eA] at hy'
  have eY : y' = Y := Except.ok.inj (hy'.symm.trans hY)
  rw [eY] at hl'
  -- the first part's Steps stand behind pre's
  have hJl : firstLen J.p.nums.stages ≤ J.laid.length := by
    rw [← hlaid, List.length_zip, ho, Nat.min_self]
    omega
  have hA : ((firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.steps σ.block.name ⟨σ.block.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) none c.1).length = firstLen J.p.nums.stages := by
    rw [steps_len, needsField_length, first_moves_len, List.length_take, Nat.min_eq_left hJl, Nat.min_self]
  have hsteps : R.shared = l₁ ++ ((firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.steps
      σ.block.name ⟨σ.block.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) none c.1 ++
      (rowSteps σ.block.name σ.block.place none [(restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField] 1
        (J.laid.drop (firstLen J.p.nums.stages)) c.2 ++ l₂)) := by
    rw [hsh]
    have e : (proverSideOfProximityTest J : Placed Empty (Common W₀ Rc Ky) X₀).needsField.steps σ.block
        (Face.shared.sees R.common) c =
        (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.steps σ.block.name ⟨σ.block.place, 0⟩
          ((σ.block.rounds.zip σ.block.oracles).take
            (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.moves.length) none c.1 ++
        rowSteps σ.block.name σ.block.place none
          [(restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField] 1
          ((σ.block.rounds.zip σ.block.oracles).drop
            (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.moves.length) c.2 := rfl
    rw [e, hlaid, needsField_length, first_moves_len, List.append_assoc]
  have htakeS : R.shared.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) = l₁ ++
      (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.steps σ.block.name ⟨σ.block.place, 0⟩
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
  obtain ⟨zb, mb, ps, w1, hmb, hp, hzl⟩ := play_in_block ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ hLo pre
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
  obtain ⟨m2, -, cs, hm2, hop, -, -⟩ := ProofFile.Honest.K12.Sim2.called_columns hpl hR hrun σ u pre t _ S hc
  have emm : m2 = m := Option.some.inj (Except.ok.inj (hm2.symm.trans hm))
  rw [emm] at hop
  have hopb : mb.opened = some cs := by
    have := ProofFile.Honest.play_opened _ _ _ _ _ hp
    exact this.symm.trans hop
  have hgs := steps_needsField (firstPart J : Part Empty (Common W₀ Rc Ky) X₀) σ.block.name ⟨σ.block.place, 0⟩
    (J.laid.take (firstLen J.p.nums.stages)) none c.1
  rw [hgs, ProofFile.Honest.play_guarded _ _ _ _ cs hopb] at hp
  refine ⟨c, mb, m, (ps, m), hl, hm, hp, rfl, ?_, ?_, ?_⟩
  · rw [i0]
    exact hcom
  · rw [snz, List.take_left']
    rw [hs0, roundsOf_length, hlen0]
  · show ps = _
    rw [← hl', hzl, ← hlen0, List.drop_left]

/-- **The five at a run.** -/
theorem five_own_at_run {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Common W₀ Rc Ky) X₀) (hfr : J.fresh = none)
    (Js : SimJob Pb)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Pb) (u : Member Empty (Common W₀ Rc Ky) X₀ Pb)
    (hu : u.number = 1) (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t (firstLen J.p.nums.stages))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (e₂ : Ahead) (hf : (carryE Bk ⟨J.p.place, 0 + 1⟩)[J.members.length]? = some e₂)
    (ho : e₂.owner = ⟨J.p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < J.members.length → ∃ a a', (carryE Bk ⟨J.p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨J.p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest D
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Common W₀ Rc Ky) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : ProofFile.Honest.RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField, (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      carriedAt Bk k 1 ⟨σ.block.place, u.number⟩
        (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      firstLen J.p.nums.stages ≤ m.st.heard.length ∧
      firstLen J.p.nums.stages ≤ m.seen.length ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, u.number⟩)
        (firstLen J.p.nums.stages)).map (·.drawn) =
        m.st.lately (firstLen J.p.nums.stages) ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, u.number⟩)
        (firstLen J.p.nums.stages)).tail =
        aFold (coinsOf J.p.nums.stages (carriedCoins J (stretches _ c.2.1.2.2)).hide fun _ => 0) 0
          J.s₀ 1
          (rowsAt J (stretches _ c.2.1.2.2) m)
          (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m) := by
  obtain ⟨c, m₀, m, y, hl, hm, hplay, hy, hin0, -, -⟩ :=
    first_play_guarded hpl J hR σ _ pre t S hg hlaid hrun hc
  have hplace : J.p.place = σ.block.place := by
    have := List.find?_some hg
    exact beq_iff_eq.1 this
  have Q := (F.planOk_ok).1 hpl
  have hp := Q.places
  obtain ⟨-, tr', -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨m', hm', hseen⟩ := mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  have hbef := before_shared hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 1)
    (shown_is (runOk_of hrun).1 1 (by decide)) st
  have hfront : m'.seen = (r.run.beforeAt st
      ⟨σ.block.place, u.number⟩).seen := by
    rw [hbef, seen_by, roundsOff_by, hseen]
  have hinm : m'.st.input = ⟨w₀, rc, P.key x⟩ := by
    rw [← hy, (play_mid _ _ _ _ y hplay).1]
    exact hin0
  refine ⟨c, m', hm, by rw [hu]; exact carried_of_row k σ.block.place _ _ c hl, hinm, ?_⟩
  rw [← hplace] at hl
  obtain ⟨l1, l2'⟩ := lendRow_cons_ok hl
  obtain ⟨l2, -⟩ := lendRow_cons_ok l2'
  obtain ⟨-, -, k1⟩ := lendPart_ok l1
  obtain ⟨-, -, k2⟩ := lendPart_ok l2
  have ow := lendPart_own l1
  obtain ⟨y', hplay', -, hon⟩ := five_of_lent_own (V := Empty) J hfr Bk
    (sharedLook Bk k.shared) c.1 c.2.1 ow k1 k2 e₂ hf ho hst hmem σ.block.name ⟨σ.block.place, 0⟩ none s next rest m₀ D _ T hk
    (hrows _ _) hfit (r.run.beforeAt st ⟨σ.block.place, u.number⟩)
  obtain rfl : y' = y := Except.ok.inj (hplay'.symm.trans hplay)
  rw [hy] at hon
  exact hon hfront

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.five_of_lent_own
#print axioms ProofFile.Honest.K12.Light.first_play_guarded
#print axioms ProofFile.Honest.K12.Light.five_own_at_run
#print axioms ProofFile.Honest.K12.Light.lendPart_own
#print axioms ProofFile.Honest.K12.Light.agree_own
