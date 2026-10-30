-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the state on entry, from what a view holds.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Door.lean: the simulators' state on entry of a proximity test on the shared chain, as a function of a public part and of a Before alone: the description's own fold over the blocks in front, at the rounds and columns that the Before lists
of that chain, then the way in. And the one equation that ties it to a run: at the front of a called part of the shared chain, cut back to the rounds in front of the test. Twin of Sim2/DoorTrue.lean and DoorStand.lean, at the frame's chain number 1.

  `doorFromViewOnSharedChain`, `stateFromViewOnSharedChain`   the state, with a refusal; its value or a fall-back
  `stateFromViewOnSharedChain_reads`   it reads the start, the chain's rounds and the listed columns alone
  `treeCols_shared`     what a Before in closed form lists of a tree of the shared chain
  `view_columns_shared` where the reads of the rounds in front are filled at a run, the cut front lists those columns
  `called_columns`      the stand's field holds just the columns of the fold in front, and they are the filling of what these blocks read
  `stateFromViewOnSharedChain_at_stand`   **THE EQUATION**

WHERE THE FOLD REFUSES OR A COLUMN IS NOT LISTED THE FALL-BACK IS TAKEN: at such a front the value is no state of the verifier. `hstart`: that the start at the public part is the description's start at the input: a premise. At the front of a test that stands behind another test the fold runs over that test too: so the equation holds where the run reaches
the part, by `called_at_run`, and no other way: nothing here shows that a part is called. Of the walk (runC). No law, no coin. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorW
import Johnson.Desc.ProofFile.Honest.K12.CalledAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun
import Johnson.Desc.ProofFile.Honest.K12.LiveField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks Place)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light

variable {S Cl Pb Xi : Type}

/-- The fold over the blocks in front, at the rounds that f shows of the shared chain and the columns that it lists, then the way in. -/
def doorFromViewOnSharedChain (pre : List (Block S Cl)) (start : Pb → S) (enter : S → Except String T12) (pb : Pb)
    (f : Before) : Except String T12 :=
  match columnsOfChain f 1 0 (pre.flatMap (·.rounds)) with
  | some cs => (foldBlocks 0 pre (start pb) (roundsOfChain f 1) cs).bind fun r => enter r.1
  | none => .error "a column that the rounds in front read is not listed"

/-- **The simulators' state on entry.** Of the public part and of a Before alone. -/
def stateFromViewOnSharedChain (pre : List (Block S Cl)) (start : Pb → S) (enter : S → Except String T12) (fall : T12)
    (pb : Pb) (f : Before) : T12 :=
  (doorFromViewOnSharedChain pre start enter pb f).toOption.getD fall

/-- **It reads nothing else.** -/
theorem stateFromViewOnSharedChain_reads (pre : List (Block S Cl)) (start : Pb → S) (enter : S → Except String T12)
    (fall : T12) (pb pb' : Pb) (f f' : Before) (hs : start pb = start pb')
    (hr : roundsOfChain f 1 = roundsOfChain f' 1)
    (hc : columnsOfChain f 1 0 (pre.flatMap (·.rounds)) = columnsOfChain f' 1 0 (pre.flatMap (·.rounds))) :
    stateFromViewOnSharedChain pre start enter fall pb f = stateFromViewOnSharedChain pre start enter fall pb' f' := by
  unfold stateFromViewOnSharedChain doorFromViewOnSharedChain
  rw [hc, hs, hr]

/-- What a Before in closed form lists of a tree of the shared chain. -/
theorem treeCols_shared (tree : ℕ → List ℕ) (l : List Played)
    (st : List (ℕ × ℕ × List UInt64)) (j : ℕ) :
    (⟨shownBy 1 tree l 0, st⟩ : Before).treeCols 1 j =
      ((allTabs l)[j]?).map fun T => colsOfT T (tree j) := by
  show (((shownBy 1 tree l 0).filter fun r => r.1 == 1).flatMap fun r => r.2.1.cols)[j]? = _
  rw [filter_same]
  have h := cols_at 1 tree l 0 j
  rw [Nat.zero_add] at h
  exact h

/-- **Where the reads of the rounds in front are filled at a run, a front in closed form lists just these columns.** -/
theorem view_columns_shared {F : FileDescription Xi} {ρ : Draws} {stored : ℕ → ℕ → Option (List UInt64)}
    (l : List Played) (N : ℕ) (decls : List Fmt.DeclaredRound) (hdecl : decls = F.roundsDeclaredByBlocks.2.1.take N)
    (drawn : List Fmt.Drawn) (hdraw : drawn = ρ.shared.take N) (cs : List OpenedColumn)
    (hfill : fillCols (readsOf 1 0 stored (treeOwn l) decls drawn) [] = .ok cs)
    (f : Before) (hf : f = ⟨shownBy 1 (treeAsks F ρ 1) l 0,
      storedShown stored (storedAsks F ρ)⟩) (hseen : (roundsOfChain f 1).map (·.drawn) = drawn) :
    columnsOfChain f 1 0 decls = some cs := by
  have hb := colsOff_fill f _ cs hfill fun q hq w hw => ?_
  · unfold columnsOfChain
    rw [hseen, ← readsOf_bare 1 0 stored (treeOwn l)]
    exact hb
  have hall : q.bare ∈ allBare F ρ := by
    have h1 : q ∈ readsOf 1 0 stored (treeOwn l) F.roundsDeclaredByBlocks.2.1 ρ.shared := by
      rw [hdecl, hdraw] at hq
      exact reads_of_prefix 1 0 stored (treeOwn l) N _ _ q hq
    have h2 : q.bare ∈ readsOf 1 0 (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.1 ρ.shared := by
      rw [← readsOf_bare 1 0 stored (treeOwn l)]
      exact List.mem_map.2 ⟨q, h1, rfl⟩
    unfold allBare bareReads
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h2)))
  rcases readsOf_form 1 0 stored (treeOwn l) decls drawn q hq with ⟨i, h1, -, h3⟩ | ⟨o, h1, h2, h3⟩
  · have hi : q.bare.item = some i := h1
    unfold Before.wordsAt
    rw [hi, hf]
    show (((storedShown stored (storedAsks F ρ)).find? fun c =>
      c.1 == i && c.2.1 == q.pos).map (·.2.2)) = some w
    exact find_stored stored i q.pos w (h3.symm.trans hw) _ (mem_storedAsks F ρ q.bare hall i hi)
  · have hi : q.bare.item = none := h1
    rw [hw] at h3
    cases o with
    | taken a b => simp [treeOwn] at h3
    | own n =>
      have hs : q.bare.src = some (1, n) := h2
      cases hto : treeOwn l (.own n) with
      | none =>
        rw [hto] at h3
        cases h3
      | some pT =>
        rw [hto] at h3
        have hwT : w = pT.2.col q.pos := Option.some.inj h3
        have htab : ((allTabs l)[n]?).join = some pT.2 := by
          have e := tables_tabs l n
          have e2 : (((tablesOf l)[n]?).bind id) = some pT := hto
          rw [e2] at e
          exact e.symm
        have hget : (allTabs l)[n]? = some (some pT.2) := by
          cases hg : (allTabs l)[n]? with
          | none =>
            rw [hg] at htab
            cases htab
          | some t =>
            rw [hg] at htab
            exact congrArg some htab
        have hcols := treeCols_shared (treeAsks F ρ 1) l (storedShown stored (storedAsks F ρ)) n
        rw [hget] at hcols
        unfold Before.wordsAt
        rw [hi, hs, hf]
        show ((((⟨shownBy 1 (treeAsks F ρ 1) l 0, storedShown stored (storedAsks F ρ)⟩ :
          Before)).treeCols 1 n).bind fun cols => (cols.find? fun c => c.1 == q.pos).map (·.2)) =
          some w
        rw [hcols, hwT]
        exact find_col pT.2 q.pos _ (mem_treeAsks F ρ q.bare hall _ _ hs)

/-- **The stand of a called part of the shared chain**: the field holds just the columns that the fold over the blocks in front reads, and they are the filling of what these blocks read. -/
theorem called_columns {W₀ Rc Ky Tr X₀ Y V Pq : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pq) (u : Member V (Common W₀ Rc Ky) X₀ Pq)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : Mid (Common W₀ Rc Ky) X₀) (s : F.S₂) (cols : List OpenedColumn),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.opened = some cols ∧
      foldBlocks 0 pre (F.start₂ (F.pub x))
        (roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      fillCols (readsOf 1 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
        ((r.run.played.2.1.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
  obtain ⟨a₂, y, m, ha₂, hy, hl, hym, hmid⟩ := played_at_run hpl hR hrun σ u pre t i _ S rfl hc
  have hi : i < σ.block.rounds.length := by
    have h1 := S.le
    have h2 := S.pos
    omega
  have hlen : (R.shared.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [List.length_take]
    exact Nat.min_eq_left (by have h3 := S.fits; omega)
  rw [S.cut] at ha₂
  have hLo : ∀ ps, treeOwn ps = (envOf (P.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) ps [] []).1).symm
  obtain ⟨s, cols, -, -, -, -, ho, hf, hfill⟩ := live_field ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ hLo pre
    σ.block t i hi (R.start₂ P) (F.start₂ (F.pub x)) [] ha₂ hy hlen hym
  have e : y.laid.take (pre.flatMap (·.rounds)).length =
      r.run.played.2.1.take (pre.flatMap (·.rounds)).length := by
    rw [hl, List.take_take]
    simp
  rw [e] at hf hfill
  refine ⟨m, s, cols, hmid, ?_, hf, hfill⟩
  rw [ho, List.nil_append]

/-- **One function on both sides.** i: the rounds of the test in front of the member. -/
theorem stateFromViewOnSharedChain_at_stand {W₀ Rc Ky Tr X₀ Y V Pq : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pq) (u : Member V (Common W₀ Rc Ky) X₀ Pq)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (start : Pb → F.S₂) (enter : F.S₂ → Except String T12) (fall : T12) (pb : Pb)
    (hstart : start pb = F.start₂ (F.pub x)) :
    ∃ (m : Mid (Common W₀ Rc Ky) X₀) (s : F.S₂) (cols : List OpenedColumn),
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      m.opened = some cols ∧ m.seen = roundsOf (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + i)) ∧
      foldBlocks 0 pre (F.start₂ (F.pub x))
        (roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      roundsOfChain ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i) 1 =
        roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) ∧
      columnsOfChain ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i) 1 0 (pre.flatMap (·.rounds)) = some cols ∧
      stateFromViewOnSharedChain pre start enter fall pb
        ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, u.number⟩).cut i) = (enter s).toOption.getD fall := by
  obtain ⟨m, s, cols, hm, ho, hfold, hfill⟩ := called_columns hpl hR hrun σ u pre t i S hc
  obtain ⟨m', hm', hin, -, -, hseen, hbf, -, -, -, hask⟩ := frame_at_run hpl hR hrun σ u pre t i _ S rfl hc
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  have hmm : m' = m := by
    rw [hm] at hm'
    exact (Option.some.inj (Except.ok.inj hm')).symm
  subst hmm
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, -, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨-, l2, -⟩ := runC_laidAs hrun hR (steps_shaped s1 Q.blocks₁) (steps_shaped s2 Q.blocks₂)
    (steps_shaped s3 Q.blocks₃)
  have d₂ := laidAs_drawn l2
  have hall : r.run.played.2.1.length = R.shared.length := by
    have h1 := congrArg List.length d₂
    rw [List.length_map] at h1
    exact h1.trans l2.1
  have hfits := S.fits
  have hn : (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [List.length_take, hall]
    omega
  have hf : (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i =
      ⟨shownBy 1 (treeAsks F ρ 1) (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩ := by
    rw [hbf, hask]
    show (⟨shownBy 1 (treeAsks F ρ 1) (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + i)) 0,
      storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩ : Before).cut i = _
    unfold Before.cut
    simp only [shownBy_length, hn, Nat.add_sub_cancel]
    rw [← shownBy_take, List.take_take]
    simp
  have hround : roundsOfChain ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i) 1 =
      roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) := by
    rw [hf]
    unfold roundsOfChain
    show roundsOff ((shownBy 1 (treeAsks F ρ 1) _ 0).filter fun r => r.1 == 1) = _
    rw [filter_same, roundsOff_by]
  have hdraw : (roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)).map (·.drawn) =
      ρ.shared.take (pre.flatMap (·.rounds)).length := by
    rw [← d₂]
    simp only [roundsOf, List.map_map, List.map_take]
    rfl
  have hdecl : pre.flatMap (·.rounds) = F.roundsDeclaredByBlocks.2.1.take (pre.flatMap (·.rounds)).length := by
    show _ = (F.shared.blocksInOrder.flatMap (·.rounds)).take _
    rw [S.cut, List.flatMap_append]
    simp
  have hfill' : fillCols (readsOf 1 0 (P.storedWords w₀ rc)
      (treeOwn (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
      ((roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)).map (·.drawn))) [] = .ok cols := by
    have e : (roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)).map (·.drawn) =
        (r.run.played.2.1.take (pre.flatMap (·.rounds)).length).map (·.drawn) := by
      simp only [roundsOf, List.map_map]
      rfl
    rw [e]
    exact hfill
  have hv := view_columns_shared (F := F) (ρ := ρ) (stored := P.storedWords w₀ rc)
    (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) (pre.flatMap (·.rounds)).length
    (pre.flatMap (·.rounds)) hdecl _ hdraw cols hfill' _ hf (by rw [hround])
  refine ⟨m', s, cols, hm, hin, ho, hseen, hfold, hround, hv, ?_⟩
  unfold stateFromViewOnSharedChain doorFromViewOnSharedChain
  rw [hv, hround, hstart]
  dsimp only
  rw [hfold]
  rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.doorFromViewOnSharedChain
#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnSharedChain
#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnSharedChain_reads
#print axioms ProofFile.Honest.K12.Sim2.treeCols_shared
#print axioms ProofFile.Honest.K12.Sim2.view_columns_shared
#print axioms ProofFile.Honest.K12.Sim2.called_columns
#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnSharedChain_at_stand
