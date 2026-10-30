-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Trees.lean: HOW MANY TREES A YES OF THE PROXIMITY TEST BRINGS: ONE FOR EACH SWITCH (the stages less one), where the first fold's mask has come earlier. Statements with proofs.
OBJECT. (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide: the record's count of roots and its book's number of trees. USER. Johnson/RunOne/Law/K12Join15.lean's premise htr (the tables' sizesB at border 16); the like at the key file's other proximity tests whose first mask has come earlier.
LETTERS. p t0 tE rs gs: free. Premises: early · answers = 1 (as the kind's files' laws on what a yes leaves) · the yes · the record names the first fold's mask (t0.mask = some m) · OneTree: at the record's codes each switch's prover's message lays ONE tree.
WHY IT IS WANTED. OutK3 (Johnson/Desc/K12/Law/OutK3.lean) says that the roots rise just as the trees come, and its head: "Not proved …: how many trees come (one for each switch, and one where the fold sends its own mask) … Both hang on 'each prover's message of the test lays one tree' (layTrees at the record's codes)". Here the count is made along the stages, over the kind's files' own parts' laws: foldJ_form (a fold whose mask has come receives nothing) · switch_roots (a switch's part raises the roots by the trees that its message lays) · behindJ_roots · baseJ5_bk · stage_st (behind a stage the record names the next mask).

  OneTree codes: the premise on layTrees, at all stages' numbers and either flag.
  stages_roots: by recursion along the stages. k12_roots: the roots. k12_trees: the trees.
  OneTreeMask · foldJ_roots_any · k12_roots_any | k12_trees_any: either arm: one tree more where the first fold sends its own mask (own t0 = 1).
Limits. A block that says no to all meets every statement. OneTree is a premise here. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.GrowsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Trees
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok got_ok)

/-- At these codes each switch's prover's message lays one tree. -/
def OneTree (codes : Codes) : Prop :=
  ∀ (nx : IoppStage) (last : Bool) (lay : TreeLay),
    layTrees codes (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf last nx)) = some lay → lay.shapes.size = 1

/-- A fold whose mask has come earlier leaves the roots and the codes. -/
theorem foldJ_roots (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) (m : ℕ) (hm : t.mask = some m) : t1.roots = t.roots := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨hn, _⟩
  · rfl
  · rw [hm] at hn
    cases hn

/-- **By recursion along the stages**: one root for each stage that lies behind the present one. -/
theorem stages_roots (p : P12) (he : p.early = true) (ha : p.answers = 1) (codes : Codes) (hone : OneTree codes) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs = .ok tE → t.st.codes = codes → (∃ m, t.mask = some m) →
      tE.roots = t.roots + rest.length
  | [], j, cur, l, t, tE, rs, gs, h, _, _ => by
    rw [stagesFrom_last] at h
    exact (baseJ5_bk p _ _ _ t tE rs gs (ranged_ok _ _ _ _ _ _ h).1).2
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h, hc, ⟨m, hm⟩ => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok guardedProximityTestParts p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur l : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have f1' := (like_P5 p).fold _ _ _ _ _ _ _ f1
    have f2' := (like_P5 p).switch _ _ _ _ _ _ _ _ _ f2
    have f3' := (like_P5 p).behind _ _ _ _ _ f3
    have r1 := foldJ_roots p j cur _ t t1 _ _ f1' m hm
    have c1 : t1.st.codes = codes := (foldJ_grows p j cur _ t t1 _ _ f1').1.trans hc
    obtain ⟨nx, lay, _, hl, r2⟩ := switch_roots p he ha j cur nxt rest.isEmpty _ t1 t2 _ _ f2'
    rw [c1] at hl
    have r2' := hone nx _ lay hl
    have r3 := behindJ_roots p (j + 1) nxt _ t2 t3 f3'
    have c3 : t3.st.codes = codes :=
      ((behindJ_grows p (j + 1) nxt _ t2 t3 _ _ f3').1.trans (switchJ_grows p j cur nxt _ _ t1 t2 _ _ f2').1).trans c1
    have m3 := (stage_st p he ha j cur nxt rest.isEmpty _ _ t t1 t2 t3 _ _ _ _ hlen f1' f2' f3').2.2.2.2.2.2.2
    have ih := stages_roots p he ha codes hone rest (j + 1) nxt _ t3 tE _ _ f5 c3 ⟨_, m3⟩
    rw [ih, r3, r2, r2', r1, List.length_cons]
    omega

/-- **The roots behind a yes of the test**: risen by the stages less one. -/
theorem k12_roots (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hone : OneTree t0.st.codes) (m : ℕ) (hm : t0.mask = some m) :
    tE.roots = t0.roots + (p.nums.stages.length - 1) := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have k := stages_roots p he ha tF.st.codes hone rest 0 first _ _ tE _ _ hst (begun_keeps tF.st tF.g G).1 ⟨m, hm⟩
  rw [k, hs]
  rfl

/-- **The trees behind a yes of the test**: one more for each switch. -/
theorem k12_trees (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hone : OneTree t0.st.codes) (m : ℕ) (hm : t0.mask = some m) :
    tE.book.trees.size = t0.book.trees.size + (p.nums.stages.length - 1) := by
  have k1 := k12_roots p he ha t0 tE rs gs h hone m hm
  have k3 := (k12_out3 p he ha t0 tE rs gs h).rootsTrees
  omega

/-! ## The arm in which the first fold sends its own mask -/

/-- At these codes a fold's own mask, sent alone, lays one tree. -/
def OneTreeMask (codes : Codes) : Prop :=
  ∀ (c : IoppStage) (L : GroupLayout) (lay : TreeLay), layTrees codes #[foldMaskNotice (ioppFoldShape c L)] = some lay → lay.shapes.size = 1

/-- A fold: the roots rise by one where it sends its own mask, and not at all where the mask has come. -/
theorem foldJ_roots_any (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) (hmask : OneTreeMask t.st.codes) : t1.roots = t.roots + own t := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨hm, rfl⟩ | ⟨hn, ids, hr, _⟩
  · have e : own t = 0 := by simp [own, hm]
    rw [e]
    rfl
  · obtain ⟨lay, hl, _, _, rfl⟩ := recvP_ok hr
    have e : own t = 1 := by simp [own, hn]
    have e1 := hmask c L lay hl
    show t.roots + lay.shapes.size = t.roots + own t
    rw [e, e1]

/-- **The roots behind a yes of the test, either arm**: risen by the stages less one, and by one more where the first fold sends its own mask. -/
theorem k12_roots_any (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hone : OneTree t0.st.codes) (hmask : OneTreeMask t0.st.codes) :
    tE.roots = t0.roots + own t0 + (p.nums.stages.length - 1) := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have hcB : (begun tF.st tF.g G).codes = tF.st.codes := (begun_keeps tF.st tF.g G).1
  cases rest with
  | nil =>
    exfalso
    unfold H2U.roundsOfNums at hr
    rw [hs] at hr
    cases hr
  | cons nxt rest =>
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok guardedProximityTestParts p 0 first nxt rest _ _ tE _ _).1 hst
    have hlen : ∀ (l : Laid) (rs : List Fmt.RoundView), ((rs.drop (foldAt guardedProximityTestParts p 0 first l : Blk').rounds.length).take
               (switchAt guardedProximityTestParts p 0 first nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      intro l rs
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + first.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have f1' := (like_P5 p).fold _ _ _ _ _ _ _ f1
    have f2' := (like_P5 p).switch _ _ _ _ _ _ _ _ _ f2
    have f3' := (like_P5 p).behind _ _ _ _ _ f3
    have r1 := foldJ_roots_any p 0 first _ _ t1 _ _ f1' (by
      show OneTreeMask (begun tF.st tF.g G).codes
      rw [hcB]
      exact hmask)
    have c1 : t1.st.codes = tF.st.codes := (foldJ_grows p 0 first _ _ t1 _ _ f1').1.trans hcB
    obtain ⟨nx, lay, _, hl, r2⟩ := switch_roots p he ha 0 first nxt rest.isEmpty _ t1 t2 _ _ f2'
    rw [c1] at hl
    have r2' := hone nx _ lay hl
    have r3 := behindJ_roots p (0 + 1) nxt _ t2 t3 f3'
    have c3 : t3.st.codes = tF.st.codes :=
      ((behindJ_grows p (0 + 1) nxt _ t2 t3 _ _ f3').1.trans (switchJ_grows p 0 first nxt _ _ t1 t2 _ _ f2').1).trans c1
    have m3 := (stage_st p he ha 0 first nxt rest.isEmpty _ _ _ t1 t2 t3 _ _ _ _ (hlen _ _) f1' f2' f3').2.2.2.2.2.2.2
    have ih := stages_roots p he ha tF.st.codes hone rest (0 + 1) nxt _ t3 tE _ _ f5 c3 ⟨_, m3⟩
    have r1' : t1.roots = tF.roots + own tF := r1
    rw [ih, r3, r2, r2', r1', hs]
    simp only [List.length_cons]
    omega

/-- **The trees behind a yes of the test, either arm.** -/
theorem k12_trees_any (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hone : OneTree t0.st.codes) (hmask : OneTreeMask t0.st.codes) :
    tE.book.trees.size = t0.book.trees.size + own t0 + (p.nums.stages.length - 1) := by
  have k1 := k12_roots_any p he ha t0 tE rs gs h hone hmask
  have k3 := (k12_out3 p he ha t0 tE rs gs h).rootsTrees
  omega

end Johnson.RunOne.Law.K12Trees

#print axioms Johnson.RunOne.Law.K12Trees.k12_roots_any
#print axioms Johnson.RunOne.Law.K12Trees.k12_trees_any
#print axioms Johnson.RunOne.Law.K12Trees.stages_roots
#print axioms Johnson.RunOne.Law.K12Trees.k12_roots
#print axioms Johnson.RunOne.Law.K12Trees.k12_trees
