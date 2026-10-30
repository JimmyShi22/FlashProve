-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Top.lean: the law of the proximity test at the top: of the block `proximityTestKind guardedProximityTestParts
p` and of `Block.step`.

Reduces the law (a yes of the block gives `Chain.Acc`) to the two propositions on the code switch
(`SwitchUnfolds`, `SeatReads`: Johnson/Desc/K12/Law/SwDid.lean) and to one bundle of premises on
what stands in front of the test, `StartK`. Statements and proofs.
Main names:
  `rds_len`: a chain has as many written rounds as its stages need.
  `idx_len`: the block's test on the plan gives a pair of code numbers for each stage.
  `fixed_of_planOk`: the block's test on the plan holds `fixedOk p`
    (Johnson/Desc/K12/FixedBefore.lean).
  `cut_of_planOk`: the block's test on the plan holds `cutOk p`
    (Johnson/Desc/K12/Law/FirstCut.lean).
  `early_of_planOk`, `answers_of_planOk`: the block's test on the plan holds `p.early = true` and
    `p.answers = 1`.
  `batK_comb`: a yes of the batching's part of `guardedProximityTestParts` holds guard (c), `combOk`, at the record
    in front.
  `frontK_ok`: a yes of the front's part of `guardedProximityTestParts` holds the yes of the front of Join.lean, that
    the plan's count of roots in front of the test is the record's, and `pubOk` at the record's
    codes.
  `batJ_ok`, `batK_ok`, `noKept_spec`: what a yes of the batching's part holds; in `guardedProximityTestParts` also
    that the batched row has no kept form and the layout no kept member, and `gpOk` at the record
    that it leaves.
  `StartK`: what is assumed in front of the test. Four fields. `stages` and `pub` are public: the
    chain's stages are the place's, and `Chain.Pub` holds at the record's codes. `rounds` is on the
    reading of the view: behind the round "BAT" the rounds as shown are the chain's written rounds.
    `behind` has three parts: the claim q is the batched row read in the field (no premise on a
    prover: it says which claim the law speaks of); under each later switch's cut of the groups
    stand columns of that switch's written tree; and `ReadTie` for the group's own trees at the
    first stage.
  `k12_law`: the test on the plan, `StartK` and a yes of the decision of `proximityTestKind guardedProximityTestParts p` give
    `c.Acc q y z g b`, under the two propositions.
  `k12_law_of_step`: the same from a yes of `Block.step`, by `step_ok`
    (Johnson/Top/H0/P5Law/Law.lean).
Limits: The law of the proximity test is not proved for a view that comes from bytes: see `StartK`.
That the premises on the view and the block's yes hold together on any view is not shown; the two
public fields of `StartK` have a member wherever `pubOk` says yes (`pub_of_ok`,
Johnson/Desc/K12/Law/ChainOf.lean). It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the
parts of Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves.
So the kind must take `guardedProximityTestParts` for its parts: no lemma "a yes of `proximityTestKind proximityTestParts p` through
`Block.step` gives a yes of `proximityTestKind guardedProximityTestParts p`" is proved. Two numbers of the place are
premises: `p.early = true` and `p.answers = 1`. Of the front's part the proof spends only that it
turns nothing. The letter `firstTree` of `Block.step` is tied to `p.nums.firstTree` by nothing; that
is harmless, because the step's keys are dropped by `regroup` and made anew at `p.nums.firstTree`.
At stage 0 the words y and z are letters, tied to the view at the opened positions alone. An
implication knows no order in time: that these words are fixed before the test's first draw is owed
by whoever spends `Chain.Acc` in a game; they must be functions of messages that `P12.before` names,
not of b. Behind a switch the type pays it. No statement and no proof of this file reaches a routine
that runs in a context of the program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`,
`OnBytes.Chan`); plain functions of that program, some with names that begin with `Blk.`, are
reached. No soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.SwitchKeeps
import Johnson.Desc.K12.Law.FrameLens

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)
open H2K.FrameLens (roundsFor)

theorem stagesOf_ne : ∀ {s : Sg} (c : Chain s), ∃ l, stagesOf c = s.st :: l
  | _, .last _ _ _ _ _ _ _ => ⟨[], rfl⟩
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => ⟨stagesOf next, rfl⟩

theorem rds_len {s : Sg} (c : Chain s) : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
    stagesOf c = cur :: rest → c.rds.length = roundsFor cur rest := by
  induction c with
  | last s e dL dB fu fs εb =>
    intro cur rest h
    obtain ⟨_, rfl⟩ := List.cons.inj h
    rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro cur rest h
    obtain ⟨rfl, hr⟩ := List.cons.inj h
    obtain ⟨l', hl'⟩ := stagesOf_ne next
    have hr' : rest = s'.st :: l' := hr.symm.trans hl'
    subst hr'
    show (foldRds s dE dT ++ ([dS, dC] ++ next.rds)).length = s.st.k + 3 + roundsFor s'.st l'
    rw [← ih _ _ hl']
    show _ = s.h + s.g + 3 + _
    simp [foldRds]
    omega

theorem stagesAt_some (p : P12) : ∀ (l : List Fmt.M1.Stage) (j : Nat), j + l.length ≤ p.idx.length →
    ∃ r, stagesAt p j l = some r
  | [], _, _ => ⟨[], rfl⟩
  | a :: l, j, h => by
    have hj : j < p.idx.length := by simp at h; omega
    obtain ⟨r, hr⟩ := stagesAt_some p l (j + 1) (by simp at h; omega)
    refine ⟨{ code := p.idx[j].1, maskCode := p.idx[j].2, k := a.k, h := a.h } :: r, ?_⟩
    unfold stagesAt stageAt
    rw [List.getElem?_eq_getElem hj, hr]
    rfl

/-- The block's test on the plan gives a pair of code numbers for each stage. -/
theorem idx_len (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    p.idx.length = p.nums.stages.length := by
  simp only [proximityTestKind] at hp
  split at hp
  · simp only [Block.andThen, Part.at, asks, guardedProximityTestParts, ranged, batJ, Bool.and_eq_true,
      beq_iff_eq] at hp
    exact hp.2.1.1.2.1.2
  · simp at hp

/-- The block's test on the plan holds `fixedOk p` (it stands in the front's test on the plan in
`guardedProximityTestParts`). -/
theorem fixed_of_planOk (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    H2K.FixedBefore.fixedOk p = true := by
  simp only [proximityTestKind] at hp
  split at hp
  · simp only [Block.andThen, Part.at, asks, guardedProximityTestParts, ranged, Bool.and_eq_true] at hp
    exact hp.2.1.1.1.1.1.1.2
  · simp at hp

/-- The block's test on the plan holds `cutOk p` (it stands in the front's test on the plan in
`guardedProximityTestParts`). -/
theorem cut_of_planOk (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    H2K.First.cutOk p = true := by
  simp only [proximityTestKind] at hp
  split at hp
  · simp only [Block.andThen, Part.at, asks, guardedProximityTestParts, ranged, Bool.and_eq_true] at hp
    exact hp.2.1.1.1.1.1.2
  · simp at hp

/-- The block's test on the plan holds `p.early` (it stands in the front's test on the plan in
`guardedProximityTestParts`). -/
theorem early_of_planOk (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    p.early = true := by
  simp only [proximityTestKind] at hp
  split at hp
  · simp only [Block.andThen, Part.at, asks, guardedProximityTestParts, ranged, Bool.and_eq_true] at hp
    exact hp.2.1.1.1.1.2
  · simp at hp

/-- The block's test on the plan holds `p.answers = 1` (it stands in the front's test on the plan
in `guardedProximityTestParts`). -/
theorem answers_of_planOk (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    p.answers = 1 := by
  simp only [proximityTestKind] at hp
  split at hp
  · simp only [Block.andThen, Part.at, asks, guardedProximityTestParts, ranged, Bool.and_eq_true] at hp
    exact beq_iff_eq.1 hp.2.1.1.1.2
  · simp at hp

/-- A yes of the front's part of `guardedProximityTestParts` holds the yes of `frontJ`, that the plan's count of
roots in front of the test is the record's, and `pubOk` at the record's codes. -/
theorem frontK_ok (p : P12) (t tF : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (guardedProximityTestParts.front p).decide t rs gs = .ok tF) :
    (frontJ p).decide t rs gs = .ok tF ∧ p.nums.free = t.roots ∧
      H2K.Pub.pubOk p tF.st.codes = true := by
  obtain ⟨_, hf, h⟩ := bind_ok h
  obtain ⟨t', ha, h⟩ := bind_ok h
  obtain ⟨_, hq, h⟩ := bind_ok h
  cases h
  exact ⟨ha, by simpa using needD_ok hf, needD_ok hq⟩

/-- A yes of the batching's part of `guardedProximityTestParts` holds the yes of `batJ`, the guard `noKept`, and
`gpOk` at the record that it leaves. -/
theorem batK_ok (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (guardedProximityTestParts.bat p cut).decide t rs gs = .ok t1) :
    (batJ p cut).decide t rs gs = .ok t1 ∧ noKept t1 = true ∧ H2K.First.gpOk p t1 = true := by
  obtain ⟨h1, _⟩ := ranged_ok _ _ _ _ _ _ h
  obtain ⟨_, _, h1⟩ := bind_ok h1
  obtain ⟨t', ha, hb⟩ := bind_ok h1
  obtain ⟨_, hk, hc⟩ := bind_ok hb
  obtain ⟨_, hg, hc⟩ := bind_ok hc
  cases hc
  have hg' := needD_ok hg
  rw [Bool.and_eq_true] at hg'
  exact ⟨ha, needD_ok hk, hg'.1⟩

/-- A yes of the batching's part of `guardedProximityTestParts` holds guard (c) at the record in front. -/
theorem batK_comb (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (guardedProximityTestParts.bat p cut).decide t rs gs = .ok t1) : combOk t = true := by
  obtain ⟨h1, _⟩ := ranged_ok _ _ _ _ _ _ h
  obtain ⟨_, hc, _⟩ := bind_ok h1
  exact needD_ok hc

/-- What guard (k) says. -/
theorem noKept_spec (t : T12) (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (h : noKept t = true) :
    row.kept = #[] ∧ ∀ i, i < L.members.size → L.kept.getD i false = false := by
  unfold noKept at h
  rw [hp] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  exact ⟨Array.isEmpty_iff.1 h.1, h.2⟩

/-- What a yes of the batching's part holds. -/
theorem batJ_ok (p : P12) (he : p.early = true) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (batJ p cut).decide t rs gs = .ok t1) :
    ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
      rs = [r] ∧ First.Close.bat t.st t.g e r = .ok (row, L, S') ∧
      t1 = { t with st := S', pass := .claim row L } := by
  unfold batJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨⟨row, L⟩, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, hr0, _, _⟩ := back_ok h
    unfold H2K.batE at hx
    split at hx
    · rename_i e es r rs' he1 hr1
      obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨⟨row', L', S'⟩, hb, hx⟩ := bind_ok hx
      cases hx
      have hrs : rs = r :: rs' := hr1
      have hrs' : rs' = [] := hr0
      subst hrs'
      refine ⟨e, r, row', L', S', hrs, mapError_ok hb, ?_⟩
      simp [he, lay]
    · cases hx
  · cases h

theorem bat_codes (S S' : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (h : First.Close.bat S g e r = .ok (row, L, S')) : S'.codes = S.codes := by
  unfold First.Close.bat at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, hb, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  have hb' := H2K.FoldLaw.got_ok hb
  unfold Ground.beginRunP at hb'
  split at hb'
  · cases hG : (First.Close.onSt S).st.groups[g]? with
    | none => simp [hG] at hb'
    | some G =>
      simp [hG] at hb'
      rw [← hb'.2]
      show (closeLedgers S _).codes = _
      exact closeLedgers_codes _ _
  · cases hb'

/-- What is assumed in front of the test. The file's head sorts the fields. -/
structure StartK (p : P12) {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word)
    (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl) (t0 : T12) (rs : List Fmt.RoundView) (gs : Gs) : Prop
        where
  /-- public -/
  stages : stagesOf c = p.nums.stages
  /-- public -/
  pub : ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage)
    (restI : List IoppStage), p.nums.stages = first :: rest → stageAt p 0 first = some cu →
    stagesAt p 1 rest = some restI → c.Pub t0.st.codes cu restI
  /-- on the reading of the view -/
  rounds : rs.drop 1 = (c.rvs b).map noDigest
  /-- of whatever the batching returns on the first round as shown: which claim the law speaks of;
  and, on the reading of the view, the later columns and the first stage's tie -/
  behind : ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage)
    (ds : List Fmt.DeclaredRound) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout)
    (S' : Statement), p.nums.stages = first :: rest → stageAt p 0 first = some cu →
    H2U.roundsOfNums p.nums = some ds → rs.take 1 = [r] →
    First.Close.bat t0.st t0.g e r = .ok (row, L, S') →
    ClaimNow c q row ∧
    ShownLater c b ((ds.zip p.oracles).drop 1)
      (gs.drop (nOpen (((ds.zip p.oracles).take 1).map (·.1)))) ∧
    TieNow p cu { t0 with st := S', pass := .claim row L } L c y z g b ((ds.zip p.oracles).drop 1)
      (gs.drop (nOpen (((ds.zip p.oracles).take 1).map (·.1))))

/-- The law of the proximity test, of the block's decision, under `SwitchUnfolds` and `SeatReads`.
-/
theorem k12_law (p : P12) (he : p.early = true) (ha : p.answers = 1) (hU : H2K.Sw.SwitchUnfolds p)
    (hR : H2K.Sw.SeatReads) {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word)
    (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (h0 : StartK p c q y z g b t0 rs gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : c.Acc q y z g b := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨first', rest', ds', e1', e2', l1, l2⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts p hp
  obtain ⟨rfl, rfl⟩ := List.cons.inj (e1'.symm.trans e1)
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
  -- the front turns nothing
  have hF : tF = t0 := by
    have hfr' : (frontJ p).decide t0 [] [] = .ok tF := (frontK_ok p _ _ _ _ hfr).1
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  have nB : (batAt guardedProximityTestParts p (ds'.zip p.oracles) : Blk').rounds.length = 1 := by
    show (((ds'.zip p.oracles).take 1).map (·.1)).length = 1
    rw [List.length_map, l1]
  rw [nB] at hbat hst
  obtain ⟨hbat', hnk, _⟩ := batK_ok p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', hr1, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ hbat'
  obtain ⟨k2, k3⟩ := noKept_spec _ row L rfl hnk
  have hidx := idx_len p hp
  rw [e1] at hidx
  obtain ⟨all, hall⟩ := stagesAt_some p (first' :: rest') 0 (by rw [hidx]; simp)
  have hall' := hall
  unfold stagesAt at hall'
  cases hcu : stageAt p 0 first' with
  | none => rw [hcu] at hall'; cases hall'
  | some cu =>
    rw [hcu] at hall'
    cases hri : stagesAt p (0 + 1) rest' with
    | none => simp [hri] at hall'
    | some restI =>
      obtain ⟨k1, k4, k5⟩ := h0.behind first' rest' cu ds' e r row L S' e1 hcu e2 hr1 hb
      have hstg : stagesOf c = first' :: rest' := h0.stages.trans e1
      have hJ : JointK p c q y z g b 0 first' rest' ((ds'.zip p.oracles).drop 1)
          { tF with st := S', pass := .claim row L } (rs.drop 1)
          (gs.drop (batAt guardedProximityTestParts p (ds'.zip p.oracles) : Blk').openings) :=
        ⟨row, L, cu, restI, rfl, hcu, hri, by
          show c.Pub S'.codes cu restI
          rw [bat_codes _ _ _ _ _ _ _ hb]
          exact h0.pub first' rest' cu restI e1 hcu hri, k1, k2, k3, h0.rounds,
          l2.trans (rds_len c _ _ hstg).symm, k4, k5, hstg⟩
      exact later_law guardedProximityTestParts p (foldKeeps_P5 p)
        (H2K.Sw.switchKeeps guardedProximityTestParts p he ha (fun _ _ _ _ _ _ _ _ _ h => (ranged_ok _ _ _ _ _ _
                             h).1)
          (fun _ _ _ _ _ _ _ h => h) hU hR)
        (baseGives_P5 p) c q y z g b 0 first' rest' _ _ tE _ _ hJ hst

/-- The law of the proximity test, of `Block.step`, under `SwitchUnfolds` and `SeatReads`. -/
theorem k12_law_of_step (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hU : H2K.Sw.SwitchUnfolds p) (hR : H2K.Sw.SeatReads) {s : Sg} (c : Chain s)
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl)
    (firstTree : Nat) (t0 tE : T12) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h0 : StartK p c q y z g b t0 (rs.map noDigest)
      (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))).map
          (·.length))
        (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
          (rs.map (·.drawn))).flatMap id).length)))
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n)) : c.Acc q y z g b :=
  k12_law p he ha hU hR c q y z g b t0 tE _ _ hp h0 (Prox.step_ok firstTree _ t0 tE rs cols n h).2.2

end H2K.JointK
