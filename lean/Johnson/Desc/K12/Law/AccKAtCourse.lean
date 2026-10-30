-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.Law.OwnSeatStep
import Johnson.Desc.K12.Law.AccKConst
import Johnson.Desc.K12.Law.CanonAtFold
/-
Johnson/Desc/K12/Law/AccKAtCourse.lean: FROM A YES OF THE DECISION's COURSE (runCore, Johnson/Desc/Block.lean) TO accK's YES AT A SEAT OF THE PROXIMITY TEST: (S5) ∘ the seat's step ∘ accK_yes_real_const. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
WHY. Johnson/Desc/K12/Law/CanonAtFold.lean's runCore_steps_canon gives a yes of the step of THE BLOCK THAT STANDS IN THE CHAIN's LIST; accK_yes_real_const (Johnson/Desc/K12/Law/AccKConst.lean) wants the step of proximityTestKind guardedProximityTestParts p ITSELF, at its own record. All four seats of the kind are of one form: Block.inside enter (proximityTestKind guardedProximityTestParts p) leave (atFinish; onGu · onGomega · onOwn), and Chain.blocksInOrder lays a front or back block with its test on the plan alone turned. So the join is typed ONCE, GENERAL IN THE DOOR.
SPENT, NOT TYPED AGAIN: inside_step (Johnson/Top/H0/StepLaws/StepLaws.lean): the step of a block laid by Block.inside says yes just where the door lets in, the inner block's step says yes ON THE SAME ROUNDS AND COLUMNS, and the way out does. (step_inside, Johnson/Desc/K12/SeatLaws.lean:272, says the same.) · Johnson/Desc/K12/Law/CanonAtFold.lean's chain_step_canon | runCore_views (the version with the ties kept) and what these spend · accK_yes_real_const | accK_yes_real_own · k12_guards · lastOk_of_step · aloneAt_of_step (Johnson/Desc/K12/Law/OwnSeatStep.lean).
  step_same           Block.step reads a block's rounds and decision alone.
  seat_step           a block B with the rounds of b and the decision of b.inside enter leave: B's step's yes gives the door's yes, b's own step's yes on the same rounds and columns, and the way out's.
  YesConst | YesOwn X p F t0 r0 rs' cols     accK_yes_real_const's | _own's WHOLE CONCLUSION under a name: THE TEXT LIFTED BY PROGRAM, no sign turned (yesConst_is | yesOwn_is: the elder theorems prove them as they stand).
  yesConst_of_step    the elder theorem at a stretch «mine» with canonOk of the whole stretch: the stretch is r0 :: rs' (k12_guards: the batching takes a first round).
  yesOwn_of_step      the like for the own mask's arm: OF THE ELDER's FOUR LETTERS (eB · rowB · LB · SB) AND FOUR PREMISES (hbB · hmask · hlast · halone) ON THE RECORD AND THE ROUND ONE PREMISE IS LEFT: t0.mask = none (IT FALLS TOO, in Johnson/Desc/K12/Law/AccKAtCourseAll.lean, by hmask_of_step): the batching's yes comes of k12_guards; lastOk and aloneAt of the step's yes.
  AtSeat Y p ft bs s s' v     what is said of a chain's list bs from s to s' at the view v: WHEREVER bs = pre ++ B :: l and B has the kind's block's rounds and the decision of the kind's block behind a door: m and cols are what the fold over pre leaves of s, the view's rounds and THE VIEW's OPENED COLUMNS · the door lays t0 of m · B's own stretch of the view's rounds is r0 :: rs' · the kind's block's own step says yes at t0, that stretch, cols · the way out lays t, from which the fold over l goes on to (s', [], []) · Y.
  chain_atSeat        a chain's yes, canonOk of the view's rounds, the premises on p ⇒ AtSeat (YesConst X p).
  chain_atSeat_own    the like with p.nums.ownMask · ownTieOk p ⇒ AtSeat (fun … => t0.mask = none → YesOwn …).
  course_atSeat | course_atSeat_own     runCore's yes and the premises on p ⇒ AtSeat at each of the three chains (the first at the view with the seal's round behind it; the second chain, b₃, from the record that start₃ makes).
  atSeat_mask         where the door lays no mask at any record (∀ s t, enter s = .ok t → t.mask = none), «t0.mask = none» is paid: SO AT onGomega, whose door writes «mask := none» (Johnson/Desc/K12/Seat.lean: enter (·.gOmega) fun _ => none): by rfl in a tree that holds it. HELD BY A COMPILE in Johnson/Desc/K12/Law/AccKAtSeats.lean (onGomega_mask). It throws what AtSeat holds beside (the step's yes, the way out, the fold behind): whoever goes on along the chain goes back to AtSeat. BY hmask_of_step NEITHER IT NOR henter IS NEEDED: see Johnson/Desc/K12/Law/AccKAtCourseAll.lean.
No sorry and no axiom of our own stands in this file.
NO MEMBER IS SHOWN: no list with a seat of the kind's block at a real p has been laid under these theorems; where no such B stands in the list, AtSeat says nothing.
LIMITS. (1) THAT A WRITTEN DESCRIPTION's LIST IS pre ++ B :: l WITH SUCH A B IS A PREMISE INSIDE AtSeat. At a seat laid into a chain's front or back, Chain.blocksInOrder turns the test on the plan alone: there the two equations on B are ⟨rfl, rfl⟩. (2) Cl := Unit, as the elder theorems are typed: a description whose claims are of another type wants one lemma more. (3) The premises on p (early · one answer · planOk · nzOk · dealOk · tieOk · logOk; ownMask · ownTieOk) stay. (4) All of the elder theorems' limits: "BAT"'s own round is outside τ; ∃ W0 · ∃ τ.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters sgOf WR writtenOf)
open H2K.First (gpOf gpL Plain nzOk dealOk tieOk ownTieOk aloneOk canonOk logOk lastOk aloneAt
  plainAt last_of_ok)

theorem step_same {S Cl : Type} (B B' : Block S Cl) (hr : B.rounds = B'.rounds)
    (hd : B.decide = B'.decide) (F : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    B.step F s rs cols = B'.step F s rs cols := by
  unfold Block.step
  rw [hr, hd]

/-- A block with the rounds of b and the decision of b behind a door: its step's yes is the door's, b's own step's on the same rounds and columns, and the way out's. -/
theorem seat_step {S T Cl : Type} (B : Block S Cl) (enter : S → Except String T) (b : Block T Cl)
    (leave : S → T → Except String S) (hr : B.rounds = b.rounds)
    (hd : B.decide = (Block.inside enter b leave).decide) (F : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : ℕ) (h : B.step F s rs cols = .ok (s', k)) :
    ∃ t t', enter s = .ok t ∧ b.step F t rs cols = .ok (t', k) ∧ leave s t' = .ok s' := by
  rw [step_same B (Block.inside enter b leave) hr hd] at h
  exact (inside_step enter b leave F s s' rs cols k).1 h

/-- accK_yes_real_const's whole conclusion, under a name. -/
def YesConst (X : Letters) (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) : Prop :=
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain),
        H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
        ∃ (W0 : ℕ → WO), DeepK D W0 (fun _ : H2K.Pub.Msg1 c => W0 D.fresh.t) ∧
          ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fun _ => W0 D.fresh.t) τ = true ∧
            cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
              colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
                (srcK p c (blOf c τ) D.ts fun z x =>
                  colW (wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) (blOf c τ) z).1
                    (wAt c W0 D.fresh.t (fun _ => W0 D.fresh.t) (blOf c τ) z).2 x)

/-- accK_yes_real_own's whole conclusion, under a name. -/
def YesOwn (X : Letters) (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) : Prop :=
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain),
        H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
        ∃ (W0 : ℕ → WO), DeepK D W0 (orc1 c) ∧
          ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t (orc1 c)) τ = true ∧
            cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
              colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
                (srcK p c (blOf c τ) D.ts fun z x =>
                  colW (wAt c W0 D.fresh.t (orc1 c) (blOf c τ) z).1
                    (wAt c W0 D.fresh.t (orc1 c) (blOf c τ) z).2 x)

/-- The elder theorem proves it as it stands. -/
theorem yesConst_is (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (t0 : T12) (F : ℕ)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    YesConst X p F t0 r0 rs' cols :=
  accK_yes_real_const X p he ha t0 hp hnz hdeal htie hlog F r0 rs' cols hcan tE n hstep

/-- The elder theorem of the own mask's arm proves it as it stands. -/
theorem yesOwn_is (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (ho : p.nums.ownMask = true)
    (hown : ownTieOk p = true) (t0 : T12) (F : ℕ)
    (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB))
    (hmask : t0.mask = none)
    (hlast : lastOk p { t0 with st := SB, pass := .claim rowB LB } = true)
    (halone : aloneAt p { t0 with st := SB, pass := .claim rowB LB } = some true) :
    YesOwn X p F t0 r0 rs' cols :=
  accK_yes_real_own X p he ha t0 hp hnz hdeal htie hlog ho hown F r0 rs' cols hcan tE n hstep
    eB rowB LB SB hbB hmask hlast halone

/-- The same at a stretch with canonOk of the whole stretch: the stretch has a first round. -/
theorem yesConst_of_step (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (t0 : T12) (F : ℕ) (mine : List Fmt.RoundView) (cols :
               List OpenedColumn)
    (hcan : canonOk mine = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 mine cols = .ok (tE, n)) :
    ∃ r0 rs', mine = r0 :: rs' ∧ YesConst X p F t0 r0 rs' cols := by
  obtain ⟨_, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨_, _, e, r, row, L, S', hr, _, _⟩ := k12_guards p he t0 tE _ _ hp hdec
  cases mine with
  | nil => simp at hr
  | cons r0 rs' =>
    exact ⟨r0, rs', rfl, yesConst_is X p he ha hp hnz hdeal htie hlog t0 F r0 rs' cols
      (H2K.First.canonOk_sublist (List.sublist_cons_self _ _) hcan) tE n hstep⟩

/-- The own mask's arm at a stretch: of the elder's premises on the record and the round one is left: the record in front names no mask. -/
theorem yesOwn_of_step (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (ho : p.nums.ownMask = true)
    (hown : ownTieOk p = true) (t0 : T12) (F : ℕ) (mine : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk mine = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 mine cols = .ok (tE, n)) :
    ∃ r0 rs', mine = r0 :: rs' ∧ (t0.mask = none → YesOwn X p F t0 r0 rs' cols) := by
  obtain ⟨_, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨_, _, e, r, row, L, S', hr, hb, _⟩ := k12_guards p he t0 tE _ _ hp hdec
  cases mine with
  | nil => simp at hr
  | cons r0 rs' =>
    obtain rfl : noDigest r0 = r := by simpa using hr
    exact ⟨r0, rs', rfl, fun hmask =>
      yesOwn_is X p he ha hp hnz hdeal htie hlog ho hown t0 F r0 rs' cols
        (H2K.First.canonOk_sublist (List.sublist_cons_self _ _) hcan) tE n hstep e row L S' hb hmask
        (lastOk_of_step p he t0 tE F n r0 rs' cols hp hstep e row L S' hb)
        (aloneAt_of_step p he t0 tE F n r0 rs' cols hp hstep e row L S' hb hmask)⟩

/-- What is said of a chain's list of blocks, from s to s' at the view v, at every seat of the kind's block at p in it. -/
def AtSeat (Y : ℕ → T12 → Fmt.RoundView → List Fmt.RoundView → List OpenedColumn → Prop) (p : P12) (ft : ℕ) {S : Type}
    (bs : List (Block S Unit)) (s s' : S) (v : Fmt.View) : Prop :=
  ∀ (pre : List (Block S Unit)) (B : Block S Unit) (l : List (Block S Unit))
    (enter : S → Except String T12) (leave : S → T12 → Except String S),
    bs = pre ++ B :: l → B.rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds →
    B.decide = (Block.inside enter (proximityTestKind guardedProximityTestParts p : Blk') leave).decide →
    ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12) (n : ℕ)
      (t : S),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
      enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
      (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) ∧ leave m tE = .ok t ∧
      foldBlocks ft l t ((behindOf pre v.rounds).drop B.rounds.length) (cols.drop n) =
        .ok (s', [], []) ∧
      Y ft t0 r0 rs' cols

/-- The join, general in what the kind's block's step's yes gives at a canonical stretch. -/
theorem atSeat_of_steps (Y : ℕ → T12 → Fmt.RoundView → List Fmt.RoundView → List OpenedColumn → Prop) (p : P12) (ft : ℕ)
    (hY : ∀ (t0 : T12) (mine : List Fmt.RoundView) (cols : List OpenedColumn), canonOk mine = true →
      ∀ (tE : T12) (n : ℕ), (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 mine cols = .ok (tE, n) →
      ∃ r0 rs', mine = r0 :: rs' ∧ Y ft t0 r0 rs' cols)
    {S : Type} (bs : List (Block S Unit)) (s s' : S) (v : Fmt.View)
    (h : H2K.First.StepsAt ft bs s s' v) : AtSeat Y p ft bs s s' v := by
  intro pre B l enter leave hb hr hd
  obtain ⟨m, cols, t, k, h0, h1, h2, h3⟩ := h pre B l hb
  obtain ⟨t0, tE, e1, e2, e4⟩ := seat_step B enter _ leave hr hd ft m t _ cols k h1
  obtain ⟨r0, rs', e3, hy⟩ := hY t0 _ cols h3 tE k e2
  exact ⟨m, t0, r0, rs', cols, tE, k, t, h0, e1, e3, e3 ▸ e2, e4, h2, hy⟩

/-- A chain's yes, at a view whose drawn elements are canonical. -/
theorem chain_atSeat (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) {S : Type} (name : String) (ft : ℕ)
    (bs : List (Block S Unit)) (s s' : S) (v : Fmt.View) (hc : canonOk v.rounds = true)
    (h : chainAt name ft bs s v = .ok s') : AtSeat (YesConst X p) p ft bs s s' v :=
  atSeat_of_steps _ p ft
    (fun t0 mine cols hcan tE n hs =>
      yesConst_of_step X p he ha hp hnz hdeal htie hlog t0 ft mine cols hcan tE n hs)
    bs s s' v (H2K.First.chain_step_canon name ft bs s s' v hc h)

/-- The own mask's arm. -/
theorem chain_atSeat_own (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (ho : p.nums.ownMask = true)
    (hown : ownTieOk p = true) {S : Type} (name : String) (ft : ℕ)
    (bs : List (Block S Unit)) (s s' : S) (v : Fmt.View) (hc : canonOk v.rounds = true)
    (h : chainAt name ft bs s v = .ok s') :
    AtSeat (fun F t0 r0 rs' cols => t0.mask = none → YesOwn X p F t0 r0 rs' cols) p ft bs s s' v :=
  atSeat_of_steps _ p ft
    (fun t0 mine cols hcan tE n hs =>
      yesOwn_of_step X p he ha hp hnz hdeal htie hlog ho hown t0 ft mine cols hcan tE n hs)
    bs s s' v (H2K.First.chain_step_canon name ft bs s s' v hc h)

/-- The three chains of a course that says yes, at one Y. -/
theorem course_of_steps (Y : ℕ → T12 → Fmt.RoundView → List Fmt.RoundView → List OpenedColumn → Prop) (p : P12)
    (hY : ∀ (ft : ℕ) (t0 : T12) (mine : List Fmt.RoundView) (cols : List OpenedColumn), canonOk mine = true →
      ∀ (tE : T12) (n : ℕ), (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 mine cols = .ok (tE, n) →
      ∃ r0 rs', mine = r0 :: rs' ∧ Y ft t0 r0 rs' cols)
    {S₁ S₂ S₃ : Type} (planWord : Option String)
    (okStart : Bool) (s₁ : S₁) (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : ℕ)
    (b₁ : List (Block S₁ Unit)) (b₂ : List (Block S₂ Unit)) (b₃ : List (Block S₃ Unit))
    (fin : S₁ → S₂ → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    AtSeat Y p 0 b₁ s₁ e.1 (withEmptySealRound v₁) ∧ AtSeat Y p 0 b₂ s₂ e.2.1 v₂ ∧
      ∃ s₃, start₃ e.1 e.2.1 = .ok s₃ ∧ AtSeat Y p ft b₃ s₃ e.2.2 v₃ := by
  obtain ⟨a1, a2, s₃, hs, a3⟩ := H2K.First.runCore_steps_canon _ _ _ _ _ _ _ _ _ _ _ _ _ e h
  exact ⟨atSeat_of_steps Y p 0 (hY 0) _ _ _ _ a1, atSeat_of_steps Y p 0 (hY 0) _ _ _ _ a2,
    s₃, hs, atSeat_of_steps Y p ft (hY ft) _ _ _ _ a3⟩

/-- FROM A YES OF THE DECISION's COURSE: at every seat of the kind's block at p, in each of the three chains. -/
theorem course_atSeat (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) {S₁ S₂ S₃ : Type} (planWord : Option String)
    (okStart : Bool) (s₁ : S₁) (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : ℕ)
    (b₁ : List (Block S₁ Unit)) (b₂ : List (Block S₂ Unit)) (b₃ : List (Block S₃ Unit))
    (fin : S₁ → S₂ → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    AtSeat (YesConst X p) p 0 b₁ s₁ e.1 (withEmptySealRound v₁) ∧
      AtSeat (YesConst X p) p 0 b₂ s₂ e.2.1 v₂ ∧
      ∃ s₃, start₃ e.1 e.2.1 = .ok s₃ ∧ AtSeat (YesConst X p) p ft b₃ s₃ e.2.2 v₃ :=
  course_of_steps _ p
    (fun F t0 mine cols hcan tE n hs =>
      yesConst_of_step X p he ha hp hnz hdeal htie hlog t0 F mine cols hcan tE n hs)
    planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ e h

/-- The own mask's arm. -/
theorem course_atSeat_own (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (ho : p.nums.ownMask = true)
    (hown : ownTieOk p = true) {S₁ S₂ S₃ : Type} (planWord : Option String)
    (okStart : Bool) (s₁ : S₁) (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : ℕ)
    (b₁ : List (Block S₁ Unit)) (b₂ : List (Block S₂ Unit)) (b₃ : List (Block S₃ Unit))
    (fin : S₁ → S₂ → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    AtSeat (fun F t0 r0 rs' cols => t0.mask = none → YesOwn X p F t0 r0 rs' cols) p 0 b₁ s₁ e.1
        (withEmptySealRound v₁) ∧
      AtSeat (fun F t0 r0 rs' cols => t0.mask = none → YesOwn X p F t0 r0 rs' cols) p 0 b₂ s₂
        e.2.1 v₂ ∧
      ∃ s₃, start₃ e.1 e.2.1 = .ok s₃ ∧
        AtSeat (fun F t0 r0 rs' cols => t0.mask = none → YesOwn X p F t0 r0 rs' cols) p ft b₃ s₃
          e.2.2 v₃ :=
  course_of_steps _ p
    (fun F t0 mine cols hcan tE n hs =>
      yesOwn_of_step X p he ha hp hnz hdeal htie hlog ho hown t0 F mine cols hcan tE n hs)
    planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ e h

/-- Where the door lays no mask at any record, the own arm's one premise on the record is paid. -/
theorem atSeat_mask (X : Letters) (p : P12) (ft : ℕ) {S : Type} (bs : List (Block S Unit))
    (s s' : S) (v : Fmt.View)
    (h : AtSeat (fun F t0 r0 rs' cols => t0.mask = none → YesOwn X p F t0 r0 rs' cols) p ft bs s s'
      v)
    (pre : List (Block S Unit)) (B : Block S Unit) (l : List (Block S Unit))
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (henter : ∀ s t, enter s = .ok t → t.mask = none)
    (hb : bs = pre ++ B :: l) (hr : B.rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds)
    (hd : B.decide = (Block.inside enter (proximityTestKind guardedProximityTestParts p : Blk') leave).decide) :
    ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
      enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
      YesOwn X p ft t0 r0 rs' cols := by
  obtain ⟨m, t0, r0, rs', cols, _, _, _, h0, e1, e3, _, _, _, hy⟩ := h pre B l enter leave hb hr hd
  exact ⟨m, t0, r0, rs', cols, h0, e1, e3, hy (henter m t0 e1)⟩

end H2K.JointK

#print axioms H2K.JointK.seat_step
#print axioms H2K.JointK.yesConst_of_step
#print axioms H2K.JointK.yesOwn_of_step
#print axioms H2K.JointK.chain_atSeat
#print axioms H2K.JointK.chain_atSeat_own
#print axioms H2K.JointK.course_atSeat
#print axioms H2K.JointK.course_atSeat_own
#print axioms H2K.JointK.atSeat_mask
