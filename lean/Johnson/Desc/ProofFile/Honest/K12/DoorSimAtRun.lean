-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorSimAtRun.lean

What it proves. The clause door of the condition at a part's entry (OnFreeT.door,
Sim/TreesExact.lean) as a conclusion, at the proximity test on G_u, at a run of the frame's walking
prover (runC) at the proof file's own description under the head P5J.AtMg. The prover's state
function is doorUF (DoorsByShape.lean) with the reader colsLoc (DoorReturns.lean) at the prover's
own stored columns. The simulator's, simDoorU, given the stored table's columns opened at "LOC"'s
positions, is the same text at another function for the stored columns: the look-up in what a
simulator is given (Before.stored). At the stand's input, and at the input's public part and the
run's own front cut back by the rounds of the test in front of the part, the two give one state
(door_sim_at_run).

Names.
  storedIn, simDoorU   the look-up; the simulator's state function, given these columns.
  doorUF_congr, colsLoc_congr, mem_colsLoc   what doorUF and colsLoc read of their arguments.
  reads_loc, fill_some   the frame's reads at "LOC"'s round; where fillCols returns, each stored
      column that is read is there.
  four_of   a list with a member of number 3, written out.
  door_sim_at_run   the theorem.

By what. called_at_run (CalledAtRun.lean); rounds_eight (DoorAtWalk.lean); decl_shared_F0T
(DoorAtFile.lean); reads_skip (DoorReturns.lean). Of the frame's laws (ProofFile/Honest/Law/):
mid_shared (RunMidFile.lean); before_shared, shownBy_take (RunBefore.lean); shownBy_length
(Rule/Shown.lean); roundsOff_by, seen_by, find_stored (Rule/Faith.lean); shown_is, runOk_of
(Rule/Reads.lean); runC_bare (WalkReads.lean); runC_laidAs (RunAtFile.lean); laidAs_drawn
(RunAt.lean); stretch_back (OwedParts.lean); ready_ok, steps_shaped.

Limits.
- It is the clause door alone, of the eight of OnFreeT, and at a simulator's job whose state
  function is simDoorU.
- The equation holds whether or not the fold in front returns: that the one state is the verifier's
  is door_at_run's sentence (DoorAtRun.lean), which asks besides that the prover's key is the
  instance's.
- The front is Run.beforeAt at storedShown of the prover's stored columns at Run.storedAsked
  (ProofFile/Honest/Side.lean). Another term for a front wants a lemma of its own.
- The simulator is given the stored table's columns opened at "LOC"'s positions: these are computed
  from the weights; what covers them is the result on the committed tables, within its budget of
  columns: they count against it.
- simDoorU reads of a front its rounds as a view shows them and its stored columns at "LOC"'s
  positions. What is read is said here, and no more: of Before.stored the frame's own text says that
  in a real run the values are the prover's own and depend on its input.
- It is of the walk (runC), not of play (run): the stand m is the state that midSharedAtW
  (ProofFile/Honest/MidW.lean) returns in front of the part. Nothing on whether ready or runC
  returns, or whether the part is called.
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone.
- It stands over the files that MarksBehind.lean's head names
  and over sixteen others: the frame's authors'
  Honest/Blind, Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW, WalkHeard, WalkLive,
  WalkOpened, Law/WalkMid, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt, Law/Rule/OpenedStep, and this
  folder's LiveField.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.Desc.ProofFile.Honest.Law.Rule.Faith
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12)
open Desc.K14 (P14 St blocks first readsAtLoc)
open Desc.K14.Honest (ReadsNone flatOf_carried)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt Before Read Table
  ready runC midSharedAtW storedShown readsOf fillCols)

/-! ## 1 The simulator's state function -/

/-- A stored table's column, looked up in what a simulator is given of the stored tables
(Before.stored): in the text of the frame's own look-up (Before.wordsAt,
ProofFile/Honest/Law/Rule/Session.lean). -/
def storedIn (st : List (ℕ × ℕ × List UInt64)) (i x : ℕ) : Option (List UInt64) :=
  (st.find? fun c => c.1 == i && c.2.1 == x).map (·.2.2)

/-- **The simulator's state function at the test on G_u, given the stored table's columns opened at
"LOC"'s positions**: the same text as the prover's, doorUF with the reader colsLoc, at another
function for the stored columns: the look-up in what the simulator is given. pb: the public part of
a shared part's input: the key. It reads of front its rounds as a view shows them and its stored
columns; no input, no coin. The Front that it lays for doorUF hands no columns (Seen.bare: the field
opened is none); its reader takes of that Front the rounds alone. -/
def simDoorU (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit)) (pb : TableKey)
    (front : Before) : T12 :=
  doorUF Q sentU bs (fun w : TableKey × Before => w.1)
    (fun w fr => colsLoc Q (storedIn w.2.stored) fr.seen.rounds) (pb, front)
    (⟨[], (), Seen.bare front.seen⟩ : Front Unit)

/-! ## 2 What doorUF and colsLoc read -/

/-- doorUF reads of its arguments the key, the rounds seen and what the reader cols returns, alone.
The reader is handed the Front whole. -/
theorem doorUF_congr {W X W' X' : Type} (Q : P14) (sentU : Array OracleNotice)
    (bs : List (Block St Unit)) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (key' : W' → TableKey) (cols' : W' → Front X' → List OpenedColumn) (w : W) (fr : Front X) (w' : W')
    (fr' : Front X') (hk : key w = key' w') (hr : fr.seen.rounds = fr'.seen.rounds)
    (hc : cols w fr = cols' w' fr') :
    doorUF Q sentU bs key cols w fr = doorUF Q sentU bs key' cols' w' fr' := by
  unfold doorUF doorOf
  dsimp only
  rw [hk, hr, hc]

/-- A column that colsLoc lays stands at a position of "LOC"'s list at the round of number 3. -/
theorem mem_colsLoc (Q : P14) (stored : ℕ → ℕ → Option (List UInt64)) (rs : List Fmt.RoundView) (c : OpenedColumn)
    (h : c ∈ colsLoc Q stored rs) : ∃ R' : Fmt.RoundView, rs[3]? = some R' ∧
      c.2.1 ∈ Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R'.drawn.poss).map
        (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a)) := by
  unfold colsLoc at h
  split at h
  · rename_i R' hR
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    exact ⟨R', hR, hx⟩
  · cases h

/-- Two functions for the stored columns that agree at the positions which colsLoc lays give one
list. -/
theorem colsLoc_congr (Q : P14) (stored stored' : ℕ → ℕ → Option (List UInt64))
    (rs : List Fmt.RoundView)
    (h : ∀ c ∈ colsLoc Q stored rs, stored Q.item c.2.1 = stored' Q.item c.2.1) :
    colsLoc Q stored rs = colsLoc Q stored' rs := by
  cases hR : rs[3]? with
  | none =>
    unfold colsLoc
    rw [hR]
  | some R' =>
    have hm : ∀ x ∈ Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R'.drawn.poss).map
        (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a)), stored Q.item x = stored' Q.item x := by
      intro x hx
      refine h (Fmt.storedKey (readsAtLoc Q.S.fold Q.item).item, x,
        (stored (readsAtLoc Q.S.fold Q.item).item x).getD []) ?_
      unfold colsLoc
      rw [hR]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    unfold colsLoc
    rw [hR]
    refine List.map_congr_left fun x hx => ?_
    show (_, _, (stored Q.item x).getD []) = (_, _, (stored' Q.item x).getD [])
    rw [hm x hx]

/-! ## 3 The frame's reads at "LOC"'s round -/

/-- The frame's reads where the declared rounds are three that read nothing, then "LOC"'s, then
others: "LOC"'s reads of the committed table, then those of the rounds behind. -/
theorem reads_loc (Q : P14) (chain ft : ℕ) (st : ℕ → ℕ → Option (List UInt64))
    (tr : Fmt.TreeSource → Option (Place × Table)) (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry)
    (post : List Fmt.DeclaredRound) (h0 : ReadsNone d0) (h1 : ReadsNone d1) (h2 : ReadsNone d2)
    (R0 R1 R2 R : Fmt.Drawn) (Rest : List Fmt.Drawn) :
    readsOf chain ft st tr
        (d0 :: d1 :: d2 :: { entry := e, stored := [readsAtLoc Q.S.fold Q.item] } :: post)
        (R0 :: R1 :: R2 :: R :: Rest) =
      (Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R.poss).map
      (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a))).map (fun x =>
        (⟨Fmt.storedKey (readsAtLoc Q.S.fold Q.item).item, x,
          some (readsAtLoc Q.S.fold Q.item).item, none, none,
          st (readsAtLoc Q.S.fold Q.item).item x, (readsAtLoc Q.S.fold Q.item).sh.W⟩ : Read)) ++
        readsOf chain ft st tr post Rest := by
  rw [reads_skip _ _ _ _ d0 h0, reads_skip _ _ _ _ d1 h1, reads_skip _ _ _ _ d2 h2]
  conv_lhs => unfold readsOf
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Where the frame's fillCols returns at reads of one stored table in front of others, with no
stored run handed, each of these columns is there. -/
theorem fill_some (key item width : ℕ) (stored : ℕ → Option (List UInt64)) :
    ∀ (l : List ℕ) (B : List Read) (c : List OpenedColumn),
      fillCols (l.map (fun x => (⟨key, x, some item, none, none, stored x, width⟩ : Read)) ++ B)
        [] = .ok c → ∀ x ∈ l, ∃ w, stored x = some w
  | [], _, _, _, _, hx => by cases hx
  | y :: l, B, c, h, x, hx => by
    rw [List.map_cons, List.cons_append] at h
    unfold fillCols at h
    cases hs : stored y with
    | none =>
      simp only [hs, List.head?_nil] at h
      cases h
    | some wd =>
      simp only [hs, List.tail_nil] at h
      split at h
      · cases h
      · cases hq : fillCols (l.map (fun x =>
            (⟨key, x, some item, none, none, stored x, width⟩ : Read)) ++ B) [] with
        | error e =>
          rw [hq] at h
          cases h
        | ok c' =>
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact ⟨wd, hs⟩
          · exact fill_some key item width stored l B c' hq x hx'

/-- A list with a member of number 3, written out. -/
theorem four_of {α : Type} (l : List α) (a : α) (h : l[3]? = some a) :
    ∃ a0 a1 a2 t, l = a0 :: a1 :: a2 :: a :: t := by
  match l, h with
  | a0 :: a1 :: a2 :: b :: t, h =>
    have e : b = a := Option.some.inj h
    exact ⟨a0, a1, a2, t, by rw [e]⟩

/-! ## 4 The theorem -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The clause door of the condition at a part's entry (OnFreeT.door, Sim/TreesExact.lean) as a
conclusion, at a run of the proof file's own description under the head**: the prover's state
function at the stand's input and the simulator's at the input's public part and at the run's own
front, cut back by the i rounds of the test that come before the part, give one state.
The prover's Front fr is any that shows just the rounds in front of the test, as the stand has seen
them: at every value of the field opened.
The prover's: doorUF with colsLoc at the prover's own stored columns. The simulator's: simDoorU,
given the stored table's columns opened at "LOC"'s positions.
The front: Run.beforeAt at storedShown of the prover's stored columns at all that the run reads of
stored tables (ProofFile/Honest/Side.lean).
The premises are door_at_run's, less hα: the equation holds whether or not the fold in front
returns, so the prover's key is not asked to be the instance's. It is of the walk (runC), not of
play (run); nothing on whether runC returns or calls the part. That the one state is the verifier's
is door_at_run's sentence, not this one's. The test on G_u alone. -/
theorem door_sim_at_run {W₀ Rc Tr X₀ Y V Pb X : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre t : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀,
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length + i ∧
      ∀ fr : Front X, fr.seen.rounds =
          m.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length →
        doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
            (fun w : Common W₀ Rc TableKey => w.key)
            (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
            m.st.input fr =
          simDoorU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
            m.st.input.key
            ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
              ⟨σ.block.place, u.number⟩).cut i) := by
  obtain ⟨m, s, cols, more, rest, hm, hin, hrounds, hlen, hcols, hfold, hfill⟩ :=
    called_at_run h.laid.planOk hR σ u pre t i S hrun hc
  -- the blocks in front are the nine
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  subst epre
  have eR : ([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  have hlen : m.seen.length =
      (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds)).length +
        i := hlen
  have hfill : fillCols (readsOf 1 0 (P.storedWords w₀ rc)
      (ProofFile.Honest.treeOwn (r.run.played.2.1.take
              (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
                (·.rounds)).length))
      (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds))
      ((m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
        (·.rounds)).length).map (·.drawn))) [] = .ok cols := hfill
  have Sstr : ProofFile.Honest.InStretch R.shared ⟨σ.block.place, u.number⟩
      ((([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
        (·.rounds)).length + i) u.rounds.length := S.str
  have Sfits : (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
      (·.rounds)).length + i + u.rounds.length ≤ R.shared.length := S.fits
  rw [eR] at hlen hfill Sstr Sfits
  -- the frame's laws at this run
  have Q := ((P5J.F0T o Zp Np cF).planOk_ok).1 h.laid.planOk
  have hp := Q.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ProofFile.Honest.ready_ok hR
  have o₁ := ProofFile.Honest.steps_shaped s1 Q.blocks₁
  have o₂ := ProofFile.Honest.steps_shaped s2 Q.blocks₂
  have o₃ := ProofFile.Honest.steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := ProofFile.Honest.stretch_back Sstr S.pos Sfits
  obtain ⟨m', hm', hseen⟩ := ProofFile.Honest.mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  rw [hN] at hseen
  have hbef := ProofFile.Honest.before_shared hrun hR o₁ o₂ o₃ hp ha hseg
    (ProofFile.Honest.treeAsks (P5J.F0T o Zp Np cF) ρ 1)
    (ProofFile.Honest.shown_is (ProofFile.Honest.runOk_of hrun).1 1 (by decide))
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  rw [hN] at hbef
  obtain ⟨-, lS, -⟩ := ProofFile.Honest.runC_laidAs hrun hR o₁ o₂ o₃
  have hdr := ProofFile.Honest.laidAs_drawn lS
  have hbare := (ProofFile.Honest.runC_bare hrun hR o₁ o₂ o₃).2.1.1
  -- what the stand has seen of the eight
  have htake : m'.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length =
      ProofFile.Honest.roundsOf (r.run.played.2.1.take
              ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length) := by
    rw [hseen]
    unfold ProofFile.Honest.roundsOf
    rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  have hplen : ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length + i ≤
      r.run.played.2.1.length := by
    have e := congrArg List.length hseen
    rw [hlen, ProofFile.Honest.roundsOf_length, List.length_take] at e
    omega
  -- the front, cut back
  have hcut : ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i) =
      ⟨ProofFile.Honest.shownBy 1 (ProofFile.Honest.treeAsks (P5J.F0T o Zp Np cF) ρ 1)
        (r.run.played.2.1.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) r.run.storedAsked⟩ := by
    rw [hbef]
    unfold ProofFile.Honest.Before.cut
    simp only [ProofFile.Honest.shownBy_length, List.length_take, Nat.min_eq_left hplen,
      Nat.add_sub_cancel]
    rw [← ProofFile.Honest.shownBy_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  refine ⟨m', hm, hlen, fun fr hfr => ?_⟩
  unfold simDoorU
  rw [hcut]
  have hseenF : (⟨ProofFile.Honest.shownBy 1 (ProofFile.Honest.treeAsks (P5J.F0T o Zp Np cF) ρ 1)
        (r.run.played.2.1.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) r.run.storedAsked⟩ : Before).seen =
      m'.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length := by
    rw [ProofFile.Honest.seen_by, ProofFile.Honest.roundsOff_by, htake]
  refine doorUF_congr _ _ _ _ _ _ _ _ _ _ _ rfl (by rw [hfr, hseenF]; rfl) ?_
  show colsLoc (K1.qAt Zp Np) (P.storedWords m'.st.input.w₀ m'.st.input.rc) fr.seen.rounds =
    colsLoc (K1.qAt Zp Np) (storedIn (storedShown (P.storedWords w₀ rc) r.run.storedAsked))
      (⟨ProofFile.Honest.shownBy 1 (ProofFile.Honest.treeAsks (P5J.F0T o Zp Np cF) ρ 1)
        (r.run.played.2.1.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) r.run.storedAsked⟩ : Before).seen
  rw [hseenF, hfr, hin]
  refine colsLoc_congr _ _ _ _ fun c hcm => ?_
  obtain ⟨R', hR3, hx⟩ := mem_colsLoc _ _ _ c hcm
  -- the stored column is there
  obtain ⟨r0, r1, r2, rt, ers⟩ := four_of _ R' hR3
  obtain ⟨d0, d1, d2, e, post, q0, q1, q2, eq⟩ := rounds_eight (K1.qAt Zp Np)
    (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb (facts_at_head h).2.2
  rw [ers, eq] at hfill
  simp only [List.map_cons] at hfill
  rw [reads_loc (K1.qAt Zp Np) 1 0 _ _ d0 d1 d2 e post q0 q1 q2] at hfill
  obtain ⟨wd, hwd⟩ := fill_some _ _ _
    (P.storedWords w₀ rc (readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item).item) _ _ cols
    hfill c.2.1 hx
  -- the position stands among what the run reads of stored tables
  have h3 : ρ.shared[3]? = some R'.drawn := by
    have e1 : (ProofFile.Honest.roundsOf r.run.played.2.1)[3]? = some R' := by
      rw [htake] at hR3
      unfold ProofFile.Honest.roundsOf at hR3 ⊢
      rw [List.map_take, List.getElem?_take] at hR3
      split at hR3
      · exact hR3
      · cases hR3
    rw [← hdr]
    have e2 : r.run.played.2.1.map (·.drawn) =
        (ProofFile.Honest.roundsOf r.run.played.2.1).map (·.drawn) := by
      unfold ProofFile.Honest.roundsOf
      rw [List.map_map]
      rfl
    rw [e2, List.getElem?_map, e1]
    rfl
  obtain ⟨D0, D1, D2, Dt, eρ⟩ := four_of _ _ h3
  obtain ⟨d0', d1', d2', e', post', q0', q1', q2', eq'⟩ := decl_shared_F0T (o := o) h
  rw [eq', eρ, reads_loc (K1.qAt Zp Np) 1 0 _ _ d0' d1' d2' e' post' q0' q1' q2'] at hbare
  have hmemB : (⟨Fmt.storedKey (readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item).item, c.2.1,
      some (readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item).item, none, none, none,
      (readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item).sh.W⟩ : Read) ∈
      r.run.reads.2.1.map Read.bare := by
    rw [hbare]
    exact List.mem_append_left _ (List.mem_map.2 ⟨c.2.1, hx, rfl⟩)
  obtain ⟨q, hq, eqb⟩ := List.mem_map.1 hmemB
  have hitem : q.item = some (K1.qAt Zp Np).item := congrArg Read.item eqb
  have hpos : q.pos = c.2.1 := congrArg Read.pos eqb
  have hask : ((K1.qAt Zp Np).item, c.2.1) ∈ r.run.storedAsked := by
    unfold ProofFile.Honest.Run.storedAsked
    refine List.mem_filterMap.2 ⟨q, List.mem_append_left _ (List.mem_append_right _ hq), ?_⟩
    rw [hitem, hpos]
    rfl
  have hwd' : P.storedWords w₀ rc (K1.qAt Zp Np).item c.2.1 = some wd := hwd
  rw [hwd']
  exact (ProofFile.Honest.find_stored (P.storedWords w₀ rc) _ _ wd hwd' _ hask).symm

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.storedIn
#print axioms ProofFile.Honest.K12.Light.simDoorU
#print axioms ProofFile.Honest.K12.Light.doorUF_congr
#print axioms ProofFile.Honest.K12.Light.mem_colsLoc
#print axioms ProofFile.Honest.K12.Light.colsLoc_congr
#print axioms ProofFile.Honest.K12.Light.reads_loc
#print axioms ProofFile.Honest.K12.Light.fill_some
#print axioms ProofFile.Honest.K12.Light.four_of
#print axioms ProofFile.Honest.K12.Light.door_sim_at_run
