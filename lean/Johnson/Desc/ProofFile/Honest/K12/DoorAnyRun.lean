-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorAnyRun.lean

What it proves. The two sentences on the door at the proximity test on G_u at a run of the frame's
walking prover (DoorAtRun.lean, DoorSimAtRun.lean), in forms that serve at every description: under
the head and at a small made-up file alike. (1) door_sim_any: the prover's state function and the
simulator's, given the stored table's columns opened at "LOC"'s positions, give one state: general
in the description outright: no text in it names the shared chain's state type. (2) door_of_called:
the prover's state function against what called_at_run (CalledAtRun.lean) returns at a description
whose shared chain's state is St: no description stands in it; a caller's terms meet it by
unfolding.

Names.
  door_sim_any     (1).
  door_of_called   (2).

By what. called_at_run (CalledAtRun.lean); simDoorU, doorUF_congr, colsLoc_congr, mem_colsLoc,
reads_loc, fill_some, four_of (DoorSimAtRun.lean); door_of_cols (DoorAtWalk.lean); foldBlocks_more
(DoorReturns.lean); fold_like, peel_front (Johnson/Desc/K14/Honest/FlatSteps.lean); and the frame's
laws that DoorSimAtRun.lean's head names.

Limits.
- In door_sim_any Q, sentU and bs are free: it says that the two state functions agree: one text at
  equal arguments. Not that either is a door of the description; not that the state is the
  verifier's.
- In door_of_called k, vr, vo and pre are free: no verifier stands in it: it is against what
  called_at_run returns.
- door_at_run and door_sim_at_run have proofs of their own, of the same text: two texts of one proof
  each.
- Of the walk (runC), not of play (run); nothing on whether ready or runC returns, or whether the
  part is called.
- The simulator is given the stored table's columns opened at "LOC"'s positions: these are computed
  from the weights and count against the committed tables' budget of columns (DoorSimAtRun.lean's
  head).
- simDoorU reads of a front its rounds as a view shows them and its stored columns at "LOC"'s
  positions: what is read is said, and no more (DoorSimAtRun.lean's head).
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone.
- What MarksBehind.lean stands over are files of this library.
  Also beneath this file: K12/LiveField.lean and, of the frame's authors (ProofFile/Honest/): Blind,
  Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW, WalkHeard, WalkLive, WalkOpened,
  Law/WalkMid, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt, Law/Rule/OpenedStep.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorSimAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn Place FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (Seat.enter)
open Desc.K14 (P14 St blocks first readsAtLoc withU frontBlock)
open Desc.K14.Honest (ReadsNone Like fold_like peel_front)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt Before Read Table
  ready runC midSharedAtW storedShown readsOf fillCols)

/-- **The clause door at a run, general in the description.** F: any description; its shared chain's
state type is not named. Q, sentU, bs: the letters of the two state functions, free. hpre: the
rounds that the blocks in front of the part's block declare are three that read no column, then
"LOC"'s round at Q, then others. Then, at the stand in front of a called part of the shared chain,
the prover's state function (doorUF with colsLoc at the prover's own stored columns) at the stand's
input and the simulator's (simDoorU, given the stored table's columns opened at "LOC"'s positions)
at the input's key and at the run's own front, cut back by the i rounds of the part's block that
come before the part, give one state.
The prover's Front fr is any that shows just the rounds in front of the part's block, as the stand
has seen them: at every value of the field opened.
Public: hpl, hpre. On the filling and the book: hR, S. On the run: hrun, hc.
The equation holds whether or not the fold over bs returns; that the state is the verifier's is not
said. It is of the walk (runC), not of play (run); nothing on whether runC returns or calls the
part. -/
theorem door_sim_any {Xi W₀ Rc Tr X₀ Y V Pb X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit))
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre t : List (Block F.S₂ F.Cl)) (i : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry) (post : List Fmt.DeclaredRound)
    (h0 : ReadsNone d0) (h1 : ReadsNone d1) (h2 : ReadsNone d2)
    (hpre : pre.flatMap (·.rounds) =
      d0 :: d1 :: d2 :: { entry := e, stored := [readsAtLoc Q.S.fold Q.item] } :: post)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀,
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      ∀ fr : Front X, fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        doorUF Q sentU bs (fun w : Common W₀ Rc TableKey => w.key)
            (fun w fr => colsLoc Q (P.storedWords w.w₀ w.rc) fr.seen.rounds) m.st.input fr =
          simDoorU Q sentU bs m.st.input.key
            ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
              ⟨σ.block.place, u.number⟩).cut i) := by
  obtain ⟨m, s, cols, more, rest, hm, hin, hrounds, hlen, hcols, hfold, hfill⟩ :=
    called_at_run hpl hR σ u pre t i S hrun hc
  have Q' := (F.planOk_ok).1 hpl
  have hp := Q'.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ProofFile.Honest.ready_ok hR
  have o₁ := ProofFile.Honest.steps_shaped s1 Q'.blocks₁
  have o₂ := ProofFile.Honest.steps_shaped s2 Q'.blocks₂
  have o₃ := ProofFile.Honest.steps_shaped s3 Q'.blocks₃
  obtain ⟨ha, hN, -, hseg⟩ := ProofFile.Honest.stretch_back S.str S.pos S.fits
  obtain ⟨m', hm', hseen⟩ := ProofFile.Honest.mid_shared hrun hR o₁ o₂ o₃ hp ha hseg hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  rw [hN] at hseen
  have hbef := ProofFile.Honest.before_shared hrun hR o₁ o₂ o₃ hp ha hseg
    (ProofFile.Honest.treeAsks F ρ 1) (ProofFile.Honest.shown_is (ProofFile.Honest.runOk_of hrun).1 1 (by decide))
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  rw [hN] at hbef
  obtain ⟨-, lS, -⟩ := ProofFile.Honest.runC_laidAs hrun hR o₁ o₂ o₃
  have hdr := ProofFile.Honest.laidAs_drawn lS
  have hbare := (ProofFile.Honest.runC_bare hrun hR o₁ o₂ o₃).2.1.1
  have htake : m'.seen.take (pre.flatMap (·.rounds)).length =
      ProofFile.Honest.roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) := by
    rw [hseen]
    unfold ProofFile.Honest.roundsOf
    rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  have hplen : (pre.flatMap (·.rounds)).length + i ≤ r.run.played.2.1.length := by
    have e' := congrArg List.length hseen
    rw [hlen, ProofFile.Honest.roundsOf_length, List.length_take] at e'
    omega
  have hcut : ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i) =
      ⟨ProofFile.Honest.shownBy 1 (ProofFile.Honest.treeAsks F ρ 1)
        (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) r.run.storedAsked⟩ := by
    rw [hbef]
    unfold ProofFile.Honest.Before.cut
    simp only [ProofFile.Honest.shownBy_length, List.length_take, Nat.min_eq_left hplen,
      Nat.add_sub_cancel]
    rw [← ProofFile.Honest.shownBy_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
  refine ⟨m', hm, hlen, fun fr hfr => ?_⟩
  unfold simDoorU
  rw [hcut]
  have hseenF : (⟨ProofFile.Honest.shownBy 1 (ProofFile.Honest.treeAsks F ρ 1)
        (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) r.run.storedAsked⟩ : Before).seen =
      m'.seen.take (pre.flatMap (·.rounds)).length := by
    rw [ProofFile.Honest.seen_by, ProofFile.Honest.roundsOff_by, htake]
  refine doorUF_congr _ _ _ _ _ _ _ _ _ _ _ rfl (by rw [hfr, hseenF]; rfl) ?_
  show colsLoc Q (P.storedWords m'.st.input.w₀ m'.st.input.rc) fr.seen.rounds =
    colsLoc Q (storedIn (storedShown (P.storedWords w₀ rc) r.run.storedAsked))
      (⟨ProofFile.Honest.shownBy 1 (ProofFile.Honest.treeAsks F ρ 1)
        (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) r.run.storedAsked⟩ : Before).seen
  rw [hseenF, hfr, hin]
  refine colsLoc_congr _ _ _ _ fun c hcm => ?_
  obtain ⟨R', hR3, hx⟩ := mem_colsLoc _ _ _ c hcm
  obtain ⟨r0, r1, r2, rt, ers⟩ := four_of _ R' hR3
  rw [ers, hpre] at hfill
  simp only [List.map_cons] at hfill
  rw [reads_loc Q 1 0 _ _ d0 d1 d2 e post h0 h1 h2] at hfill
  obtain ⟨wd, hwd⟩ := fill_some _ _ _
    (P.storedWords w₀ rc (readsAtLoc Q.S.fold Q.item).item) _ _ cols hfill c.2.1 hx
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
  have hdecl : F.roundsDeclaredByBlocks.2.1 = d0 :: d1 :: d2 ::
      { entry := e, stored := [readsAtLoc Q.S.fold Q.item] } ::
        (post ++ (σ.block :: t).flatMap (·.rounds)) := by
    show F.shared.blocksInOrder.flatMap (·.rounds) = _
    rw [S.cut, List.flatMap_append, hpre]
    rfl
  rw [hdecl, eρ, reads_loc Q 1 0 _ _ d0 d1 d2 e _ h0 h1 h2] at hbare
  have hmemB : (⟨Fmt.storedKey (readsAtLoc Q.S.fold Q.item).item, c.2.1,
      some (readsAtLoc Q.S.fold Q.item).item, none, none, none,
      (readsAtLoc Q.S.fold Q.item).sh.W⟩ : Read) ∈ r.run.reads.2.1.map Read.bare := by
    rw [hbare]
    exact List.mem_append_left _ (List.mem_map.2 ⟨c.2.1, hx, rfl⟩)
  obtain ⟨q, hq, eqb⟩ := List.mem_map.1 hmemB
  have hitem : q.item = some Q.item := congrArg Read.item eqb
  have hpos : q.pos = c.2.1 := congrArg Read.pos eqb
  have hask : (Q.item, c.2.1) ∈ r.run.storedAsked := by
    unfold ProofFile.Honest.Run.storedAsked
    refine List.mem_filterMap.2 ⟨q, List.mem_append_left _ (List.mem_append_right _ hq), ?_⟩
    rw [hitem, hpos]
    rfl
  have hwd' : P.storedWords w₀ rc Q.item c.2.1 = some wd := hwd
  rw [hwd']
  exact (ProofFile.Honest.find_stored (P.storedWords w₀ rc) _ _ wd hwd' _ hask).symm

/-- **The door against what called_at_run returns, with no description in it.** pre: blocks of the
state St that are, member by member, like the shared chain's front block and the eight. seen, cols,
vr, vo, s: what called_at_run returns at a description whose shared chain's state is St: the rounds
that the stand has seen; the columns; the shared view's rounds and columns; the state that the fold
over pre returns. Then the fold over the plain eight at the whole view returns the same state, and
doorUF with colsLoc gives what the seat's way in makes of it, at every input and front whose three
readers agree with k, stored and the eight's rounds as seen. k, vr, vo and pre are free: no verifier
stands in it. -/
theorem door_of_called {Cl V X : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (pre : List (Block St Cl))
    (hpre : List.Forall₂ Like pre [frontBlock c, b1, b2, b3, b4, b5, b6, b7, b8])
    (stored : ℕ → ℕ → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table))
    (k : TableKey) (seen rest vr : List Fmt.RoundView) (cols more vo : List OpenedColumn) (s : St)
    (hvr : vr = seen ++ rest) (hvo : vo = cols ++ more)
    (hfold : foldBlocks 0 pre (first Q.codes k) (seen.take (pre.flatMap (·.rounds)).length) cols =
      .ok (s, [], []))
    (hfill : fillCols (readsOf 1 0 stored tree (pre.flatMap (·.rounds))
      ((seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols) :
    (∃ rest', foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) vr vo =
        .ok (s, rest', more)) ∧
      pre.flatMap (·.rounds) = [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) ∧
      ∀ (key : V → TableKey) (st : V → ℕ → ℕ → Option (List UInt64)) (w : V) (fr : Front X),
        key w = k → st w = stored →
        fr.seen.rounds = seen.take (pre.flatMap (·.rounds)).length →
        Seat.enter (·.gU) (·.firstMask) s =
          .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
            (fun w fr => colsLoc Q (st w) fr.seen.rounds) w fr) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :
      ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8, pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] ∧
        Like x0 (frontBlock c) ∧ Like x1 b1 ∧ Like x2 b2 ∧ Like x3 b3 ∧ Like x4 b4 ∧ Like x5 b5 ∧
        Like x6 b6 ∧ Like x7 b7 ∧ Like x8 b8 := by
    cases hpre with
    | cons l0 h => cases h with
      | cons l1 h => cases h with
        | cons l2 h => cases h with
          | cons l3 h => cases h with
            | cons l4 h => cases h with
              | cons l5 h => cases h with
                | cons l6 h => cases h with
                  | cons l7 h => cases h with
                    | cons l8 h =>
                      cases h
                      exact ⟨_, _, _, _, _, _, _, _, _, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩
  have eR : [x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  have hfill' := hfill
  rw [eR] at hfill'
  have hfold' := hfold
  rw [eR] at hfold'
  obtain ⟨-, g2⟩ := door_of_cols (V := V) (X := X) c Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU _ hpre 1
    stored tree k _ cols s hfold' hfill'
  have gE := peel_front c 0 _ _ _ _ _ (fold_like 0 _ _ hpre _ _ _ _ hfold')
  have hview := foldBlocks_more 0 _ _ _ _ _ gE
    (seen.drop ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length ++ rest) more
  rw [← List.append_assoc, List.take_append_drop, ← hvr, ← hvo] at hview
  refine ⟨⟨_, hview⟩, eR, fun key st w fr hk hs hfr => ?_⟩
  rw [eR] at hfr
  exact g2 key st w fr hk hs hfr

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.door_sim_any
#print axioms ProofFile.Honest.K12.Light.door_of_called
