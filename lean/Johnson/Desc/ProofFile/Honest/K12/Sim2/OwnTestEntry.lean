-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the door at the request's own test, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/OwnTestEntry.lean: at a called part of the request's own
proximity test (the place placeW, on the last chain), at a run of the walking prover, the job's state
on entry doorW at the stand's front is the simulators' stateAtOwnTest at the run's front cut back: on
both sides it is what enterOwn makes of the state of the run's own fold. No property of the protocol
is claimed.

  door_last_with_columns   door_last_at_called (DoorLastAtRun.lean) with one clause more: the columns are
                      what fillCols returns. A second text of that proof
  state_on_last_chain_with_columns   stateFromViewOnLastChain_at_stand (Sim2/DoorW.lean) with that
                      clause. A second text of that proof
  first_play_guarded_at_second, five_at_second_guarded   first_play_at_second, five_at_second where
                      the prover's half stands behind needsField, as halfW lays it
  lendPart_guarded, lend_guarded   the lending does not see the guard
  door_at_own_test    the equation
  draws_fit_last_chain, foldl_guarded_row, fits_guarded_row   three small lemmas
  five_at_own_test    under the head, at the side with the guarded row, the five clauses at a run

Limits. Conditional on ready, runC and the part's being called; of the walk. In door_at_own_test any
member u stands, guarded or not: S and hc speak of it. five_at_own_test leaves by name hg, that the
prover's last list holds the job's guarded half (the filling's), and hT, the test on the book; it
stands under the head. The clause fold speaks of the job's own state on entry. Nothing on what a part
shows. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorWAt
import Johnson.Desc.ProofFile.Honest.K12.DoorLastAtRun
import Johnson.Desc.ProofFile.Honest.K12.FiveAtSecond
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsAtSecond
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Clauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks Oracle Place withEmptySealRound)
open Johnson.Prover.Link (μOf rowOf)
open H2K.Pub (sgOf)
open H2K.Member (piWFull)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light

section
variable {Xi : Type}

theorem door_last_with_columns {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x c = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hrun : runC F Bk P w₀ rc x c ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (e₁ : F.S₁) (e₂ : F.S₂) (v₀ s : F.S₃)
      (cols : List OpenedColumn) (tr : Tr),
      midAtW F Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      m.seen.length = (F.first.blocksInOrder.flatMap (·.rounds)).length +
        (F.shared.blocksInOrder.flatMap (·.rounds)).length + (pre.flatMap (·.rounds)).length + i ∧
      m.opened = some (r.run.views.1.opened ++ r.run.views.2.1.opened ++ cols) ∧
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧ F.start₃ (F.pub x) e₁ e₂ = .ok v₀ ∧
      foldBlocks F.lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      fillCols (readsOf 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
        (treeThird r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols ∧
      ∀ {W : Type} (xOf : W → Xi) (w : W) (enter : F.S₃ → Except String T12)
        (fr : Front Y) (k : ℕ), xOf w = x →
        (F.first.blocksInOrder.flatMap (·.rounds)).length + (F.shared.blocksInOrder.flatMap (·.rounds)).length +
          (pre.flatMap (·.rounds)).length ≤ k →
        fr.seen.rounds = m.seen.take k → fr.seen.opened = m.opened →
          doorLastTry F.first.blocksInOrder F.shared.blocksInOrder pre F.lastChainFirstTreeNumber
            (fun w => F.start₁ (F.pub (xOf w))) (fun w => F.start₂ (F.pub (xOf w)))
            (fun w => F.start₃ (F.pub (xOf w))) enter colsOpened w fr = enter s := by
  obtain ⟨m, e₁, e₂, v₀, -, -, -, -, tr, hm, -, hin, hseen, he₁, he₂, hst, -⟩ :=
    called_at_second hpl hR σ u pre t i S hrun hc
  obtain ⟨m₁, m₂, m', a₁, z₁, a₂, z₂, a₃, y, ha₁, hz₁, -, -, ha₂, hz₂, -, -, ha₃, hy, ly, hym,
    hmid⟩ := played_at_second hpl hR hrun σ u pre t i _ S rfl hc
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hmid))
  obtain ⟨⟨g1, g2, g3⟩, ⟨g4, g5, g6⟩, -⟩ := runC_ends hrun
  obtain ⟨R', b₁, w₁, b₂, w₂, b₃, w₃, hR', hb₁, hw₁, hq, hb₂, hw₂, -, -, hr⟩ := runC_parts hrun
  rw [hR] at hR'
  cases hR'
  obtain rfl : b₁ = a₁ := Except.ok.inj (hb₁.symm.trans ha₁)
  obtain rfl : w₁ = z₁ := Except.ok.inj (hw₁.symm.trans hz₁)
  obtain rfl : b₂ = a₂ := Except.ok.inj (hb₂.symm.trans ha₂)
  obtain rfl : w₂ = z₂ := Except.ok.inj (hw₂.symm.trans hz₂)
  subst hr
  have hs₁ : (withEmptySealRound (⟨(roundsOf w₁.laid).dropLast, w₁.cols⟩ : Fmt.View)).rounds =
      roundsOf w₁.laid := seal_back hq
  have q₁ : w₁.ver = some e₁ := he₁
  have q₂ : w₂.ver = some e₂ := he₂
  have n₁ : (roundsOf w₁.laid).length = (F.first.blocksInOrder.flatMap (·.rounds)).length := by
    have k := g1
    rw [show (withEmptySealRound (⟨(roundsOf w₁.laid).dropLast, w₁.cols⟩ : Fmt.View)).rounds =
      roundsOf w₁.laid from hs₁] at k
    exact k
  have n₂ : (roundsOf w₂.laid).length = (F.shared.blocksInOrder.flatMap (·.rounds)).length := g4
  have c₁ : w₁.cols.length = owed 0 F.first.blocksInOrder (roundsOf w₁.laid) := by
    have k := g2
    rw [show (withEmptySealRound (⟨(roundsOf w₁.laid).dropLast, w₁.cols⟩ : Fmt.View)).rounds =
      roundsOf w₁.laid from hs₁] at k
    exact k
  have c₂ : w₂.cols.length = owed 0 F.shared.blocksInOrder (roundsOf w₂.laid) := g5
  have f₁ : foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (roundsOf w₁.laid) w₁.cols =
      .ok (e₁, [], []) := by
    refine (fold_some 0 _ _ e₁ _ _ n₁ c₁).1 ?_
    have k := g3
    rw [show (withEmptySealRound (⟨(roundsOf w₁.laid).dropLast, w₁.cols⟩ : Fmt.View)).rounds =
      roundsOf w₁.laid from hs₁] at k
    exact k.symm.trans q₁
  have f₂ : foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) (roundsOf w₂.laid) w₂.cols =
      .ok (e₂, [], []) := by
    refine (fold_some 0 _ _ e₂ _ _ n₂ c₂).1 ?_
    exact g6.symm.trans q₂
  have hd : door₃ F x w₁.ver w₂.ver = some v₀ := by
    unfold door₃
    rw [q₁, q₂]
    show (F.start₃ (F.pub x) e₁ e₂).toOption = _
    rw [hst]
    rfl
  rw [hd, S.cut] at ha₃
  have hLo : ∀ ps, treeThird w₁.laid w₂.laid ps =
      (envOf (P.storedWords w₀ rc) (fun ch k => if ch == 0 then ((tablesOf w₁.laid)[k]?).bind id
        else if ch == 1 then ((tablesOf w₂.laid)[k]?).bind id else none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) w₁.laid w₂.laid ps).2).symm
  have hi : i < σ.block.rounds.length := by
    have h1 := S.le
    have h2 := S.pos
    omega
  have hlen : (R.second.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [List.length_take]
    exact Nat.min_eq_left (by have h3 := S.fits; omega)
  obtain ⟨s, cols, -, -, -, -, ho, hf, hfl⟩ := ProofFile.Honest.K12.live_field
    ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird w₁.laid w₂.laid⟩ hLo pre σ.block t i hi
    (R.start₃ P m₁ m₂) v₀ (w₁.cols ++ w₂.cols) ha₃ hy hlen hym
  have tk : ∀ (a b : List Fmt.RoundView) (j : ℕ), (a ++ b).take (a.length + j) = a ++ b.take j := by
    intro a b j
    induction a with
    | nil => simp
    | cons z zs ih =>
      have e : (z :: zs).length + j = (zs.length + j) + 1 := by
        simp only [List.length_cons]
        omega
      rw [e, List.cons_append, List.take_succ_cons, ih, List.cons_append]
  have ey : roundsOf y.laid = roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) ++
      roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length) := by
    rw [← roundsOf_append, List.take_append_drop]
  have hs : m.seen = roundsOf w₁.laid ++ (roundsOf w₂.laid ++
      (roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) ++
        roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length))) := by
    have k := hseen
    rw [← ly, ey] at k
    rw [k]
    simp only [List.append_assoc]
  have hlY : y.laid.length = (pre.flatMap (·.rounds)).length + i := by
    rw [walk_laid_length _ _ _ _ _ hy, start_laid ha₃, hlen]
    exact Nat.zero_add _
  have ny : (roundsOf (y.laid.take (pre.flatMap (·.rounds)).length)).length =
      (pre.flatMap (·.rounds)).length := by
    rw [roundsOf_length, List.length_take]
    omega
  have hfold : foldBlocks F.lastChainFirstTreeNumber pre v₀ (roundsOf ((w₃.laid).take
                    (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) := by
    have e : (w₃.laid.take ((pre.flatMap (·.rounds)).length + i)).take
        (pre.flatMap (·.rounds)).length = w₃.laid.take (pre.flatMap (·.rounds)).length := by
      rw [List.take_take]
      congr 1
      omega
    have k := hf
    rw [show y.laid = w₃.laid.take ((pre.flatMap (·.rounds)).length + i) from ly, e] at k
    exact k
  have hlenS : m.seen.length = (F.first.blocksInOrder.flatMap (·.rounds)).length +
      (F.shared.blocksInOrder.flatMap (·.rounds)).length + (pre.flatMap (·.rounds)).length + i := by
    rw [hs]
    simp only [List.length_append]
    rw [ny, n₁, n₂, roundsOf_length, List.length_drop, hlY]
    omega
  have hfill : fillCols (readsOf 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
      (treeThird w₁.laid w₂.laid (w₃.laid.take (pre.flatMap (·.rounds)).length))
      (pre.flatMap (·.rounds))
      ((w₃.laid.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
    have e : (w₃.laid.take ((pre.flatMap (·.rounds)).length + i)).take
        (pre.flatMap (·.rounds)).length = w₃.laid.take (pre.flatMap (·.rounds)).length := by
      rw [List.take_take]
      congr 1
      omega
    have k := hfl
    rw [show y.laid = w₃.laid.take ((pre.flatMap (·.rounds)).length + i) from ly, e] at k
    exact k
  refine ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlenS, ho, he₁, he₂, hst, hfold, hfill, ?_⟩
  intro W xOf w enter fr k hx hk hfr hop
  obtain ⟨j, rfl⟩ : ∃ j, k = (roundsOf w₁.laid).length + ((roundsOf w₂.laid).length +
      ((roundsOf (y.laid.take (pre.flatMap (·.rounds)).length)).length + j)) :=
    ⟨k - ((roundsOf w₁.laid).length + ((roundsOf w₂.laid).length +
      (roundsOf (y.laid.take (pre.flatMap (·.rounds)).length)).length)), by
        rw [n₁, n₂, ny]
        omega⟩
  have hfr' : fr.seen.rounds = roundsOf w₁.laid ++ (roundsOf w₂.laid ++
      (roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) ++
        (roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length)).take j)) := by
    rw [hfr, hs, tk, tk, tk]
  have hco : colsOpened w fr = w₁.cols ++ (w₂.cols ++ cols) := by
    show fr.seen.opened.getD [] = _
    rw [hop, ho, List.append_assoc]
    rfl
  have h₁ : foldBlocks 0 F.first.blocksInOrder ((fun w => F.start₁ (F.pub (xOf w))) w) fr.seen.rounds
      (colsOpened w fr) = .ok (e₁, roundsOf w₂.laid ++
        (roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) ++
          (roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length)).take j),
        w₂.cols ++ cols) := by
    show foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub (xOf w))) _ _ = _
    rw [hx, hfr', hco, ProofFile.Honest.foldBlocks_more 0 F.first.blocksInOrder _ _ _ _ _ n₁ c₁, f₁]
    rfl
  have h₂ : foldBlocks 0 F.shared.blocksInOrder ((fun w => F.start₂ (F.pub (xOf w))) w)
      (roundsOf w₂.laid ++ (roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) ++
        (roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length)).take j)) (w₂.cols ++ cols) =
      .ok (e₂, roundsOf (y.laid.take (pre.flatMap (·.rounds)).length) ++
        (roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length)).take j, cols) := by
    show foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub (xOf w))) _ _ = _
    rw [hx, ProofFile.Honest.foldBlocks_more 0 F.shared.blocksInOrder _ _ _ _ _ n₂ c₂, f₂]
    rfl
  have h₃ := ProofFile.Honest.K10.fold_more F.lastChainFirstTreeNumber pre v₀ _ cols (s, [], []) hf
    ((roundsOf (y.laid.drop (pre.flatMap (·.rounds)).length)).take j)
  have hs₃ : (fun w => F.start₃ (F.pub (xOf w))) w e₁ e₂ = .ok v₀ := by
    show F.start₃ (F.pub (xOf w)) e₁ e₂ = _
    rw [hx]
    exact hst
  exact doorLastTry_of_folds _ _ _ _ _ _ _ enter colsOpened w fr h₁ h₂ hs₃ h₃

theorem state_on_last_chain_with_columns {W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (enter : F.S₃ → Except String T12) (fall : T12) :
    ∃ (e₁ : F.S₁) (e₂ : F.S₂) (v₀ s : F.S₃) (cols : List OpenedColumn),
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧ F.start₃ (F.pub x) e₁ e₂ = .ok v₀ ∧
      foldBlocks F.lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      fillCols (readsOf 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
        (treeThird r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols ∧
      stateFromViewOnLastChain F pre enter fall x
        ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, u.number⟩).cut i) = (enter s).toOption.getD fall := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, more, rest, tr, -, -, -, -, he₁, he₂, hs₃, -, -, hfold, hfill⟩ :=
    called_at_second hpl hR σ u pre t i S hrun hc
  obtain ⟨m', -, -, -, -, -, hbf, -, -, -, hask⟩ := frame_at_second hpl hR hrun σ u pre t i _ S rfl hc
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, -, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hrun hR (steps_shaped s1 Q.blocks₁) (steps_shaped s2 Q.blocks₂)
    (steps_shaped s3 Q.blocks₃)
  refine ⟨e₁, e₂, v₀, s, cols, he₁, he₂, hs₃, hfold, hfill, ?_⟩
  have d₀ : (roundsOf r.run.played.1).map (·.drawn) = ρ.first := by
    rw [← laidAs_drawn l1]
    simp only [roundsOf, List.map_map]
    rfl
  have d₁ : (roundsOf r.run.played.2.1).map (·.drawn) = ρ.shared := by
    rw [← laidAs_drawn l2]
    simp only [roundsOf, List.map_map]
    rfl
  have d₂ := laidAs_drawn l3
  have hall : r.run.played.2.2.length = R.second.length := by
    have h1 := congrArg List.length d₂
    rw [List.length_map] at h1
    exact h1.trans l3.1
  have hfits := S.fits
  have hn : (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)).length =
      (pre.flatMap (·.rounds)).length + i := by
    rw [List.length_take, hall]
    omega
  -- the front, cut back by i
  have hf : (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
      ⟨σ.block.place, u.number⟩).cut i =
      (laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ)) := by
    rw [hbf, hask]
    show (⟨shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++ shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0 ++
      shownBy 2 (treeAsks F ρ 2) (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) 0,
      storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩ : Before).cut i =
      ⟨shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++ shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0 ++
        shownBy 2 (treeAsks F ρ 2) (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) 0,
        storedShown (P.storedWords w₀ rc) (storedAsks F ρ)⟩
    unfold Before.cut
    simp only
    have hC : (shownBy 2 (treeAsks F ρ 2)
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) 0).length =
        (pre.flatMap (·.rounds)).length + i := by
      rw [shownBy_length, hn]
    have hk : (shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++
        shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0 ++
        shownBy 2 (treeAsks F ρ 2) (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) 0).length - i =
        (shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++
          shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0).length + (pre.flatMap (·.rounds)).length := by
      rw [List.length_append, hC]
      omega
    rw [hk, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      ← shownBy_take, List.take_take]
    simp
  have Pc := pieces_front F ρ r.run.played.1 r.run.played.2.1
    (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)
    (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))
  obtain ⟨hok, f₀, f₁, -⟩ := runOk_of hrun
  obtain ⟨E₁, E₂, -⟩ := runC_ends hrun
  obtain ⟨v₁, v₂⟩ := views_rounds hrun
  rw [hf]
  -- the two earlier chains
  have hfirst : firstChainEnd F x ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) = some e₁ := by
    have c0 : columnsOfChain ((laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) 0 0 F.roundsDeclaredByBlocks.1 =
        some r.run.views.1.opened := by
      unfold columnsOfChain
      rw [Pc.1, d₀]
      have kk := colsOff_fill _ r.run.reads.1 _ f₀ fun q hq w hw =>
        early_words hrun (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) q
          (List.mem_append.2 (Or.inl hq)) w hw
      rw [hok.bare₀] at kk
      exact kk
    unfold firstChainEnd
    rw [c0, Pc.1]
    have hv : withSealingRound (roundsOf r.run.played.1) = (withEmptySealRound r.run.views.1).rounds := by
      show _ = r.run.views.1.rounds ++ _
      rw [v₁]
      rfl
    rw [hv]
    show (foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened).toOption.map (·.1) = _
    rw [← E₁.2.2, he₁]
  have hshared : sharedChainEnd F x ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) = some e₂ := by
    have c1 : columnsOfChain ((laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) 1 0 F.roundsDeclaredByBlocks.2.1 =
        some r.run.views.2.1.opened := by
      unfold columnsOfChain
      rw [Pc.2.1, d₁]
      have kk := colsOff_fill _ r.run.reads.2.1 _ f₁ fun q hq w hw =>
        early_words hrun (r.run.played.2.2.take (pre.flatMap (·.rounds)).length) q
          (List.mem_append.2 (Or.inr hq)) w hw
      rw [hok.bare₁] at kk
      exact kk
    unfold sharedChainEnd
    rw [c1, Pc.2.1, ← v₂]
    show (foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened).toOption.map (·.1) = _
    rw [← E₂.2.2, he₂]
  -- the last chain's blocks in front
  have hdecl : pre.flatMap (·.rounds) = F.roundsDeclaredByBlocks.2.2.take (pre.flatMap (·.rounds)).length := by
    show _ = (F.second.blocksInOrder.flatMap (·.rounds)).take _
    rw [S.cut, List.flatMap_append]
    simp
  have hdr : (r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn) =
      ρ.second.take (pre.flatMap (·.rounds)).length := by
    rw [List.map_take, d₂]
  have hc2 : columnsOfChain ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) 2 F.lastChainFirstTreeNumber (pre.flatMap (·.rounds)) =
      some cols := by
    unfold columnsOfChain
    rw [Pc.2.2]
    have hd : (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)).map (·.drawn) =
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn) := by
      simp only [roundsOf, List.map_map]
      rfl
    rw [hd, ← readsOf_bare 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
      (treeThird r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))]
    refine colsOff_fill _ _ cols hfill fun q hq w hw => ?_
    have hb : q.bare ∈ allBare F ρ := by
      have h2 : q.bare ∈ readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none)
          (pre.flatMap (·.rounds)) ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn)) := by
        rw [← readsOf_bare 2 F.lastChainFirstTreeNumber (P.storedWords w₀ rc)
          (treeThird r.run.played.1 r.run.played.2.1
            (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))]
        exact List.mem_map.2 ⟨q, hq, rfl⟩
      have h3 : q.bare ∈ readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.2 ρ.second :=
        reads_of_prefix 2 F.lastChainFirstTreeNumber _ _ (pre.flatMap (·.rounds)).length F.roundsDeclaredByBlocks.2.2 ρ.second q.bare
          (by rw [← hdecl, ← hdr]; exact h2)
      unfold allBare bareReads
      exact List.mem_append.2 (Or.inr h3)
    exact faith_one F ρ _ _ _ (P.storedWords w₀ rc) 2 F.lastChainFirstTreeNumber _ _ _
      (fun o pT h => third_tab _ _ _ o pT h) q hq hb w hw
  unfold stateFromViewOnLastChain doorFromViewOnLastChain
  rw [hfirst, hshared, hc2]
  dsimp only
  rw [hs₃, Pc.2.2]
  show ((foldBlocks F.lastChainFirstTreeNumber pre v₀ _ cols).bind fun r => enter r.1).toOption.getD fall = _
  rw [hfold]
  rfl

/-- The lending of a part does not see the guard. -/
theorem lendPart_guarded {V W X : Type} (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) :
    lendPart Bk rows look a p.needsField = lendPart Bk rows look a p := by
  unfold lendPart
  dsimp only [Part.needsField]
  congr 1
  cases (look a).snd.cut { f := 0, e := 0 } p.takes <;> rfl

/-- Nor does the lending of two parts. -/
theorem lend_guarded {V W X : Type} (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Place) (p q : Part V W X) :
    lendRow Bk rows look a [p.needsField, q.needsField] 0 = lendRow Bk rows look a [p, q] 0 := by
  simp only [lendRow]
  rw [lendPart_guarded, lendPart_guarded]
  rfl

/-- **The play of a proximity test's first part in the last chain, behind the guard**:
first_play_at_second (FirstPlayAtSecond.lean) where the half that the prover holds is the job's behind
needsField. The walk holds the guarded Steps; the field is some there (live_field), so they play as
the bare ones (play_guarded). A second text of that proof. -/
theorem first_play_guarded_at_second {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl))
    (S : StandsAt F.second.blocksInOrder R.second σ u pre t (firstLen J.p.nums.stages))
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some
      ((proverSideOfProximityTest J : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m₀ m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (y : List Played × ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      lendRow Bk (Bk.rowsOf 2) (k.look 2) σ.block.place
        [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J] 0 = .ok c ∧
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      play ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
          ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1)
        ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) [] m₀ =
        .ok y ∧
      y.2 = m ∧ m₀.st.input = R.own ∧
      m.seen = m₀.seen ++ roundsOf y.1 := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl1, ho⟩ :=
    block_steps_at_second hR pre σ.block t S.cut (proverSideOfProximityTest J).needsField hg
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨ha, hN, -, -⟩ := stretch_back S.str S.pos S.fits
  obtain ⟨-, -, lS⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  have hρ : ρ.second.length = R.second.length := lS.1
  have hfits := S.fits
  have hle := S.le
  -- the stand is a walk's own state
  obtain ⟨m₁, m₂, m, a₁, z₁, a₂, z₂, a₃, Yw, -, -, -, -, -, -, -, -, ha₃, hY, -, hYm, hm⟩ :=
    played_at_second hpl hR hrun σ u pre t _ _ S rfl hc
  obtain ⟨m₀', v₀, -, ev⟩ := start_live ha₃ (walk_live _ _ _ a₃ Yw m hY hYm)
  rw [ev, S.cut] at ha₃
  -- the first part's Steps stand behind pre's
  have hJl : firstLen J.p.nums.stages ≤ J.laid.length := by
    rw [← hlaid, List.length_zip, ho, Nat.min_self]
    omega
  have hA : (((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name ⟨σ.block.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1).map Step.guarded).length =
      firstLen J.p.nums.stages := by
    rw [List.length_map, ProofFile.Honest.K12.Light.steps_len, ProofFile.Honest.K12.Light.first_moves_len,
      List.length_take, Nat.min_eq_left hJl, Nat.min_self]
  have hsteps : R.second = l₁ ++ (((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
      ⟨σ.block.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1).map
        Step.guarded ++
      (rowSteps σ.block.name σ.block.place (some R.own)
        [(restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField] 1
        (J.laid.drop (firstLen J.p.nums.stages)) c.2 ++ l₂)) := by
    rw [hsh]
    have e : (proverSideOfProximityTest J : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField.steps σ.block
        (Face.own.sees R.own) c =
        (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField.steps σ.block.name
            ⟨σ.block.place, 0⟩
          ((σ.block.rounds.zip σ.block.oracles).take
            (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField.moves.length)
                (some R.own) c.1 ++
        rowSteps σ.block.name σ.block.place (some R.own)
          [(restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField] 1
          ((σ.block.rounds.zip σ.block.oracles).drop
            (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField.moves.length) c.2 := rfl
    rw [e, hlaid, needsField_length, ProofFile.Honest.K12.Light.first_moves_len, steps_needsField,
      List.append_assoc]
  have htakeS : R.second.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) = l₁ ++
      ((firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).steps σ.block.name
          ⟨σ.block.place, 0⟩
        (J.laid.take (firstLen J.p.nums.stages)) (some R.own) c.1).map Step.guarded := by
    rw [hsteps, ← List.append_assoc, List.take_left']
    rw [List.length_append, hl1, hA]
  have htakeD : ρ.second.take ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages) =
      ρ.second.take (pre.flatMap (·.rounds)).length ++
        (ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages) :=
    List.take_add
  rw [htakeS, htakeD] at hY
  have hLo : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (P.storedWords w₀ rc) (fun ch k => if ch == 0 then ((tablesOf z₁.laid)[k]?).bind id
        else if ch == 1 then ((tablesOf z₂.laid)[k]?).bind id else none) ps).tree :=
    fun ps => ((envOf_tree (P.storedWords w₀ rc) z₁.laid z₂.laid ps).2).symm
  obtain ⟨zb, mb, ps, w1, hmb, hp, -⟩ := play_in_block
    ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ hLo pre
    σ.block t (R.start₃ P m₁ m₂) v₀ ha₃ hl1
    (by rw [List.length_take, hl1, Nat.min_eq_left (by omega)])
    (by
      rw [hA]
      have := S.pos
      omega)
    (fun s hs => steps_part0 _ _ s3 s (by
      rw [hsteps]
      exact List.mem_append_right _ (List.mem_append_left _ hs)))
    hY hYm
  obtain ⟨i0, -, -⟩ := walk_mid ha₃ w1 hmb
  have hblock : 0 < σ.block.rounds.length := by
    have := S.pos
    have := S.le
    omega
  obtain ⟨-, cols₀, -, -, -, -, hop, -, -⟩ := ProofFile.Honest.K12.live_field
    ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ hLo pre σ.block t 0 hblock
    (R.start₃ P m₁ m₂) v₀ _ ha₃ w1 (by rw [hl1, Nat.add_zero]) hmb
  rw [play_guarded _ _ _ _ _ hop] at hp
  have hl' : lendRow Bk (Bk.rowsOf 2) (k.look 2) σ.block.place
      [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J] 0 = .ok c :=
    (lend_guarded Bk _ _ σ.block.place _ _).symm.trans hl
  refine ⟨c, mb, m, (ps, m), hl', hm, hp, rfl, ?_, (play_mid _ _ _ _ _ hp).2.2⟩
  rw [i0]
  rfl

/-- **The five clauses at a run in the last chain, behind the guard**: five_at_second
(FiveAtSecond.lean) there. A second text of that proof. -/
theorem five_at_second_guarded {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) (f : Addr × ℕ) (hfr : J.fresh = some f)
    (Js : SimJob Pb)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb) (pre t : List (Block F.S₃
        F.Cl))
    (S : StandsAt F.second.blocksInOrder R.second σ (restMember J Js).guarded pre t
      (firstLen J.p.nums.stages))
    (hg : (P.second.find? fun g => g.place == σ.block.place) = some
      ((proverSideOfProximityTest J : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : tiesB Bk J.p.place J.members.length = true)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest D
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Local W₀ Rc Xi Tr) (fr : Front Y) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩ =
        .ok (some m) ∧
      carriedAt Bk k 2 ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩
        (restMember (V := Local W₀ Rc Xi Tr) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      firstLen J.p.nums.stages ≤ m.st.heard.length ∧
      firstLen J.p.nums.stages ≤ m.seen.length ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J
          Js).number⟩)
        (firstLen J.p.nums.stages)).map (·.drawn) =
        m.st.lately (firstLen J.p.nums.stages) ∧
      (lastSeen (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J
          Js).number⟩)
        (firstLen J.p.nums.stages)).tail =
        aFold (coinsOf J.p.nums.stages (carriedCoins J (stretches _ c.2.1.2.2)).hide fun _ => 0) 0
          J.s₀ 1
          (rowsAt J (stretches _ c.2.1.2.2) m)
          (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m) := by
  obtain ⟨c, m₀, m, y, hl, hm, hplay, hy, hin0, -⟩ :=
    first_play_guarded_at_second hpl J hR σ _ pre t S hg hlaid hrun hc
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
  obtain ⟨m', hm', hseen⟩ := mid_second hrun hR o₁ o₂ o₃ hp ha hseg hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  have hbef := before_second hrun hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0) (treeAsks F ρ 1)
    (treeAsks F ρ 2) (shown_is (runOk_of hrun).1 0 (by decide))
    (shown_is (runOk_of hrun).1 1 (by decide)) (shown_is (runOk_of hrun).1 2 (by decide)) st
  have hfront : m'.seen = (r.run.beforeAt st
      ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).number⟩).seen := by
    change m'.seen = (r.run.beforeAt st
      ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).guarded.number⟩).seen
    rw [hbef, seen_by, hseen]
    unfold roundsOff
    rw [List.map_append, List.map_append]
    have e0 := roundsOff_by 0 (treeAsks F ρ 0) r.run.played.1 0
    have e1 := roundsOff_by 1 (treeAsks F ρ 1) r.run.played.2.1 0
    have e2 := roundsOff_by 2 (treeAsks F ρ 2) (r.run.played.2.2.take
      (R.second.takeWhile fun s =>
        s.addr != ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J Js).guarded.number⟩).length) 0
    unfold roundsOff at e0 e1 e2
    rw [e0, e1, e2]
  have hinm : m'.st.input = R.own := by
    rw [← hy, (play_mid _ _ _ _ y hplay).1]
    exact hin0
  refine ⟨c, m', hm, carried_of_row_second k σ.block.place _ _ c hl, hinm, ?_⟩
  rw [← hplace] at hl
  obtain ⟨y', hplay', -, hon⟩ := five_of_lent (V := Local W₀ Rc Xi Tr) J f hfr Bk (Bk.rowsOf 2)
    (k.look 2) c hl hT σ.block.name ⟨σ.block.place, 0⟩ (some R.own) s next rest m₀ D _ T hk
    (hrows _ _) hfit (r.run.beforeAt st ⟨σ.block.place, (restMember (V := Local W₀ Rc Xi Tr) J
        Js).number⟩)
  obtain rfl : y' = y := Except.ok.inj (hplay'.symm.trans hplay)
  rw [hy] at hon
  exact hon hfront

end

/-- **The door at the request's own test, at a called part.** J: a job whose state on entry is doorW
at the description's own way in. u: the member in front of which the first n rounds of the block
stand, n the first part's rounds. The stand that midAtW returns, and at it the job's state on entry at
the part's own front is the simulators' state at the run's front cut back by n. -/
theorem door_at_own_test {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain P5J.TS ProofFile.Cl} {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hpl : (P5J.F0T o Zp Np cF).planOk = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J.rec₀ = doorW (P5J.F0T o Zp Np cF) (·.x) enterOwn placeW idleT12)
    (σ : Side (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).second.blocksInOrder R.second σ u pre t (firstLen J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = placeW) :
    ∃ m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y,
      midAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      J.rec₀ m.st.input (restFront J m) = stateAtOwnTest o Zp Np cF x
        ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, u.number⟩).cut (firstLen J.p.nums.stages)) := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlen, -, he₁, he₂, hst, hfold, hfill, hd⟩ :=
    door_last_with_columns hpl hR σ u pre t _ S hrun hc
  obtain ⟨e₁', e₂', v₀', s', cols', he₁', he₂', hst', hfold', hfill', hval⟩ :=
    state_on_last_chain_with_columns hpl hR hrun σ u pre t _ S hc enterOwn idleT12
  obtain rfl : e₁' = e₁ := Option.some.inj (he₁'.symm.trans he₁)
  obtain rfl : e₂' = e₂ := Option.some.inj (he₂'.symm.trans he₂)
  obtain rfl : v₀' = v₀ := Except.ok.inj (hst'.symm.trans hst)
  obtain rfl : cols' = cols := Except.ok.inj (hfill'.symm.trans hfill)
  have hs : s' = s := (Prod.mk.inj (Except.ok.inj (hfold'.symm.trans hfold))).1
  subst hs
  have hn := (places_nodup (((P5J.F0T o Zp Np cF).planOk_ok).1 hpl).places).2.2
  have hcut : (P5J.F0T o Zp Np cF).second.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : (P5J.F0T o Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW) = pre := by
    rw [← ha, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  refine ⟨m, hm, ?_⟩
  have hx : (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input = x := by rw [hin]
  have hk : ((P5J.F0T o Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
      ((P5J.F0T o Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
      (pre.flatMap (·.rounds)).length ≤ m.seen.length - firstLen J.p.nums.stages := by
    omega
  have hdoor := hd (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input enterOwn (restFront J m)
    (m.seen.length - firstLen J.p.nums.stages) hx hk rfl rfl
  unfold stateAtOwnTest
  rw [hJ, hpre, hval]
  unfold doorW doorLast
  rw [hpre, hdoor]

/-- A stretch of the last chain's challenges that passes Draws.due has the declared form. -/
theorem draws_fit_last_chain {Xi : Type} {F : FileDescription Xi} {ρ : Draws} (hρ : ρ.due F = true)
    (pre t : List (Block F.S₃ F.Cl)) (b : Block F.S₃ F.Cl)
    (hcut : F.second.blocksInOrder = pre ++ b :: t) (n : ℕ) (hn : n ≤ b.rounds.length) :
    drawsFit (b.rounds.take n) ((ρ.second.drop (pre.flatMap (·.rounds)).length).take n) = true := by
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.second.blocksInOrder.flatMap (·.rounds)) ρ.second = true := hρ.1.2
  rw [hcut, List.flatMap_append, List.flatMap_cons] at h2
  have h3 := (drawsFit_cut (pre.flatMap (·.rounds)).length _ _ h2).2
  rw [List.drop_left] at h3
  have h4 := (drawsFit_cut b.rounds.length _ _ h3).1
  rw [List.take_left] at h4
  have h5 := (drawsFit_cut n _ _ h4).1
  rw [List.take_take, Nat.min_eq_left hn] at h5
  exact h5

section Guard
variable {S Cl V W X Pb : Type}

theorem foldl_guarded_row (row : List (Part V W X × Sim Pb)) : ∀ n : ℕ,
    ((guardRow row).map (·.1)).foldl (fun n p => n + p.moves.length) n =
      (row.map (·.1)).foldl (fun n p => n + p.moves.length) n := by
  induction row with
  | nil => intro n; rfl
  | cons x l ih =>
    intro n
    show ((guardRow l).map (·.1)).foldl (fun n p => n + p.moves.length)
        (n + (x.1.needsField).moves.length) =
      (l.map (·.1)).foldl (fun n p => n + p.moves.length) (n + x.1.moves.length)
    rw [needsField_length, ih]

/-- The guard changes nothing of Side.fits. -/
theorem fits_guarded_row (b : Block S Cl) (row : List (Part V W X × Sim Pb))
    (f : S → List Fmt.Drawn → Option String) :
    (⟨b, guardRow row, f⟩ : Side S Cl V W X Pb).fits = (⟨b, row, f⟩ : Side S Cl V W X Pb).fits := by
  have e1 : (guardRow row).zipIdx.all (fun s => s.1.2.addr == (⟨b.place, s.2⟩ : Addr)) =
      row.zipIdx.all (fun s => s.1.2.addr == (⟨b.place, s.2⟩ : Addr)) := by
    unfold guardRow
    rw [List.zipIdx_map, List.all_map]
    rfl
  have e2 : (⟨b.place, (guardRow row).map (·.1)⟩ : Placed V W X).rounds =
      (⟨b.place, row.map (·.1)⟩ : Placed V W X).rounds := foldl_guarded_row row 0
  unfold Side.fits Side.half
  simp only [e1, e2]

end Guard

section AtHead
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T o Zp Np cF

theorem rest_rounds_at_own_test : restLen piWFull.nums.stages ≠ 0 := by decide +kernel

/-- **The five clauses at a run, at the request's own test**, at the side that seats the job's two
parts behind the guard. hg: on the filling. hT: on the book. hrows: the rows read the stretches of the
job's members alone. -/
theorem five_at_own_test (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {W₀ Rc Ky Tr X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC 𝔽}
    (hρ : ρ.due 𝔽 = true) (hR : ready 𝔽 Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : J.p = (fourOf Np).W) (f : Addr × ℕ) (hfr : J.fresh = some f)
    (hrows : ∀ (s : Fmt.M1.Stage) (w : Local W₀ Rc ProofFile.Inst Tr) (fr : Front Y) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).W) (ho : Js.own = false)
    (fs : List (Fall (𝔽).S₃))
    (σ : Side (𝔽).S₃ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : Side.seated (𝔽).second.blocksInOrder J.p.place (guardRow (testPairs J Js)) fs = some σ)
    (hg : (P.second.find? fun g => g.place == σ.block.place) =
      some ((proverSideOfProximityTest J : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).needsField))
    (hT : tiesB Bk J.p.place J.members.length = true)
    (hrun : runC 𝔽 Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (c : RowCoins [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y), restPart J])
      (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y),
      midAtW 𝔽 Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 2 ⟨σ.block.place, 1⟩
        (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      FiveAt J (stretches _ c.2.1.2.2) m (r.run.beforeAt st ⟨σ.block.place, 1⟩) := by
  have hfrN : J.fresh.isNone = false := by rw [hfr]; rfl
  have Fc := facts_head_W h
  rw [← hp] at Fc
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ
  have hbare : testSide (V := Local W₀ Rc ProofFile.Inst Tr) (𝔽).second.blocksInOrder J Js fs =
      some (⟨b, testPairs J Js, fallOf fs J.p.place⟩ :
        Side (𝔽).S₃ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst) := by
    unfold testSide Side.seated
    show Option.map _ ((𝔽).second.blocksInOrder.find? fun b => b.place == J.p.place) = _
    rw [hb]
    rfl
  obtain ⟨hfit, hmem, -⟩ :=
    (first_any_head_W (V := Local W₀ Rc ProofFile.Inst Tr) h J Js hp hfrN hs ho).2.2 fs _ hbare
  have hrow : σ.row = guardRow (testPairs J Js) := by rw [← e]
  have hblk : σ.block ∈ (𝔽).second.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hb
  have hfitg : σ.fits = true := by
    rw [← e]
    show (⟨b, guardRow _, _⟩ : Side (𝔽).S₃ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst).fits = true
    rw [fits_guarded_row]
    exact hfit
  have hmemg : (restMember J Js).guarded ∈ σ.members := by
    have e2 : σ.members = [(firstMember J Js).guarded, (restMember J Js).guarded] := by
      rw [← e]
      show membersOf (guardRow _) 0 _ = _
      rw [membersOf_guardRow]
      exact congrArg (List.map Member.guarded) hmem
    rw [e2]
    simp
  obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
    have hform := Fc.form
    unfold formPubB at hform
    cases hs' : J.p.nums.stages with
    | nil => rw [hs'] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs'] at hform; cases hform
      | cons b' r' => exact ⟨a, b', r', rfl⟩
  have FP := formPub_of_B J.p s next rest hst Fc.form
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have l2 : (restPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).moves.length =
      restLen J.p.nums.stages := by
    rw [rest_moves J s next rest hst]
    exact (List.length_map _).trans List.length_range
  have hpos : (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).guarded.part.moves.length ≠ 0 := by
    show (restPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).needsField.moves.length ≠ 0
    rw [needsField_length, l2, hp, (reads_head_W h).1]
    exact rest_rounds_at_own_test
  obtain ⟨pre, t, S'⟩ := stands_member_last h.laid.planOk hR σ hblk hfitg
    (restMember J Js).guarded hmemg hpos (proverSideOfProximityTest J).needsField hg (by rw [hrow]; rfl)
  have eN : ((σ.row.take (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).guarded.number).map
      (·.1.moves.length)).sum = firstLen J.p.nums.stages := by
    rw [hrow]
    show (firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).needsField.moves.length + 0 = _
    rw [Nat.add_zero, needsField_length, ProofFile.Honest.K12.Light.first_moves_len]
  rw [eN] at S'
  obtain ⟨b', hf, hpl', hr, hor⟩ := find_own h
  have hb' : b = b' := by
    rw [hp] at hb
    exact Option.some.inj (hb.symm.trans hf)
  have eb : σ.block = b' := by rw [← hb', ← e]
  have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
    rw [eb, hr, hor]
    show _ = H2K.JointK.laidOf J.p
    rw [hp]
    exact zip_laid _ (facts_head_W h).plan
  have hsh : σ.block.shaped = true := planOk_shaped_second h.laid.planOk σ.block hblk
  have hol := shaped_len σ.block hsh
  have hlenb : σ.block.rounds.length = (H2K.JointK.laidOf J.p).length := by
    show _ = J.laid.length
    rw [← hzip, List.length_zip, hol, Nat.min_self]
  have hcut : (𝔽).second.blocksInOrder = pre ++ σ.block :: t := S'.cut
  have g0 := draws_fit_last_chain hρ pre t σ.block hcut (firstLen J.p.nums.stages)
    (by rw [hlenb]; exact Fc.enough)
  have e1 : ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) =
      σ.block.rounds.take (firstLen J.p.nums.stages) := by
    have hz : H2K.JointK.laidOf J.p = σ.block.rounds.zip σ.block.oracles := hzip.symm
    rw [List.map_take, hz, List.map_fst_zip (by rw [hol])]
  have hfitd : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    rw [e1]
    exact g0
  have hlen : ((ρ.second.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    have hh := ProofFile.Honest.drawsFit_length _ _ hfitd
    rw [hh, List.length_map, List.length_take]
    exact Nat.min_eq_left Fc.enough
  have T : FirstTies J s next rest (byNo ((ρ.second.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨hst, Fc.enough, FP.sorts, by rw [tablesFitB_eq, hfrN]; exact Fc.tab, hlen,
      fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩
  obtain ⟨c, m, hm, hca, hin, le, leS, hF, hH, hFold⟩ := five_at_second_guarded (F := 𝔽)
    h.laid.planOk J f hfr Js hR σ pre t S' hg hzip hT s next rest _ T hk
    (fun w fr mem mem' hh => hrows s w fr mem mem' hh) hfitd hrun hc st
  exact ⟨c, m, hm, hca, hin, ⟨le, leS, hF, hH, hFold⟩⟩

end AtHead

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.door_last_with_columns
#print axioms ProofFile.Honest.K12.Sim2.state_on_last_chain_with_columns
#print axioms ProofFile.Honest.K12.Sim2.first_play_guarded_at_second
#print axioms ProofFile.Honest.K12.Sim2.five_at_second_guarded
#print axioms ProofFile.Honest.K12.Sim2.door_at_own_test
#print axioms ProofFile.Honest.K12.Sim2.draws_fit_last_chain
#print axioms ProofFile.Honest.K12.Sim2.fits_guarded_row
#print axioms ProofFile.Honest.K12.Sim2.five_at_own_test
