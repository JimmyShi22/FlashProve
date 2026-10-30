-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorLastAtRun.lean: a conditional: nothing here shows that ready
or runC returns or that the part is called. AT A CALLED PART OF THE LAST CHAIN, AT A RUN OF THE
FRAME's WALKING PROVER, THE DOOR's TEXT (`doorLastTry`, DoorLast.lean) IS THE WAY IN AT THE STATE
THAT THE DESCRIPTION's OWN FOLDS REACH: the twin of fold_at_called (DoorOpened.lean) at the last
chain.

  `enterOwn_returns`, `atHand_of_try`   the way in returns at every state; so the test says yes
  `door_own_at_called`   AT THE LIBRARY's DESCRIPTION AND ITS OWN WAY IN: `atHandLast` says yes at
      every such front: the door's default is not taken
  `door_last_at_called`   the law: the stand, its input, how many rounds it has seen, its field;
      both earlier ends, the start, the fold over the blocks in front; and behind these the clause
      on the text:
      at every front whose rounds are the stand's cut at k, k at least the three chains' count in
      front of the block, and whose field is the stand's.

By what. called_at_second (CalledAtSecond.lean); played_at_second (Sim/PlayedAtSecond.lean);
live_field (LiveField.lean) at the last chain, with the front z₁.cols ++ z₂.cols; the frame's
runC_parts, runC_ends, fold_some, seal_back, foldBlocks_more; fold_more (K10/RoundsStretch.lean);
doorLastTry_of_folds (DoorLast.lean).

What may be said here on hiding, and no more
(a rule of use for whoever builds on this file;
no theorem):
«The state on entry reads the instance's public part, the rounds shown, and ALL columns opened in
front of this test, in the order of reading: the first chain's, the shared chain's, the last
chain's own. They are computed from the witness, the index, the stored tables' pads and encoding
randomness, AND THE RUN's COINS. Never a word on a simulator at this place without «given the
instance's public part, the rounds shown and all columns opened in front, in all three chains».
But for the stored tables' columns no one can hand a simulator these from outside: the simulators
of EVERY part in front must have made them: this test stands last, and its «given» is the whole
view in front. At a called part of the walk the field begins with the two earlier chains' views'
own columns (door_last_at_called); that what follows them are the last chain's view's is not
typed, and that each tree's budget counts them is typed by nobody.»

Limits.
- Of the walk (runC), not of play. The fronts are those that a move lays in front of a part's
  rounds (Parts.lean; restFront, Sim/Row.lean); that a given move hands one is the caller's; later
  moves of a part: not said.
- It is stated at `pre`: that S.cut's pre is `F.second.blocksInOrder.takeWhile` at the test's place, as
  `doorW` has it, is the caller's.
- `door_own_at_called` speaks of the door at `enterOwn`; in `jobRealW` `enter` is a letter, so it
  speaks of `halfW` only where that letter is laid so.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorLast
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.ProofFile.Honest.K12.CalledAtSecond
import Johnson.Desc.ProofFile.Honest.K12.LiveField
import Johnson.Desc.ProofFile.Honest.K10.RoundsStretch
import Johnson.Desc.ProofFile.Honest.Law.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks withEmptySealRound)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest

/-- The way in at the request's own test returns at every state. -/
theorem enterOwn_returns (s : VerifiableInference.Desc.Third.S₃) :
    ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn s = .ok t := ⟨_, rfl⟩

/-- **At hand**: where the text is the way in at s and the way in returns, the test says yes. -/
theorem atHand_of_try {S₁ S₂ S₃ C₁ C₂ C₃ W X : Type} (b₁ : List (Block S₁ C₁))
    (b₂ : List (Block S₂ C₂)) (pre : List (Block S₃ C₃)) (ft : ℕ) (s₁ : W → S₁) (s₂ : W → S₂)
    (st₃ : W → S₁ → S₂ → Except String S₃) (enter : S₃ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) {s : S₃}
    (h : doorLastTry b₁ b₂ pre ft s₁ s₂ st₃ enter cols w fr = enter s)
    (he : ∃ t, enter s = .ok t) :
    atHandLast b₁ b₂ pre ft s₁ s₂ st₃ enter cols w fr = true := by
  obtain ⟨t, ht⟩ := he
  unfold atHandLast
  rw [h, ht]
  rfl

/-- **At a called part of the last chain, at a run of the frame's walking prover, the door's text is
the way in at the fold's state.** Public: hpl. On the filling and the book: hR, S. On the run: hrun,
hc. midAtW returns a stand m, with the request's own input; m has seen as many rounds as the two
earlier chains' and those in front of the part, and i more; its field holds the two earlier views'
columns and then cols; both earlier ends are there, the last chain's start returns v₀ at them, and
the description's own fold over the blocks in front returns s at the run's rounds and at cols.
Behind the stand: xOf reads the request's instance off w; k: how many of the stand's rounds the
front shows, at least those of the three chains in front of the block; the field is the
stand's. -/
theorem door_last_at_called {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
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
  obtain ⟨s, cols, -, -, -, -, ho, hf, -⟩ := ProofFile.Honest.K12.live_field
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
  refine ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlenS, ho, he₁, he₂, hst, hfold, ?_⟩
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

/-- **At the library's description and its own way in, at a called part of the last chain of a
run, the door is at hand** at every front of that form: its default is not taken there. That a
move lays such a front is the caller's. -/
theorem door_own_at_called {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hpl : (P5J.F0T o Zp Np cF).planOk = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x c = .ok R)
    (σ : Side (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).second.blocksInOrder R.second σ u pre t i)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x c ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (tr : Tr),
      midAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      m.seen.length = ((P5J.F0T o Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
        ((P5J.F0T o Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
        (pre.flatMap (·.rounds)).length + i ∧
      ∀ {W : Type} (xOf : W → ProofFile.Inst) (w : W) (fr : Front Y) (k : ℕ), xOf w = x →
        ((P5J.F0T o Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
          ((P5J.F0T o Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
          (pre.flatMap (·.rounds)).length ≤ k →
        fr.seen.rounds = m.seen.take k → fr.seen.opened = m.opened →
          atHandLast (P5J.F0T o Zp Np cF).first.blocksInOrder (P5J.F0T o Zp Np cF).shared.blocksInOrder pre
            (P5J.F0T o Zp Np cF).lastChainFirstTreeNumber
            (fun w => (P5J.F0T o Zp Np cF).start₁ ((P5J.F0T o Zp Np cF).pub (xOf w)))
            (fun w => (P5J.F0T o Zp Np cF).start₂ ((P5J.F0T o Zp Np cF).pub (xOf w)))
            (fun w => (P5J.F0T o Zp Np cF).start₃ ((P5J.F0T o Zp Np cF).pub (xOf w)))
            VerifiableInference.Desc.K12.Seat.enterOwn colsOpened w fr = true := by
  obtain ⟨m, -, -, -, s, -, tr, hm, hin, hl, -, -, -, -, -, hd⟩ :=
    door_last_at_called hpl hR σ u pre t i S hrun hc
  refine ⟨m, tr, hm, hin, hl, fun xOf w fr k hx hk hfr hop => ?_⟩
  exact atHand_of_try _ _ _ _ _ _ _ _ _ w fr
    (hd xOf w VerifiableInference.Desc.K12.Seat.enterOwn fr k hx hk hfr hop)
    (enterOwn_returns s)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.enterOwn_returns
#print axioms ProofFile.Honest.K12.Light.atHand_of_try
#print axioms ProofFile.Honest.K12.Light.door_last_at_called
#print axioms ProofFile.Honest.K12.Light.door_own_at_called
