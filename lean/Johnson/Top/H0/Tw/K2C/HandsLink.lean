-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HandsLink.lean: code switching (the kind K2): AT A LINK, BEHIND AN ACCEPT OF
THE SWITCH's DECISION, THREE OF THE TABLE OF JOINTS' FOUR FIXED TESTS ON THE VERIFIER's STATE
ACCEPT: rowsHeld · membersHeld · bookAt. NO BLOCK IMPORTS THIS FILE. s, t': the verifier's state
in front of the decision and behind it. x: the front that the switch takes off s. W: the frame at
x. lay: the program's layout of what the sending announces.
  range_shift · gain_numbers   the numbers that the new group gains are n0, n0 + 1, … (1 + K + the
                               link's own of moment 0)
  LinkDebts N m pIn pOut s t x W lay   WHAT IS OWED ON THE NUMBERS N, IN ONE STRUCTURE, six
                                       fields: keptPos (each kept shape of the target has a main
                                       row) · carried | position (N.rowsAt m at the two classes) ·
                                       sent (the new members' seats are, as a set, N.sent m 0) ·
                                       trees | msgs (N.treesAt | N.msgsAt grow by the layout's
                                       trees | the sending's notices). t: the number of the
                                       positions drawn.
  yes_link_grp      an accept at a link: the number of groups in front is the list of rounds' own
                    number p.grp (the switch's guard on the group that it has opened)
  k2_step_two       an accept of the kind's step: two rounds; the second draws p.positions
                    positions; the decision accepts at these rounds, shown without the sealed
                    digest
  link_three        p.stands = .link · an accept at s · N.groupAt m = p.grp · bookAt in front ·
                    the closed facts on the open set behind (the switch's three classes of rows
                    alone; of segment m's pins «pin m 0» alone) · LinkDebts at the front: the
                    three tests accept at t'
LIMITS. LinkDebts is met by nobody here: each field is a fact on the list of rounds against the
state in front. The fourth test (shapeAt) and whatever else the promise asks: not here. No
soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HeldBehind
import Johnson.Top.H0.Tw.K2C.RowsClasses
import Johnson.Top.H0.Tw.K2C.GroupsAtYes
import Johnson.Top.H0.Tw.K2C.RunStays
import Johnson.Top.H0.Tw.K2C.StillKeeps
import Johnson.Top.H0.StepLaws.RoundsFit
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open _root_.Tw.K2 (sendByL8 firstFront switchNotices)

theorem range_shift (a b c : Nat) : (List.range (a + b)).map (· + c) =
    (List.range a).map (· + c) ++ (List.range b).map (· + (c + a)) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show a + i + c = i + (c + a)
  omega

theorem gain_numbers (x : _root_.Tw.K2.Front) : (switchGain x ++ ownGain x).map (·.1) =
    (List.range (1 + x.T.kept.size + x.own.length)).map (· + x.st.oracles.size) := by
  have e1 : (switchGain x).map (·.1) = (List.range (1 + x.T.kept.size)).map
      (· + x.st.oracles.size) := by
    rw [range_shift]
    unfold switchGain
    rw [List.map_cons, List.map_map]
    have : ((fun p : Nat × Bool => p.1) ∘ fun p : Nat × KeptTarget => (p.1, p.2.keptAgain)) =
        Prod.fst := rfl
    rw [this, List.map_fst_zip (by simp)]
    simp
  have e2 : (ownGain x).map (·.1) = (List.range x.own.length).map
      (· + (x.st.oracles.size + (1 + x.T.kept.size))) := by
    unfold ownGain
    rw [List.map_map]
    have : ((fun p : Nat × Bool => p.1) ∘
        fun y : Params.ReqMessage × Nat => (y.2, decide (0 < y.1.life))) = Prod.snd := rfl
    rw [this, List.map_snd_zip (by simp)]
  rw [List.map_append, e1, e2, range_shift (1 + x.T.kept.size)]

/-- **What is owed on the numbers at a link's switch.** -/
structure LinkDebts (N : Numbers) (m : Nat) (pIn pOut : Option Place) (s : S) (t : Nat)
    (x : _root_.Tw.K2.Front) (W : SwitchFrame) (lay : TreeLay) : Prop where
  keptPos : KeptPos x.T
  carried : N.rowsAt m .carried = (0, 1 + keptSamples x W)
  position : N.rowsAt m .position =
    (1 + keptSamples x W, t * (1 + targetRows x.T + 2))
  sent : sameMembers ((List.range (1 + x.T.kept.size + x.own.length)).map fun i =>
    (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true
  trees : N.treesAt pOut = N.treesAt pIn + lay.shapes.size
  msgs : N.msgsAt pOut = N.msgsAt pIn + (switchNotices x.T x.others).size

theorem yes_link_grp {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    s.st.groups.size = p.grp := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  rw [← k.hGrp, bA.frame]
  exact (firstFront_st k.hFront).2.symm

theorem k2_step_two {p : P2} {ft : Nat} {t t' : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn} {n : Nat}
    (h : (codeSwitchKind p : VerifiableInference.Desc.Block S Unit).step ft t rs cols = .ok (t', n)) :
    ∃ r₁ r₂ gs, r₂.drawn.poss.length = p.positions ∧
      decideWith sendByL8 p t [r₁, r₂] gs = .ok t' := by
  obtain ⟨hfit, _, _, hd⟩ := (VerifiableInference.Desc.Sound.step_ok_iff ft _ t t' rs cols n).1 h
  have hF := (VerifiableInference.Desc.roundsFit_iff _ _).1 hfit
  have hF' : List.Forall₂ VerifiableInference.Desc.RoundFits (rounds p) rs := hF
  unfold rounds at hF'
  obtain ⟨r₁, l₁, _, h2, rfl⟩ := List.forall₂_cons_left_iff.1 hF'
  obtain ⟨r₂, l₂, f2, h3, rfl⟩ := List.forall₂_cons_left_iff.1 h2
  obtain rfl := List.forall₂_nil_left_iff.1 h3
  exact ⟨_, _, _, f2.count, hd⟩

theorem link_three {p : P2} {s t' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok t') (N : Numbers)
    (m : Nat) (pIn pOut : Option Place) (O' : List Item)
    (hO : O'.filter Item.isRow = switchRowsOpen m) (hP0 : O'.contains (.pin m 0) = true)
    (hP1 : O'.contains (.pin m 1) = false) (hP2 : O'.contains (.pin m 2) = false)
    (hgrp : N.groupAt m = p.grp) (hb : bookAt N pIn s = true)
    (D : ∀ x W lay, firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N m pIn pOut s r₂.drawn.poss.length x W lay) :
    rowsHeld N O' t' = true ∧ membersHeld N O' t' = true ∧ bookAt N pOut t' = true := by
  obtain ⟨x, hx, hn0, hgr, _, _, Gm, hGm, mM, _⟩ := yes_link_groups hp h
  have hfx : frontAt p s = some x := by
    unfold frontAt
    rw [hp]
    simp only
    rw [hx]
    rfl
  obtain ⟨x1, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs t' h
  obtain rfl : x = x1 := Option.some.inj (hfx.symm.trans A.front)
  obtain ⟨x2, lay, hF, hlay, _, St⟩ := yes_seated h
  obtain rfl : x = x2 := by
    rcases hF with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact Except.ok.inj (hx.symm.trans e)
    · rw [hp] at e; cases e
    · rw [hp] at e; cases e
  obtain ⟨x3, hF3, _, _, zO, _⟩ := yes_size h
  obtain rfl : x = x3 := by
    rcases hF3 with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact Except.ok.inj (hx.symm.trans e)
    · rw [hp] at e; cases e
    · rw [hp] at e; cases e
  obtain ⟨G0, hG0, hz⟩ := frontAt_fresh hp hfx
  have hf : G.rows = #[] := by
    have e := A.before
    rw [hG0] at e
    have e' : G0.rows = G.rows := Option.some.inj e
    rw [← e']
    exact Array.eq_empty_of_size_eq_zero hz
  -- the frame, so that the debts can be called
  obtain ⟨W₀, hW₀⟩ : ∃ W, frameAt x = some W := by
    obtain ⟨W, _, _, _, hW, _⟩ := rows_split A.made
    exact ⟨W, by rw [← frame_of_front A]; exact hW⟩
  have Dx := D x W₀ lay hx hW₀ hlay
  obtain ⟨W, carried, samples, gens, G', hW, hG', hR, _, _, _, hs, hg, kc, ks, kg⟩ :=
    yes_row_kinds A Dx.keptPos hf
  obtain rfl : W₀ = W := Option.some.inj (hW₀.symm.trans hW)
  have hGN : t'.st.groups[N.groupAt m]? = some G' := by
    rw [hgrp, ← yes_link_grp hp h, ← hgr]
    exact hG'
  have hrun : G'.inRun = false := by
    obtain ⟨x4, hf4, R⟩ := yes_rs h
    obtain rfl : x = x4 := Option.some.inj (hfx.symm.trans hf4)
    have e := R x.f.group
    rw [hG', (firstFront_st hx).1, hgr] at e
    simpa [withFresh, freshGroup] using e
  obtain rfl : G' = Gm := by
    rw [← hgr] at hGm
    exact Option.some.inj (hG'.symm.trans hGm)
  have hNn : (switchNotices x.T x.others).size = 1 + x.T.kept.size + x.others.size := by
    simp [switchNotices]
    omega
  have ho : x.others.size = x.own.length + 1 := by
    obtain ⟨L, Gq, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
    rw [a.out]
    simp [ReqFrame.notices]
  refine ⟨?_, ?_, ?_⟩
  · exact rowsHeld_behind N m t' O' hO hGN hrun hR kc ks kg (by rw [Dx.carried, hs])
      (by rw [Dx.position, hs, hg])
  · refine membersHeld_behind N m t' O' hO hP0 hP1 hP2 hGN
      (n := 1 + x.T.kept.size + x.own.length) (n0 := x.st.oracles.size)
      (seat := fun i => (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) ?_
      (fun i hi => St.new i (by omega)) Dx.sent
    rw [mM]
    exact gain_numbers x
  · exact bookAt_behind N pIn pOut s t' lay.shapes.size (switchNotices x.T x.others).size hb
      St.size St.count (by rw [zO, hn0]) Dx.trees Dx.msgs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.gain_numbers
#print axioms VerifiableInference.Desc.First.K2.k2_step_two
#print axioms VerifiableInference.Desc.First.K2.link_three
