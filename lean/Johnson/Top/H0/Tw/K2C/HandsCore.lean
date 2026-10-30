-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HandsCore.lean: code switching (the kind K2): THE RULE BENEATH
K2C/HandsLink.lean's link_three, FREE OF THE SORT OF PLACE: behind an accept of the switch's
decision AND a way out that leaves the groups' rows, begins no proximity test and keeps the book,
three of the table of joints' four fixed tests on the verifier's state accept. For the head's link
and the finish. NO BLOCK IMPORTS THIS FILE. t, t': the state in front of the decision and behind
it. u: the state behind the way out. x: the front. n: how many of the sending's messages have
joined the group in u.
  SwitchDebts N m pIn pOut base d n x W lay   what is owed on the numbers N: keptPos · carried ·
                                              position (d: the number of the positions drawn) ·
                                              sent (the first n messages' seats, counted from the
                                              tree number base, are, as a set, N.sent m 0) · trees
                                              · msgs
  core_three   AtYes at t, t' · the front's group has no row yet · u's groups have t''s rows · in
               u the switch's group has not begun its test and has the members n0, n0 + 1, … (n of
               them) · the book of u seats the sending's messages by the layout (SeatedBut) · u
               has the sending's messages more than t · N.groupAt m is the front's group · bookAt
               in front · the closed facts on the open set behind · SwitchDebts: rowsHeld ·
               membersHeld · bookAt accept at u
LIMITS. SwitchDebts is met by nobody here. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HandsLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open _root_.Tw.K2 (switchNotices)

/-- **What is owed on the numbers at a switch.** -/
structure SwitchDebts (N : Numbers) (m : Nat) (pIn pOut : Option Place) (base d n : Nat)
    (x : _root_.Tw.K2.Front) (W : SwitchFrame) (lay : TreeLay) : Prop where
  keptPos : KeptPos x.T
  carried : N.rowsAt m .carried = (0, 1 + keptSamples x W)
  position : N.rowsAt m .position = (1 + keptSamples x W, d * (1 + targetRows x.T + 2))
  sent : sameMembers ((List.range n).map fun i =>
    (base + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true
  trees : N.treesAt pOut = N.treesAt pIn + lay.shapes.size
  msgs : N.msgsAt pOut = N.msgsAt pIn + (switchNotices x.T x.others).size

theorem core_three {p : P2} {t t' u : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p t t' r₁ r₂ gs x y S3 Y rows G c) (hf : G.rows = #[])
    (hRows : ∀ i : Nat, (u.st.groups[i]?).map (·.rows) = (t'.st.groups[i]?).map (·.rows))
    {Gu : Group} (hGu : u.st.groups[x.f.group]? = some Gu) (hRun : Gu.inRun = false) {n : Nat}
    (hMem : Gu.members.toList = (List.range n).map (· + x.st.oracles.size)) {lay : TreeLay}
    {num : Nat → Nat} {src : Nat → Fmt.Src}
    (St : SeatedBut t.book u.book (switchNotices x.T x.others).size x.st.oracles.size lay num src)
    (hn : n ≤ (switchNotices x.T x.others).size)
    (hOr : u.st.oracles.size = t.st.oracles.size + (switchNotices x.T x.others).size)
    (N : Numbers) (m : Nat) (pIn pOut : Option Place) (O' : List Item)
    (hO : O'.filter Item.isRow = switchRowsOpen m) (hP0 : O'.contains (.pin m 0) = true)
    (hP1 : O'.contains (.pin m 1) = false) (hP2 : O'.contains (.pin m 2) = false)
    (hgrp : N.groupAt m = x.f.group) (hb : bookAt N pIn t = true)
    (D : ∀ W, frameAt x = some W →
      SwitchDebts N m pIn pOut t.book.trees.size r₂.drawn.poss.length n x W lay) :
    rowsHeld N O' u = true ∧ membersHeld N O' u = true ∧ bookAt N pOut u = true := by
  obtain ⟨W₀, hW₀⟩ : ∃ W, frameAt x = some W := by
    obtain ⟨W, _, _, _, hW, _⟩ := rows_split A.made
    exact ⟨W, by rw [← frame_of_front A]; exact hW⟩
  have Dx := D W₀ hW₀
  obtain ⟨W, carried, samples, gens, G', hW, hG', hR, _, _, _, hs, hg, kc, ks, kg⟩ :=
    yes_row_kinds A Dx.keptPos hf
  obtain rfl : W₀ = W := Option.some.inj (hW₀.symm.trans hW)
  have hRu : Gu.rows = (carried :: samples ++ gens).toArray := by
    have e := hRows x.f.group
    rw [hGu, hG'] at e
    exact (Option.some.inj e).trans hR
  have hGN : u.st.groups[N.groupAt m]? = some Gu := by rw [hgrp]; exact hGu
  refine ⟨?_, ?_, ?_⟩
  · exact rowsHeld_behind N m u O' hO hGN hRun hRu kc ks kg (by rw [Dx.carried, hs])
      (by rw [Dx.position, hs, hg])
  · exact membersHeld_behind N m u O' hO hP0 hP1 hP2 hGN (n := n) (n0 := x.st.oracles.size)
      (seat := fun i => (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) hMem
      (fun i hi => St.new i (by omega)) Dx.sent
  · exact bookAt_behind N pIn pOut t u lay.shapes.size (switchNotices x.T x.others).size hb
      St.size St.count hOr Dx.trees Dx.msgs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.core_three
