-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSwitchBehind.lean: the step behind a switch's sending
(`Tw.L9.switchBehind`, Johnson/Top/H0/Tw/L9/Switch.lean) returns ok, from its guards: general in
what the step reads.

Main names (namespace `Johnson.Prover.Link`).
  `loc_yes`   the closing of the round of the positions ([G1] to [G7]) returns the list of the draws
  `tail_yes`   the step's last lines, from the joining on ([G17] to [G33])
  `behind_yes`   the whole step: the old main code is there · `loc_yes`'s facts · the reading of the
      old rows says yes · the new message is there · the joining says yes · the group's test has not
      begun · the rows can be made · each made row is added: then the step returns the statement
      with the rows, the book and the columns that the reading left, and what the switch returns

The converse of `switchBehind_ok` (Johnson/Desc/K12/Law/SwUnfold.lean), over that file's
`switchBehind_eq` and its device `tailB`.

Limits. The reading, the joining and the adding of the rows are asked as yeses of the description's
own functions. Served: a target without a kept member, with mask rows. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open H2K.Sw

/-- **The closing of the round of the positions.** -/
theorem loc_yes (i : Tw.L9.SwIn) (logN : Nat) (h1 : i.entry.name = "LOC")
    (h2 : i.entry.drawNZ = 0) (h3 : i.settled = true) (h4 : i.itemsLeft = 0)
    (h5a : i.drawn.elems.length = i.entry.drawE) (h5b : i.drawn.poss.length = i.entry.poss)
    (h5c : i.drawn.trits.length = i.entry.trits) (h6a : i.entry.logN = logN)
    (h6b : 0 < i.entry.poss) (h7 : i.drawn.elems = []) :
    Tw.L9.locPositions i logN = .ok (Positions.ofDraws logN i.drawn.poss) := by
  have h5 : i.entry.drawE = 0 := by
    rw [← h5a, h7]
    rfl
  unfold Tw.L9.locPositions
  simp [h1, h2, h3, h4, h5, h5b, h5c, h6a, h6b, h7]

/-- **The step's last lines.** -/
theorem tail_yes (i : Tw.L9.SwIn) (out : Switched) (B : TreeBook) (left : List Tw.L9.Col)
    (y : Array E) (S1 S2 S4 : Statement) (hk : i.T.kept = #[])
    (hjoin : Tw.L9.joinS S1 i.grp out.g false = .ok S2)
    (hfresh : ∃ G, S2.groups[i.grp]? = some G ∧ G.inRun = false)
    (hcan : Tw.K2.rowsCan S2 i.old i.T out.kept out.positions y = true)
    (hadd : ((Own.swRows S2 i.old i.T out.g out.kept out.positions y).getD []).foldlM
      (fun S r => Tw.L9.addRowS S i.grp r) S2 = .ok S4) :
    tailB i out B left y S1 = .ok ⟨S4, B, left, out⟩ := by
  obtain ⟨G, hG, hrun⟩ := hfresh
  have hz : out.kept.zip i.T.kept = #[] := by
    rw [hk]
    simp
  unfold tailB
  rw [hjoin, hz]
  simp only [Tw.K2.rowsMade, hcan, hG, hrun, hadd, bind, Except.bind, pure, Except.pure,
    Array.foldlM_empty, if_true, Bool.false_eq_true, if_false]

/-- **The step behind the sending returns ok.** -/
theorem behind_yes (i : Tw.L9.SwIn) (code : OnBytes.Code) (pos : Positions) (B : TreeBook)
    (left : List Tw.L9.Col) (y : Array E) (S2 S4 : Statement) (hk : i.T.kept = #[])
    (hcode : i.st.codes.base[i.old.code]? = some code)
    (hloc : Tw.L9.locPositions i code.logN = .ok pos)
    (hread : Tw.L9.readOld i pos = .ok (B, left, y)) (hm : 0 < i.T.shape.maskRows)
    (hg : i.ids.getD 0 noId < i.st.oracles.size)
    (hjoin : Tw.L9.joinS (ledgerShut i.st i.T (i.ids.getD 0 noId)) i.grp (i.ids.getD 0 noId)
      false = .ok S2)
    (hfresh : ∃ G, S2.groups[i.grp]? = some G ∧ G.inRun = false)
    (hcan : Tw.K2.rowsCan S2 i.old i.T #[] pos y = true)
    (hadd : ((Own.swRows S2 i.old i.T (i.ids.getD 0 noId) #[] pos y).getD []).foldlM
      (fun S r => Tw.L9.addRowS S i.grp r) S2 = .ok S4) :
    Tw.L9.switchBehind i =
      .ok ⟨S4, B, left, ⟨i.ids.getD 0 noId, #[], i.ids.extract 1 i.ids.size, pos⟩⟩ := by
  have hkept : i.ids.extract 1 (1 + i.T.kept.size) = #[] := by
    rw [hk]
    simp
  have hoth : i.ids.extract (1 + i.T.kept.size) i.ids.size = i.ids.extract 1 i.ids.size := by
    rw [hk]
    rfl
  have ht := tail_yes i ⟨i.ids.getD 0 noId, #[], i.ids.extract 1 i.ids.size, pos⟩ B left y
    (ledgerShut i.st i.T (i.ids.getD 0 noId)) S2 S4 hk hjoin hfresh hcan hadd
  unfold ledgerShut at ht
  rw [if_pos hm] at ht
  rw [switchBehind_eq]
  simp only [hcode, hloc, hread, hkept, hoth, if_pos hm, if_pos hg, bind, Except.bind, pure,
    Except.pure]
  exact ht

end Johnson.Prover.Link
