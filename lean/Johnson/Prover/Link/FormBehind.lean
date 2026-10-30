-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormBehind.lean: behind a code switch of the proximity test whose record
`SwitchFacts` (Johnson/Prover/Link/FormSwitch.lean) is met: the rows are made, the batching is paid
whole, and the soundness side's record `Did` stands at the same letters.

Main names (namespace `Johnson.Prover.Link`).
  `rows_of_facts`   the switch's rows are the library's `switchRows`
  `did_of_batch`   `Did` (Johnson/Desc/K12/Law/SwDid.lean) from `SwitchFacts` and three facts on the
      batching: the group behind the switch, its layout, and that the rows are batched to a row.
      No count of rows is asked
  `behind_paid`   `SwitchFacts` into a new empty group, the statement in front in order, the codes'
      lengths in order, the plan's count "two rows, and three for each position": then there is
      a row with `BehindFront`, `Did` at the same letters, and the statement behind in order

By: `begin_inOrder` (Johnson/Desc/Means/Order.lean), `inOrder_switch`
(Johnson/Prover/Link/SwitchOrder.lean), `count_of` (Johnson/Prover/Link/FormNextSwitch.lean).

Limits. Every premise is asked. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSwitchFacts
import Johnson.Prover.Link.FormNextSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

variable {p : P12} {n : IoppStage} {last : Bool} {dS dC : Fmt.DeclaredRound} {t : T12}
  {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {rows : SingleRows} {gp j : ℕ}
  {D : Taken} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}

/-- The switch's rows are the library's. -/
theorem rows_of_facts (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x) :
    switchRows (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n)
      t.st.oracles.size #[] (swPos rC D) D.y = some D.rows := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1
    (Tw.K2.rowsCan_some (g := t.st.oracles.size) F.can)
  have hrows : D.rows = l := by
    rw [F.made]
    show (switchRows _ _ _ _ _ _ _).getD [] = l
    rw [hl]
    rfl
  rw [hrows]
  exact hl

/-- The group behind the switch. -/
theorem group_behind (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x) :
    (D.stR (swTarget p n) gp (othersOf last n) t.st).groups[gp]? = some (D.grown t.st) :=
  withRows_group gp D.rows _ _ (joined_group _ gp _ false D.G F.group)

/-- **`Did` from `SwitchFacts` and three facts on the batching.** -/
theorem did_of_batch {row : GroupRow} {lay : GroupLayout}
    (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x)
    (hlay : (D.stR (swTarget p n) gp (othersOf last n) t.st).layout gp = some lay)
    (hrow : Bat.combine (begun (D.stR (swTarget p n) gp (othersOf last n) t.st) gp (D.grown t.st))
      gp ⟨lay, runRows (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)⟩
      (E.ofTriple x) = some row) (hS : D.rS = rS) (hC : D.rC = rC) :
    Did p.nums.firstTree (keyed p [dS, dC] gs) rows (swTarget p n) gp (othersOf last n) t.st t.book
      t.roots (behindT p n last t rC gp D B row lay).st B (swOut p n last t rC D) row lay
      (E.ofTriple x) D := by
  have e := swNotices_eq p n last
  obtain ⟨-, -, -, -, -, c6, -⟩ := switchCut_says F.cut
  obtain ⟨⟨f1, -, -, -⟩, -, -⟩ := fit_says F.fit
  have F1 := front_of_facts F
  obtain ⟨S2, h2⟩ := ok_of_isSome F.joinOk
  obtain ⟨G, hG, hrun, -⟩ := joinS_ok h2
  obtain rfl : G = D.G := Option.some.inj (hG.symm.trans F.group)
  have hrecv := F.recv
  simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hrecv
  exact
    { check := (Tw.K2.targetOk_eq _ _ _).symm.trans F.guard
      trees := by
        have h := F.trees
        rw [Own.treesMade_eq, e] at h
        exact h
      places := hrecv.2
      valsS := by
        rw [hS]
        rw [c6] at f1
        exact List.map_eq_nil_iff.1 f1
      seed := by
        rw [hS]
        exact F.seed
      factor := F.factor
      form := by
        unfold Taken.z
        rw [hS]
        exact F.form
      pad := F.pad
      valsC := by
        rw [hC]
        exact F.ans
      elem := by
        rw [hC, F.elem]
        rfl
      code := F.code
      g := swIds_zero p n last t
      kept := rfl
      riders := by
        show (swIds p n last t).extract 1 (swIds p n last t).size = _
        unfold swIds
        rw [e]
        refine Array.ext (by simp) fun i h1 h2 => ?_
        simp only [Array.getElem_extract, Array.getElem_map, Array.getElem_range]
        omega
      positions := by
        rw [hC]
        rfl
      read := ⟨swIn p n last dS dC t rC gs rows gp D, [], rfl, rfl, rfl, rfl, rfl, F.read⟩
      group := F.group
      fresh := hrun
      rows := rows_of_facts F
      kinds := (addRowsS_ok gp D.rows _ _ F1.add).1
      layout := hlay
      row := hrow
      st := rfl }

/-- **The batching behind the switch is paid whole.** -/
theorem behind_paid {s s' : Sg} (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x)
    (ff : FoldedFit s s' t.st.codes n.code n.maskCode rows) (hO : Means.InOrder t.st)
    (hl : t.st.codes.lengthsOk = true) (hG : D.G = { code := n.code, maskCode := n.maskCode })
    (hS : D.rS = rS) (hC : D.rC = rC) (hcount : dC.entry.rows = 2 + 3 * dC.entry.poss) :
    ∃ row, BehindFront p n last dC t gp D (E.ofTriple x) row
        (Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)) ∧
      Did p.nums.firstTree (keyed p [dS, dC] gs) rows (swTarget p n) gp (othersOf last n) t.st
        t.book t.roots (behindT p n last t rC gp D B row
          (Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st))).st B
        (swOut p n last t rC D) row
        (Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st))
        (E.ofTriple x) D ∧
      Means.InOrder (D.stR (swTarget p n) gp (othersOf last n) t.st) ∧
      Means.InOrder (behindT p n last t rC gp D B row
        (Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st))).st := by
  have hm : D.G.members = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  have hR := inOrder_switch (front_of_facts F) hO hl
  have hgrp := group_behind F
  have ρ : Model.Reading PUnit :=
    ⟨fun _ => PUnit.unit, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨hlay, row, hrow, -⟩ := Means.begin_inOrder ρ hR gp (D.grown t.st) (E.ofTriple x) hgrp
  have elay : Means.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st) =
      Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st) :=
    Option.some.inj (hlay.symm.trans (Own.layout_of_group hgrp))
  rw [elay] at hrow hlay
  have hd := did_of_batch (B := B) F hlay hrow hS hC
  obtain ⟨-, ⟨-, g3, -, -⟩, -⟩ := fit_says F.fit
  have hsize := count_of hd ff.kept ff.prog.masks ff.prog.noKept hm hr
  rw [hC, g3] at hsize
  obtain ⟨row', F', hB⟩ := behindFront_of (B := B) F hO hl hm (hcount.trans hsize.symm) (by
    rw [hcount]
    omega)
  have erow : row' = row := Option.some.inj (F'.batch.symm.trans hrow)
  subst erow
  exact ⟨row', F', hd, hR, hB⟩

end Johnson.Prover.Link
