-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormLast.lean: two small laws at the last stage of a proximity test.

Main names (namespace `Johnson.Prover.Link`).
  `logNzk_of_trees`   where a switch's announcements are laid in one tree, the tree's depth for mask
      rows is that of the new message's mask code
  `lastForm_behind`   `lastForm_next` (Johnson/Prover/Link/FormClose.lean) without its two premises
      of their own: the depth by `logNzk_of_trees`, the label by the plan's clause `StepPlan.label`

By: `treesMade_gives` (Johnson/Desc/Own/TreesMean.lean).

Limits. Every premise is asked. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormClose
import Johnson.Desc.Own.TreesMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

/-- The one tree's depth for mask rows is that of the new message's mask code. -/
theorem logNzk_of_trees (K : Codes) (T : SwitchTarget) (others : Array OracleNotice)
    (lay : TreeLay) (sh : TreeShape)
    (h : layTrees K (OnBytes.Slice.sentOf T others) = some lay) (h1 : lay.shapes = #[sh])
    (h0 : lay.tree.getD 0 0 = 0) (hm : 0 < T.shape.maskRows) :
    sh.logNzk = (K.mask.getD T.shape.maskCode default).logN := by
  have h' : Own.treesMade K (OnBytes.Slice.sentOf T others) = some lay :=
    (Own.treesMade_eq _ _).trans h
  obtain ⟨-, -, h3, -⟩ := Own.treesMade_gives h'
  have h4 := (h3 0 (by simp [OnBytes.Slice.sentOf]) (by
    simpa [Own.maskRowsAt, OnBytes.Slice.sentOf] using hm)).1
  rw [h0, h1] at h4
  simpa [Own.maskLenAt, OnBytes.Slice.sentOf] using h4

/-- **Behind the stage in front of the last**: `lastForm_next` without its two own premises. -/
theorem lastForm_behind {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {c n : IoppStage}
    {dS dC d₁ d₂ : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree} {rs : List Fmt.RoundView} {rS rC : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {a x : Fmt.Ext} {D : Taken} {row' : GroupRow}
    (Pl : StepPlan p t.st.codes j cur next true l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (Dn : StepDone (sgOf cur) (sgOf next) p n true dS dC
      (foldT t row L c (n.code, n.maskCode) id rs) rS rC gs (foldOut t row L c id rs)
      t.st.groups.size j cur next tN a D x row')
    (Lp : LastPlan p t.st.codes (j + 1) next (l.drop (cur.k + 3)) n d₁ d₂) :
    LastForm p (j + 1) next
      (stepT3 p n true dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
        (foldOut t row L c id rs) t.st.groups.size D tN row') row'
      (stepL p n true (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size D) n
      ⟨dense (row'.c.fixLow [zeroE]) (ceilLog2 next.C.l), row'.d.map (·.triple),
        row'.target.triple⟩
      (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size
      ((foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1) t.book.trees.size := by
  refine lastForm_next Pl I Dn Lp (Pl.label rfl) fun sh hsh => ?_
  obtain ⟨sh', l1, -, l3, -, -⟩ := Pl.oneTree D.lay Dn.did.trees
  rw [logNzk_of_trees t.st.codes (swTarget p n) (othersOf true n) D.lay sh Dn.did.trees hsh
    (l3 0 (by simp [OnBytes.Slice.sentOf])).1 (Nat.two_pow_pos _)]
  exact congrArg (·.a) (getD_of_map_some Pl.zkN)

end Johnson.Prover.Link
