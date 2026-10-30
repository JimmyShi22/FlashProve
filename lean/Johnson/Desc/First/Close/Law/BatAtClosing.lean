-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatAtClosing.lean: the batching as the closing of a link runs it
(`bat`, Johnson/Desc/First/Close/Closing.lean): its layout is the verifier's own, and the row that
it returns has the defect that BatApply.lean, beside this file, computes. Statements and proofs.

  `bat_inv_layout`: `bat_inv` (Inv.lean) with two clauses more: the layout that `bat` returns is
    what `Statement.layout` returns for the group, at the statement in front and at the statement
    behind.
  `bat_defect`: tab: tables of the oracle messages. If `bat` says yes and every row that it batches
    meets `RowFits` and `MaskFits`: what the returned row says of the group's two tables, made of
    tab, and of the kept members' own tables, minus its target, is the sum under the powers of the
    drawn element of what each row says of tab, seen through the group, minus that row's target.
Nothing is asked of the layout or of the group's tables (LayBlocks.lean to LayBegun.lean).

Limits. One direction: from a yes of `bat`. `RowFits` and `MaskFits` are asked of every row that is
batched: the group's open rows, the members' sample rows, the rows from reads. "Seen through the
group" (`rowSumIn`) is the row's coefficients on the oracle messages' own tables only for a row that
names the group's members alone (`NamesMembers`, `rowSumIn_eq`: BatApply.lean). The tables are
letters: nothing says which tables a prover is bound to. Nothing on the fold behind the batching.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Inv
import Johnson.Desc.First.Close.Law.LayBegun
import Johnson.Desc.Own.LayoutAgree
import OnBytes.Slice.BlkRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.LayLaw Cb

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- What a yes of the batching says, with the layout: it is the one that the verifier's own function
returns for the group, in front of the batching and behind it. -/
theorem bat_inv_layout {S S1 : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow}
    {lay : GroupLayout} (h : bat S g e r = .ok (row, lay, S1)) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ r.drawn.elems = [x.triple] ∧
      Bat.combine (begun S g G) g ⟨lay, runRows S G⟩ x = some row ∧ S1 = begun S g G ∧
      S.layout g = some lay ∧ (begun S g G).layout g = some lay := by
  obtain ⟨G, x, hG, hx, hc, hS⟩ := bat_inv h
  have hl : S.layout g = some lay := by
    unfold bat at h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    have k1 := got_ok k1
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    unfold Ground.beginRunP at k1
    split at k1
    · cases hG' : (onSt S).st.groups[g]? with
      | none => simp [hG'] at k1
      | some G' =>
        first
          | (simp [hG'] at k1
             subst k1
             exact Own.layout_of_group hG')
          | (cases hl : (onSt S).st.layout g with
             | none => simp [hG', hl] at k1
             | some l =>
               simp [hG', hl] at k1
               subst k1
               exact hl)
    · exact absurd k1 (by simp)
  exact ⟨G, x, hG, hx, hc, hS, hl, (begun_layout S g G hG).trans hl⟩

/-- **THE DEFECT OF THE ROW THAT THE CLOSING's BATCHING RETURNS.** tab: tables of the oracle
messages. If `bat` says yes and every row that it batches fits: what the returned row says of the
group's two tables, made of tab, and of the kept members' own tables, minus its target, is the sum
under the powers of the drawn element of what each row says, minus that row's target. Nothing is
asked of the layout. -/
theorem bat_defect {S S1 : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow}
    {lay : GroupLayout} (h : bat S g e r = .ok (row, lay, S1)) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ r.drawn.elems = [x.triple] ∧ S1 = begun S g G ∧
      ((∀ w ∈ (runRows S G).toList, RowFits S1 w ∧ MaskFits S1 lay w) →
        ∀ (N : Nat), lay.top ≤ N → ∀ tab : Nat → Part → Nat → GE,
          groupSum rdE S1 lay N tab (groupMain S1 lay N fun o => tab o .main)
              (groupMask S1 lay N fun o => tab o .mask) row - readE row.target =
            hornerSum (readE x) ((runRows S G).toList.map fun w =>
              rowSumIn rdE S1 lay N tab w - readE w.target)) := by
  obtain ⟨G, x, hG, hx, hc, rfl, -, hl⟩ := bat_inv_layout h
  exact ⟨G, x, hG, hx, rfl, fun hr N hN tab =>
    defect_at_layout rdE (begun S g G) g lay hl (runRows S G) x row hc hr N hN tab⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.bat_inv_layout
#print axioms VerifiableInference.Desc.First.Close.bat_defect
