-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontCoding.lean: TABLES THAT THE FORMAT's OWN ENCODER MAKES MEET THE PREMISES
ON THE TWO TABLES OF front_holds (Johnson/Prover/Link/FrontWhole.lean). Statements and proofs,
general in the sizes; msg, tl: the rows' messages' and tails' words.

  tab_honest    the stored string honestTab S msg tl IS the table of the code words of
                honestPolys S msg tl (OnBytes/Slice/Honest.lean), at the link with a record
  rec_honest    the sample map's own answers at honestMsgs S msg are each row's answers at
                honestPolys
  same_honest   two tables whose messages read alike before the cut agree on the entries that are
                compared
  cells_same    before the cut an entry of Johnson/Flat/CodingCells.lean's cellEntry does not read
                the second letter η
  same_cells    so two tables that codingCells' encoder makes of ONE matrix, at any η, η' and any
                tails, agree on the entries that are compared, where these lie before the coding's
                cut and in the message

Not shown here. That the object's encoder and OOD sample at the description's own letters unfold
to these. Nothing on a decision; nothing on soundness; nothing on what η or a tail is for, or on
what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.Honest
import OnBytes.Slice.CorePeelRec
import Johnson.Flat.CodingCells

set_option autoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice OnBytes.Flat Cb Cb.Ood

variable (S : Sz) (Z : Sample GE S.En)

theorem tab_honest (msg tl : ℕ → List UInt64) :
    (S.lkR Z).tab (honestTab S msg tl) = fun ρ => (S.ixR Z).G.mulVec (honestPolys S msg tl ρ) :=
  funext fun r => funext fun x => tab_honestTab S msg tl r x

theorem rec_honest (msg tl : ℕ → List UInt64) (σ : Z.D) (r : (S.ixR Z).Row) (s : Z.S) :
    (S.ixR Z).ZR.val σ (honestMsgs S msg) (r, s) =
      ∑ j, Z.mat σ s j * honestPolys S msg tl r ((S.ixR Z).pl j) := by
  show ∑ n : (S.ixR Z).Row × S.En, (S.ixR Z).ZR.mat σ (r, s) n * honestMsgs S msg n = _
  rw [Fintype.sum_prod_type, Finset.sum_eq_single r]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have e : (S.ixR Z).ZR.mat σ (r, s) (r, j) = Z.mat σ s j := if_pos rfl
    rw [e, ← view_honestPolys S msg tl]
    rfl
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    have e : (S.ixR Z).ZR.mat σ (r, s) (b, j) = 0 := if_neg hb
    rw [e, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ r) h

theorem same_honest (msg₀ tl₀ msg₁ tl₁ : ℕ → List UInt64)
    (h : ∀ (r : S.ix.Row) e, e < S.P.cut →
      toF ((msg₀ (Sz.rowNo r)).getD e 0) = toF ((msg₁ (Sz.rowNo r)).getD e 0)) :
    (S.lwR Z).SameOn ((S.ixR Z).view (honestPolys S msg₀ tl₀))
      ((S.ixR Z).view (honestPolys S msg₁ tl₁)) := by
  intro r a
  have e0 := congrFun (view_honestPolys S msg₀ tl₀) (r, (S.lwR Z).lay a)
  have e1 := congrFun (view_honestPolys S msg₁ tl₁) (r, (S.lwR Z).lay a)
  refine e0.trans (Eq.trans ?_ e1.symm)
  show algebraMap GF GE (toF ((msg₀ (Sz.rowNo r)).getD a.val 0)) =
    algebraMap GF GE (toF ((msg₁ (Sz.rowNo r)).getD a.val 0))
  rw [h _ _ a.isLt]

theorem cells_same (cut : ℕ) (N : MatrixNums) (M : Cells (S.toDecR Z cut) N)
    (η η' : PadsOf S cut) (b e : ℕ) (he : e < cut) :
    cellEntry S Z cut N M η b e = cellEntry S Z cut N M η' b e := by
  unfold cellEntry cellEntryAt
  rw [if_pos he, if_pos he]

theorem same_cells (cut : ℕ) (N : MatrixNums) (M : Cells (S.toDecR Z cut) N)
    (η η' : PadsOf S cut) (tl₀ tl₁ : ℕ → List UInt64) (hc : S.P.cut ≤ cut)
    (hl : S.P.cut ≤ S.P.T.l) :
    (S.lwR Z).SameOn
      ((S.ixR Z).view
        (honestPolys S (rowWords S (honestMsgs S (cellWords S Z cut N M η))) tl₀))
      ((S.ixR Z).view
        (honestPolys S (rowWords S (honestMsgs S (cellWords S Z cut N M η'))) tl₁)) := by
  refine same_honest S Z _ _ _ _ fun r e he => ?_
  have hel : e < S.P.T.l := lt_of_lt_of_le he hl
  have key : ∀ ζ : PadsOf S cut,
      toF ((rowWords S (honestMsgs S (cellWords S Z cut N M ζ)) (Sz.rowNo r)).getD e 0) =
        toF (cellEntry S Z cut N M ζ (Sz.rowNo r) e) := fun ζ => by
    have h1 := rowWords_getD S (honestMsgs S (cellWords S Z cut N M ζ)) r ⟨e, hel⟩
    have h2 : (rowWords S (honestMsgs S (cellWords S Z cut N M ζ)) (Sz.rowNo r)).getD e 0 =
        ofF (honestMsgs S (cellWords S Z cut N M ζ) (r, ⟨e, hel⟩)).c0 := h1
    rw [h2, toF_ofF]
    show (algebraMap GF GE (toF ((cellWords S Z cut N M ζ (Sz.rowNo r)).getD e 0))).c0 = _
    rw [cellWords_getD S Z cut N M ζ _ e hel]
    rfl
  rw [key η, key η', cells_same S Z cut N M η η' _ e (lt_of_lt_of_le he hc)]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.same_cells
#print axioms Johnson.Prover.Link.tab_honest
#print axioms Johnson.Prover.Link.rec_honest
#print axioms Johnson.Prover.Link.same_honest
#print axioms Johnson.Prover.Link.cells_same
