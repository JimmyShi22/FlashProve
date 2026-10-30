-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormRow.lean: THE FORM's HALF: THE ROW THAT A BATCHING RETURNS PASSES THE FOLD's
TEST ON THE ROW (Own.foldRowFits, Johnson/Desc/Own/Fold.lean): where the rows that the batching
takes in are dense (DenseRow, OnBytes/Slice/BlkProxDense.lean).

Main names.
  formFits_of_cfits a dense form (DenseForm f) of n ≤ 63 variables throughout, with its single
    entries below 2^n (CFits n f), passes Own.formFits: formFits_of_dense
    (Johnson/Desc/Means/Dense.lean) with its premises on variables and entries folded into CFits.
  addEntryTo_dsize, addTermTo_dsize, addRunTo_dsize, addFormTo_dsize, addToGroupRow_dsize,
  combine_dsize       the batched row's vector on the mask table has the table's full length.
  rowFits_of_combine  THE STATEMENT.

What pays what. The variables and indices: combine_cfits (Johnson/Desc/Means/Shape.lean). Dense:
combine_dense (OnBytes/Slice/BlkProxDense.lean). The mask table's length: this file.

Limits. DenseRow OF THE ROWS IS A PREMISE: it is paid where a row has no written-out factor
(denseRow_of_plain), where its terms pass the verifier's test on a tensor and its whole coefficient
vectors the test on a form (denseRow_of_tests, Johnson/Desc/Means/Dense.lean), and, for a switch's
carried row, where the old claim's form is dense (denseRow_carriedRow; the first and the third:
OnBytes/Slice/BlkProxDense.lean). Rows with a written-out factor (the key file's and the proof
file's tests have such rows) are served where they are dense; AT A ROW THAT IS NOT DENSE THIS FILE
SAYS NOTHING. More than 63 variables are not served (hv).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Means.Dense
import Johnson.Desc.Own.Fold
import Johnson.Desc.Own.FoldMean
import Johnson.Desc.Means.Shape
import OnBytes.Slice.BlkPlain
import OnBytes.Iop.SpreadLaws
import OnBytes.Iop.Prox

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc
open OnBytes.Slice.ProxRun (DenseForm DenseRow combine_dense)

/-- **A dense form passes the test on a form**: under CFits n f, DenseForm f and n ≤ 63. -/
theorem formFits_of_cfits {f : Form} {n : Nat} (hc : CFits n f) (hp : DenseForm f) (hn : n ≤ 63) :
    Own.formFits f n = true :=
  formFits_of_dense hc hp hn

/-! ## The mask table's length -/

theorem addEntryTo_dsize (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (o : Nat)
    (part : Part) (index : Nat) (coeff : E)
    (h : addEntryTo S L x acc o part index coeff = some acc') : acc'.d.size = acc.d.size := by
  unfold addEntryTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; simp only [Array.size_modify])

theorem addTermTo_dsize (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (h : addTermTo S L x acc t = some acc') : acc'.d.size = acc.d.size := by
  unfold addTermTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; simp only [Tensor.addTo_size])

theorem addRunTo_dsize (S : Statement) (L : GroupLayout) (x : E) (n : Nat) (acc acc' : GroupRow)
    (w : Run) (hp : acc.d.size = n) (h : addRunTo S L x acc w = some acc') : acc'.d.size = n :=
  foldlM_keeps (fun a : GroupRow => a.d.size = n) _ _ acc acc'
    (fun _ _ y y' hy hstep => (addEntryTo_dsize S L x y y' _ _ _ _ hstep).trans hy) hp h

theorem addFormTo_dsize (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (h : addFormTo S L x acc f = some acc') : acc'.d.size = acc.d.size := by
  unfold addFormTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; rfl)

theorem ready_dsize (acc : GroupRow) (L : GroupLayout) (h : MaskReady L acc) :
    (acc.ready L).d.size = 2 ^ (L.h + L.logEllZk) := by
  unfold GroupRow.ready
  rcases h with h | h
  · simp [h]
  · by_cases he : acc.d.isEmpty = true
    · simp [he]
    · simp only [he, Bool.false_eq_true, if_false]
      exact h

theorem addToGroupRow_dsize (S : Statement) (L : GroupLayout) (row : Row) (x : E)
    (acc acc' : GroupRow) (hp : MaskReady L acc) (h : addToGroupRow S L row x acc = some acc') :
    acc'.d.size = 2 ^ (L.h + L.logEllZk) := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨a1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  have p0 := ready_dsize acc L hp
  have p1 : a1.d.size = 2 ^ (L.h + L.logEllZk) :=
    foldlM_keeps (fun a : GroupRow => a.d.size = 2 ^ (L.h + L.logEllZk)) _ _ _ _
      (fun t _ y y' hy hs => (addTermTo_dsize S L x y y' t hs).trans hy) p0 h1
  have p2 : a2.d.size = 2 ^ (L.h + L.logEllZk) :=
    foldlM_keeps (fun a : GroupRow => a.d.size = 2 ^ (L.h + L.logEllZk)) _ _ _ _
      (fun _ _ y y' hy hs => (addEntryTo_dsize S L x y y' _ _ _ _ hs).trans hy) p1 h2
  have p3 : a3.d.size = 2 ^ (L.h + L.logEllZk) :=
    foldlM_keeps (fun a : GroupRow => a.d.size = 2 ^ (L.h + L.logEllZk)) _ _ _ _
      (fun w _ y y' hy hs => addRunTo_dsize S L x _ y y' w hy hs) p2 h3
  have p4 : a4.d.size = 2 ^ (L.h + L.logEllZk) :=
    foldlM_keeps (fun a : GroupRow => a.d.size = 2 ^ (L.h + L.logEllZk)) _ _ _ _
      (fun f _ y y' hy hs => (addFormTo_dsize S L x y y' f hs).trans hy) p3 h4
  cases h
  exact p4

/-- **The batched row's vector on the mask table has the table's full length.** -/
theorem combine_dsize (S : Statement) (g : Nat) (input : RunInput) (x : E) (G : GroupRow)
    (h : Bat.combine S g input x = some G) :
    G.d.size = 2 ^ (input.layout.h + input.layout.logEllZk) := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
  have inv : MaskReady input.layout s.1 :=
    foldlM_keeps (fun s : GroupRow × Row × E => MaskReady input.layout s.1) _ _ _ _
      (fun r _ y y' hy hstep => by
        obtain ⟨acc, hacc, hy'⟩ := Option.bind_eq_some_iff.1 hstep
        cases hy'
        exact Or.inr (addToGroupRow_dsize S input.layout _ _ _ _ hy hacc))
      (Or.inl rfl) hs
  exact addToGroupRow_dsize S input.layout _ _ _ _ inv h

/-- **THE BATCHED ROW PASSES THE FOLD's TEST ON THE ROW.** S: the statement behind the test's
beginning. c: the stage in the program's form. -/
theorem rowFits_of_combine {S : Statement} {G : Group} {g : Nat} {L : GroupLayout}
    {rows : Array Row} {x : E} {row : GroupRow} (hG : S.groups[g]? = some G)
    (hL : S.layout g = some L) (hOk : GroupOk S G) (hr : ∀ r ∈ rows.toList, RowIn S G r)
    (hc : Bat.combine S g ⟨L, rows⟩ x = some row) (hp : ∀ r ∈ rows.toList, DenseRow r)
    (hk : row.kept = #[]) (c : IoppStage) (ck : c.k = L.k) (ch : c.h = L.h)
    (c1 : G.code = c.code) (c2 : G.maskCode = c.maskCode) (hv : L.k + L.logEll ≤ 63)
    (hz : (S.codes.mask.getD c.maskCode default).ell =
      2 ^ ceilLog2 (S.codes.mask.getD c.maskCode default).ell) :
    Own.foldRowFits S (ioppFoldShape c L) row = true := by
  have eL : L = layoutOf S G := Option.some.inj (hL.symm.trans (layout_eq S g G hG))
  have e1 : L.logEll = ceilLog2 (S.codes.base.getD c.code default).ell := by
    rw [eL, ← c1]
    rfl
  have e2 : L.logEllZk = ceilLog2 (S.codes.mask.getD c.maskCode default).ell := by
    rw [eL, ← c2]
    rfl
  rw [Own.foldRowFits_iff]
  refine ⟨?_, ?_, fun f hf => ?_⟩
  · show Own.formFits row.c (c.k + ceilLog2 (S.codes.base.getD c.code default).ell) = true
    rw [ck, ← e1]
    exact formFits_of_cfits (combine_cfits hG hL hOk hr hc) (combine_dense S g _ x row hp hc) hv
  · show row.d.size = (S.codes.mask.getD c.maskCode default).ell * 2 ^ c.h
    rw [combine_dsize S g _ x row hc, hz, ← e2, ch, ← Nat.pow_add, Nat.add_comm]
  · rw [hk] at hf
    exact absurd hf (by simp)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.formFits_of_cfits
#print axioms Johnson.Prover.Link.addEntryTo_dsize
#print axioms Johnson.Prover.Link.addTermTo_dsize
#print axioms Johnson.Prover.Link.addRunTo_dsize
#print axioms Johnson.Prover.Link.addFormTo_dsize
#print axioms Johnson.Prover.Link.ready_dsize
#print axioms Johnson.Prover.Link.addToGroupRow_dsize
#print axioms Johnson.Prover.Link.combine_dsize
#print axioms Johnson.Prover.Link.rowFits_of_combine
