-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Returns.lean: THE CLOSING OF A SEGMENT (K10): ITS DECISION RETURNS, AND WHAT
THE RECORD BEHIND IS: in one theorem, and a lemma on `foldOutput`. Lemmas on the verifier's own text
(`Close.kind`, Johnson/Desc/First/Close/Kind.lean); no honest side's frame in them; none of the
library's goals.

THE FORM. Premises on the record in front (`CloseBase`, Johnson/Desc/K10/Honest/Base.lean; as a test
with code: `closeBaseB`, BaseB.lean) that name NO ELEMENT THAT IS SENT OR DRAWN IN THE BLOCK's OWN
ROUNDS, and the rounds' number and shape. Then: the decision returns; and the record behind is the
record in front but for these fields: in the frame the fresh mask is gone, the link's number is one
more, the next step is the first of a link, and the single rows are the library's own `foldOutput`
(OnBytes/Iop/Fold.lean) at the row that the batching returns at what "BAT" drew, at what "FOLD
epsilon" drew, and at the challenges and the running claim that the verifier's own reading of the
rounds "FOLD round" yields (`RoundsMeans`, Johnson/Desc/First/Close/Law/CloseMeans.lean); the
statement is the one behind the beginning of the test with the fresh mask marked as spent. Nothing
is owed, as in front.

ONE GUARD OF THE KIND COMPARES ELEMENTS OF THE FIELD, AND IT STANDS IN THE PREMISES. The verifier's
text asks of the batched row's structured vectors that they are in order (K10.rowfits:
`foldRowFits`, `formFits`, `tensorInOrder`, Johnson/Desc/Own/Shapes.lean), and that test holds a
written-out variable's pair against (1, 1). The facts ask the like of the open rows in front
(`termsOk`: `Tensor.ok`, OnBytes/Iop/Tensor.lean; `rowsIn`): of pairs that are the record's own,
whoever made them. Beside it the kind tests no value: the guards on the rounds read counts and the
sort of an item alone.

All else of the record is carried along as it was, VALUES WITH IT (the frame's plain scalars; the
oracle messages' sample rows; the other groups' open rows): the law gives the whole record, not
shape fields alone.

  `closeBehind`     the record behind, of the record in front, the facts' data and the single rows
  `rounds_len`      the rounds "FOLD round" yield as many challenges as they have entries
  `CloseLeft`          what a yes leaves, as one proposition
  `yes_behind`      EACH yes of the decision leaves that, under the facts
  `rows_shape`      the fields of such single rows that hang on neither eps, the challenges nor the
                    claim
  `close_returns`   THE TWO JOINED: under the facts, at every list of 2 + k rounds of the kind's
                    shape, the decision returns, and `CloseLeft` holds
  `close_returns_of`   the same from the test with code
  `base_one`        the facts fix their data
  `Toy.returns`     called at a small record

Limits. Of the block's decision, not its step, its plan's test or its "before" (the step:
Johnson/Desc/K10/Honest/Step.lean, AtS.lean). NOT SAID OF THE SINGLE ROWS BEHIND: the forms of `c`
and of the kept forms (how many variables; in order), and the lengths of `d`'s two rows; that the
kept forms' number and oracle messages are the same at every element that "BAT" may draw. THE FACTS
HOLD MORE THAN SIZES: `GroupOk`, `RowIn` and the test on the terms speak of the open rows' forms
(which tables, how many variables, in which order); `foldShapeFits`, `foldMaskFits` and the ground's
clauses read the members' shapes and marks (sampled, spent as a mask, a test begun, kept). Of the
place's data the facts read k and the count of rows alone: not h, the link, the piece, the bits of
work, the trees. The opened columns' groups are ignored by the decision. Shown of no honest run.
Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.BaseB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- **The record behind the closing.** rows: the single rows that the fold has left. -/
def closeBehind (s : Rec) (D : BaseData) (rows : SingleRows) : Rec :=
  ⟨none, { s.frame with rows := rows, mask := none, link := s.frame.link + 1, next := .first },
    spent (D.S1 s) D.m⟩

/-- The rounds "FOLD round" yield as many challenges as they have entries. -/
theorem rounds_len : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (claim : E) (gs : List E) (cl : E),
    RoundsMeans es rs claim gs cl → gs.length = es.length
  | [], [], _, _, _, h => by rw [h.1]; rfl
  | _ :: es, _ :: rs, _, _, cl, h => by
    obtain ⟨c0, c2, g, gs', _, hr, rfl⟩ := h
    rw [List.length_cons, List.length_cons, rounds_len es rs _ gs' cl hr]
  | [], _ :: _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, h => h.elim

/-- **What a yes of the decision leaves.** The rounds are "BAT", "FOLD epsilon" and the rounds "FOLD
round". "BAT" drew one element t, and the batching at t returned row. The verifier's own reading of
"FOLD epsilon" yields the sent sum and the drawn eps; its reading of the rounds "FOLD round", from
the claim sum + eps * the row's target on, yields the k challenges gamma and the running claim. The
record behind is `closeBehind` at the library's `foldOutput` of these. -/
def CloseLeft (P : Par) (s : Rec) (D : BaseData) (rs : List Fmt.RoundView) (s' : Rec) : Prop :=
  ∃ (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (t : Fmt.Ext) (row : GroupRow) (sum eps : E)
    (gamma : List E) (claim : E),
    rs = rB :: rE :: rR ∧ rB.drawn.elems = [t] ∧
    Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩
      (E.ofTriple t) = some row ∧
    HeardMeans "FOLD epsilon" 1 (eEps P) rE 0 [sum] eps ∧
    RoundsMeans (List.replicate P.k (eRound P)) rR (maddE sum eps row.target) gamma claim ∧
    gamma.length = P.k ∧
    s' = closeBehind s D (foldOutput (spent (D.S1 s) D.m) (D.F s) row D.m eps gamma claim)

/-- **Each yes of the decision leaves that**, under the facts on the record in front. -/
theorem yes_behind {Cl : Type} {P : Par} {s s' : Rec} {D : BaseData} (H : CloseBase P s D)
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') : CloseLeft P s D rs s' := by
  obtain ⟨y, hy, rfl⟩ := (kind_decide_iff P s s' rs gs).1 h
  obtain ⟨_, L, k2, G, k3, _, rows, hc, hf'⟩ := (closeFrame_iff _ _ _ _ _ y.1 y.2).1 hy
  obtain ⟨eB, es₁, rB, rs₁, e1, rfl, m, hm, row, Ly, S1, hbat, _, hfold⟩ := hc
  obtain ⟨_, input, d, b2, xs, x, b3, _, b5, rfl, rfl⟩ := hbat
  obtain ⟨eE, eR, rE, rR, e2, rfl, _, _, _, _, _, d2, f6, sum, eps, f7, _, gam, cl, f9, f10,
    f11⟩ := hfold
  rw [entries_eq] at e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e2
  obtain ⟨t, ht, rfl⟩ := b3.2.2.2.2.2.2
  obtain rfl : D.m = m := Option.some.inj (H.mask.symm.trans hm)
  obtain rfl : D.Gq = G := Option.some.inj (H.group.symm.trans k3)
  have eb : (input, d) = (⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩,
      { onSt s.st with st := D.S1 s }) := by
    unfold Ground.beginRunP at b2
    have hb : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true := H.beginRun
    have ht' : (onSt s.st).st.groups[s.frame.group]? = some D.G := H.there
    rw [if_pos hb, ht'] at b2
    exact (Option.some.inj b2).symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eb
  have hd2 : d2.st = spent (D.S1 s) D.m := by
    unfold Ground.spendAsMaskP at f6
    split at f6
    · obtain rfl := Option.some.inj f6
      rfl
    · cases f6
  refine ⟨rB, rE, rR, t, row, sum, eps, gam, cl, rfl, ht, b5, f7, f9, ?_, ?_⟩
  · rw [rounds_len _ _ _ _ _ f9, List.length_replicate]
  · show (⟨none, y.1, y.2⟩ : Rec) = _
    unfold closeBehind
    rw [hf', f11, f10, hd2]
    rfl

/-- **The fields of the single rows behind that hang on neither eps, the challenges nor the claim**:
the two codes' numbers and the layout are the fold's shape's; there are two masks; the fresh mask's
number is the one handed in; the count of kept rows is the layout's and the statement's; the kept
forms are as many as the row's, on the row's oracle messages. And the challenges are laid in as they
are; `d` has two rows. -/
theorem rows_shape (S : Statement) (F : FoldShape) (row : GroupRow) (m : Nat) (eps : E)
    (gamma : List E) (claim : E) :
    let R := foldOutput S F row m eps gamma claim
    R.code = F.code ∧ R.maskCode = F.maskCode ∧ R.layout = F.layout ∧ R.masks = 2 ∧ R.fresh = m ∧
      R.gamma = gamma ∧ R.d.size = 2 ∧ R.kept.size = row.kept.size ∧
      R.kept.toList.map (·.oracle) = row.kept.toList.map (·.oracle) ∧
      R.keptRows = (foldOutput S F {} 0 zeroE [] zeroE).keptRows := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · show (row.kept.map _).size = _
    rw [Array.size_map]
  · show (row.kept.map _).toList.map _ = _
    rw [Array.toList_map, List.map_map]
    rfl

/-- **THE DECISION RETURNS, AND WHAT THE RECORD BEHIND IS**: under facts that name no element sent
or drawn in the block's own rounds, at every list of 2 + k rounds of the kind's shape. -/
theorem close_returns {Cl : Type} {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) :
    ∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s' ∧ CloseLeft P s D rs s' := by
  obtain ⟨s', h⟩ := close_yes_all (Cl := Cl) H rs gs hl hs
  exact ⟨s', h, yes_behind H h⟩

/-- The facts fix their data. -/
theorem base_one {P : Par} {s : Rec} {D D' : BaseData} (H : CloseBase P s D)
    (H' : CloseBase P s D') : D = D' := by
  cases D
  cases D'
  have a := Option.some.inj (H.link.symm.trans H'.link)
  have b := Option.some.inj (H.group.symm.trans H'.group)
  have c := Option.some.inj (H.mask.symm.trans H'.mask)
  have d := Option.some.inj (H.there.symm.trans H'.there)
  simp only at a b c d
  subst a b c d
  rfl

/-- `close_returns` from the test with code. -/
theorem close_returns_of {Cl : Type} {P : Par} {s : Rec} (h : closeBaseB P s = true)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) :
    ∃ D s', CloseBase P s D ∧ ((kind (Cl := Cl)) P).decide s rs gs = .ok s' ∧
      CloseLeft P s D rs s' := by
  obtain ⟨D, H⟩ := closeBase_of h
  obtain ⟨s', a, b⟩ := close_returns (Cl := Cl) H rs gs hl hs
  exact ⟨D, s', H, a, b⟩

namespace Toy

/-- `close_returns_of` called, at the small record of Johnson/Desc/K10/Honest/FrontToy.lean (that it
passes the test with code: BaseB.lean's `base_member`): at every list of four rounds of the kind's
shape. -/
theorem returns (rs : List Fmt.RoundView) (hl : rs.length = 4) (hs : ShapedAll rs) :
    ∃ D s', CloseBase P s D ∧ ((kind (Cl := Unit)) P).decide s rs [] = .ok s' ∧
      CloseLeft P s D rs s' :=
  close_returns_of base_member rs [] hl hs

end Toy

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.rounds_len
#print axioms ProofFile.Honest.K10.YesFree.yes_behind
#print axioms ProofFile.Honest.K10.YesFree.rows_shape
#print axioms ProofFile.Honest.K10.YesFree.close_returns
#print axioms ProofFile.Honest.K10.YesFree.base_one
#print axioms ProofFile.Honest.K10.YesFree.close_returns_of
#print axioms ProofFile.Honest.K10.YesFree.Toy.returns
