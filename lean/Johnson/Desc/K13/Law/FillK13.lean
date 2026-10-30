-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillK13.lean: ONE LAYER OF THE FILLING of the first chain's table of joints:
the items that kinds K1 and K13 make at the chain's start, at the members' batching and at W's
commitment, each with its test on the record, laid into a `Meaning` over whatever is there.
Definitions, and statements that hold by the make. It turns nothing of the table.
THIN: it imports its tests and its sentences alone: the tests as code
(Johnson/Desc/K13/PubK13.lean), the door's three fillings (SitsDoor.lean, AsksDoor.lean,
MasksDoor.lean), "all rows on the table are true" (Letters.lean) and the test "tidy"
(Johnson/Desc/Means/TestsBack.lean). THE LAWS THAT SPEND THE LAYER STAND BESIDE: FillK13Laws.lean
(each test is the one of which the laws speak), FillFromSentences.lean.
What is said.
  `DataK13`: the layer's data: the kind's numbers P; the plan's codes, request's shape and layout;
    the table's numbers N (indexNo, w and groupAt 0 are read); rw: the reader of a witness's
    matrix and mask entries: A LETTER.
  `inOrderK13`: the statement is tidy, and its codes, the frame's shape and the rows' layout are the
    plan's.
  `fillK13`: the layer: `pile` and `pileOne` are "all rows on the table are true" at
    the reader; `pub` is `pubK13C` over what was there; the door's filling gains `wSitsMore`; every
    other field as it was, `inOrder` among them. Not laid here: `inOrderK13` in
    `inOrder`; the names "K13.pileMasks", "K13.pileWithin", "K13.oneRow"; `k13Asks`.
  `fillK13Plus`: these, as a layer of its own: over `fillK13 D Mg` it gives the
    wider meaning, field by field (`fillK13Plus_‹item›`, `fillK13Plus_over`): for whoever wants a
    meaning at whose door the three names still stand.
  `fillK13_pub`, `fillK13_‹item›`, `fillK13_inOrder`, `fillK13_more`, `fillK13_pile`,
    `fillK13_pileOne`: what it lays, at every `Meaning`: by the make. `fillK13_else`,
    `fillK13_fields`: what it leaves.
Limits. (1) rw is a letter. (2) Nothing says here who makes or keeps an item. (3) `pubP` is left as
it was. (4) `Item.pile` IS OPEN FROM THE CHAIN's START: at this layer it says "all rows on the table
are true" AT THE READER rw, at every record: SO EVERY BLOCK IN FRONT OF K13's OWES, in its tie for
what rides or goes back, that sentence's going back over its own step. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.PubK13
import Johnson.Desc.K13.Law.SitsDoor
import Johnson.Desc.K13.Law.AsksDoor
import Johnson.Desc.K13.Law.MasksDoor
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.Means.TestsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S Pub Meaning Numbers More)

/-- The layer's data. -/
structure DataK13 (Pp W : Type) (nR : ℕ) where
  P : Where
  codes : Codes
  shape : Params.ReqShape
  layout : Params.ReqLayout
  N : Numbers
  rw : Pp × S → W → Wit GE nR P.lin.kCol

/-- The statement is in order, and three values of the record are the plan's. -/
def inOrderK13 (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) (s : S) :
    Bool :=
  OnBytes.Means.tidy4B s.st && decide (s.st.codes = codes) &&
    decide (s.check.frame.shape = shape) && decide (s.check.rows.layout = layout)

/-- **THE LAYER.** -/
def fillK13 {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (Mg : Meaning Pp W) : Meaning Pp W :=
  { Mg with
    pile := fun x _ w => RowsTrue (D.rw x) x.2 w
    pileOne := fun x _ w => RowsTrue (D.rw x) x.2 w
    pub := pubK13C D.P D.codes D.N Mg.pub
    more := Mg.more.merge wSitsMore }

/-- **WHAT `fillK13` DOES NOT LAY, AS A LAYER OF ITS OWN**: "in order" gains
`inOrderK13`; the three names "K13.pileMasks", "K13.pileWithin", "K13.oneRow" are answered and stand
at the door; K13's block and W's commitment ask "K12.seatsCarried". -/
def fillK13Plus {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (Mg : Meaning Pp W) : Meaning Pp W :=
  { Mg with
    inOrder := fun x => Mg.inOrder x && inOrderK13 D.codes D.shape D.layout x.2
    pub := pubK13PlusC Mg.pub
    more := Mg.more.merge
      (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore))) }

section
variable {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (Mg : Meaning Pp W)

/-! ## 1 What it lays: by the make -/

theorem fillK13_pub : (fillK13 D Mg).pub = pubK13C D.P D.codes D.N Mg.pub := rfl

theorem fillK13_noneSent (a : Pp × S) : (fillK13 D Mg).pub .noneSent a = noneSentC D.N a.2 := rfl

theorem fillK13_indexIs (a : Pp × S) :
    (fillK13 D Mg).pub .indexIs a = indexIsC D.N.indexNo a.2 := rfl

theorem fillK13_indexThere (a : Pp × S) : (fillK13 D Mg).pub .indexThere a = indexThereC a.2 := rfl

theorem fillK13_frontOk (a : Pp × S) : (fillK13 D Mg).pub .frontOk a = frontOkC D.P a.2 := rfl

theorem fillK13_evalLaid (a : Pp × S) : (fillK13 D Mg).pub .evalLaid a = evalLaidC D.P a.2 := rfl

theorem fillK13_wSits (a : Pp × S) : (fillK13 D Mg).pub wSitsItem a =
    (wSitsC D.codes D.P a.2 && wSeatC D.N.w a.2) := rfl

theorem fillK13_inOrder : (fillK13 D Mg).inOrder = Mg.inOrder := rfl

theorem fillK13_more : (fillK13 D Mg).more = Mg.more.merge wSitsMore := rfl

theorem fillK13_pile (x : Pp × S) (y : Strs) (w : W) :
    (fillK13 D Mg).pile x y w ↔ RowsTrue (D.rw x) x.2 w := Iff.rfl

theorem fillK13_pileOne (x : Pp × S) (y : Strs) (w : W) :
    (fillK13 D Mg).pileOne x y w ↔ RowsTrue (D.rw x) x.2 w := Iff.rfl

/-! ## 2 What it leaves -/

/-- Every other public item is handed on. -/
theorem fillK13_else (q : Pub) (h : k13ItemC q = false) (a : Pp × S) :
    (fillK13 D Mg).pub q a = Mg.pub q a := pubK13C_else D.P D.codes D.N Mg.pub q h a

theorem fillK13_fields : (fillK13 D Mg).pin = Mg.pin ∧ (fillK13 D Mg).noColl = Mg.noColl ∧
    (fillK13 D Mg).shown = Mg.shown ∧ (fillK13 D Mg).held = Mg.held ∧
    (fillK13 D Mg).pinW = Mg.pinW ∧ (fillK13 D Mg).decodes = Mg.decodes ∧
    (fillK13 D Mg).pubP = Mg.pubP :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3 The layer of what `fillK13` does not lay -/

theorem fillK13Plus_pileMasks (a : Pp × S) :
    (fillK13Plus D Mg).pub pileMasksItem a = pileMasksC a.2 := rfl

theorem fillK13Plus_pileWithin (a : Pp × S) :
    (fillK13Plus D Mg).pub pileWithinItem a = pileWithinC a.2 := rfl

theorem fillK13Plus_oneRow (a : Pp × S) : (fillK13Plus D Mg).pub oneRowItem a = oneRowC a.2 := rfl

theorem fillK13Plus_inOrder (a : Pp × S) : (fillK13Plus D Mg).inOrder a =
    (Mg.inOrder a && inOrderK13 D.codes D.shape D.layout a.2) := rfl

theorem fillK13Plus_more : (fillK13Plus D Mg).more = Mg.more.merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore))) := rfl

theorem fillK13Plus_else (q : Pub) (h : k13PlusItemC q = false) (a : Pp × S) :
    (fillK13Plus D Mg).pub q a = Mg.pub q a := pubK13PlusC_else Mg.pub q h a

/-- Over the layer, what it lays stands as it lays it. -/
theorem fillK13Plus_over (x : Pp × S) (y : Strs) (w : W) :
    ((fillK13Plus D (fillK13 D Mg)).pile x y w ↔ RowsTrue (D.rw x) x.2 w) ∧
      ((fillK13Plus D (fillK13 D Mg)).pileOne x y w ↔ RowsTrue (D.rw x) x.2 w) ∧
      (fillK13Plus D (fillK13 D Mg)).pub .noneSent x = noneSentC D.N x.2 ∧
      (fillK13Plus D (fillK13 D Mg)).pub .indexIs x = indexIsC D.N.indexNo x.2 ∧
      (fillK13Plus D (fillK13 D Mg)).pub .indexThere x = indexThereC x.2 ∧
      (fillK13Plus D (fillK13 D Mg)).pub .frontOk x = frontOkC D.P x.2 ∧
      (fillK13Plus D (fillK13 D Mg)).pub .evalLaid x = evalLaidC D.P x.2 ∧
      (fillK13Plus D (fillK13 D Mg)).pub wSitsItem x =
        (wSitsC D.codes D.P x.2 && wSeatC D.N.w x.2) :=
  ⟨Iff.rfl, Iff.rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end VerifiableInference.Desc.K13.Law
