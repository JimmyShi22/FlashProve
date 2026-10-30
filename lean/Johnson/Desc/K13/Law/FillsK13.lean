-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillsK13.lean: KIND K13's PREMISES ON THE TABLE's LETTERS, IN ONE STRUCTURE,
IN A LIGHT FILE: over our layer's own files, the reader, and other light files alone.
A definition; no theorem. The law that spends it stands elsewhere
(Johnson/Desc/K13/Law/MgK13.lean).
Why. In the composing of the one filling each kind gets one lemma: "your premises hold at the
composed filling". Its file must import the composed filling and the file that holds the
structure: so the structure stands apart from the laws' cone. Each field says what ONE LETTER of
Mg is, in the names of the layer that lays it: at that layer it holds by the make.
  `FillsK13`: `pile`, `pileOne`: "all rows on the table are true" at the reader `rwBook arr mat`;
    `frontOk`, `evalLaid`, `wSits`, `indexIs`, `indexThere`, `masks`, `within`, `oneRow`: our
    layer's tests as code
    (Johnson/Desc/K13/PubK13.lean); `inOrder`: what other layers say of it (rest) and `inOrderK13`;
    `book`, `seats`, `shapes`: the proximity test's three (Johnson/Desc/K12/Door/); `held`, `shown`,
    `noColl`, `pin` AT THE INDEX MASKS' SEAT, `pinW`, `decodes`: the six letters of
    Johnson/Desc/Sound/MeaningSig.lean; `quiet`: `pubP` says nothing beside the Bool at nine items.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillK13
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem pinJT noCollJT shownJT pinWOf decodesOf)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB)

/-- The nine public items at which `pubP` is asked to say nothing beside the Bool. -/
def quietK13 : List Pub :=
  [.frontOk, .evalLaid, wSitsItem, pileMasksItem, pileWithinItem, oneRowItem,
    First.moreItem K12.Door.nBook,
    First.moreItem K12.Door.nSeats, First.moreItem K12.Door.nShapes]

/-- **KIND K13's PREMISES ON THE LETTER Mg**, each in the names of the layer that lays it. -/
structure FillsK13 {Pp Xi Cells Tok : Type} {nR : ℕ} (P : Where) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (rest : Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid) : Prop where
  pile : ∀ x y w, Mg.pile x y w ↔ RowsTrue (rwBook arr mat x) x.2 w
  pileOne : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rwBook arr mat x) x.2 w
  frontOk : ∀ x, Mg.pub .frontOk x = frontOkC P x.2
  evalLaid : ∀ x, Mg.pub .evalLaid x = evalLaidC P x.2
  wSits : ∀ x, Mg.pub wSitsItem x = (wSitsC cs P x.2 && wSeatC N.w x.2)
  indexIs : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2
  indexThere : ∀ x, Mg.pub .indexThere x = indexThereC x.2
  masks : ∀ x, Mg.pub pileMasksItem x = pileMasksC x.2
  within : ∀ x, Mg.pub pileWithinItem x = pileWithinC x.2
  oneRow : ∀ x, Mg.pub oneRowItem x = oneRowC x.2
  inOrder : ∀ x, Mg.inOrder x = (rest x && inOrderK13 cs sh ly x.2)
  book : ∀ x, Mg.pub (First.moreItem K12.Door.nBook) x = bookInOrderB 0 x.2.book x.2.roots
  seats : ∀ x, Mg.pub (First.moreItem K12.Door.nSeats) x = seatsCarriedB L x.2.book
  shapes : ∀ x, Mg.pub (First.moreItem K12.Door.nShapes) x = msgShapesB M x.2.st
  held : ∀ x, Mg.held N.index.1 N.index.2 x = smpHeld x.2.st x.2.book N.index.1 N.index.2
  shown : ∀ y, Mg.shown N.index.1 N.index.2 y ↔ shownJT cs G ms N.index.1 N.index.2 y
  noColl : ∀ x y, Mg.noColl N.index.1 N.index.2 x y ↔
    noCollJT cs G smp ms N.index.1 N.index.2 x y
  pin : ∀ x y w, Mg.pin N.index.1 N.index.2 x y w ↔
    pinJT cs G arr smp ms N.index.1 N.index.2 x y w
  pinW : ∀ x y w, Mg.pinW x y w ↔ pinWOf decT x y w
  decodes : ∀ x y, Mg.decodes x y ↔ decodesOf decT x y
  quiet : ∀ q ∈ quietK13, ∀ x, Mg.pubP q x

end VerifiableInference.Desc.K13.Law
