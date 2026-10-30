-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillsK13C.lean: KIND K13's PREMISES ON THE TABLE's LETTERS AT A FILLING FROM
WHICH THE NAMES THAT ONLY CARRY A FACT ON THE VERIFIER's STATE HAVE BEEN STRUCK, IN ONE LIGHT
STRUCTURE; and that it gives the elder structure (`FillsK13`, Johnson/Desc/K13/Law/FillsK13.lean)
at the wider filling `plus13` (Johnson/Desc/K13/Law/BridgeK13.lean). A definition, and statements
with their proofs. Why. In the composing of the one filling each kind gets one lemma: "your premises
hold at the composed filling". At the filling without the struck names these are the fields below:
thirteen equations on letters that stay, and that `pubP` says nothing beside the test at eleven
items. `FillsK13C`: `pile`, `pileOne`; the tests at frontOk, evalLaid, "K13.wSits", indexIs,
  indexThere; the six
    letters at the index masks' seat; `quiet`.
  `quietC`: the eleven items: the three that stay, and the eight that are laid over again.
  `fillsK13_plus`: **`FillsK13` at `plus13 D d Mg`**, with rest := Mg's own "in order", WHERE D's
  numbers, codes, shape and layout are the statement's, and the proximity test's data counts its
    trees from 0.
  `weights_plus`, `fits_plus`: what `plus13 D d Mg` says at "K13.weightsOk" and "K12.bookFits": by
  the make.
What is not claimed. A member of `FillsK13C`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillsK13
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem pinJT noCollJT shownJT pinWOf decodesOf)
open VerifiableInference.Desc.K12.Door (K12Data)

/-- The eleven items at which `pubP` is asked to say nothing beside the test. -/
def quietC : List Pub :=
  [.frontOk, .evalLaid, wSitsItem, pileMasksItem, pileWithinItem, oneRowItem,
    First.moreItem K12.Door.nBook, First.moreItem K12.Door.nSeats,
    First.moreItem K12.Door.nShapes, First.moreItem K12.Door.nFits,
    First.moreItem First.nWeights]

/-- **KIND K13's PREMISES ON THE LETTER Mg, at the narrower filling.** -/
structure FillsK13C {Pp Xi Cells Tok : Type} {nR : ℕ} (P : Where) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (cs : Codes) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) : Prop where
  pile : ∀ x y w, Mg.pile x y w ↔ RowsTrue (rwBook arr mat x) x.2 w
  pileOne : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rwBook arr mat x) x.2 w
  frontOk : ∀ x, Mg.pub .frontOk x = frontOkC P x.2
  evalLaid : ∀ x, Mg.pub .evalLaid x = evalLaidC P x.2
  wSits : ∀ x, Mg.pub wSitsItem x = (wSitsC cs P x.2 && wSeatC N.w x.2)
  indexIs : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2
  indexThere : ∀ x, Mg.pub .indexThere x = indexThereC x.2
  held : ∀ x, Mg.held N.index.1 N.index.2 x = smpHeld x.2.st x.2.book N.index.1 N.index.2
  shown : ∀ y, Mg.shown N.index.1 N.index.2 y ↔ shownJT cs G ms N.index.1 N.index.2 y
  noColl : ∀ x y, Mg.noColl N.index.1 N.index.2 x y ↔
    noCollJT cs G smp ms N.index.1 N.index.2 x y
  pin : ∀ x y w, Mg.pin N.index.1 N.index.2 x y w ↔
    pinJT cs G arr smp ms N.index.1 N.index.2 x y w
  pinW : ∀ x y w, Mg.pinW x y w ↔ pinWOf decT x y w
  decodes : ∀ x y, Mg.decodes x y ↔ decodesOf decT x y
  quiet : ∀ q ∈ quietC, ∀ x, Mg.pubP q x

section
variable {Pp Xi Cells Tok : Type} {nR : ℕ} {N : Numbers}
  {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {arr : ℕ → ℕ → ℕ} {G : FileDescription Xi} {ms : List Mem}
  {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  (D : DataK13 Pp (Desc.Wit Cells Tok MsgT) nR) (d : K12Data)

/-- **The elder structure at the wider filling.** -/
theorem fillsK13_plus {mat : Cells → Fin nR → (Fin D.P.lin.kCol → Bool) → GE}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf D.codes s.l).om i).Smp}
    (h : FillsK13C D.P N Mg D.codes arr mat G smp ms decT) (hft : d.ft = 0) :
    FillsK13 D.P N (plus13 D d Mg) D.codes D.shape D.layout Mg.inOrder arr mat G smp ms decT d.M
      d.L where
  pile := h.pile
  pileOne := h.pileOne
  frontOk := fun x => (plus13_hand D d Mg _ rfl x).trans (h.frontOk x)
  evalLaid := fun x => (plus13_hand D d Mg _ rfl x).trans (h.evalLaid x)
  wSits := fun x => (plus13_hand D d Mg _ rfl x).trans (h.wSits x)
  indexIs := fun x => (plus13_hand D d Mg _ rfl x).trans (h.indexIs x)
  indexThere := fun x => (plus13_hand D d Mg _ rfl x).trans (h.indexThere x)
  masks := fun _ => rfl
  within := fun _ => rfl
  oneRow := fun _ => rfl
  inOrder := fun _ => rfl
  book := fun x => by
    show K12.Door.atFirstBook d.ft x.2 = _
    rw [hft]
    rfl
  seats := fun _ => rfl
  shapes := fun _ => rfl
  held := h.held
  shown := h.shown
  noColl := h.noColl
  pin := h.pin
  pinW := h.pinW
  decodes := h.decodes
  quiet := fun q hq x => h.quiet q (by
    simp only [quietK13, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [quietC]) x

/-- What the wider filling says at "K13.weightsOk". -/
theorem weights_plus (x : Pp × S) :
    (plus13 D d Mg).pub (First.moreItem First.nWeights) x = First.weightsB x.2 := rfl

/-- And at "K12.bookFits". -/
theorem fits_plus (x : Pp × S) :
    (plus13 D d Mg).pub (First.moreItem K12.Door.nFits) x = Sound.bookFitsB x.2.book := rfl

end

end VerifiableInference.Desc.K13.Law
