-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MgK13.lean: KIND K13's PREMISES ON THE TABLE's LETTERS, GATHERED IN ONE
STRUCTURE, AND WHAT THE KIND's TIE ASKS OF THE LETTERS (`FillM3`,
Johnson/Desc/K13/Law/AtTable.lean) OUT OF IT. Definitions, and a statement with its proof.
Why. The composing of the one filling asks of each kind: prove your kind's tie over a letter Mg,
under premises of the form "Mg's field is my sentence", gathered in one structure; the composing
then gives one lemma: these hold at the composed filling.
Main names:
  `MgK13`: THE STRUCTURE: each field says what one letter of Mg is: our layer's sentences
    (`Sentences`, at the reader through the record's own book, `rwBook`); six letters at the index
    masks' seat (`SigLetters`); the proximity test's three public items; "K13.pileMasks"; that
    `pubP` says nothing beside the Bool at these four.
  `PlanK13`: FIVE TESTS ON THE PLAN's VALUES (no letter of Mg in them).
  `knownK13`: the four public items of which this file shows that they ride past the block.
  `fillM3_at`: **`FillM3` at any list Q of riders that holds the proximity test's three.** BESIDE
    THE TWO STRUCTURES IT TAKES: two statements that are owed (`OwedSeed3`, `OwedPinsStay`:
    OwedSig.lean); two premises on the letters beneath (`SmpReads`: what the sample's reader reads
    of the record; the decoder reads the public part alone); that what other layers say of "in
    order" rides; and a rider's premise for every item of Q that is not one of the four.
What is not claimed. A member of `MgK13` or `PlanK13`. The premises named. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.Others3AtSig
import Johnson.Desc.K13.Law.PileMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB toTree)

/-- The four public items of which this file shows that they ride past kind K13's block. -/
def knownK13 : List Pub := [bookItem, seatsItem, shapesItem, pileMasksItem]

/-- **KIND K13's PREMISES ON THE LETTER Mg.** -/
structure MgK13 {Pp Xi Cells Tok : Type} {nR : ℕ} (P : Where) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (cs : Codes) (sh : Params.ReqShape)
    (ly : Params.ReqLayout) (rest : Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid) : Prop where
  ours : Sentences P cs sh ly N rest Mg (rwBook arr mat)
  sig : SigLetters N Mg cs G arr smp ms decT
  book : ∀ x, Mg.pub bookItem x = bookInOrderB 0 x.2.book x.2.roots
  seats : ∀ x, Mg.pub seatsItem x = seatsCarriedB L x.2.book
  shapes : ∀ x, Mg.pub shapesItem x = msgShapesB M x.2.st
  masks : ∀ x, Mg.pub pileMasksItem x = pileMasksC x.2
  quiet : ∀ q ∈ knownK13, ∀ x, Mg.pubP q x

/-- **THE TESTS ON THE PLAN's VALUES.** -/
structure PlanK13 (Pp : Type) (N : Numbers) (cs : Codes) (ms : List Mem) (M : List OracleShape)
    (L : K12.Door.Laid) : Prop where
  /-- the plan's list of seats has the index masks' seat at the index masks' number -/
  seat : (toTree L).places[N.indexNo]? = some N.index
  /-- the members at that seat have the shape that the plan's list of shapes has at that number -/
  shape : ∀ m ∈ ms, SitsAt m N.index.1 N.index.2 → M[N.indexNo]? = some (m.1.l.get m.2).1
  /-- that shape's mask code is in the list -/
  code : ∀ s, M[N.indexNo]? = some s → s.maskCode < cs.mask.size
  /-- the codes' message lengths are powers of two -/
  lengths : cs.lengthsOk = true
  /-- where the book stands as the plan says of a place, the plan's places name trees that are there
  -/
  below : ∀ (x : Pp × S) p, First.bookAt N p x.2 = true → seatsCarriedB L x.2.book = true →
    placesBelowB L x.2.book.place.size x.2.book.trees.size = true

/-- "In order" as our layer lays it gives the record's code table. -/
theorem codes_of_inOrderK13 {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout} {s : S}
    (h : inOrderK13 cs sh ly s = true) : s.st.codes = cs := by
  unfold inOrderK13 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-- **`FillM3` out of the two structures.** -/
theorem fillM3_at {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub)
    (hMg : MgK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) (hPl : PlanK13 Pp N cs ms M L)
    (hbIn : bookItem ∈ Q) (hsIn : seatsItem ∈ Q) (hmIn : shapesItem ∈ Q)
    (S1 : OwedSeed3) (S2 : OwedPinsStay)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true)
    (hR : ∀ q ∈ Q, q ∉ knownK13 → Rider3 Cl P Mg q) : FillM3 Cl P N Mg (rwBook arr mat) Q :=
  fillM3_of Q hMg.ours
    (others3_at_sig P arr mat N Mg Q cs G smp ms decT M L hMg.sig
      (fun x h => by
        rw [hMg.ours.inOrder, Bool.and_eq_true] at h
        exact codes_of_inOrderK13 h.2)
      hbIn hsIn hmIn hMg.book hMg.seats hMg.shapes
      (fun x h => by rw [hMg.ours.indexIs] at h; exact h)
      (fun x h => by rw [hMg.ours.indexThere] at h; exact h)
      hPl.seat hPl.shape hPl.code hPl.lengths hPl.below S1 S2 hsmp hdec)
    hrest fun q hq => by
      by_cases hk : q ∈ knownK13
      · have hP := hMg.quiet q hk
        simp only [knownK13, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · exact rider3_book (ft := 0) hMg.book hP
        · exact rider3_seats (L := toTree L) hMg.seats hP
        · exact rider3_shapes hMg.shapes hP
        · exact rider3_pileMasks hMg.masks hP
      · exact hR q hq hk

end VerifiableInference.Desc.K13.Law
