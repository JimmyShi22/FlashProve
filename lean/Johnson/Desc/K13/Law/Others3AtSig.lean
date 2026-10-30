-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Others3AtSig.lean: WHAT STAYS AT KIND K13's BLOCK (`Others3`,
Johnson/Desc/K13/Law/FillFromSentences.lean), AT THE READER THROUGH THE RECORD's OWN BOOK AND AT SIX
LETTERS OF THE FORM IN WHICH OTHER FILES HAVE FILLED THEM (`meaningSig`,
Johnson/Desc/Sound/BordersFill.lean): all eight clauses, from named premises. A definition and a
statement with its proof.
  `SigLetters`: what the six letters say at the index masks' seat: "held" is `smpHeld`; "shown", "no
    collision", "pin" are `shownJT`, `noCollJT`, `pinJT`; "pinW" and "decodes" are `pinWOf` and
    `decodesOf` at a decoder decT. At `meaningSig` each holds by the make.
  `others3_at_sig`: **`Others3`.** `reader`: Reader3.lean. `det`: DetByBook.lean. The other six:
    from TWO STATEMENTS THAT ARE OWED (`OwedSeed3`, `OwedPinsStay`:
    Johnson/Desc/K13/Law/OwedSig.lean: they are premises here) and two premises on the letters
    beneath: the sample's reader smp reads of the record the public part, the book, the code table
    and each message's sample (`SmpReads`, SmpReads.lean); the decoder decT gives the same over a
    step of the block.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.DetByBook
import Johnson.Desc.K13.Law.Reader3
import Johnson.Desc.K13.Law.OwedSig
import Johnson.Desc.K13.Law.SigDecodes
import Johnson.Desc.K13.Law.SmpReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt pinJT noCollJT shownJT)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB toTree)

/-- **What the six letters say at the index masks' seat.** -/
structure SigLetters {Pp Xi Cells Tok : Type} (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) : Prop where
  held : ∀ x, Mg.held N.index.1 N.index.2 x = smpHeld x.2.st x.2.book N.index.1 N.index.2
  shown : ∀ y, Mg.shown N.index.1 N.index.2 y ↔ shownJT cs G ms N.index.1 N.index.2 y
  noColl : ∀ x y, Mg.noColl N.index.1 N.index.2 x y ↔
    noCollJT cs G smp ms N.index.1 N.index.2 x y
  pin : ∀ x y w, Mg.pin N.index.1 N.index.2 x y w ↔
    pinJT cs G arr smp ms N.index.1 N.index.2 x y w
  pinW : ∀ x y w, Mg.pinW x y w ↔ decT y.cell x = some w.cells
  decodes : ∀ x y, Mg.decodes x y ↔ (decT y.cell x).isSome = true

/-- **`Others3` at these letters and this reader.** -/
theorem others3_at_sig {Pp Cl Xi Cells Tok : Type} {nR : ℕ} (P : Where) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (Q : List Pub) (cs : Codes) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid) (hG : SigLetters N Mg cs G arr smp ms decT)
    (hcodes : ∀ x, Mg.inOrder x = true → x.2.st.codes = cs)
    (hbIn : bookItem ∈ Q) (hsIn : seatsItem ∈ Q) (hmIn : shapesItem ∈ Q)
    (hB : ∀ x, Mg.pub bookItem x = bookInOrderB 0 x.2.book x.2.roots)
    (hSe : ∀ x, Mg.pub seatsItem x = seatsCarriedB L x.2.book)
    (hSh : ∀ x, Mg.pub shapesItem x = msgShapesB M x.2.st)
    (hI : ∀ x, Mg.pub .indexIs x = true → K1.indexIsB N.indexNo x.2 = true)
    (hT : ∀ x, Mg.pub .indexThere x = true → K1.indexThereB x.2 = true)
    (hL : (toTree L).places[N.indexNo]? = some N.index)
    (hshape : ∀ m ∈ ms, SitsAt m N.index.1 N.index.2 → M[N.indexNo]? = some (m.1.l.get m.2).1)
    (hcode : ∀ sh, M[N.indexNo]? = some sh → sh.maskCode < cs.mask.size)
    (hlen : cs.lengthsOk = true)
    (hbelow : ∀ (x : Pp × S) p, First.bookAt N p x.2 = true → seatsCarriedB L x.2.book = true →
      placesBelowB L x.2.book.place.size x.2.book.trees.size = true)
    -- the two statements that are owed
    (S1 : OwedSeed3) (S2 : OwedPinsStay)
    -- the letters beneath
    (hsmp : SmpReads smp)
    (hdec : DecBlind decT) : Others3 Cl P N Mg (rwBook arr mat) Q where
  reader := fun x x' w h h0 => reader3 arr mat x x' w h h0
  held := fun x x' h h0 => by
    rw [hG.held] at h0 ⊢
    unfold smpHeld at h0 ⊢
    rw [S1 P x x' _ _ h]
    exact h0
  shown := fun y y' ho h0 =>
    (hG.shown y').2 (((S2 (A := Unit) (Cells := Cells) (Tok := Tok) cs G arr (fun _ _ _ => none) ms
      N.index.1 N.index.2 () () y y' ho.2 fun _ _ _ => rfl).1).1 ((hG.shown y).1 h0))
  noColl := fun x x' y y' h ho h0 =>
    (hG.noColl x' y').2 (((S2 (Cells := Cells) (Tok := Tok) cs G arr smp ms N.index.1 N.index.2 x x'
      y y' ho.2 fun m _ _ => smp_same_M3 hsmp h m).2.1).1 ((hG.noColl x y).1 h0))
  decodes := fun x x' y y' h hc h0 => by
    rw [hG.decodes] at h0 ⊢
    exact decodes_M3 hdec x x' y y' h hc h0
  pinWBack := fun x x' y y' w h hc h0 => by
    rw [hG.pinW] at h0 ⊢
    exact pinWBack_M3 hdec x x' y y' w h hc h0
  pinIBack := fun x x' y y' w h ho h0 =>
    (hG.pin x y w).2 (((S2 cs G arr smp ms N.index.1 N.index.2 x x' y y' ho.2
      fun m _ _ => smp_same_M3 hsmp h m).2.2 w).2 ((hG.pin x' y' w).1 h0))
  det := fun x y p w w' hQ hii hit hbk hin _ _ _ _ hw hw' hp hp' =>
    det_by_book arr mat N Mg Q cs G smp ms decT M L (fun x y w => (hG.pin x y w).1)
      (fun x y w => (hG.pinW x y w).1) hcodes hbIn hsIn hmIn hB hSe hSh hI hT hL hshape hcode hlen
      hbelow x y p w w' hQ hii hit hbk hin hw hw' hp hp'

end VerifiableInference.Desc.K13.Law
