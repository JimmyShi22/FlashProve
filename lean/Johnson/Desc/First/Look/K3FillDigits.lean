-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3FillDigits.lean: the kind "lookup" (K3): ITS LAYER OF THE FILLING OF THE
TABLE OF JOINTS' MEANING: THE ITEM constr m lookDigits (the table's own inner item: what the lookup
on the digits of a link's smallness test proves of the witness): digitsPartK3 X D L: a value for the
letter digitsPart of the model's relation's layer; fillK3Digits: the same as a layer of its own;
fDig, the digits' rows' premise on that item, at both. AND TWO LIGHT SENTENCES in the place of two
premises under a yes: where «in order» reads the statement, the chain's check and the request alone,
and «held» the statement and the book alone, both ride over SameBut. Definitions, statements,
proofs. NO SOUNDNESS IS CLAIMED.

Main names.
  digitsPartK3 X D L m a y w: at digAt X m's (x, tl): DgP.DigIn tl (enOf x.arrays) (digMu x D L.rad
    ‹L's seats› L.arr w): every entry of the smallness test's digits' arrays, read off the witness's
    messages, is a digit. WHERE digAt X m ANSWERS NOTHING: False (so that nobody can spend what no
    law proves).
  fDig_part: the rows' fDig at that value. fillK3Digits, fDig_fill, fillDigits_other: the layer,
    fDig at it, every other part and segment's sentence left as it was.
  InOrderReads Mg, HeldReads Mg; inOrder_sameBut, held_sameBut.
OBJECT. No block's text: Meaning.constr (Johnson/Desc/First/Borders.lean) at Part.lookDigits;
Meaning.inOrder, Meaning.held.
USER. The composed term's letter digitsPart; fDig, hIn, hHeld of k3_digits_seatLaws_term
(K3DigitsAtTerm.lean). WHO SPENDS THE ITEM (the smallness test's row) must read the same sentence:
not shown. Nobody yet.
LETTERS. X, D, L, Mg.
IS IT EMPTY? Props on a witness: nothing to run. InOrderReads, HeldReads: shown at no filling here.
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. L is a letter. Nothing on who opens or spends the item.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3FillWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)

section
variable {P Cells Tok : Type} (X : Verify.Public) (D : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok)

/-- **WHAT constr m lookDigits SAYS.** -/
def digitsPartK3 (m : ℕ) (_a : P × Desc.First.S) (_y : Strs) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  match digAt X m with
  | some v =>
    DgP.DigIn v.2 (enOf v.1.arrays)
      (digMu v.1 D L.rad (fun j => L.seat v.1.link true j.1) L.arr w)
  | none => False

/-- **fDig at that value.** -/
theorem fDig_part (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : DgP.DigIn tl (enOf x.arrays)
      (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w)) :
    digitsPartK3 X D L m a y w := by
  unfold digitsPartK3
  rw [hx]
  exact h

/-- And back: what whoever spends the item has in hand. -/
theorem digitsPart_at (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) (h : digitsPartK3 X D L m a y w) :
    DgP.DigIn tl (enOf x.arrays)
      (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w) := by
  unfold digitsPartK3 at h
  rw [hx] at h
  exact h

variable (Mg : Meaning P (Desc.Wit Cells Tok MsgT))

/-- **The item's layer.** -/
def fillK3Digits : Meaning P (Desc.Wit Cells Tok MsgT) :=
  { Mg with
    constr := fun m p a y w =>
      if p = .lookDigits then digitsPartK3 X D L m a y w else Mg.constr m p a y w }

theorem fDig_fill (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : DgP.DigIn tl (enOf x.arrays)
      (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w)) :
    (fillK3Digits X D L Mg).constr m .lookDigits a y w := by
  show if (Desc.First.Part.lookDigits = .lookDigits) then digitsPartK3 X D L m a y w
    else Mg.constr m .lookDigits a y w
  rw [if_pos rfl]
  exact fDig_part X D L m hx a y w h

theorem fillDigits_other (m : ℕ) (p : Desc.First.Part) (hp : p ≠ .lookDigits)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    (fillK3Digits X D L Mg).constr m p a y w = Mg.constr m p a y w := by
  show (if p = .lookDigits then digitsPartK3 X D L m a y w else Mg.constr m p a y w) = _
  rw [if_neg hp]

end

/-! ## Two light sentences on a meaning -/

section
variable {P W : Type}

/-- "In order" reads the statement, the chain's own check and the request's words alone. -/
def InOrderReads (Mg : Meaning P W) : Prop :=
  ∀ (z : P) (s t : Desc.First.S), t.st = s.st → t.check = s.check → t.req = s.req →
    Mg.inOrder (z, t) = Mg.inOrder (z, s)

/-- "Held" reads the statement and the book alone. -/
def HeldReads (Mg : Meaning P W) : Prop :=
  ∀ (j k : ℕ) (z : P) (s t : Desc.First.S), t.st = s.st → t.book = s.book →
    Mg.held j k (z, t) = Mg.held j k (z, s)

theorem inOrder_sameBut {Mg : Meaning P W} (hR : InOrderReads Mg) {s t : Desc.First.S}
    (T : SameBut s t) (z : P) (h : Mg.inOrder (z, s) = true) : Mg.inOrder (z, t) = true := by
  rw [hR z s t T.st T.check T.req]
  exact h

theorem held_sameBut {Mg : Meaning P W} (hR : HeldReads Mg) {s t : Desc.First.S}
    (T : SameBut s t) (j k : ℕ) (z : P) (h : Mg.held j k (z, s) = true) :
    Mg.held j k (z, t) = true := by
  rw [hR j k z s t T.st T.book]
  exact h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.fDig_part
#print axioms VerifiableInference.OnPublicFiles.digitsPart_at
#print axioms VerifiableInference.OnPublicFiles.fDig_fill
#print axioms VerifiableInference.OnPublicFiles.fillDigits_other
#print axioms VerifiableInference.OnPublicFiles.inOrder_sameBut
#print axioms VerifiableInference.OnPublicFiles.held_sameBut
