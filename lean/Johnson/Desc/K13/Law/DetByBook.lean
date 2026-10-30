-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/DetByBook.lean: INSIDE THE PROMISE THE TWO PINS FIX WHAT THE ROWS ON THE
TABLE READ (`FillM3.det`, Johnson/Desc/K13/Law/AtTable.lean), AT THE READER THROUGH THE RECORD's
OWN BOOK, CUT TO THE TABLE (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean), AND AT PINS OF THE
FORM IN WHICH OTHER FILES HAVE FILLED THEM (`pinJT`, `pinWOf`:
Johnson/Desc/Sound/MeaningSig.lean). Statements with their proofs.
Main names:
  `tabs_of_pins`: two witnesses that are pinned at one seat, at one record and strings: a member
    sits there, and their tables at that seat agree at every mask row below the shape's mask rows
    and every place below the mask code's message length: by `pinAt_one` ("a pin is
    functional").
  `ranges_one`: the reader's ranges are these: at a message of the shape sh the statement's real
    mask rows are sh's, and the places that its bits index are the mask code's message length,
    where that length is a power of two.
  `det_by_book`: **THE CLAUSE.** Premises: what the letters say (the pins; the proximity test's
    three items; our two; "in order" gives the record's code table); FIVE TESTS ON THE PLAN: the
    plan's list of seats has `N.index` at `N.indexNo`; the members at `N.index` have the shape
    that the plan's list of shapes has there; that shape's mask code is in the list; the codes'
    lengths are powers of two; the plan's places name trees that are there.
What is not claimed. These premises at any filling. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K13.Law.RidersK12
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open OnBytes.Means (realRows)
open Johnson.Pack (sigOf pMask)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt pinJT pinAt_one msgsOf)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB toTree
  msgShape_at)

/-- **Two witnesses that are pinned at one seat** have tables that agree inside the ranges. -/
theorem tabs_of_pins {A Xi Cells Tok : Type} (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a : A) (y : Strs) (w w' : Desc.Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp ms j t a y w) (h' : pinJT cs G arr smp ms j t a y w') :
    ∃ x ∈ ms, SitsAt x j t ∧ ∀ row place, row < (x.1.l.get x.2).1.maskRows →
      place < (pMask cs (x.1.l.get x.2).1).ell →
      w.tab cs (x.1.l.get x.2).1 (arr j t) j t true row place =
        w'.tab cs (x.1.l.get x.2).1 (arr j t) j t true row place := by
  obtain ⟨⟨x, hx, hs⟩, hall⟩ := h
  have e := pinAt_one cs G arr smp x a y w w' (hall x hx hs) (h'.2 x hx hs)
  refine ⟨x, hx, hs, fun row place hr hp => ?_⟩
  have e1 := congrFun e (Sum.inr (⟨row, hr⟩, ⟨place, hp⟩))
  have hs' : x.1.seat x.2 = (j, t) := hs
  simpa [msgsOf, hs'] using e1

/-- **The reader's ranges are the pins'.** -/
theorem ranges_one (st : Statement) (o : ℕ) (sh : OracleShape)
    (hx : (st.oracles[o]?).map (·.shape) = some sh) (hl : st.codes.lengthsOk = true)
    (hc : sh.maskCode < st.codes.mask.size) (row place : ℕ) (hr : row < realRows st o .mask)
    (hp : place < 2 ^ st.placeBits o .mask) :
    row < sh.maskRows ∧ place < (pMask st.codes sh).ell := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hx
  unfold realRows at hr
  rw [ha] at hr
  have hr' : row < a.shape.maskRows := hr
  refine ⟨hr', ?_⟩
  unfold Statement.placeBits at hp
  rw [ha] at hp
  have h0 : (a.shape.rows .mask == 0) = false := by
    have : a.shape.rows .mask = a.shape.maskRows := rfl
    rw [this]
    exact beq_false_of_ne (by omega)
  simp only [h0] at hp
  have hpow : powerOfTwo (st.codes.mask.getD a.shape.maskCode default).ell = true := by
    unfold Codes.lengthsOk at hl
    rw [Bool.and_eq_true] at hl
    have := Array.all_eq_true.1 hl.2 a.shape.maskCode hc
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc]
    exact this
  unfold powerOfTwo at hpow
  rw [Bool.and_eq_true] at hpow
  have e : 2 ^ ceilLog2 (st.codes.mask.getD a.shape.maskCode default).ell =
      (st.codes.mask.getD a.shape.maskCode default).ell := eq_of_beq hpow.2
  have hp' : place < 2 ^ ceilLog2 (st.codes.mask.getD a.shape.maskCode default).ell := hp
  rw [e] at hp'
  exact hp'

/-- **THE CLAUSE `det`**, at the reader through the record's own book and at pins of that form. -/
theorem det_by_book {Pp Xi Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (N : Numbers)
    (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (Q : List Pub) (cs : Codes) (G : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (M : List OracleShape) (L : K12.Door.Laid)
    -- what the letters say
    (hpin : ∀ x y w, Mg.pin N.index.1 N.index.2 x y w →
      pinJT cs G arr smp ms N.index.1 N.index.2 x y w)
    (hpinW : ∀ x y w, Mg.pinW x y w → decT y.cell x = some w.cells)
    (hcodes : ∀ x, Mg.inOrder x = true → x.2.st.codes = cs)
    (hbIn : bookItem ∈ Q) (hsIn : seatsItem ∈ Q) (hmIn : shapesItem ∈ Q)
    (hB : ∀ x, Mg.pub bookItem x = bookInOrderB 0 x.2.book x.2.roots)
    (hSe : ∀ x, Mg.pub seatsItem x = seatsCarriedB L x.2.book)
    (hSh : ∀ x, Mg.pub shapesItem x = msgShapesB M x.2.st)
    (hI : ∀ x, Mg.pub .indexIs x = true → K1.indexIsB N.indexNo x.2 = true)
    (hT : ∀ x, Mg.pub .indexThere x = true → K1.indexThereB x.2 = true)
    -- tests on the plan
    (hL : (toTree L).places[N.indexNo]? = some N.index)
    (hshape : ∀ m ∈ ms, SitsAt m N.index.1 N.index.2 → M[N.indexNo]? = some (m.1.l.get m.2).1)
    (hcode : ∀ sh, M[N.indexNo]? = some sh → sh.maskCode < cs.mask.size)
    (hlen : cs.lengthsOk = true)
    (hbelow : ∀ (x : Pp × S) p, First.bookAt N p x.2 = true → seatsCarriedB L x.2.book = true →
      placesBelowB L x.2.book.place.size x.2.book.trees.size = true)
    (x : Pp × S) (y : Strs) (p : Option Place) (w w' : Desc.Wit Cells Tok MsgT)
    (hQ : ∀ q ∈ Q, Mg.pub q x = true) (hii : Mg.pub .indexIs x = true)
    (hit : Mg.pub .indexThere x = true) (hbk : First.bookAt N p x.2 = true)
    (hin : Mg.inOrder x = true) (hw : Mg.pinW x y w) (hw' : Mg.pinW x y w')
    (hp : Mg.pin N.index.1 N.index.2 x y w) (hp' : Mg.pin N.index.1 N.index.2 x y w') :
    AgreeAt x.2.out.indexMasks (rwBook arr mat x w) (rwBook arr mat x w') := by
  have h₁ : msgShapesB M x.2.st = true := by rw [← hSh]; exact hQ _ hmIn
  have h₂ : bookInOrderB 0 x.2.book x.2.roots = true := by rw [← hB]; exact hQ _ hbIn
  have h₃ : seatsCarriedB L x.2.book = true := by rw [← hSe]; exact hQ _ hsIn
  have hseat : x.2.book.place[x.2.out.indexMasks]? = some N.index :=
    eq_of_beq (seat_in_hand N Mg (toTree L) Q hsIn (fun z hz => by rw [hSe] at hz; exact hz) hI hT
      hL x p hQ hii hit hbk)
  have hidx : x.2.out.indexMasks = N.indexNo := eq_of_beq (hI x hii)
  have hthere : x.2.out.indexMasks < x.2.st.oracles.size := by
    have := hT x hit
    unfold K1.indexThereB at this
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at this
    cases this
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hcs := hcodes x hin
  obtain ⟨m, hm, hsit, htab⟩ := tabs_of_pins cs G arr smp ms N.index.1 N.index.2 x y w w'
    (hpin x y w hp) (hpin x y w' hp')
  have hcell : w.cells = w'.cells :=
    Option.some.inj ((hpinW x y w hw).symm.trans (hpinW x y w' hw'))
  refine agree_in_ranges arr mat N M L x.1 x.2 h₁ h₂ h₃ hbk'.1.2 (hbelow x p hbk h₃) hthere hseat
    w w' (by rw [hcell]) fun sh hsh row place hr hpl => ?_
  rw [hidx] at hsh
  obtain rfl : sh = (m.1.l.get m.2).1 := Option.some.inj (hsh.symm.trans (hshape m hm hsit))
  have hx : (x.2.st.oracles[x.2.out.indexMasks]?).map (·.shape) = some (m.1.l.get m.2).1 := by
    rw [msgShape_at h₁ _ hthere, hidx]
    exact hsh
  obtain ⟨a1, a2⟩ := ranges_one x.2.st _ _ hx (by rw [hcs]; exact hlen)
    (by rw [hcs]; exact hcode _ hsh) row place hr hpl
  rw [hcs] at a2 ⊢
  exact htab row place a1 a2

end VerifiableInference.Desc.K13.Law
