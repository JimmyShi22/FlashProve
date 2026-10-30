-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_calls_mgAll: no parameters Dm are shown here that meet its five
premises on Dm's letters.
Johnson/Desc/Sound/MgAt/K3Rides.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll
(Johnson/Desc/Sound/MgAll.lean): WHAT RIDES PAST A SEATED LOOKUP ON A LINK's CALLS, SECOND FORM:
the five facts of the tight rule (ridesAtR_of_plain, Johnson/Desc/First/Look/K3RidesR.lean), each
against the composed meaning's own text of that field, over "the public part is the same, the two
states are SameBut, the strings stay below base". Statements and proofs. Ties of texts: no error
term. NO SOUNDNESS IS CLAIMED.

WHAT IS PAID OUTRIGHT: row (it reads the statement and the book) · pile (these, the pile in "out"
and the sort of "here").
WHAT IS PAID UNDER A NAMED PREMISE ON Dm's LETTERS: pinW: hDec: Dm.decT gives one thing at two
states that are SameBut · pinI: hSmp: Dm.smp keeps the samples of the members at the index's seat;
hj: that tree lies below base · constr: hDec; hReq: Dm.H.req likewise; hDig, hHead: Dm.digitsPart
k and Dm.headPart p i go back. WHO COULD PAY hHead: headPartK6_goesBack
(Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean), by report: SameBut keeps "out".

OBJECT: the composed meaning's fields row, pile, pinW, pin, constr.
Used by K3RidesLedger.lean, K3RidesDig.lean, K3RidesDigTight.lean and K3RidesDigStep.lean
  (Johnson/Desc/Sound/MgAt/).
LETTERS: Dm, Mg, base; Rch, k, q, b', a at the end.
IMPORTS:
  Johnson/Desc/First/Look/K3RidesR.lean,
  Johnson/Desc/Sound/MgAll.lean.
  Compiled with the whole library.
Main names:
  `rows_sameBut`: SameBut keeps S.rows. `classRows_same`: classRows reads the statement and the
    book.
  `wordOf_stays`, `pinAt_stays`, `pinJT_stays`: a pin reads the strings at its own tree alone.
  `constrQAt_back_all`: the meant sentence goes back, in all three of its arms.
  `mgAll_row_back`, `mgAll_pile_back`, `mgAll_pinW_back`, `mgAll_pin_back`, `mgAll_constr_back`.
  `ridesAtR_calls_mgAll`: THE END.

Limits. At the calls alone. The arm of constrQAt_back_all at k ≠ hd, p ≠ lookDigits is another
file's lemma in other words (constrQAt_back, Johnson/Desc/Sound/ConstrRides.lean).
mgAll_row_back stands where the statement and the book are the same;
rowSaysFirst_back (Johnson/Desc/First/Close/Law/FillRowRides.lean) is the wider rule.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3RidesR
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice Fo.Peel
open _root_.Run (ckP)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start flatPlacesOf)
open VerifiableInference.OnPublicFiles (SameBut relOf RidesAtR ridesAtR_of_plain headLink)
open Johnson.Desc.First.Walk.Tied (Stays)

/-! ## 1 Tools -/

/-- SameBut keeps the rows on the table. -/
theorem rows_sameBut {s s' : First.S} (h : SameBut s s') : s'.rows = s.rows := by
  rcases h.sort with ⟨a, a', e, e'⟩ | ⟨a, a', e, e'⟩ | ⟨a, a', e, e', -, -⟩ <;>
    simp only [First.S.rows, e, e', h.out]

/-- The rows of a class read the statement and the book. -/
theorem classRows_same (N : Numbers) (m : ℕ) (c : First.RowClass) {s s' : First.S}
    (h1 : s'.st = s.st) (h2 : s'.book = s.book) :
    First.classRows N m c s' = First.classRows N m c s := by
  unfold First.classRows
  rw [h1, h2]

section
variable {Xi : Type} (G : FileDescription Xi)

/-- The committed word of a tenant reads the strings at its own tree. -/
theorem wordOf_stays {y y' : Strs} {j : ℕ} (h : ∀ u, y'.col j u = y.col j u) (t : ℕ) :
    wordOf G y' j t = wordOf G y j t := by
  funext u
  unfold wordOf
  rw [h u]

variable (cs : OnBytes.Codes) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- A member's pin reads the strings at its own tree, and the state through its sample. -/
theorem pinAt_stays (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (smp : A → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp) (i : Fin l.length)
    {a b : A} {y y' : Strs} (hc : ∀ u, y'.col (seat i).1 u = y.col (seat i).1 u)
    (hs : smp b i = smp a i) (w : Wit Cells Tok MsgT)
    (h : PinAt G cs l seat smp arr i b y' w) : PinAt G cs l seat smp arr i a y w := by
  have e0 := wordOf_stays G hc (seat i).2
  have e1 : wordsOf G cs l seat y' i = wordsOf G cs l seat y i := by
    unfold wordsOf
    funext p
    cases p <;> simp only [wordAt, e0]
  unfold PinAt ShownAt at h ⊢
  rw [e0, e1, hs] at h
  exact h

/-- So does the pin of a seat. -/
theorem pinJT_stays
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) {a b : A} {y y' : Strs} (hc : ∀ u, y'.col j u = y.col j u)
    (hs : ∀ x ∈ ms, SitsAt x j t → smp b x.1 x.2 = smp a x.1 x.2) (w : Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp ms j t b y' w) : pinJT cs G arr smp ms j t a y w := by
  refine ⟨h.1, fun x hx hx' => ?_⟩
  have e : (x.1.seat x.2).1 = j := by
    have e' : x.1.seat x.2 = (j, t) := hx'
    rw [e']
  exact pinAt_stays G cs arr x.1.l x.1.seat (fun z => smp z x.1) x.2 (by rw [e]; exact hc)
    (hs x hx hx') w (h.2 x hx hx')

end

section
variable {X : OnBytes.Model.Verify.Public} {P W : Type} {rows cols : ℕ}

/-- **The meant sentence goes back, in all three of its arms.** -/
theorem constrQAt_back_all (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq) (H : P5J.HidAt X P W rows cols)
    (headPart : P5J.TPart → IdxQ → P × P5J.TS → Strs → W → Prop)
    (digitsPart : ℕ → P × P5J.TS → Strs → W → Prop) (k : ℕ) (p : P5J.TPart)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hreq : ∀ a y b y', rel a y b y' → H.req a = H.req b)
    (hdec : ∀ a y b y', rel a y b y' → H.dec a y = H.dec b y')
    (hDig : GoesBack rel (digitsPart k)) (hHead : ∀ i, GoesBack rel (headPart p i)) :
    GoesBack rel (P5J.constrQAt hd put H headPart digitsPart k p) := by
  intro a y b y' w hr h
  unfold P5J.constrQAt at h ⊢
  by_cases hp : p = .lookDigits
  · rw [if_pos hp] at h ⊢
    exact hDig a y b y' w hr h
  · rw [if_neg hp] at h ⊢
    refine ⟨h.1, fun M i hM hH => ?_⟩
    have h2 := h.2 M i (by rw [← hdec a y b y' hr]; exact hM) hH
    by_cases hk : k = hd
    · rw [if_pos hk] at h2 ⊢
      exact hHead i a y b y' w hr h2
    · rw [if_neg hk] at h2 ⊢
      rw [hreq a y b y' hr]
      exact h2

end

/-! ## 2 The five facts at the composed meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (base : ℕ)

/-- **row.** -/
theorem mgAll_row_back (m : ℕ) (c : First.RowClass) :
    GoesBack (relOf SameBut base) ((mgAll Dm Mg).row m c) := by
  rw [mgAll_row, First.fillRowFirst_row]
  intro a y b y' w hr hb
  obtain ⟨-, hs, -⟩ := hr
  unfold First.rowSays First.wordsAtFirst at hb ⊢
  rw [classRows_same Dm.N m c hs.st hs.book, hs.st, hs.book] at hb
  exact hb

/-- **pile.** -/
theorem mgAll_pile_back : GoesBack (relOf SameBut base) (mgAll Dm Mg).pile := by
  rw [mgAll_pile]
  intro a y b y' w hr hb
  obtain ⟨-, hs, -⟩ := hr
  have e : Dm.rw13 b = Dm.rw13 a := by
    funext w'
    unfold MgData.rw13 K13.Law.rwBook
    rw [hs.st, hs.book]
  have hb' : K13.Law.RowsTrue (Dm.rw13 b) b.2 w := hb
  show K13.Law.RowsTrue (Dm.rw13 a) a.2 w
  rw [e] at hb'
  unfold K13.Law.RowsTrue at hb' ⊢
  rw [rows_sameBut hs] at hb'
  exact hb'

variable (hDec : ∀ c (z : P) s s', SameBut s s' → Dm.decT c (z, s) = Dm.decT c (z, s'))
include hDec

/-- **pinW.** -/
theorem mgAll_pinW_back : GoesBack (relOf SameBut base) (mgAll Dm Mg).pinW := by
  rw [mgAll_pinW]
  intro a y b y' w hr hb
  obtain ⟨z, s⟩ := a
  obtain ⟨z', s'⟩ := b
  obtain ⟨e, hs, hy⟩ := hr
  have e' : z = z' := e
  subst e'
  have ec : y'.cell = y.cell := funext hy.1
  unfold pinWOf at hb ⊢
  rw [ec, ← hDec y.cell z s s' hs] at hb
  exact hb

/-- **constr.** -/
theorem mgAll_constr_back
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s')) (m : ℕ)
    (p : First.Part) (hDig : GoesBack (relOf SameBut base) (Dm.digitsPart m))
    (hHead : ∀ i, GoesBack (relOf SameBut base) (Dm.headPart p i)) :
    GoesBack (relOf SameBut base) ((mgAll Dm Mg).constr m p) := by
  rw [mgAll_constr]
  refine constrQAt_back_all (headLink X) Dm.put (oneDec Dm.decT Dm.H) Dm.headPart Dm.digitsPart m
    p _ ?_ ?_ hDig hHead
  · rintro ⟨z, s⟩ y ⟨z', s'⟩ y' ⟨e, hs, -⟩
    have e' : z = z' := e
    subst e'
    exact hReq z s s' hs
  · rintro ⟨z, s⟩ y ⟨z', s'⟩ y' ⟨e, hs, hy⟩
    have e' : z = z' := e
    subst e'
    have ec : y'.cell = y.cell := funext hy.1
    show Dm.decT y.cell (z, s) = Dm.decT y'.cell (z, s')
    rw [ec]
    exact hDec y.cell z s s' hs

omit hDec in
/-- **pin**, at a tree below base. -/
theorem mgAll_pin_back (j t : ℕ) (hj : j < base)
    (hSmp : ∀ (z : P) s s', SameBut s s' → ∀ x ∈ Dm.ms, SitsAt x j t →
      Dm.smp (z, s') x.1 x.2 = Dm.smp (z, s) x.1 x.2) :
    GoesBack (relOf SameBut base) ((mgAll Dm Mg).pin j t) := by
  rw [mgAll_pin]
  rintro ⟨z, s⟩ y ⟨z', s'⟩ y' w ⟨e, hs, hy⟩ hb
  have e' : z = z' := e
  subst e'
  exact pinJT_stays Dm.G Dm.cs Dm.arr Dm.smp Dm.ms j t (fun u => hy.2 j u hj) (hSmp z s s' hs) w hb

/-! ## 3 The end -/

/-- **WHAT RIDES PAST A LOOKUP ON THE CALLS, SECOND FORM, AT THE COMPOSED MEANING.** -/
theorem ridesAtR_calls_mgAll {Cl : Type} {Fr : Frame}
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place}
    (ha : (flatPlacesOf linksFull true)[k]? = some a) (hK : a.kind = .K3) (hp : a.piece ≤ 3)
    (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl (Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ =
          some v → SameBut u.1 v.1)
    (hj : Dm.N.index.1 < q.base)
    (hSmp : ∀ (z : P) s s', SameBut s s' → ∀ x ∈ Dm.ms, SitsAt x Dm.N.index.1 Dm.N.index.2 →
      Dm.smp (z, s') x.1 x.2 = Dm.smp (z, s) x.1 x.2)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hDig : ∀ m, GoesBack (relOf SameBut q.base) (Dm.digitsPart m))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i)) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch k q b' :=
  ridesAtR_of_plain Dm.N (mgAll Dm Mg) Rch k q b' ha hK hp hback SameBut hRel
    (mgAll_pile_back Dm Mg q.base) (mgAll_pin_back Dm Mg q.base _ _ hj hSmp)
    (mgAll_pinW_back Dm Mg q.base hDec) (mgAll_row_back Dm Mg q.base)
    fun m p _ _ => mgAll_constr_back Dm Mg q.base hDec hReq m p (hDig m) (hHead p)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgAll_row_back
#print axioms VerifiableInference.Desc.Sound.mgAll_pile_back
#print axioms VerifiableInference.Desc.Sound.mgAll_pinW_back
#print axioms VerifiableInference.Desc.Sound.mgAll_pin_back
#print axioms VerifiableInference.Desc.Sound.mgAll_constr_back
#print axioms VerifiableInference.Desc.Sound.ridesAtR_calls_mgAll
