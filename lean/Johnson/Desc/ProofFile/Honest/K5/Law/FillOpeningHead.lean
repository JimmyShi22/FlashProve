-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillOpeningHead.lean: CONDITIONAL, under the library's
hypothesis h on the public input (`P5J.AtMgA`): AT THE FIRST SEGMENT THE SHARED SENDING's
WHOLE-MESSAGE LOT OF AN OWN MESSAGE OF THE OPENING COVERS THE FILLING's LOT THERE (`Covers`,
Covers.lean in this folder) UNDER ONE TEST WITH CODE ON THE BOOK, THE ADDRESS's SEAT AND TWO CLAUSES
ON NUMBERS. It is `covers_fill_opening_book` (FillOpening.lean in this folder) WITHOUT its two
public premises ha and hIn: hIn IS DERIVED UNDER h; ha IS DERIVED WHERE THE FILLING LAYS SOMETHING,
AND NOWHERE ELSE IS IT WANTED. No premise comes for the two. The laws that bear this are the shared
sending's own: `K1.first_lays_room` (Johnson/Desc/ProofFile/Honest/K1/FirstOffPad.lean),
`msgFits_pub` (Honest/Law/LaysRoomPub.lean), `lays_says` (Honest/Law/LaidLaw.lean): here they are
called. No definition; two theorems.

Main names:
  `in_at_opening`: WHERE THE FILLING LAYS SOMETHING at `⟨K1.firstAddr, n⟩`, at that row and place:
    message n of the job's plan has a sample (ha's clause), and the row and place lie inside its
    main rows and its code's message length and off the places of the pad of its sample (hIn's
    three).
  `covers_fill_opening_head`: the covering.

THE PREMISES, ALL OF THEM.
  h: the library's hypothesis: a letter of `fillLot`, with the fence told in FillSwitch.lean; HERE
    IT IS ALSO SPENT: its field `laid.pub` says that the public part is a return of the maker's.
  hG: G is the maker's own ground.
  q (`in_at_opening`): the filling lays something at that address, row and place.
  hAd, hnum, hc, hBk (`covers_fill_opening_head`): as in FillOpening.lean, with what is told of each
    there: hBk IS A TEST WITH CODE ON THE BOOK, RUN HERE AT NO BOOK, and it COVERS, IT DOES NOT
    EQUAL.
  S, rd, X, own₀, n, m', num, fx, ch, Vd, N ARE LETTERS, as in FillOpening.lean.

WHAT IS NOT DERIVED. ha BY ITSELF, a clause on the message alone: at a message in which the filling
lays nothing it may fail. There `Covers` asks nothing: so the covering is proved ENTRY BY ENTRY:
where the filling's text answers it lays something (`fillTxt_some`, `lays_of_ask`); there
`in_at_opening` hands ha, and hIn at every row and place under its own hypothesis; then
`covers_fill_opening_book` is called at that entry.

How `in_at_opening` goes. `lays_says` is called for one thing alone: a message's number below the
length of its segment's list. At a public part that the maker returns every code's message length is
a power of two (`msgFits_pub`; the maker's road's `pub` is `ProofFile.pubPlain` by its text, and h has
that return). `K1.first_lays_room` gives the four clauses at the plan's record; the filling at the
form's letters is that record's (`firstFill_at`), and the job's record is the plan's
(`blank_first`).

Limits. CONDITIONAL. THEY MAY HOLD EMPTILY: where the two numbers differ; where the filling's text
is silent at every entry (`Covers` is one-way); where hAd or hBk fails; and at a book that has more
than the part takes hBk and the covering hold and the frame lends the opening's part nothing (told
in FillOpening.lean). That hBk holds at any book is not said. That the Script's message at the
opening is `K1.msgTxt`, and that its lot stands in the frame's list, is not said. At the code
switches the like is not here. The file imports FillOpening.lean and the shared sending's
K1/FirstOffPad.lean and Law/LaidLaw.lean: these, and further files beneath them, lie in no seal.
Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under
ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash `OnBytes.secondHashFunction`
alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FillOpening
import Johnson.Desc.ProofFile.Honest.K1.FirstOffPad
import Johnson.Desc.ProofFile.Honest.Law.LaidLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K1 (cellsVals firstData)
open ProofFile.Honest.FirstThread (MsgLot Covers)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **WHERE THE FILLING LAYS SOMETHING AT AN OWN MESSAGE OF THE OPENING, THE MESSAGE HAS A SAMPLE,
AND THE ROW AND PLACE LIE INSIDE ITS ROWS AND ITS CODE's LENGTH AND OFF ITS PAD.** CONDITIONAL:
under the hypothesis h; hG: G is the maker's own ground; q: the filling lays something there. -/
theorem in_at_opening (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G) {X : Type}
    {n row place : ℕ}
    (q : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
      (K1.firstSeat h.𝔇.sent.shape 0) fun _ => 0).lays ⟨K1.firstAddr, n⟩ row place = true) :
    (shapeAt (K1.firstJob (X := X) S Zp G).P n).answers ≠ 0 ∧
      row < (shapeAt (K1.firstJob (X := X) S Zp G).P n).mainRows ∧
      place < ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell ∧
      (row, place) ∉ padInMain ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell
        (shapeAt (K1.firstJob (X := X) S Zp G).P n) := by
  have eG : G.first = Zp.first := _root_.Meaning.K2.blank_first hG
  obtain ⟨l, m, M, _, _, _, -, hM, -⟩ :=
    lays_says h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K1.firstSeat h.𝔇.sent.shape 0)
      (fun _ => 0) (cellsVals S) ⟨K1.firstAddr, n⟩ row place q
  have hM' : (Zp.first.shape.link.getD l default).messages[m]? = some M := hM
  obtain ⟨hm, -⟩ := List.getElem?_eq_some_iff.1 hM'
  have hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.toAtMg.laid.pub
  have hlen : Zp.first.codes.lengthsOk = true := (msgFits_pub hpub hm).2
  have q' : (K1.firstFill S Zp.first).lays ⟨K1.firstAddr, n⟩ row place = true := by
    rw [firstFill_at h S]
    exact q
  have R := fun gp => K1.first_lays_room S Zp.first gp hlen n row place q'
  have sw : ∀ {A B C E : Prop}, A ∧ B ∧ C ∧ E → E ∧ A ∧ B ∧ C :=
    fun ⟨a, b, c, e⟩ => ⟨e, a, b, c⟩
  unfold K1.firstJob K1.firstJobAt
  rw [eG]
  exact sw (R _)

/-- **THE OPENING's LOT COVERS THE FILLING's.** CONDITIONAL: as `covers_fill_opening_book`, without
ha and hIn. -/
theorem covers_fill_opening_head (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) {X : Type} (own₀ : X) {n m' num : ℕ}
    (hAd : K1.firstSeat h.𝔇.sent.shape 0 ⟨K1.firstAddr, n⟩ = some (0, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp 0 m')
    (hc : ch ≤ 1)
    (hBk : K1.bookCovers Bk ch ⟨(K1.firstJob (X := X) S Zp G).P.place, 0⟩
      (K1.dueR (K1.firstJob (X := X) S Zp G).P (K1.firstJob (X := X) S Zp G).ride) = true)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : ℕ) :
    Covers Vd N ⟨num, fx, K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀ n⟩
      (fillLot (Bk := Bk) h S rd (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0)
        ⟨K1.firstAddr, n⟩ 0 m') := by
  refine ⟨hnum, fun k w hd hv hN mask row place y hy => ?_⟩
  have q0 : fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd
      (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0) ⟨K1.firstAddr, n⟩ 0 m' k w (hd.take 0) mask
      row place = some y := hy
  obtain ⟨-, _, hz, -⟩ := fillTxt_some (Bk := Bk) (k := k) q0
  have ha := (in_at_opening h S hG (X := X) (lays_of_ask hz)).1
  exact (covers_fill_opening_book h S hG rd own₀ hAd fx ch hnum ha
    (fun _ _ q => (in_at_opening h S hG (X := X) q).2) hc hBk Vd N).2 k w hd hv hN mask row
    place y hy

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.in_at_opening
#print axioms ProofFile.Honest.K5.covers_fill_opening_head
