-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillOpening.lean: CONDITIONAL: AT THE FIRST SEGMENT THE
FILLING's LOT AT AN OWN MESSAGE OF THE OPENING AND THE SHARED SENDING's WHOLE-MESSAGE LOT OF THAT
MESSAGE (`K1.msgTxt` at `K1.firstJob`) ANSWER ONE ELEMENT WHEREVER BOTH ANSWER; AND THE SENDER's LOT
COVERS THE FILLING's (`Covers`, Covers.lean in this folder). It is the sister of FillSwitch.lean's
tops, where the sender is a code switch. In the last form the premise that the sender's text answers
is EXCHANGED for a test with code on the book: AN EXCHANGE, NOT A PAYMENT: that form stands under
public premises alone. The tests are run here at no book and no plan. No definition; five theorems.

Main names:
  `seated_at_opening`: an address that the opening's seat (`K1.firstSeat s 0`) seats is
    `⟨K1.firstAddr, a.msg⟩`, and its segment is 0. No premise but the seat's answer.
  `agree2_fill_opening`: `Agree2` of the filling's lot at `⟨K1.firstAddr, n⟩` and the lot `⟨num, fx,
    K1.msgTxt ch rd (K1.firstJob S Zp G) own₀ n⟩`.
  `covers_fill_opening`: that lot covers the filling's; hS: wherever the filling's text answers, the
    opening's does.
  `covers_fill_opening_book`: the same with hS exchanged for hc and hBk.
  `base_in`: an element of the base field, mapped into the extension field, is that element laid as
    an entry: a helper.

THE PREMISES, ALL OF THEM.
  h: the library's hypothesis on the public input (`P5J.AtMgA`): a letter of `fillLot`, with the
    fence told in FillSwitch.lean.
  hG: G is the maker's own ground (`blankBy pureRoad.links Zp = some G`).
  hAd: PUBLIC: the opening's seat seats the address `⟨K1.firstAddr, n⟩` at (0, m').
  hnum (the two coverings): an equation between two numbers: num = `P5J.At.num Zp 0 m'`; num is a
    free letter: NAMED, NOT PAID.
  ha: PUBLIC: message n of the job's plan has a sample (`answers ≠ 0`): what `K1.main_data_e` and
    `K1.main_data_f` ask.
  hIn: PUBLIC, NOT PROVED HERE: what the filling lays at that address lies inside the message's main
    rows and the code's message length, AND OFF THE PLACES OF THE PAD OF ITS SAMPLE (`padInMain`).
    For the last a test stands in the seat's own test (`RowData.clear` in `K1.firstSeatOk`,
    Johnson/Desc/ProofFile/Honest/K1/PlaceFirst.lean): not called here. For the first two: as hIn of
    FillSwitch.lean: whose it is to prove is open.
  hS (`covers_fill_opening`): AT EVERY RUN AND INPUT of which `Covers` speaks: THAT the opening's
    text answers wherever the filling's does, not what.
  hc (`covers_fill_opening_book`): ch ≤ 1: a number: at ch ≥ 2 the law that is called does not
    speak. The other two statements take every ch.
  hBk (`covers_fill_opening_book`): ON THE BOOK: A TEST WITH CODE: `K1.bookCovers Bk ch ⟨J.P.place,
    0⟩ (K1.dueR J.P J.ride)`, J the job (Johnson/Desc/ProofFile/Honest/K1/ScriptAt.lean): the book's
    count at the part's address covers what the part takes. RUN HERE AT NO BOOK.
  S, rd, X, own₀, n, m', fx ARE LETTERS; Vd and N in `covers_fill_opening_book` are letters of which
    nothing is asked: what is proved there holds at every run, input and list of challenges. One rd
    serves both texts.

How. The filling's text answers with what the filling's call that asks first answers
(`fillTxt_some`), an array's value (`ask_is_array`), an element of the base field. The sender's text
is the part's own cut, mapped (`K1.msgTxt`); WHATEVER THE CUT, at a sampled message, inside the rows
and off the pad, a main entry is what the job's data says (`K1.main_data_e`, `K1.main_data_f`,
Johnson/Desc/ProofFile/Honest/K1/DataLaw.lean); the job's data is the same filling's one call
(`K1.firstJob`, `firstFill_at`, `at_no_challenge`). The coverings: `covers_of_agree`. The exchange:
the sender's text answers just where the cut is there, whatever the entry; the cut is there just
where the test accepts (`K1.lentCut_isSome`, Johnson/Desc/ProofFile/Honest/K1/ScriptAtLaw.lean).

Limits. CONDITIONAL. THEY MAY HOLD EMPTILY: where the two numbers differ `Agree2` asks nothing;
where the filling's text is silent at every entry every lot of its number covers it (`Covers` is
one-way); where the part's cut is not there the sender's text is silent (at ch ≤ 1: where the book's
count does not cover what the part takes); hAd fails at an address that is not seated; ha fails at a
message without a sample; hIn fails at a filling that lays beyond the rows or on the pad; hBk fails
at a book that has less. AND ONE MORE, OF ITS OWN KIND: `K1.bookCovers` COVERS, IT DOES NOT EQUAL:
by its authors' own warning the frame's lending refuses unless the part takes just the book's count:
at a book that has more, hBk and `covers_fill_opening_book` hold, the text answers, and the frame
lends the opening's part nothing. That any of the public premises holds at the written plan, or hBk
at any book, is not said. That the Script's message at the opening is `K1.msgTxt`, and that its lot
stands in the frame's list, is not said. The file stands over FillSwitch.lean, SeatReach.lean and
the shared sending's ScriptLots.lean, ScriptAtLaw.lean, DataLaw.lean and PlaceFirst.lean: none of
the six lies in a seal. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so
above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FillSwitch
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReach
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K1 (cellsVals firstData labelNo)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers covers_of_agree)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA TS)

/-- An element of the base field, mapped into the extension field, is that element laid as an entry.
-/
theorem base_in (x : Cb.Gl.F) : algebraMap Cb.Gl.F Cb.Gl.E x = asE (some (.inl x)) := by
  have e := base_back x
  have c : (asE (some (.inl x))).c0 = x := OnBytes.Slice.toF_ofF x
  rwa [c] at e

/-- **AN ADDRESS THAT THE OPENING's SEAT SEATS IS THE OPENING's PART's, AND ITS SEGMENT IS 0.** On
public data alone. -/
theorem seated_at_opening {s : OnBytes.Params.ReqShape} {a : MsgAddr} {l m : ℕ}
    (q : K1.firstSeat s 0 a = some (l, m)) : a = ⟨K1.firstAddr, a.msg⟩ ∧ l = 0 := by
  have hs : a.sender = K1.firstAddr := by
    by_contra hne
    have e : K1.firstSeat s 0 a = none := momentSeat_other s 0 0 0 hne
    rw [e] at q
    cases q
  refine ⟨?_, ?_⟩
  · cases a
    cases hs
    rfl
  · unfold K1.firstSeat K1.momentSeat at q
    split at q
    · obtain ⟨_, -, e⟩ := Option.map_eq_some_iff.1 q
      exact (congrArg Prod.fst e).symm
    · cases q

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **THE FILLING's LOT AT THE OPENING's OWN MESSAGE NUMBER n AND THE OPENING's LOT OF THAT MESSAGE
AGREE.** CONDITIONAL: under the hypothesis h; hG: G is the maker's own ground; hAd: the address is
seated; ha: public: the message is sampled; hIn: public: what the filling lays there lies inside the
message's rows and the code's length, and off the places of the pad of its sample. -/
theorem agree2_fill_opening (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) {X : Type} (own₀ : X) {n m' : ℕ}
    (hAd : K1.firstSeat h.𝔇.sent.shape 0 ⟨K1.firstAddr, n⟩ = some (0, m')) (num fx ch : ℕ)
    (ha : (shapeAt (K1.firstJob (X := X) S Zp G).P n).answers ≠ 0)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K1.firstSeat h.𝔇.sent.shape 0) fun _ => 0).lays ⟨K1.firstAddr, n⟩ row place = true →
      row < (shapeAt (K1.firstJob (X := X) S Zp G).P n).mainRows ∧
      place < ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell ∧
      (row, place) ∉ padInMain ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell
        (shapeAt (K1.firstJob (X := X) S Zp G).P n)) :
    Agree2 (fillLot (Bk := Bk) h S rd (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0)
        ⟨K1.firstAddr, n⟩ 0 m')
      ⟨num, fx, K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀ n⟩ := by
  intro _ k w hd mask row place y y' q q'
  have q0 : fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd
      (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0) ⟨K1.firstAddr, n⟩ 0 m' k w (hd.take 0) mask
      row place = some y := q
  obtain ⟨rfl, z, hz, ey⟩ := fillTxt_some (Bk := Bk) (k := k) q0
  obtain ⟨A, i, cc, -, -, -, ez⟩ := ask_is_array hAd hz
  obtain ⟨hb, hj, hp⟩ := hIn _ _ (lays_of_ask hz)
  have hat : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
      (K1.firstSeat h.𝔇.sent.shape 0) fun _ => 0).at_ (rd w) (hd.take 0) ⟨K1.firstAddr, n⟩ row
      place = some z := by
    unfold RowData.ask at hz
    split at hz
    · cases hz
    · split at hz
      · cases hz
      · exact Except.ok.inj hz
  rw [at_no_challenge] at hat
  have q1 : K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀ n k w (hd.take fx) false row
      place = some y' := q'
  unfold K1.msgTxt at q1
  obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 q1
  have eG : G.first = Zp.first := _root_.Meaning.K2.blank_first hG
  have hdata : (K1.firstJob (X := X) S Zp G).data (rd w)
      { heard := hd.take fx, own := own₀, seen := .bare [] } n row place = some z := by
    show (K1.firstFill S G.first).forSend (rd w) K1.firstAddr (hd.take fx) n row place = some z
    rw [eG, firstFill_at h S]
    unfold RowData.forSend
    rw [at_no_challenge]
    exact hat
  show (K1.rowsR (K1.firstJob (X := X) S Zp G).P (K1.firstJob (X := X) S Zp G).ride
      ((K1.firstJob (X := X) S Zp G).data (rd w)
        { heard := hd.take fx, own := own₀, seen := .bare [] }) c n).main
      ((shapeAt (K1.firstJob (X := X) S Zp G).P n).mainDeg == 3) row place = y
  unfold Johnson.Prover.Send.Rows.main
  have ezl : ∃ x₀ : Cb.Gl.F, z = .inl x₀ := by
    rw [ez]
    unfold cellsVals
    dsimp only
    cases labelNo A.name <;> exact ⟨_, rfl⟩
  obtain ⟨x₀, rfl⟩ := ezl
  by_cases hE : ((shapeAt (K1.firstJob (X := X) S Zp G).P n).mainDeg == 3) = true
  · rw [if_pos hE, K1.main_data_e _ _ _ c n row place hE hb hj ha hp, hdata, ey]
    exact base_in x₀
  · rw [if_neg hE, K1.main_data_f _ _ _ c n row place (Bool.eq_false_iff.2 hE) hb hj ha hp, hdata,
      ey]
    exact base_in x₀

/-- **THE OPENING's LOT OF ITS OWN MESSAGE NUMBER n COVERS THE FILLING's LOT THERE.** CONDITIONAL:
under the hypothesis h; hnum: the two lots bear one number; hG, hAd, ha, hIn: as
`agree2_fill_opening`: public; hS: wherever the filling's text answers, the opening's does. -/
theorem covers_fill_opening (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) {X : Type} (own₀ : X) {n m' num : ℕ}
    (hAd : K1.firstSeat h.𝔇.sent.shape 0 ⟨K1.firstAddr, n⟩ = some (0, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp 0 m')
    (ha : (shapeAt (K1.firstJob (X := X) S Zp G).P n).answers ≠ 0)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K1.firstSeat h.𝔇.sent.shape 0) fun _ => 0).lays ⟨K1.firstAddr, n⟩ row place = true →
      row < (shapeAt (K1.firstJob (X := X) S Zp G).P n).mainRows ∧
      place < ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell ∧
      (row, place) ∉ padInMain ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell
        (shapeAt (K1.firstJob (X := X) S Zp G).P n))
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      (fillTxt (Bk := Bk) S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd
        (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0) ⟨K1.firstAddr, n⟩ 0 m' k w (hd.take 0) mask
        row place).isSome = true →
      (K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀ n k w (hd.take fx) mask row
        place).isSome = true) :
    Covers Vd N ⟨num, fx, K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀ n⟩
      (fillLot (Bk := Bk) h S rd (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0)
        ⟨K1.firstAddr, n⟩ 0 m') :=
  covers_of_agree hnum (agree2_fill_opening h S hG rd own₀ hAd num fx ch ha hIn) hS

/-- **THE SAME, WITH THE LAST PREMISE EXCHANGED FOR A TEST ON THE BOOK.** CONDITIONAL: as
`covers_fill_opening`, without hS; hc: the chain's number is at most 1; hBk: the book's count at the
part's address covers what the part takes. Vd and N are letters of which nothing is asked. -/
theorem covers_fill_opening_book (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) {X : Type} (own₀ : X) {n m' num : ℕ}
    (hAd : K1.firstSeat h.𝔇.sent.shape 0 ⟨K1.firstAddr, n⟩ = some (0, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp 0 m')
    (ha : (shapeAt (K1.firstJob (X := X) S Zp G).P n).answers ≠ 0)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K1.firstSeat h.𝔇.sent.shape 0) fun _ => 0).lays ⟨K1.firstAddr, n⟩ row place = true →
      row < (shapeAt (K1.firstJob (X := X) S Zp G).P n).mainRows ∧
      place < ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell ∧
      (row, place) ∉ padInMain ((K1.firstJob (X := X) S Zp G).P.codes.base.getD
        (shapeAt (K1.firstJob (X := X) S Zp G).P n).code default).ell
        (shapeAt (K1.firstJob (X := X) S Zp G).P n))
    (hc : ch ≤ 1)
    (hBk : K1.bookCovers Bk ch ⟨(K1.firstJob (X := X) S Zp G).P.place, 0⟩
      (K1.dueR (K1.firstJob (X := X) S Zp G).P (K1.firstJob (X := X) S Zp G).ride) = true)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : ℕ) :
    Covers Vd N ⟨num, fx, K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀ n⟩
      (fillLot (Bk := Bk) h S rd (K1.firstSeat h.𝔇.sent.shape 0) (fun _ => 0)
        ⟨K1.firstAddr, n⟩ 0 m') :=
  covers_fill_opening h S hG rd own₀ hAd fx ch hnum ha hIn
    fun k _ _ _ _ _ _ _ _ => by
      unfold K1.msgTxt
      rw [Option.isSome_map, K1.lentCut_isSome k ch hc]
      exact hBk

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.base_in
#print axioms ProofFile.Honest.K5.seated_at_opening
#print axioms ProofFile.Honest.K5.agree2_fill_opening
#print axioms ProofFile.Honest.K5.covers_fill_opening
#print axioms ProofFile.Honest.K5.covers_fill_opening_book
