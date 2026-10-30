-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/TabIsZz.lean: the honest side of the smallness test (K8): THE
WITNESS's TABLE OF THE DIGITS' MESSAGE, AS THE LIBRARY's ONE ACCESSOR READS IT OFF A SCRIPT
(`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean; `Script.wit`,
Johnson/Desc/ProofFile/Honest/Thread/First.lean), HOLDS, AT THE ROW AND PLACE AT WHICH THE LAYOUT
LAYS AN ELEMENT OF THE ARRAY "ZZ", THE KIND's OWN `zzOf`
(Johnson/Desc/ProofFile/Honest/K8/Digits.lean) OF THE READER's CELLS AND THE DRAWN MATRIX. Two
statements with their proofs; no definition. NO THREAD, NO STEP, NO STATE OF A VERIFIER.

IT NAMES THE SCRIPT's WITNESS AND, THROUGH THE LETTER wit, WHAT A READER YIELDS OF THE INPUT: AN
EQUATION ON THE SCRIPT: DATA AGAINST DATA: no coin is projected, cut or defaulted beyond the part's
own cut c, a bound letter. WHERE COINS STAND IN THE TWO ENDS: in `tab_is_zz`'s the run's coins k on
the left, inside `Q.wit`; in `main_is_zz`'s the cut c on the left, inside `rowsLaid`; ON THE RIGHT
OF BOTH: NONE. No measure; no stop. NOT IN FRONT OF A LAW OVER COINS.

  `main_is_zz`     the rows that the shared sending's part lays at the digits' job (`rowsLaid`,
                   Johnson/Desc/ProofFile/Honest/K1/ScriptAt.lean), at any cut c, hold that value
                   there
  **`tab_is_zz`**   so does the witness's table, where the Script's message is tied at that entry
THE PREMISE ON THE SCRIPT, ONE: hm: `OwnMsgs` (Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean)
at the witness's number num, AT ANY TEXT txt THAT ANSWERS AT THIS ONE ENTRY WHAT THE SENDING's OWN
TEXT ANSWERS THERE (htxt; `K1.msgTxt`, Johnson/Desc/ProofFile/Honest/K1/ScriptLots.lean): that text
whole, or cut to the entries off the pad. NO PREMISE ON A PAD, AND NO TEST FOR IT: where the lot's
data lay an element is no place of a pad (`later_lays_off_padB`,
Johnson/Desc/ProofFile/Honest/K1/LaterOffPad.lean, from hlen, hne, hmom), and there the accessor
reads the message alone. AT WHICH SENDING: the job is the shared sending at moment 2 of a segment
(`K1.laterJobAt … 2 …`) at the lot's own data: THE DIGITS' MESSAGE's FIRST SENDING. Of a copy of
that message that a later member keeps or sends again nothing is said.
CALLED: `lot_val_digits` (Johnson/Desc/ProofFile/Honest/K8/LotAtDigits.lean) · of other authors:
`at_lays` (K1/AgreeTools.lean), `later_lays_room`, `later_lays_off_padB` (K1/LaterOffPad.lean),
`main_data_f`, `main_data_e` (K1/DataLaw.lean), `msgTxt_some` (K1/ScriptLots.lean), all under
Johnson/Desc/ProofFile/Honest/. KIN, NOT CALLED: `tab_rows`
(Johnson/Desc/ProofFile/Honest/K1/ScriptTie.lean): the whole table is the rows laid, under OwnMsgs
at the whole text AND OwnPads.
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. AN IMPLICATION. hm IS PROVED OF NO SCRIPT HERE; at a Vd that holds of no input it asks
nothing. The cut c is a premise (hc). AT A SHORT BOOK ALL IS IDLE: at ch ≤ 1, where the book does
not cover the part's count (`bookCovers`, Johnson/Desc/ProofFile/Honest/K1/ScriptAt.lean;
`lentCut_isSome`, K1/ScriptAtLaw.lean), the cut is there at no k: hc holds at no k, `K1.msgTxt`
answers nothing, and hm at that text asks nothing: every Script meets it. That num is the number at
which the verifier's side reads the witness, that front is the number of challenges in front of that
sending, and that lk (the job's segment) is l (the layout's) are not said: letters. N is a letter
too: a caller whose list hd is short needs an hm with N at most its length. The rounds' numbers in
hdr are counted off the description's list Z.D.1; that a caller's list hd starts its count where
that list does is not said. All other premises are on public data, but hdr: among the first front
challenges the segment's round "RNG" has been heard and drew tr. IT IS COUNTED NOWHERE, AND
`K8TwoAt.zz` (Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) STAYS A PREMISE. SIX TIMES ONE
FACT STANDS IN TWO FORMS, AND NO LEMMA HERE GOES FROM ONE TO THE OTHER: the list `K3.matsOwn G.W`
against `matsOf` (Johnson/HonestTrace/DigitsAtTrace.lean) · `(wit w).R.cells` against the cells that
other laws read off the input's trace · `zzOf` against what the second stop asks (`smallStop`,
Johnson/Desc/ProofFile/Honest/K8/QuietForm.lean) · tl, the plan's record, against the state's behind
the draw · tr against that state's drawn matrix · the column's bound 2 * allRows (parOfTail tl)
against 2 * tl.mz. The table of cells of `zzBy_of_zzOf`
(Johnson/Desc/ProofFile/Honest/K8/DrawBridge.lean) is `cellsAhead`, here the accessor at a seat.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LotAtDigits
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.AgreeTools
import Johnson.Desc.ProofFile.Honest.K1.LaterOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.Params (ReqArray)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (pairOf seatsOf seatAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open ProofFile.Honest.K2 (drawnAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open Johnson.Prover.Send (shapeAt)

variable {X : Type}

/-- **The rows that the part lays at the digits' job hold `zzOf` at the layout's place.** c: any
cut; it stands on the left of the end. These rows are what the sending's text of the Script's
message is made of (`K1.scriptMsg`). An equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem main_is_zz (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (gp : _root_.Desc.Plain.GPar) (lk piece first : ℕ) {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.laterJobAt G.first gp lk piece 2 first (K1.lotData S Z G)) (own₀ : X) (n : ℕ)
    (c : Cs (K1.dueR J.P J.ride)) (v : K1.PlaceIn ProofFile.Inst) (h : List Fmt.Drawn)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {l : ℕ} {nm : String}
    {a : ReqArray} (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {i cc : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i cc = some rp) {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : G.first.codes.lengthsOk = true) (hne : (⟨J.P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨J.P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Z G "U3") ⟨⟨J.P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩ =
      some (l, a.message))
    {tl : HTailF2} (htl : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l = some tl) (hi : i < tl.tau)
    (hcc : cc < 2 * allRows (parOfTail tl)) {tr : List Int}
    (hdr : drawnAt (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng
      (h.take ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W)).heardAt
        ⟨⟨J.P.place, 0⟩, n⟩)) l = .ok tr) :
    (K1.rowsLaid J own₀ c v h n).main ((shapeAt J.P n).mainDeg == 3) rp.1 rp.2 =
      algebraMap GF GE (zzOf tl (K3.matsOwn G.W l) v.R.cells tr i cc) := by
  subst hJ
  have hval := lot_val_digits S Z G v.x ok ha hname hrp hM hans hne hB htl hi hcc v.R h hdr
  obtain ⟨hr, hj, hpad, hans'⟩ := K1.later_lays_room S Z G v.x gp lk piece 2 n hlen hne hmom
    (K1.at_lays _ _ _ _ _ _ _ hval)
  have hd : (K1.laterJobAt (X := X) G.first gp lk piece 2 first (K1.lotData S Z G)).data v
      { heard := h, own := own₀, seen := .bare [] } n rp.1 rp.2 =
      some (.inl (zzOf tl (K3.matsOwn G.W l) v.R.cells tr i cc)) := hval
  unfold Johnson.Prover.Send.Rows.main K1.rowsLaid
  cases h3 : ((shapeAt (K1.laterJobAt (X := X) G.first gp lk piece 2 first
      (K1.lotData S Z G)).P n).mainDeg == 3) with
  | true => rw [if_pos rfl, K1.main_data_e _ _ _ c n rp.1 rp.2 h3 hr hj hans' hpad, hd]
  | false =>
    rw [if_neg Bool.false_ne_true, K1.main_data_f _ _ _ c n rp.1 rp.2 h3 hr hj hans' hpad, hd]

/-- **UNDER hm, PROVED OF NO SCRIPT: THE WITNESS's TABLE OF THE DIGITS' MESSAGE HOLDS `zzOf` AT THE
LAYOUT's PLACE.** At that message's first sending alone: of a copy that a later member keeps or
sends again nothing is said. An equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem tab_is_zz {Bk : ProverCoinCounts} {Wl Cells Tok : Type} (Q : Script Bk Wl Cells Tok MsgT)
    (Vd : Wl → Prop) (N ch : ℕ) (wit : Wl → K1.PlaceIn ProofFile.Inst) (S : OnBytes.HonestTrace.Sz)
    (Z : Pub) (G : Ground) (gp : _root_.Desc.Plain.GPar) (lk piece first : ℕ)
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.laterJobAt G.first gp lk piece 2 first (K1.lotData S Z G)) (own₀ : X)
    (front n num j t : ℕ)
    (txt : Coins Bk → Wl → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE) {rp : ℕ × ℕ}
    (hm : OwnMsgs Q Vd N num front txt)
    (htxt : ∀ k w h y, K1.msgTxt ch wit J own₀ n k w h false rp.1 rp.2 = some y →
      txt k w h false rp.1 rp.2 = some y)
    (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {l : ℕ} {nm : String}
    {a : ReqArray} (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {i cc : ℕ}
    (hrp : laidAt a i cc = some rp) {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : G.first.codes.lengthsOk = true) (hne : (⟨J.P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨J.P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Z G "U3") ⟨⟨J.P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩ =
      some (l, a.message))
    {tl : HTailF2} (htl : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l = some tl) (hi : i < tl.tau)
    (hcc : cc < 2 * allRows (parOfTail tl)) {tr : List Int}
    (hdr : drawnAt (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng
      ((hd.take front).take ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W)).heardAt
        ⟨⟨J.P.place, 0⟩, n⟩)) l = .ok tr) :
    (Q.wit k w hd).tab J.P.codes (shapeAt J.P n) num j t false rp.1 rp.2 =
      algebraMap GF GE (zzOf tl (K3.matsOwn G.W l) (wit w).R.cells tr i cc) := by
  have hoff : padB J.P.codes (shapeAt J.P n) false rp.1 rp.2 = false := by
    subst hJ
    exact K1.later_lays_off_padB S Z G (wit w).x gp lk piece 2 n hlen hne hmom
      (K1.at_lays _ _ _ _ _ _ _
        (lot_val_digits S Z G (wit w).x ok ha hname hrp hM hans hne hB htl hi hcc (wit w).R
          (hd.take front) hdr))
  have e := hm k w hd hw hN false rp.1 rp.2 _
    (htxt k w (hd.take front) _ (K1.msgTxt_some ch wit _ own₀ n k c hc w (hd.take front) false rp.1
      rp.2))
  unfold Wit.tab
  rw [if_neg (fun hb => Bool.false_ne_true (hoff.symm.trans hb))]
  show Q.msg num k w (hd.take (Q.fixedMsg num)) false rp.1 rp.2 = _
  rw [e]
  exact main_is_zz S Z G gp lk piece first hJ own₀ n c (wit w) (hd.take front) ok ha hname hrp hM
    hans hlen hne hmom hB htl hi hcc hdr

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.main_is_zz
#print axioms ProofFile.Honest.K8.tab_is_zz
