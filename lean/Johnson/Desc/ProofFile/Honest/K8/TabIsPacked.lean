-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/TabIsPacked.lean: the honest side of the smallness test (K8): THE
WITNESS's TABLE OF A MESSAGE OF THE FIRST SEGMENT's OPENING, AS THE LIBRARY's ONE ACCESSOR READS IT
OFF A SCRIPT (`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean), HOLDS, AT THE ROW AND PLACE AT WHICH THE
LAYOUT LAYS AN ELEMENT OF AN ARRAY WHOSE NAME READS AS THE NUMBER mu, THE PACKED CELLS OF THE
READER's CELLS (`packedCells`, Johnson/HonestTrace/Packed.lean). The sister of TabIsZz.lean. Three
statements with their proofs; no definition. NO THREAD, NO STEP, NO STATE OF A VERIFIER.

IT NAMES THE SCRIPT's WITNESS AND, THROUGH THE LETTER wit, WHAT A READER YIELDS OF THE INPUT: AN
EQUATION ON THE SCRIPT: DATA AGAINST DATA: no coin is projected, cut or defaulted beyond the part's
own cut c, a bound letter. On the right of both ends: no coin. No measure; no stop.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).

  `main_is_packed`   the rows that the shared sending's part lays at the opening's job (`rowsLaid`,
                    Johnson/Desc/ProofFile/Honest/K1/ScriptAt.lean), at any cut c, hold that value
                    there
  **`tab_is_packed`**   so does the witness's table, where the Script's message is tied at that
                    entry
  `msg_is_packed`    the same at the witness's message itself; and the place is no place of a pad
THE PREMISE ON THE SCRIPT, ONE: hm: `OwnMsgs` (Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean)
at the witness's number num, at any text txt that answers at this one entry what the sending's own
text answers there (htxt). The job is the opening's, at the lot's own data (hJ). In the last two
statements three more stand: hc (c is the part's cut of the run's coins k), hw (the input is valid,
at any Vd) and hN (the list of challenges has N members or more). The rest are public, and are those
of `first_val`: the opening's seat of the message (t1), the message's test (hfit), the array lies in
it (ha), the layout's place (hrp), the name's number (hmu), the size that the values say (hz, hi);
and hlen.
CALLED, of other authors, all under Johnson/Desc/ProofFile/Honest/: `first_val`
(K1/Law/FirstIsPacked.lean), `data_first` (K1/LotData.lean), `at_lays` (K1/AgreeTools.lean),
`first_lays_room`, `first_lays_off_padB` (K1/FirstOffPad.lean), `main_data_f`, `main_data_e`
(K1/DataLaw.lean), `msgTxt_some` (K1/ScriptLots.lean).
No option is raised, no instance taken away. No tactic that searches.
Limits. Implications. None of the premises is shown here. At the message's first sending alone: of a
copy that a later member keeps or sends again nothing is said. It stands over one file of another
house that is on no row.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstIsPacked
import Johnson.Desc.ProofFile.Honest.K1.FirstOffPad
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.AgreeTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.Params (ReqArray)
open OnBytes.HonestTrace (packedCells)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open Johnson.Prover.Send (shapeAt)

variable {X : Type}

/-- The rows that the part lays at the opening's job hold the packed cells there. -/
theorem main_is_packed (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (gp : _root_.Desc.Plain.GPar) (first : ℕ) {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.placeJob (X := X) (K1.firstPar G.first gp) first (K1.firstFold G.first)
      (K1.lotData S Z G))
    (own₀ : X) (n : ℕ) (c : Cs (K1.dueR J.P J.ride)) (v : K1.PlaceIn ProofFile.Inst)
    (h : List Fmt.Drawn) (hlen : G.first.codes.lengthsOk = true) {a : ReqArray}
    (t1 : K1.firstSeat G.first.shape 0 ⟨K1.firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message) {i cc : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i cc = some rp) {mu : ℕ} (hmu : K1.labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (K1.cellsVals S).size 0 a.name = some z) (hi : i < z.1 ∧ cc < z.2) :
    (K1.rowsLaid J own₀ c v h n).main ((shapeAt J.P n).mainDeg == 3) rp.1 rp.2 =
      algebraMap GF GE (packedCells S v.R.cells.cell 0 mu i cc) := by
  subst hJ
  have hval := K1.first_val S Z G v.x v.R h t1 hfit ha hrp hmu hz hi
  have hlays : (K1.firstFill S G.first).lays ⟨K1.firstAddr, n⟩ rp.1 rp.2 = true := by
    have q := hval
    rw [K1.data_first] at q
    exact K1.at_lays _ _ _ _ _ _ _ q
  obtain ⟨hr, hj, hpad, hans⟩ := K1.first_lays_room S G.first gp hlen n rp.1 rp.2 hlays
  have hd : ∀ fr, (K1.placeJob (X := X) (K1.firstPar G.first gp) first (K1.firstFold G.first)
      (K1.lotData S Z G)).data v fr n rp.1 rp.2 =
      (K1.lotData S Z G v.x).forSend v.R K1.firstAddr fr.heard n rp.1 rp.2 := fun _ => rfl
  unfold Johnson.Prover.Send.Rows.main K1.rowsLaid
  cases h3 : ((shapeAt (K1.placeJob (X := X) (K1.firstPar G.first gp) first (K1.firstFold G.first)
      (K1.lotData S Z G)).P n).mainDeg == 3) with
  | true => rw [if_pos rfl, K1.main_data_e _ _ _ c n rp.1 rp.2 h3 hr hj hans hpad, hd, hval]
  | false =>
    rw [if_neg Bool.false_ne_true, K1.main_data_f _ _ _ c n rp.1 rp.2 h3 hr hj hans hpad, hd,
      hval]

/-- **The witness's table of the opening's message holds the packed cells there.** An equation on
the Script; no coin on its right. NOT IN FRONT OF A LAW OVER COINS. -/
theorem tab_is_packed {Bk : ProverCoinCounts} {Wl Cells Tok : Type} (Q : Script Bk Wl Cells Tok MsgT)
    (Vd : Wl → Prop) (N ch : ℕ) (wit : Wl → K1.PlaceIn ProofFile.Inst) (S : OnBytes.HonestTrace.Sz)
    (Z : Pub) (G : Ground) (gp : _root_.Desc.Plain.GPar) (first : ℕ)
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.placeJob (X := X) (K1.firstPar G.first gp) first (K1.firstFold G.first)
      (K1.lotData S Z G))
    (own₀ : X) (front n num j t : ℕ)
    (txt : Coins Bk → Wl → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE) {rp : ℕ × ℕ}
    (hm : OwnMsgs Q Vd N num front txt)
    (htxt : ∀ k w h y, K1.msgTxt ch wit J own₀ n k w h false rp.1 rp.2 = some y →
      txt k w h false rp.1 rp.2 = some y)
    (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    (hlen : G.first.codes.lengthsOk = true) {a : ReqArray}
    (t1 : K1.firstSeat G.first.shape 0 ⟨K1.firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message) {i cc : ℕ}
    (hrp : laidAt a i cc = some rp) {mu : ℕ} (hmu : K1.labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (K1.cellsVals S).size 0 a.name = some z) (hi : i < z.1 ∧ cc < z.2) :
    (Q.wit k w hd).tab J.P.codes (shapeAt J.P n) num j t false rp.1 rp.2 =
      algebraMap GF GE (packedCells S (wit w).R.cells.cell 0 mu i cc) := by
  have hoff : padB J.P.codes (shapeAt J.P n) false rp.1 rp.2 = false := by
    subst hJ
    have q := K1.first_val S Z G (wit w).x (wit w).R (hd.take front) t1 hfit ha hrp hmu hz hi
    rw [K1.data_first] at q
    exact K1.first_lays_off_padB S G.first gp hlen n rp.1 rp.2 (K1.at_lays _ _ _ _ _ _ _ q)
  have e := hm k w hd hw hN false rp.1 rp.2 _
    (htxt k w (hd.take front) _ (K1.msgTxt_some ch wit _ own₀ n k c hc w (hd.take front) false rp.1
      rp.2))
  unfold Wit.tab
  rw [if_neg (fun hb => Bool.false_ne_true (hoff.symm.trans hb))]
  show Q.msg num k w (hd.take (Q.fixedMsg num)) false rp.1 rp.2 = _
  rw [e]
  exact main_is_packed S Z G gp first hJ own₀ n c (wit w) (hd.take front) hlen t1 hfit ha hrp hmu
    hz hi

/-- The same at the witness's message itself, and the place is no place of a pad. -/
theorem msg_is_packed {Bk : ProverCoinCounts} {Wl Cells Tok : Type} (Q : Script Bk Wl Cells Tok MsgT)
    (Vd : Wl → Prop) (N ch : ℕ) (wit : Wl → K1.PlaceIn ProofFile.Inst) (S : OnBytes.HonestTrace.Sz)
    (Z : Pub) (G : Ground) (gp : _root_.Desc.Plain.GPar) (first : ℕ)
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.placeJob (X := X) (K1.firstPar G.first gp) first (K1.firstFold G.first)
      (K1.lotData S Z G))
    (own₀ : X) (front n num : ℕ)
    (txt : Coins Bk → Wl → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE) {rp : ℕ × ℕ}
    (hm : OwnMsgs Q Vd N num front txt)
    (htxt : ∀ k w h y, K1.msgTxt ch wit J own₀ n k w h false rp.1 rp.2 = some y →
      txt k w h false rp.1 rp.2 = some y)
    (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    (hlen : G.first.codes.lengthsOk = true) {a : ReqArray}
    (t1 : K1.firstSeat G.first.shape 0 ⟨K1.firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message) {i cc : ℕ}
    (hrp : laidAt a i cc = some rp) {mu : ℕ} (hmu : K1.labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (K1.cellsVals S).size 0 a.name = some z) (hi : i < z.1 ∧ cc < z.2) :
    (Q.wit k w hd).msg num false rp.1 rp.2 =
        algebraMap GF GE (packedCells S (wit w).R.cells.cell 0 mu i cc) ∧
      padB J.P.codes (shapeAt J.P n) false rp.1 rp.2 = false := by
  have hoff : padB J.P.codes (shapeAt J.P n) false rp.1 rp.2 = false := by
    subst hJ
    have q := K1.first_val S Z G (wit w).x (wit w).R (hd.take front) t1 hfit ha hrp hmu hz hi
    rw [K1.data_first] at q
    exact K1.first_lays_off_padB S G.first gp hlen n rp.1 rp.2 (K1.at_lays _ _ _ _ _ _ _ q)
  refine ⟨?_, hoff⟩
  have e := tab_is_packed Q Vd N ch wit S Z G gp first hJ own₀ front n num 0 0 txt hm htxt k c hc w
    hw hd hN hlen t1 hfit ha hrp hmu hz hi
  unfold Wit.tab at e
  rw [if_neg (fun hb => Bool.false_ne_true (hoff.symm.trans hb))] at e
  exact e

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.main_is_packed
#print axioms ProofFile.Honest.K8.tab_is_packed
#print axioms ProofFile.Honest.K8.msg_is_packed
