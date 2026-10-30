-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/LotAtDigits.lean: the honest side of the smallness test (K8): WHAT
THE SHARED SENDING's LOT's DATA (`K1.lotData`, Johnson/Desc/ProofFile/Honest/K1/LotData.lean)
ANSWERS AT A SEAT OF THE DIGITS' MESSAGE, AT THE ROW AND PLACE AT WHICH THE LAYOUT LAYS AN ELEMENT
OF THE ARRAY "ZZ": THE KIND's OWN `zzOf` (Johnson/Desc/ProofFile/Honest/K8/Digits.lean). Five
statements with their proofs; no definition. A JOINING: PUBLIC DATA, A READER R AND A LIST OF
CHALLENGES AS LETTERS: no run, no input, no witness, no Script, no coin.

  `over_at_right`   where the first of two fillings lays nothing, their join by place
                   (`RowData.over`, Johnson/Desc/ProofFile/Honest/RowData.lean) answers as the
                   second
  `bzRows_lays_not`   at the place at which the layout lays an element of an array named "ZZ" the
                   filling of "BZ" (`bzRows`, Johnson/HonestTrace/BZRows.lean) lays nothing
  `zz_at_base`      read through the one call `RowData.at_`, `zzData` is `laidData` at its own
                   letters: by their texts
  `zzDataAt_at`     at that place `zzDataAt` answers `zzVals`' value
  **`lot_val_digits`**   THE JOIN
CALLED, OF OTHER AUTHORS: `data_digits` (Johnson/Desc/ProofFile/Honest/K1/LotData.lean) ·
`laidData_at`, `laidBack_of_laidAt` (Johnson/Desc/ProofFile/Honest/K5/Law/WayBackFill.lean,
WayBack.lean): the layout's rule and its way back, under the programs' public test `reqLayoutOk` ·
`zzVals_val` (Johnson/Desc/ProofFile/Honest/K3/BzTie.lean). ITS SISTER AT THE ARRAY "U3":
`lot_val_reads` (Johnson/Desc/ProofFile/Honest/K1/Law/LotAtReads.lean). KIN, NOT CALLED: `join_at`
(Johnson/Desc/ProofFile/Honest/K1/LotFill.lean): the like of `over_at_right` at the join by address;
`over_cells` (Johnson/Desc/ProofFile/Honest/K1/LotCells.lean) and `RowBound.over_is`
(Johnson/Desc/ProofFile/Honest/RowBoundOver.lean) speak of `RowData.over`, not of what it answers.
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. EVERY PREMISE IS ASKED AND NONE IS PROVED HERE: all are on public data, but hdr, which is on
the challenges: the segment's round "RNG" has been heard and drew t. WHAT STILL LIES BETWEEN THE
JOIN's END AND THE PREMISE OF `zzBy_of_zzOf` (Johnson/Desc/ProofFile/Honest/K8/DrawBridge.lean), SIX
THINGS: the list of names is `K3.matsOwn G.W`, as `lotData` has it · tl is the plan's record at the
segment, there the state's behind the draw · the column's bound is 2 * allRows (parOfTail tl), there
2 * tl.mz · t is what `drawnAt` returns, there tl.cfF = trits.toArray · the end is `.inl` of a value
in Cb.Gl.F, there `algebraMap Cb.Gl.F Cb.Gl.E` of that value is what the table holds · `R.cells`
belongs to a reader that is a letter, there the cells of an input's trace. What the sender makes of
these data, and what a witness holds, is not said here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.K5.Law.WayBackFill
import Johnson.Desc.ProofFile.Honest.K3.BzTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes VerifiableInference.Desc
open OnBytes.Params (ReqArray ReqLayout ReqShape)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (pairOf seatsOf mineOf bzRows bzVals)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open ProofFile.Honest.K2 (drawnAt roundNumbers)
open ProofFile.Honest.K5 (laidData_at laidBack_of_laidAt)

/-- Where the first filling lays nothing the join by place answers as the second. -/
theorem over_at_right (A B : RowData) (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : ℕ)
    (h : A.lays a r j = false) : (A.over B).at_ R hd a r j = B.at_ R hd a r j := by
  show (if (A.lays a r j || B.lays a r j) = true then
      some (if A.lays a r j = true then
          A.entry R (List.take (A.heardAt a) (List.take (max (A.heardAt a) (B.heardAt a)) hd)) a r j
        else
          B.entry R (List.take (B.heardAt a) (List.take (max (A.heardAt a) (B.heardAt a)) hd)) a r
            j)
    else none) =
    if B.lays a r j = true then some (B.entry R (List.take (B.heardAt a) hd) a r j) else none
  rw [h, Bool.false_or, if_neg Bool.false_ne_true, List.take_take,
    Nat.min_eq_left (Nat.le_max_right _ _)]

/-- At the place of an element of "ZZ" the filling of "BZ" lays nothing. -/
theorem bzRows_lays_not (Z : Pub) (G : Ground) (mats : ℕ → List (ℕ × String × ℕ))
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {l : ℕ} {nm : String}
    {a : ReqArray} (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {i c : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {A : MsgAddr}
    (hA : pairOf (seatsOf Z G "BZ") A = some (l, a.message)) :
    (bzRows Z G mats).lays A rp.1 rp.2 = false := by
  have hs : (bzVals Z G mats).size l a.name = none := by
    rw [hname]
    rfl
  show (match pairOf (seatsOf Z G "BZ") A with
    | some (l', m) =>
      msgFits G.first.codes G.first.shape G.first.layout l' m &&
        (laidBack G.first.layout l' m rp.1 rp.2).any fun x =>
          ((bzVals Z G mats).size l' x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)
    | none => false) = false
  rw [hA]
  show (msgFits G.first.codes G.first.shape G.first.layout l a.message &&
    (laidBack G.first.layout l a.message rp.1 rp.2).any fun x =>
      ((bzVals Z G mats).size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) = false
  rw [laidBack_of_laidAt ok ha hrp]
  show (msgFits G.first.codes G.first.shape G.first.layout l a.message &&
    ((bzVals Z G mats).size l a.name).any fun z => decide (i < z.1 ∧ c < z.2)) = false
  rw [hs]
  exact Bool.and_false _

/-- Read through the one call, the filling of "ZZ" is its values laid at its own seat. -/
theorem zz_at_base (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (ℕ × ℕ)) (Z : ZzPub) (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr)
    (r j : ℕ) :
    (zzData codes s lay seat Z).at_ R hd a r j =
      (laidData codes s lay (bearsZz lay seat) (zzData codes s lay seat Z).heardAt (zzVals Z)).at_ R
        hd a r j := rfl

/-- **At the layout's place the filling of "ZZ" answers its values' element.** -/
theorem zzDataAt_at (G : Ground) (D : List Fmt.DeclaredRound) (seat : MsgAddr → Option (ℕ × ℕ))
    (mats : ℕ → List (ℕ × String × ℕ))
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {l : ℕ} {nm : String}
    {a : ReqArray} (ha : arrayOf G.first.layout l nm = some a) {i c : ℕ} {rp : ℕ × ℕ}
    (hrp : laidAt a i c = some rp) {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    {A : MsgAddr} (hB : bearsZz G.first.layout seat A = some (l, a.message)) {z : ℕ × ℕ}
    (hz : (zzVals (zzPubOf G D mats)).size l a.name = some z) (hi : i < z.1) (hc : c < z.2)
    (R : Readers) (hd : List Fmt.Drawn) :
    (zzDataAt G D seat mats).at_ R hd A rp.1 rp.2 =
      some ((zzVals (zzPubOf G D mats)).val R (hd.take ((zzDataAt G D seat mats).heardAt A)) l
        a.name i c) :=
  (zz_at_base G.first.codes G.first.shape G.first.layout seat (zzPubOf G D mats) R hd A rp.1
    rp.2).trans (laidData_at ok ha hrp hM hans _ hB hz hi hc R hd)

/-- **AT A SEAT OF THE DIGITS' MESSAGE, AT THE LAYOUT's PLACE OF AN ELEMENT OF "ZZ", THE LOT's DATA
ANSWER `zzOf`.** -/
theorem lot_val_digits (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {l : ℕ} {nm : String}
    {a : ReqArray} (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {i c : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    {A : MsgAddr} (h1 : A.sender ≠ K1.firstAddr)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) A = some (l, a.message))
    {tl : HTailF2} (htl : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l = some tl) (hi : i < tl.tau)
    (hc : c < 2 * allRows (parOfTail tl)) (R : Readers) (hd : List Fmt.Drawn) {t : List Int}
    (hdr : drawnAt (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng
      (hd.take ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W)).heardAt A)) l =
        .ok t) :
    (K1.lotData S Z G x).at_ R hd A rp.1 rp.2 =
      some (.inl (zzOf tl (K3.matsOwn G.W l) R.cells t i c)) := by
  have hA : pairOf (seatsOf Z G "BZ") A = some (l, a.message) :=
    (Option.filter_eq_some_iff.1 hB).1
  have h2 : mineOf (seatsOf Z G "BZ") A = true := by
    obtain ⟨s, hs, -⟩ := Option.map_eq_some_iff.1 hA
    show (OnBytes.HonestTrace.seatAt (seatsOf Z G "BZ") A).isSome = true
    rw [hs]
    rfl
  have hz : (zzVals (zzPubOf G Z.D.1 (K3.matsOwn G.W))).size l a.name =
      some (tl.tau, 2 * allRows (parOfTail tl)) := by
    rw [hname]
    show (if ("ZZ" == "ZZ") = true then
      ((zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l).map fun tl => (tl.tau, 2 * allRows (parOfTail tl))
      else none) = _
    rw [if_pos (by decide : ("ZZ" == "ZZ") = true), htl]
    rfl
  rw [K1.data_digits S Z G x R hd A rp.1 rp.2 h1 h2]
  show ((bzRows Z G (K3.matsOwn G.W)).over
    (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W))).at_ R hd A rp.1 rp.2 = _
  rw [over_at_right _ _ R hd A rp.1 rp.2 (bzRows_lays_not Z G _ ok ha hname hrp hA),
    zzDataAt_at G Z.D.1 _ _ ok ha hrp hM hans hB hz hi hc R hd, hname,
    K3.zzVals_val _ R _ l tl t htl hdr i c]
  rfl

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.over_at_right
#print axioms ProofFile.Honest.K8.bzRows_lays_not
#print axioms ProofFile.Honest.K8.zz_at_base
#print axioms ProofFile.Honest.K8.zzDataAt_at
#print axioms ProofFile.Honest.K8.lot_val_digits
