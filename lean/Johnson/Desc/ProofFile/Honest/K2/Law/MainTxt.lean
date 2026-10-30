-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MainTxt.lean: the kind "the code switch" (K2): WHAT THE LOT's
TEXT `switchMsgTxt` (Honest/K2/ScriptLots.lean) ANSWERS AT AN ENTRY OF A MAIN ROW OF ONE OF THE
SWITCH's OWN MESSAGES OF MOMENT 0, OFF THE PADS' PLACES: what the filling D lays at the message's
own address, at no challenge, as a row of the message's field takes it. Statements with their
proofs: joins; no definition.

  `msgTxt_rows`     where the part is handed its stretches and `switchRowsLaid` returns V, the
                    text's answer at (mask, r, j) is `K1.rowsMsg` of V n
  `mainRows_own`    `mainRows` at an own message is the own data's message
  `laidMain_e`, `laidMain_f`   the two fields of V n at a main entry off the pads' places
  `msgTxt_main_e`   THE END over the extension field: the answer is d
  `msgTxt_main_f`   THE END over the base field: the answer is `algebraMap Cb.Gl.F Cb.Gl.E d.c0`
  `msgTxt_inv`      where the text answers, the part was handed its stretches and the rows were laid
  `msgTxt_main_e_of`, `msgTxt_main_f_of`   the two ends for whoever holds an answer y alone

d := `senderOwn` (D w.x) (readers w) p m r j (Honest/K2/Law/SenderOwn.lean): `asRow` of what D
lays at `p.ownAddr m`. n := 1 + the kept members + m: the message's number in the sending.

By: the shared sending's `main_data_e`, `main_data_f` (Honest/K1/DataLaw.lean, of other authors),
carried to this kind's rows by `rowsAll_shared_paid` (Honest/K2/Law/SameRows.lean); `rowsLaid_inv`
(SenderOwn.lean). `NoWord` is a premise; under the opening `noWord_open`
(Honest/K2/Law/SampledOpen.lean, not imported) has it at the lot's places.

Limits. THE FENCE: r below the main rows, j below the code's length, (r, j) off `padInMain`'s
places, the message sampled: at a pad's place the entry is a coin, not data (`pad_coin_e`,
`pad_coin_f`, Honest/K1/CoinLaw.lean): not said here. OVER THE BASE FIELD THE ANSWER IS THE
EMBEDDING OF d's FIRST COORDINATE: that this is d again is not said here. D IS A LETTER: what it
lays at that address, of whichever trace, is not spoken of. Nothing at the carrying message, at a
kept copy, or at the next fold's mask. That the text gives an answer at the entry is proved nowhere
in this file: the laws on the text take it as a premise, or take what gives it: the part is handed
its coins and its rows are laid. (Whether it answers hangs on no coin, no challenge, no entry, and
of the input on its public instance alone, at the lot's own closing and under the public test
`closingOk`: `handed_public`, `msgTxt_isSome`, `msgTxt_public`, Honest/K2/Law/LotsAnswer.lean: not
called here.) The laws say what stands at which entry, no more. NO LOT IS LAID. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SenderOwn
import Johnson.Desc.ProofFile.Honest.K2.Law.SameRows
import Johnson.Desc.ProofFile.Honest.K1.DataLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows Sizes)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- The text's answer, where the part is handed its stretches and the rows are laid. -/
theorem msgTxt_rows (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (n : Nat) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V) (mask : Bool) (r j : Nat) :
    switchMsgTxt ch D readers closing p n k w hd mask r j =
      some (K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r j) := by
  unfold switchMsgTxt
  rw [hH]
  show ((switchRowsLaid D readers closing p c w hd).toOption.map fun V =>
    K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r j) = _
  rw [hV]
  rfl

/-- `mainRows` at an own message. -/
theorem mainRows_own (Z : Sizes) (W : Left) (own : Nat → Nat → Nat → Cb.Gl.E) (m : Nat) :
    mainRows Z W own (1 + Z.kept.length + m) = own m := by
  have h1 : ¬ ((1 + Z.kept.length + m == 0) = true) := by simp
  have h2 : ¬ (1 + Z.kept.length + m ≤ Z.kept.length) := by omega
  have h3 : 1 + Z.kept.length + m - 1 - Z.kept.length = m := by omega
  simp only [mainRows, if_neg h1, if_neg h2, h3]

section
variable {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
  {fresh : Option (Nat × Nat)} {data : Nat → Nat → Nat → Cb.Gl.E}
  {c : Cs (sendingDue codes sent fresh)} {V : Nat → Johnson.Prover.Send.Rows}

/-- A main entry off the pads' places, over the extension field. -/
theorem laidMain_e (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {r j : Nat}
    (h3 : ((sent.getD n default).shape.mainDeg == 3) = true)
    (hr : r < (sent.getD n default).shape.mainRows)
    (hj : j < (codes.base.getD (sent.getD n default).shape.code default).ell)
    (ha : (sent.getD n default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (codes.base.getD (sent.getD n default).shape.code default).ell
      (sent.getD n default).shape) :
    (V n).mainE r j = data n r j := by
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn]
  have e := sendingPar_shape codes sent n
  rw [K1.main_data_e (sendingPar codes sent) _ _ _ n r j (by rw [e]; exact h3)
    (by rw [e]; exact hr) (by rw [e]; exact hj) (by rw [e]; exact ha) (by rw [e]; exact hp)]
  show (match asShared (sent.getD n default).shape (data n) r j with
    | some (.inr x) => x
    | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
    | none => 0) = _
  unfold asShared
  rw [if_pos h3]

/-- The like over the base field: the first coordinate. -/
theorem laidMain_f (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {r j : Nat}
    (h3 : ((sent.getD n default).shape.mainDeg == 3) = false)
    (hr : r < (sent.getD n default).shape.mainRows)
    (hj : j < (codes.base.getD (sent.getD n default).shape.code default).ell)
    (ha : (sent.getD n default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (codes.base.getD (sent.getD n default).shape.code default).ell
      (sent.getD n default).shape) :
    (V n).mainF r j = (data n r j).c0 := by
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn]
  have e := sendingPar_shape codes sent n
  rw [K1.main_data_f (sendingPar codes sent) _ _ _ n r j (by rw [e]; exact h3)
    (by rw [e]; exact hr) (by rw [e]; exact hj) (by rw [e]; exact ha) (by rw [e]; exact hp)]
  show (match asShared (sent.getD n default).shape (data n) r j with
    | some (.inl x) => x
    | _ => 0) = _
  unfold asShared
  rw [if_neg (by rw [h3]; exact Bool.false_ne_true)]

end

/-- **THE END, OVER THE EXTENSION FIELD.** m: the own message's number. -/
theorem msgTxt_main_e (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) {m : Nat}
    (hn : 1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3) = true)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape) :
    switchMsgTxt ch D readers closing p (1 + p.sizes.kept.length + m) k w hd false r j =
      some (senderOwn (D w.x) (readers w) p m r j) := by
  obtain ⟨Wl, -, hR⟩ := rowsLaid_inv hV
  rw [msgTxt_rows ch D readers closing p _ k w hd hH hV false r j]
  show some ((V (1 + p.sizes.kept.length + m)).main (_ == 3) r j) = _
  unfold Johnson.Prover.Send.Rows.main
  rw [if_pos h3, laidMain_e hw hR hn h3 hr hj ha hp, mainRows_own]

/-- **THE END, OVER THE BASE FIELD.** -/
theorem msgTxt_main_f (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) {m : Nat}
    (hn : 1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3) = false)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape) :
    switchMsgTxt ch D readers closing p (1 + p.sizes.kept.length + m) k w hd false r j =
      some (algebraMap Cb.Gl.F Cb.Gl.E (senderOwn (D w.x) (readers w) p m r j).c0) := by
  obtain ⟨Wl, -, hR⟩ := rowsLaid_inv hV
  rw [msgTxt_rows ch D readers closing p _ k w hd hH hV false r j]
  show some ((V (1 + p.sizes.kept.length + m)).main (_ == 3) r j) = _
  unfold Johnson.Prover.Send.Rows.main
  rw [if_neg (by rw [h3]; exact Bool.false_ne_true), laidMain_f hw hR hn h3 hr hj ha hp,
    mainRows_own]

/-- Where the text answers, the part was handed its stretches and the rows were laid. -/
theorem msgTxt_inv {ch : Nat} {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : Closing} {p : SwitchPlace} {n : Nat} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {mask : Bool} {r j : Nat} {y : Cb.Gl.E}
    (hy : switchMsgTxt ch D readers closing p n k w hd mask r j = some y) :
    ∃ c V, handed ch p k = some c ∧ switchRowsLaid D readers closing p c w hd = .ok V := by
  unfold switchMsgTxt at hy
  cases hH : handed ch p k with
  | none =>
    rw [hH] at hy
    cases hy
  | some c =>
    rw [hH] at hy
    cases hV : switchRowsLaid D readers closing p c w hd with
    | error e =>
      have hy' : ((switchRowsLaid D readers closing p c w hd).toOption.map fun V =>
          K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r j) =
        some y := hy
      rw [hV] at hy'
      cases hy'
    | ok V => exact ⟨c, V, rfl, hV⟩

/-- **THE SAME, FOR WHOEVER HOLDS AN ANSWER ALONE**, over the extension field. -/
theorem msgTxt_main_e_of (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn)
    (hw : NoWord (switchSent p.sizes p.others)) {m : Nat}
    (hn : 1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3) = true)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape)
    {y : Cb.Gl.E}
    (hy : switchMsgTxt ch D readers closing p (1 + p.sizes.kept.length + m) k w hd false r j =
      some y) :
    y = senderOwn (D w.x) (readers w) p m r j := by
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy
  rw [msgTxt_main_e ch D readers closing p k w hd hH hV hw hn h3 hr hj ha hp] at hy
  exact (Option.some.inj hy).symm

/-- The like over the base field. -/
theorem msgTxt_main_f_of (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn)
    (hw : NoWord (switchSent p.sizes p.others)) {m : Nat}
    (hn : 1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3) = false)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD
      (1 + p.sizes.kept.length + m) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape)
    {y : Cb.Gl.E}
    (hy : switchMsgTxt ch D readers closing p (1 + p.sizes.kept.length + m) k w hd false r j =
      some y) :
    y = algebraMap Cb.Gl.F Cb.Gl.E (senderOwn (D w.x) (readers w) p m r j).c0 := by
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy
  rw [msgTxt_main_f ch D readers closing p k w hd hH hV hw hn h3 hr hj ha hp] at hy
  exact (Option.some.inj hy).symm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgTxt_rows
#print axioms ProofFile.Honest.K2.Law.mainRows_own
#print axioms ProofFile.Honest.K2.Law.laidMain_e
#print axioms ProofFile.Honest.K2.Law.laidMain_f
#print axioms ProofFile.Honest.K2.Law.msgTxt_main_e
#print axioms ProofFile.Honest.K2.Law.msgTxt_main_f
#print axioms ProofFile.Honest.K2.Law.msgTxt_inv
#print axioms ProofFile.Honest.K2.Law.msgTxt_main_e_of
#print axioms ProofFile.Honest.K2.Law.msgTxt_main_f_of
