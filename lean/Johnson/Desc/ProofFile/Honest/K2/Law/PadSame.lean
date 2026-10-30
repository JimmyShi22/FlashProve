-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PadSame.lean: the kind "the code switch" (K2): AT THE PAD's
PLACES (`padB`, Johnson/Desc/SeatAt.lean) THE LOT's TWO TEXTS ANSWER ALIKE: what `switchMsgTxt`
answers there, `switchPadTxt` answers too (both Honest/K2/ScriptLots.lean): the first reads rows
laid at the input's data, the second rows laid at data of zeros, off the same coins. The sister of
the shared sending's `pad_same` (Honest/K1/ScriptAtLaw.lean). Statements with their proofs: joins;
no definition.

  `rowsMsg_noData`   two returns of `rowsAll` at one sending's coins and any two data: at `padB`'s
                     places `K1.rowsMsg` reads one value of both
  `padTxt_same`      THE END

Why: a witness's table (`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean) reads the pad's own component at
`padB`'s places and the message elsewhere: so whoever ties a witness laid by lots to rows laid at
the true data wants the two texts to agree there.

By: the shared sending's `main_noData` (Honest/K1/ScriptAtLaw.lean, of other authors), carried to
this kind's rows by `rowsAll_shared_paid` (Honest/K2/Law/SameRows.lean); at a mask row `K1.rowsR`'s
text names no data; `rowsAll_fits`, `rowsAll_returns` (Honest/K2/Law/Laid.lean); `rows_of_laid`,
`own_of_handed` (Honest/K2/Law/MaskTxt.lean); `msgTxt_rows`, `msgTxt_inv`
(Honest/K2/Law/MainTxt.lean).

Limits. ONE WAY: from an answer of `switchMsgTxt`: that it answers is a premise; where it is silent
nothing is said. `NoWord` is a premise (under the opening: `noWord_open`,
Honest/K2/Law/SampledOpen.lean, not imported). Which places `padB`'s are:
Honest/K2/Law/PadPlaces.lean; which coin stands there: Honest/K2/Law/PadTxt.lean: neither is
imported. TWO TEXTS AGAINST EACH OTHER AT ONE RUN's COINS: what is WRITTEN where. NO LOT IS LAID.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.K2.Honest (zeroG)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- At `padB`'s places the rows hang on no data. -/
theorem rowsMsg_noData {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)} {d d' : Nat → Nat → Nat → Cb.Gl.E}
    {c : Cs (sendingDue codes sent fresh)} {V V' : Nat → Johnson.Prover.Send.Rows}
    (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh d c = .ok V)
    (h' : rowsAll freshTable codes sent fresh d' c = .ok V') {n : Nat} (hn : n < sent.size)
    {mask : Bool} {r j : Nat} (hp : padB codes (sent.getD n default).shape mask r j = true) :
    K1.rowsMsg (sent.getD n default).shape (V n) mask r j =
      K1.rowsMsg (sent.getD n default).shape (V' n) mask r j := by
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn,
    rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h' hn]
  have e := sendingPar_shape codes sent n
  cases mask with
  | true => rfl
  | false =>
    have key := K1.main_noData (sendingPar codes sent) (rideOf sent fresh) (dataShared sent d)
      (dataShared sent d') (sendingDue_shared (rowsAll_fits h) hw ▸ c) n r j (by rw [e]; exact hp)
    rw [e] at key
    exact key

/-- **THE END.** -/
theorem padTxt_same (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {mask : Bool} {r j : Nat}
    (hp : padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r j = true)
    {y : Cb.Gl.E} (hy : switchMsgTxt ch D readers closing p n k w hd mask r j = some y) :
    switchPadTxt ch p n k mask r j = some y := by
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  obtain ⟨V', hV'⟩ := rowsAll_returns (rowsAll_fits hR) freshTable (fun _ _ _ => zeroG) c.1
  rw [msgTxt_rows ch D readers closing p n k w hd hH hV mask r j] at hy
  unfold switchPadTxt
  rw [if_pos hp, own_of_handed ch p k c hH]
  show ((rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
    (switchFresh p.sizes p.others p.foldVars) (fun _ _ _ => zeroG) c.1).toOption.map fun V =>
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r j) = some y
  rw [hV', ← hy]
  exact congrArg some (rowsMsg_noData hw hV' hR hn hp)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.rowsMsg_noData
#print axioms ProofFile.Honest.K2.Law.padTxt_same
