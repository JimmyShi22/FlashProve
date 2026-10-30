-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieRows.lean: the closing of a segment (K10): the equation of the field tie of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean) from a sentence in the senders' own terms: at each member of the group the
witness's table is the rows that the closing's job has made anew for that member, read as a witness's message
(`K1.rowsMsg`, Honest/K1/ScriptAt.lean).

The senders' laws on a script end in that form: "the witness's table of the message is `K1.rowsMsg` of the rows that the
sender laid" (`tab_rows`, Honest/K1/ScriptTie.lean; `tab_rows_switch`, Honest/K2/Law/TabRows.lean).

  `readE_eOfF`, `readE_member`   an entry of a member as the closing takes it (`memberOf`, Honest/K10/SegmentClosing.lean), read in
                    the field, is the entry of `K1.rowsMsg` of the member's rows
  `rowsMsg_beyond`     the rows that the shared text of a message's rows returns (`messageRows`, Honest/K2/Sending.lean) are 0
                    from the code's message length on
  `tabAt_seat`         the witness's table of a message that has a seat and a shape, by the library's one accessor
  **`tie_of_rowsMsg`**   the field tie's equation, from: each member's rows in R are `memberOf` of some rows; the witness's
                    table there is `K1.rowsMsg` of these rows; these rows are 0 from the message length on

Limits. The three clauses on the members are premises, shown here of no witness and no rows. No head, thread or prover is
named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTie
import Johnson.Desc.ProofFile.Honest.K10.SegmentClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement E)
open OnBytes.Means (realRows)
open OnBytes.Slice (readE readE_ofTriple toE_ofE toE_zeroE toF_zero)
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest (GroupMember zeroG)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open Johnson.Prover.Send (Rows)
open ProofFile.Honest.K2 (FreshTable Stretch messageRows)
open ProofFile.Honest.K10.YesFree (BaseData)

/-- An element of the base field, laid as the program's element, reads as its image. -/
theorem readE_eOfF (y : Cb.Gl.F) : readE (eOfF y) = algebraMap Cb.Gl.F Cb.Gl.E y := by
  show OnBytes.Slice.toE (eOfF y).triple = _
  show OnBytes.Slice.toE (Fmt.Fld.ofF (OnBytes.Slice.ofF y)) = _
  rw [OnBytes.Slice.toE_ofF, OnBytes.Slice.toF_ofF]

/-- An entry of a member as the closing takes it, read in the field. -/
theorem readE_member (g : GroupMember) (Rr : Rows) (part : OnBytes.Part) (b p : Nat) :
    readE (rowsSel part (memberOf g Rr) b p) = K1.rowsMsg g.shape Rr (part == .mask) b p := by
  cases part
  · show readE (if g.shape.mainDeg == 3 then E.ofTriple (OnBytes.Slice.ofE (Rr.mainE b p)) else eOfF (Rr.mainF b p)) =
      Rr.main (g.shape.mainDeg == 3) b p
    unfold Rows.main
    by_cases c : (g.shape.mainDeg == 3) = true
    · rw [if_pos c, if_pos c, readE_ofTriple, toE_ofE]
    · rw [if_neg c, if_neg c, readE_eOfF]
  · show readE (E.ofTriple (OnBytes.Slice.ofE (Rr.mask b p))) = Rr.mask b p
    rw [readE_ofTriple, toE_ofE]

/-- The message length of the code of a shape's rows of a table. -/
def ellOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : OnBytes.Part → Nat
  | .main => (codes.base.getD s.code default).ell
  | .mask => (codes.mask.getD s.maskCode default).ell

/-- The rows that the shared text returns are 0 from the code's message length on. -/
theorem rowsMsg_beyond {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    {data : Nat → Nat → Cb.Gl.E} {k : Stretch} {Rr : Rows} (h : messageRows table codes s fold data k = .ok Rr)
    (part : OnBytes.Part) (b j : Nat) (hj : ellOf codes s part ≤ j) :
    K1.rowsMsg s Rr (part == .mask) b j = 0 := by
  obtain ⟨-, -, -, cF, cE, cM, cT, -, -, -, -, rfl⟩ := K2.messageRows_laid h
  have z0 : zeroG = 0 := toE_zeroE
  cases part
  · have hn : ¬ j < (codes.base[s.code]?.getD default).ell := by
      rw [← Array.getD_eq_getD_getElem?]
      exact Nat.not_lt.2 hj
    show (K2.laidRows table codes s fold data cF cE cM cT).main (s.mainDeg == 3) b j = 0
    unfold Rows.main K2.laidRows
    by_cases c : (s.mainDeg == 3) = true
    · simp [c, hn, z0]
    · simp [c, hn, toF_zero]
  · have hn : ¬ j < (codes.mask[s.maskCode]?.getD default).ell := by
      rw [← Array.getD_eq_getD_getElem?]
      exact Nat.not_lt.2 hj
    show (K2.laidRows table codes s fold data cF cE cM cT).mask b j = 0
    unfold K2.laidRows
    simp [hn, z0]

/-- The witness's table of a message that has a seat and a shape. -/
theorem tabAt_seat {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (seatAt : Nat → Option (Nat × Nat))
    (S : Statement) (v : Wit Cells Tok MsgT) {o : Nat} {q : Nat × Nat} {x : OnBytes.Oracle} (hq : seatAt o = some q)
    (hx : S.oracles[o]? = some x) : tabAt cs arr seatAt S v o = v.tab cs x.shape (arr q.1 q.2) q.1 q.2 := by
  unfold tabAt
  rw [hq, hx]

/-- **The field tie's equation, from the senders' form of a sentence on the witness's tables.** -/
theorem tie_of_rowsMsg {Cells Tok : Type} (arr : Nat → Nat → Nat) {s : First.S} {D : BaseData} {R : GroupData}
    {v : Wit Cells Tok MsgT}
    (hth : ∀ o ∈ D.G.members.toList, o < s.st.oracles.size)
    (hM : ∀ o ∈ D.G.members.toList, ∃ (i : Nat) (g : GroupMember) (Rr : Rows),
      D.G.members.idxOf? o = some i ∧ R.members[i]? = some (memberOf g Rr) ∧
      tabAt s.st.codes arr (seatBy noFirst s.book) s.st v o = K1.rowsMsg g.shape Rr ∧
      ∀ (part : OnBytes.Part) (b j : Nat), ellAt R part ≤ j → K1.rowsMsg g.shape Rr (part == .mask) b j = 0) :
    OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (wordsFirst arr s.st s.book v) =
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R) :=
  tie_of_tabAt arr hth fun o ho part b j _ => by
    obtain ⟨i, g, Rr, hi, hR, hT, h0⟩ := hM o ho
    rw [hT]
    by_cases c : j < ellAt R part
    · rw [if_pos c]
      unfold rowsAt
      rw [hi, Option.bind_some, hR]
      exact (readE_member g Rr part b j).symm
    · rw [if_neg c]
      exact h0 part b j (Nat.le_of_not_lt c)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.readE_eOfF
#print axioms ProofFile.Honest.K10.readE_member
#print axioms ProofFile.Honest.K10.ellOf
#print axioms ProofFile.Honest.K10.rowsMsg_beyond
#print axioms ProofFile.Honest.K10.tabAt_seat
#print axioms ProofFile.Honest.K10.tie_of_rowsMsg
