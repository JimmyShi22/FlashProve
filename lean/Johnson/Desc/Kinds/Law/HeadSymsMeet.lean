-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadSymsMeet.lean (the columns are a letter Cols): TWO READERS
OF ONE WITNESS FIND THE SAME COMMITTED SYMBOL:
the lookup's caller's (Johnson/Desc/First/Look/K3CallerAtt.lean: symAt, through seatCalls and its
own list of messages) and the table's (Johnson/Goal/Meaning/HidSeat.lean: symAt, through
Sound.readAt at the seats seatLay): each comes down to THE ONE ACCESSOR Wit.tab at a shape, a
number, a seat, a row and a place; where these five agree the symbols are one.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  sym_of_calls: what the caller's reader finds at (array number t, row r, column c) of link i:
      Wit.tab at member k of its list: under: the link's list names the array; the layout holds it;
      it lays the element at rp; seatCalls' own arm gives member k; rp lies inside member k's table.
  sym_of_table: what the table's reader finds at a number n, row, place: Wit.tab at the member y of
      the reader's list that sits at THE tenant x with that number.
  mask_of_calls: the like at an entry of the mask row: Wit.tab at the link's own first message with
      a mask row, row 0, place j.
  syms_meet_at: so the two are one, where codes, shape, seat, row and place agree.

  CallsSeated: WHAT TIES THE CALLER'S PUBLIC LETTERS TO THE TABLE'S, EIGHT FACTS A MATRIX.
  syms_meet: THE TWO READERS FIND THE SAME SYMBOLS IN THE COLUMNS Cols: from the
      test laidThere, PlanK6's clause named, two equations (the layout, the codes) and
      CallsSeated.

Every letter under "there is" (in CallsSeated): k: pinned by seatCalls' arm; x: by the caller's seat
of member k; y: by the table's list's first member at x.
What it does not say. THAT THE PREMISES HOLD AT ANY PLAN: they are sentences on public data (the
caller's structure of what is sent D, its seats seatT and numbers arr'; the table's numbers N, arr
and
list msR): a test with code could ask them matrix by matrix: NOT TYPED. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Desc.First.Att.K05CellAt
import Johnson.Desc.Kinds.Law.DataMeets
import Johnson.Desc.Kinds.Law.PlanK6At

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.First (Numbers)
open Johnson.Pack (pMain)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt bornAt valAt finOf
  finOf_some laidPlace)
open VerifiableInference.Desc.First.Att.P (laidPlace_one)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce seatOf numOf memTab seatTab msgsOf)

/-- **What the caller's reader finds.** -/
theorem sym_of_calls {Cells Tok : Type} (D : Sent) (rad : OracleShape → Nat) (i : Nat)
    (seatT : Fin (sigListCalls D rad i).length → Nat × Nat) (arr' : Nat → Nat → Nat)
    (w : Wit Cells Tok MsgT) (t r c : Nat) (bn : Nat × String) (A : ReqArray) (rp : Nat × Nat)
    (k : Nat) (hk : k < (sigListCalls D rad i).length)
    (h1 : (D.arrayOf.getD i #[])[t]? = some bn) (h2 : reqArray D.layout bn.1 bn.2 = some A)
    (h3 : Desc.laidAt A r c = some rp)
    (h4 : (if bn.1 == i then some (⟨(keptAt D i).length + A.message, false, rp.1, rp.2⟩ :
        First.Look.Seat)
      else ((bornAt D i).idxOf? (bn.1, A.message)).map fun k' => ⟨k', false, rp.1, rp.2⟩) =
        some ⟨k, false, rp.1, rp.2⟩)
    (h5 : rp.1 < ((sigListCalls D rad i).get ⟨k, hk⟩).1.mainRows)
    (h6 : rp.2 < (pMain D.codes ((sigListCalls D rad i).get ⟨k, hk⟩).1).ell) :
    (valAt D.codes (sigListCalls D rad i) (seatCalls D i)
        (msgsOf D.codes (sigListCalls D rad i) seatT arr' w) (.cell t r c)).getD 0 =
      w.tab D.codes ((sigListCalls D rad i).get ⟨k, hk⟩).1
        (arr' (seatT ⟨k, hk⟩).1 (seatT ⟨k, hk⟩).2) (seatT ⟨k, hk⟩).1 (seatT ⟨k, hk⟩).2 false rp.1
        rp.2 := by
  have es : seatCalls D i (.cell t r c) = some ⟨k, false, rp.1, rp.2⟩ := by
    show ((D.arrayOf.getD i #[])[t]?.bind _) = _
    rw [h1]
    show ((reqArray D.layout bn.1 bn.2).bind _) = _
    rw [h2]
    show ((laidPlace A.blocks r c).bind _) = _
    rw [laidPlace_one, h3]
    exact h4
  unfold valAt
  rw [es]
  show (First.Look.readAt D.codes (sigListCalls D rad i) _ ⟨k, false, rp.1, rp.2⟩).getD 0 = _
  unfold First.Look.readAt
  rw [dif_pos hk]
  simp only [Bool.false_eq_true, if_false]
  rw [finOf_some h5, finOf_some h6]
  rfl

/-- **What the table's reader finds.** -/
theorem sym_of_table {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (w : Wit Cells Tok MsgT) (n : Nat) (x : Nat × Nat) (y : Mem)
    (h1 : namedOnce arr N 24 n = true) (hg : x ∈ N.group 24) (hn : arr x.1 x.2 = n)
    (hy : (msR.find? fun y => Decidable.decide (seatOf y = x)) = some y) (mask : Bool)
    (row place : Nat) :
    Sound.readAt cs arr msR N 24 w n mask row place =
      w.tab cs (y.1.l.get y.2).1 n x.1 x.2 mask row place := by
  rw [readAt_at_seat cs arr msR N 24 n w h1 x hg hn]
  have hs0 := List.find?_some hy
  have hs : seatOf y = x := of_decide_eq_true hs0
  have e : seatTab cs arr msR w x = memTab cs arr w y := by
    unfold seatTab
    rw [hy]
  rw [e]
  unfold memTab numOf
  have hs' : y.1.seat y.2 = x := hs
  rw [hs', hn]

/-- **What the caller's reader finds at an entry of the mask row.** -/
theorem mask_of_calls {Cells Tok : Type} (D : Sent) (rad : OracleShape → Nat) (i : Nat)
    (seatT : Fin (sigListCalls D rad i).length → Nat × Nat) (arr' : Nat → Nat → Nat)
    (w : Wit Cells Tok MsgT) (j m0 : Nat)
    (hk : (keptAt D i).length + m0 < (sigListCalls D rad i).length)
    (h1 : ((First.Look.messagesAt D i).findIdx? fun x => x.shape.maskRows != 0) = some m0)
    (h5 : 0 < ((sigListCalls D rad i).get ⟨(keptAt D i).length + m0, hk⟩).1.maskRows)
    (h6 : j < (Johnson.Pack.pMask D.codes
      ((sigListCalls D rad i).get ⟨(keptAt D i).length + m0, hk⟩).1).ell) :
    (valAt D.codes (sigListCalls D rad i) (seatCalls D i)
        (msgsOf D.codes (sigListCalls D rad i) seatT arr' w) (.mask j)).getD 0 =
      w.tab D.codes ((sigListCalls D rad i).get ⟨(keptAt D i).length + m0, hk⟩).1
        (arr' (seatT ⟨(keptAt D i).length + m0, hk⟩).1 (seatT ⟨(keptAt D i).length + m0, hk⟩).2)
        (seatT ⟨(keptAt D i).length + m0, hk⟩).1 (seatT ⟨(keptAt D i).length + m0, hk⟩).2 true 0
        j := by
  have es : seatCalls D i (.mask j) = some ⟨(keptAt D i).length + m0, true, 0, j⟩ := by
    show (((First.Look.messagesAt D i).findIdx? fun x => x.shape.maskRows != 0).map _) = _
    rw [h1]
    rfl
  unfold valAt
  rw [es]
  show (First.Look.readAt D.codes (sigListCalls D rad i) _
    ⟨(keptAt D i).length + m0, true, 0, j⟩).getD 0 = _
  unfold First.Look.readAt
  rw [dif_pos hk]
  simp only [if_true]
  rw [finOf_some h5, finOf_some h6]
  rfl

/-- **The two are one.** -/
theorem syms_meet_at {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (D : Sent) (rad : OracleShape → Nat) (i : Nat)
    (seatT : Fin (sigListCalls D rad i).length → Nat × Nat) (w : Wit Cells Tok MsgT)
    (t r c : Nat) (bn : Nat × String) (A : ReqArray) (rp : Nat × Nat) (k : Nat)
    (hk : k < (sigListCalls D rad i).length) (n : Nat) (x : Nat × Nat) (y : Mem)
    (h1 : (D.arrayOf.getD i #[])[t]? = some bn) (h2 : reqArray D.layout bn.1 bn.2 = some A)
    (h3 : Desc.laidAt A r c = some rp)
    (h4 : (if bn.1 == i then some (⟨(keptAt D i).length + A.message, false, rp.1, rp.2⟩ :
        First.Look.Seat)
      else ((bornAt D i).idxOf? (bn.1, A.message)).map fun k' => ⟨k', false, rp.1, rp.2⟩) =
        some ⟨k, false, rp.1, rp.2⟩)
    (h5 : rp.1 < ((sigListCalls D rad i).get ⟨k, hk⟩).1.mainRows)
    (h6 : rp.2 < (pMain D.codes ((sigListCalls D rad i).get ⟨k, hk⟩).1).ell)
    (hcs : D.codes = cs) (hseat : seatT ⟨k, hk⟩ = x)
    (hshape : ((sigListCalls D rad i).get ⟨k, hk⟩).1 = (y.1.l.get y.2).1)
    (g1 : namedOnce arr N 24 n = true) (hg : x ∈ N.group 24) (hn : arr x.1 x.2 = n)
    (hy : (msR.find? fun y => Decidable.decide (seatOf y = x)) = some y) :
    (valAt D.codes (sigListCalls D rad i) (seatCalls D i)
        (msgsOf D.codes (sigListCalls D rad i) seatT arr w) (.cell t r c)).getD 0 =
      Sound.readAt cs arr msR N 24 w n false rp.1 rp.2 := by
  rw [sym_of_calls D rad i seatT arr w t r c bn A rp k hk h1 h2 h3 h4 h5 h6,
    sym_of_table cs arr msR N w n x y g1 hg hn hy false, hseat, hshape, hcs, hn]

end VerifiableInference.Desc.Kinds.Head.Law.Came

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (borderOf)
open Johnson.Pack (pMain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls keptAt bornAt)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce seatOf)

/-- **What ties the caller's public letters to the table's, A MATRIX**: for each of segment 24's
matrices that has a column in Cols (a letter: the four ranges' columns; the planes' matrix's), and
the array A that its label names in the layout:
the link's list of arrays names that array at the number that the plan's entry gives the matrix;
seatCalls' arm gives one member k of the caller's list, whatever the place; A's places lie inside
member k's table; member k sits at x, a tenant of segment 24's group with the number that num gives
the message; the first member of the table's list at x has member k's shape. -/
def CallsSeated (Cols : Nat → Nat → Prop) (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers)
    (Wp : OnBytes.Model.Verify.Public) (lay : ReqLayout) (num : Nat → Nat → Nat) (D : Sent)
    (rad : OracleShape → Nat) (i : Nat) (seatT : Fin (sigListCalls D rad i).length → Nat × Nat) :
    Prop :=
  ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (c : Nat), c < (Meaning.sizesOf Wp 24).k μ →
    Cols μ.val c → ∀ A : ReqArray,
    Desc.arrayOf lay (Meaning.ownerK (Meaning.labAt Wp 24 μ.val))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 μ.val))) = some A →
    ∃ (k : Nat) (hk : k < (sigListCalls D rad i).length) (x : Nat × Nat) (y : Mem),
      (D.arrayOf.getD i #[])[(Meaning.tlAt Wp 24).gtTree.getD μ.val 0]? =
        some (Meaning.ownerK (Meaning.labAt Wp 24 μ.val),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 μ.val))) ∧
      (∀ rp : Nat × Nat, (if Meaning.ownerK (Meaning.labAt Wp 24 μ.val) == i then
          some (⟨(keptAt D i).length + A.message, false, rp.1, rp.2⟩ : First.Look.Seat)
        else ((bornAt D i).idxOf? (Meaning.ownerK (Meaning.labAt Wp 24 μ.val), A.message)).map
          fun k' => ⟨k', false, rp.1, rp.2⟩) = some ⟨k, false, rp.1, rp.2⟩) ∧
      (∀ r c' rp, Desc.laidAt A r c' = some rp →
        rp.1 < ((sigListCalls D rad i).get ⟨k, hk⟩).1.mainRows ∧
          rp.2 < (pMain D.codes ((sigListCalls D rad i).get ⟨k, hk⟩).1).ell) ∧
      seatT ⟨k, hk⟩ = x ∧ ((sigListCalls D rad i).get ⟨k, hk⟩).1 = (y.1.l.get y.2).1 ∧
      x ∈ N.group 24 ∧
      arr x.1 x.2 = num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message ∧
      (msR.find? fun y => Decidable.decide (seatOf y = x)) = some y

namespace Came

/-- **THE TWO READERS FIND THE SAME SYMBOLS IN THE COLUMNS OF THE FOUR RANGES.** -/
theorem syms_meet {Cells Tok : Type} (Cols : Nat → Nat → Prop) (cs : OnBytes.Codes) (arr : Nat → Nat
    → Nat)
    (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (lay : ReqLayout)
    (num : Nat → Nat → Nat) (D : Sent) (rad : OracleShape → Nat) (i : Nat)
    (seatT : Fin (sigListCalls D rad i).length → Nat × Nat) (w : Wit Cells Tok MsgT)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay = true) (hlay : D.layout = lay)
    (hcs : D.codes = cs)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      Cols μ.val c →
      namedOnce arr N 24 (seatLay Wp lay num 24 μ r c).1 = true)
    (hC : CallsSeated Cols arr msR N Wp lay num D rad i seatT)
    (μ : Fin (Meaning.sizesOf Wp 24).NM) (c : Fin ((Meaning.sizesOf Wp 24).k μ))
    (hcol : Cols μ.val c.val)
    (i' : Fin (Alg.symRows ((Meaning.sizesOf Wp 24).m μ))) :
    First.Look.symAt D.codes (sigListCalls D rad i) (seatCalls D i) (Meaning.tlAt Wp 24)
        (Sound.msgsOf D.codes (sigListCalls D rad i) seatT arr w) μ i' c =
      Meaning.symAt (Meaning.sizesOf Wp 24) (seatLay Wp lay num 24)
        (Sound.readAt cs arr msR N 24 w) μ i' c := by
  obtain ⟨A, rp, hA, _, _, hl, hs⟩ :=
    Meaning.seat_of_laidThere T num (k := 24) (by decide) μ i'.isLt c.isLt
  obtain ⟨k, hk, x, y, c1, c2, c3, c4, c5, c6, c7, c8⟩ := hC μ c.val c.isLt hcol A hA
  have h8 := p1 μ i'.val c.val i'.isLt c.isLt hcol
  have e : seatLay Wp lay num 24 μ i'.val c.val =
      (num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message, rp.1, rp.2) := hs
  rw [e] at h8
  show (First.Look.valAt D.codes (sigListCalls D rad i) (seatCalls D i)
      (Sound.msgsOf D.codes (sigListCalls D rad i) seatT arr w)
      (.cell ((Meaning.tlAt Wp 24).gtTree.getD μ.val 0) i'.val c.val)).getD 0 =
    Sound.readAt cs arr msR N 24 w (seatLay Wp lay num 24 μ i'.val c.val).1 false
      (seatLay Wp lay num 24 μ i'.val c.val).2.1 (seatLay Wp lay num 24 μ i'.val c.val).2.2
  rw [e]
  exact syms_meet_at cs arr msR N D rad i seatT w _ i'.val c.val _ A rp k hk _ x y c1
    (by rw [hlay]; exact hA) hl (c2 rp) (c3 _ _ rp hl).1 (c3 _ _ rp hl).2 hcs c4 c5 h8 c6 c7 c8

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sym_of_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sym_of_table
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.mask_of_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.syms_meet_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.syms_meet
