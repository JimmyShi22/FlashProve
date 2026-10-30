-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaceSent.lean: THE SENTENCE ON THE LAYING IN TWO HALVES, so that a
filling which is wrapped, or joined of two, or seated by another's seat can call it: the layout's
half at any seat; the sender's half at any filling and any job of the shared "sending". With them:
what a joined filling lays and hands; the ties at a segment's later moment; a corollary for a bare
filling there. Theorems; no definition outside the instances at the foot. What is WRITTEN where: no
sentence on what a coin is for.

Main names (namespace ProofFile.Honest.K1).
  laidData_place   THE LAYOUT's HALF: of laidData (Honest/LaidData.lean) at ANY seat; no sender is
      spoken of. Asked: the seat names the message; the message fits (msgFits); the codes' lengths
      are lawful (Own.lengthsFit); the array is laid in the message; the element lies inside the
      array's size and the size that V says. Its end hands what the sender's half asks: the base
      code; the place; the way back; the bounds; off padInMain's places; the message is sampled; the
      filling lays data there; its entry is V's value; no other element lies there.
  sent_at_shape   THE SENDER's HALF: sent_of_lays (Honest/Law/LaidSent.lean) of ANY filling and ANY
      job, in the letters in which the layout's half ends. readyAt is asked by name, as there.
  over_left, over_right, over_ready   of RowData.over (Honest/RowData.lean): where the first lays,
      the joined filling lays and hands the first's entry at the first's own cut of the challenges;
      where the first lays nothing and the second lays, the second's; where the joined filling is
      ready, each is.
  not_lays   where the way back reads an element of an array that V does not know, laidData at V
      lays nothing: what over_right asks of the first.
  momentSeat_says   what a seat of one moment says where it names a message: general in the segment,
      the moment and the number from which the moment's messages stand.
  later_shape   at K1.parLater q gp l piece t the job's message of rank k has the shape of the
      moment's member of rank k.
  fit_of_readyAt   where laidData is ready at an address, the message that the seat names fits
      (msgFits): of any seat.
  later_sent_at   A COROLLARY: a bare laidData at momentSeat at a segment's later moment: all ties
      of seat and job but the case mark are paid; sendFits, readyAt at the list heard, and that the
      seat names a message stay premises.

By calls: once_and_back_msg (Law/LaidOnce.lean); elements_apart_msg (Law/LaidApart.lean);
lays_clear, nth_of_zipIdx (Law/LaidLaw.lean); sent_of_lays, lays_of_back, entry_of_back,
code_of_msgFits, pow_of_lengths (Law/LaidSent.lean); fits_lengths (K1/PadLaw.lean); K1.parLater_sent
(Johnson/Desc/K1/Law/Links.lean). Kin: laid_sent (Law/LaidSent.lean) is the two halves in one, at a
bare filling; it is not retyped here.

WHAT STAYS OPEN. (1) later_sent_at is general in l, piece and t: THAT THE LOT's OWN MEMBER AT A
PLACE IS THE MEMBER AT THESE NUMBERS is not said here. (2) The fillings that are meant for the later
moments are seated by another seat than momentSeat: that such a seat names, at the lot's places, the
moment's member of rank k is not said here: the rank: seats_tie (Honest/Law/SeatTie.lean); the
place, under the lot's public tests, for "U3" and "BZ": reads_every_seat, digits_every_seat
(Honest/Law/SeatAtLot.lean). No corollary here joins these with the two halves: later_sent_at is the
one here with all ties paid. (3) Where both parts of a joined filling lay at one place the first
wins, without a word: RowData.apart is the test for that: it is asked nowhere here; over_right asks
by name that the first lays nothing. (4) "None of the pad's" is padInMain's places
(Honest/RowData.lean); that at a pad's places of a sampled message's main rows the sender's entry is
one of its coins, whatever the data, where the pad is no longer than its row, is pad_coin_e and _f
(Honest/K1/CoinLaw.lean: at the places (mainRows - 1, ell - pad + i); that these are padInMain's
members is read off the two texts), and that off padInMain's places it is what the data say is
main_data_e and _f (Honest/K1/DataLaw.lean): not called here. Over the base field the sender lays 0
where the filling hands an element of the extension field. (5) Nothing on the mask table, on a
riding table, on a sample. Nothing on any property.

THE PREMISES CAN BE MET: two instances AS TERMS at the foot, at synthetic parameters (one segment; a
message of moment 1 that holds two arrays): a bare filling (later_sent_at); and a filling joined of
two, each of which knows one of the arrays, at an element of the second's: the layout's half,
not_lays, over_right and the sender's half in one term.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaidSent
import Johnson.Desc.K1.Law.Links
import Johnson.Desc.K1.Law.QFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Params (ReqArray ReqMessage ReqShape)
open OnBytes.Slice (GF GE)
open Johnson.Prover.Send (shapeAt)

/-- **What a seat of one moment says** where it names a message: the address is the sender's, at or
behind the number from which the moment's messages stand; the segment is the seat's own; the message
stands in the segment's list at the number named, and is the moment's member of that rank. -/
theorem momentSeat_says {s : ReqShape} {sender : Addr} {l t «from» : Nat} {a : MsgAddr} {l' m : Nat}
    (h : momentSeat s sender l t «from» a = some (l', m)) :
    a.sender = sender ∧ «from» ≤ a.msg ∧ l' = l ∧
      ∃ M, (s.link.getD l default).messages[m]? = some M ∧
        ((s.link.getD l default).messages.filter fun M => M.moment == t)[a.msg - «from»]? =
          some M := by
  unfold momentSeat at h
  split at h
  · rename_i hc
    obtain ⟨m', hm, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    unfold msgNo at hm
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hm
    obtain ⟨h1, h2⟩ := nth_of_zipIdx _ (fun M => M.moment == t) _ x hx
    exact ⟨by simpa using hc.1, hc.2, rfl, x.1, h2, h1⟩
  · cases h

/-- The job's message of that rank at a later place has the message's shape. -/
theorem later_shape (q : Params.First) (gp : _root_.Desc.Plain.GPar) (l piece t : Nat) {k : Nat}
    {M : ReqMessage}
    (h : ((q.shape.link.getD l default).messages.filter fun M => M.moment == t)[k]? = some M) :
    shapeAt (K1.parLater q gp l piece t) k = M.shape := by
  have hlink : ((q.shape.link[l]?.map (·.messages)).getD []) =
      (q.shape.link.getD l default).messages := by
    rw [List.getD_eq_getElem?_getD]
    cases q.shape.link[l]? <;> rfl
  have hs : (K1.parLater q gp l piece t).sent.toList[k]? =
      some ⟨M.shape, M.leafClass⟩ := by
    rw [K1.parLater_sent]
    unfold K1.laterSent K1.frameAt OnBytes.ReqFrame.notices OnBytes.ReqFrame.atMoment
    show (((q.shape.link[l]?.map (·.messages)).getD []).filter (fun M => M.moment == t) |>.map
      fun m => ({ shape := m.shape, leafClass := m.leafClass } : OracleNotice))[k]? = _
    rw [hlink, List.getElem?_map, h]
    rfl
  unfold shapeAt
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hs]
  rfl

/-- Where the filling's data is ready, the message that the seat names fits: of any seat. -/
theorem fit_of_readyAt {codes : Codes} {s : ReqShape} {lay : Params.ReqLayout}
    {seat : MsgAddr → Option (Nat × Nat)} {heard : MsgAddr → Nat} {V : ArrayVals}
    {hd : List Fmt.Drawn} {x : MsgAddr} {l m : Nat}
    (h : (laidData codes s lay seat heard V).readyAt hd x = true) (t1 : seat x = some (l, m)) :
    msgFits codes s lay l m = true := by
  unfold RowData.readyAt at h
  rw [Bool.and_eq_true] at h
  have h3 : ((seat x).all fun y => layFits s lay && msgFits codes s lay y.1 y.2 &&
      V.ready (hd.take (heard x)) y.1) = true := h.2
  rw [t1] at h3
  simp only [Option.all_some, Bool.and_eq_true] at h3
  exact h3.1.2

/-! ## The layout's half, at any seat -/

/-- **THE LAYOUT's HALF**: of laidData at ANY seat; no sender is spoken of. At a message that the
seat names and that fits, under codes whose lengths are lawful (Own.lengthsFit): each element of
each of V's arrays that is laid in it has one main row and place; from there the way back reads it;
the place lies inside the main rows and the length and off the places of the pad; the message is
sampled; the filling lays data there, and its entry is V's value at the element; no other element
lies there. -/
theorem laidData_place (codes : Codes) (s : ReqShape) (lay : Params.ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals) (x : MsgAddr)
    (l m : Nat) (M : ReqMessage) (t1 : seat x = some (l, m))
    (t2 : (s.link.getD l default).messages[m]? = some M)
    (hfit : msgFits codes s lay l m = true) (hlen : Own.lengthsFit codes = true)
    (a : ReqArray) (ha : a ∈ (lay.link.getD l []).filter fun a => a.message == m) (i c : Nat)
    (hi : i < a.sizeI) (hc : c < a.sizeC) (z : Nat × Nat) (hV : V.size l a.name = some z)
    (hz : i < z.1 ∧ c < z.2) :
    ∃ cd r j, codes.base[M.shape.code]? = some cd ∧
      laidAt a i c = some (r, j) ∧ laidBack lay l m r j = some (a, i, c) ∧
      r < M.shape.mainRows ∧ j < cd.ell ∧ (r, j) ∉ padInMain cd.ell M.shape ∧
      M.shape.answers ≠ 0 ∧
      (laidData codes s lay seat heard V).lays x r j = true ∧
      (∀ Rd h, (laidData codes s lay seat heard V).entry Rd h x r j = V.val Rd h l a.name i c) ∧
      ∀ a' ∈ (lay.link.getD l []).filter (fun a => a.message == m), ∀ i' c',
        laidAt a' i' c' = some (r, j) → a' = a ∧ i' = i ∧ c' = c := by
  obtain ⟨cd, t5⟩ := code_of_msgFits codes s lay hfit t2 ha
  obtain ⟨r, j, hp, hb⟩ := once_and_back_msg hfit ha hi hc
  have hl := lays_of_back codes s lay seat heard V t1 hfit hb hV hz
  obtain ⟨b1, b2, b3, b4⟩ := lays_clear codes s lay seat heard V x r j l m M cd hl t1 t2 t5
    (pow_of_lengths codes hlen t5)
  exact ⟨cd, r, j, t5, hp, hb, b1, b2, b3, b4, hl,
    fun Rd h => entry_of_back codes s lay seat heard V Rd h t1 hb,
    fun a' ha' i' c' h' => elements_apart_msg hfit ha' ha h' hp⟩

/-! ## The sender's half, at any filling -/

/-- **THE SENDER's HALF**, of ANY filling D and ANY job, in the letters in which the layout's half
ends: sent_of_lays (Honest/Law/LaidSent.lean) at a message M whose shape the job's message number k
has, under the filling's codes. -/
theorem sent_at_shape (D : RowData) (Rd : Readers) (hd : List Fmt.Drawn) (P : K1.Par)
    (ride : Nat → Option Ride) (sender : Addr) (k : Nat) (cs : Cs (dueR P ride)) (codes : Codes)
    (M : ReqMessage) (cd : Code) (r j : Nat) (t3 : shapeAt P k = M.shape) (t4 : P.codes = codes)
    (t5 : codes.base[M.shape.code]? = some cd) (hl : D.lays ⟨sender, k⟩ r j = true)
    (hready : D.readyAt hd ⟨sender, k⟩ = true) (hr : r < M.shape.mainRows) (hj : j < cd.ell)
    (hp : (r, j) ∉ padInMain cd.ell M.shape) (ha : M.shape.answers ≠ 0) :
    ((hd.take (D.heardAt ⟨sender, k⟩)).length = D.heardAt ⟨sender, k⟩ ∧
      D.ready (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ = true) ∧
    ((M.shape.mainDeg == 3) = true →
      (rowsR P ride (D.forSend Rd sender hd) cs k).mainE r j =
        match D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j with
        | .inr x => x
        | .inl x => algebraMap GF GE x) ∧
    ((M.shape.mainDeg == 3) = false →
      (rowsR P ride (D.forSend Rd sender hd) cs k).mainF r j =
        match D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j with
        | .inl x => x
        | .inr _ => 0) := by
  have ec : (P.codes.base.getD (shapeAt P k).code default) = cd := by
    rw [t3, t4, Array.getD_eq_getD_getElem?, t5, Option.getD_some]
  have hs := sent_of_lays D Rd hd P ride sender k cs r j hl hready (by rw [t3]; exact hr)
    (by rw [ec]; exact hj) (by rw [t3]; exact ha) (by rw [ec, t3]; exact hp)
  rw [t3] at hs
  exact hs

/-! ## Two fillings of one message, joined by place -/

/-- Where the first lays, the joined filling lays, and hands the first's entry, at the challenges
cut to the first's own count. -/
theorem over_left (A B : RowData) (x : MsgAddr) (r j : Nat) (h : A.lays x r j = true) :
    (A.over B).lays x r j = true ∧
      ∀ Rd hd, (A.over B).entry Rd hd x r j = A.entry Rd (hd.take (A.heardAt x)) x r j := by
  refine ⟨?_, fun Rd hd => ?_⟩
  · show (A.lays x r j || B.lays x r j) = true
    rw [h, Bool.true_or]
  · show (if A.lays x r j then A.entry Rd (hd.take (A.heardAt x)) x r j
      else B.entry Rd (hd.take (B.heardAt x)) x r j) = _
    rw [if_pos h]

/-- Where the first lays nothing and the second lays, the joined filling lays, and hands the
second's entry, at the challenges cut to the second's own count. -/
theorem over_right (A B : RowData) (x : MsgAddr) (r j : Nat) (h : A.lays x r j = false)
    (h' : B.lays x r j = true) :
    (A.over B).lays x r j = true ∧
      ∀ Rd hd, (A.over B).entry Rd hd x r j = B.entry Rd (hd.take (B.heardAt x)) x r j := by
  refine ⟨?_, fun Rd hd => ?_⟩
  · show (A.lays x r j || B.lays x r j) = true
    rw [h', Bool.or_true]
  · show (if A.lays x r j then A.entry Rd (hd.take (A.heardAt x)) x r j
      else B.entry Rd (hd.take (B.heardAt x)) x r j) = _
    rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- Where the way back reads an element of an array that V does not know, the filling lays
nothing: what the joined filling's second arm asks of the first. -/
theorem not_lays (codes : Codes) (s : ReqShape) (lay : Params.ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals) {x : MsgAddr}
    {l m r j i c : Nat} {a : ReqArray} (t1 : seat x = some (l, m))
    (hb : laidBack lay l m r j = some (a, i, c)) (hV : V.size l a.name = none) :
    (laidData codes s lay seat heard V).lays x r j = false := by
  show (match seat x with
    | some (l, m) =>
      msgFits codes s lay l m && (laidBack lay l m r j).any fun y =>
        (V.size l y.1.name).any fun z => decide (y.2.1 < z.1 ∧ y.2.2 < z.2)
    | none => false) = false
  rw [t1]
  simp only [hb, hV, Option.any_some, Option.any_none, Bool.and_false]

/-- Where the joined filling is ready, each of the two is ready. (One direction.) -/
theorem over_ready (A B : RowData) (hd : List Fmt.Drawn) (x : MsgAddr)
    (h : (A.over B).readyAt hd x = true) : A.readyAt hd x = true ∧ B.readyAt hd x = true := by
  have h' : (decide (max (A.heardAt x) (B.heardAt x) ≤ hd.length) &&
      (A.ready ((hd.take (max (A.heardAt x) (B.heardAt x))).take (A.heardAt x)) x &&
        B.ready ((hd.take (max (A.heardAt x) (B.heardAt x))).take (B.heardAt x)) x)) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.take_take, List.take_take,
    Nat.min_eq_left (Nat.le_max_left _ _), Nat.min_eq_left (Nat.le_max_right _ _)] at h'
  constructor
  · show (decide (A.heardAt x ≤ hd.length) && A.ready (hd.take (A.heardAt x)) x) = true
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.le_trans (Nat.le_max_left _ _) h'.1, h'.2.1⟩
  · show (decide (B.heardAt x ≤ hd.length) && B.ready (hd.take (B.heardAt x)) x) = true
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.le_trans (Nat.le_max_right _ _) h'.1, h'.2.2⟩

/-! ## A corollary: a bare filling at a segment's later moment -/

/-- **AT A SEGMENT's LATER MOMENT, OF A BARE FILLING**: the job's numbers are K1.parLater q gp l
piece t; the seat is that moment's (momentSeat); the filling is laidData at any values V and any
count of challenges heard. All ties of seat and job but the case mark are paid. STILL ASKED:
sendFits at these numbers and the ride; readyAt of the filling at the list heard; that the seat
names a message at the address; that the array is laid in that message; that the element lies inside
the array's size and the size that V says. The end: the row and place of laidData_place, and the
sender's main entry there is V's value at the element (over the base field: 0 where V hands an
element of the extension field). -/
theorem later_sent_at (q : Params.First) (gp : _root_.Desc.Plain.GPar) (l piece t part : Nat)
    (heard : MsgAddr → Nat) (V : ArrayVals) (Rd : Readers) (hd : List Fmt.Drawn)
    (ride : Nat → Option Ride) (cs : Cs (dueR (K1.parLater q gp l piece t) ride)) (k l' m : Nat)
    (hsend : sendFits (K1.parLater q gp l piece t) ride = true)
    (hready : (laidData q.codes q.shape q.layout
      (momentSeat q.shape ⟨⟨1, some l, piece, .K1⟩, part⟩ l t 0) heard V).readyAt hd
        ⟨⟨⟨1, some l, piece, .K1⟩, part⟩, k⟩ = true)
    (t1 : momentSeat q.shape ⟨⟨1, some l, piece, .K1⟩, part⟩ l t 0
      ⟨⟨⟨1, some l, piece, .K1⟩, part⟩, k⟩ = some (l', m))
    (a : ReqArray) (ha : a ∈ (q.layout.link.getD l' []).filter fun a => a.message == m)
    (i c : Nat) (hi : i < a.sizeI) (hc : c < a.sizeC) (z : Nat × Nat)
    (hV : V.size l' a.name = some z) (hz : i < z.1 ∧ c < z.2) :
    ∃ M cd r j, (q.shape.link.getD l' default).messages[m]? = some M ∧
      q.codes.base[M.shape.code]? = some cd ∧
      laidAt a i c = some (r, j) ∧ laidBack q.layout l' m r j = some (a, i, c) ∧
      r < M.shape.mainRows ∧ j < cd.ell ∧ (r, j) ∉ padInMain cd.ell M.shape ∧
      ((M.shape.mainDeg == 3) = true →
        (rowsR (K1.parLater q gp l piece t) ride
            ((laidData q.codes q.shape q.layout
              (momentSeat q.shape ⟨⟨1, some l, piece, .K1⟩, part⟩ l t 0) heard V).forSend Rd
                ⟨⟨1, some l, piece, .K1⟩, part⟩ hd) cs k).mainE r j =
          match V.val Rd (hd.take (heard ⟨⟨⟨1, some l, piece, .K1⟩, part⟩, k⟩)) l' a.name i c with
          | .inr x => x
          | .inl x => algebraMap GF GE x) ∧
      ((M.shape.mainDeg == 3) = false →
        (rowsR (K1.parLater q gp l piece t) ride
            ((laidData q.codes q.shape q.layout
              (momentSeat q.shape ⟨⟨1, some l, piece, .K1⟩, part⟩ l t 0) heard V).forSend Rd
                ⟨⟨1, some l, piece, .K1⟩, part⟩ hd) cs k).mainF r j =
          match V.val Rd (hd.take (heard ⟨⟨⟨1, some l, piece, .K1⟩, part⟩, k⟩)) l' a.name i c with
          | .inl x => x
          | .inr _ => 0) ∧
      ∀ a' ∈ (q.layout.link.getD l' []).filter (fun a => a.message == m), ∀ i' c',
        laidAt a' i' c' = some (r, j) → a' = a ∧ i' = i ∧ c' = c := by
  obtain ⟨-, -, rfl, M, t2, hM⟩ := momentSeat_says t1
  have t3 : shapeAt (K1.parLater q gp l' piece t) k = M.shape :=
    later_shape q gp l' piece t (by simpa using hM)
  obtain ⟨cd, r, j, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ :=
    laidData_place q.codes q.shape q.layout _ heard V _ l' m M t1 t2 (fit_of_readyAt hready t1)
      (fits_lengths _ ride hsend) a ha i c hi hc z hV hz
  have hs := sent_at_shape _ Rd hd (K1.parLater q gp l' piece t) ride
    ⟨⟨1, some l', piece, .K1⟩, part⟩ k cs q.codes M cd r j t3 rfl e1 e8 hready e4 e5 e6 e7
  rw [e9] at hs
  exact ⟨M, cd, r, j, t2, e1, e2, e3, e4, e5, e6, hs.2.1, hs.2.2, e10⟩

/-! ### The premises can be met: two instances, as terms -/

namespace PlaceSentToy

/-- One base code; no mask code. -/
def codes : Codes := { base := #[⟨6, 16, 1⟩] }
/-- A message of two main rows over the base field, sampled. -/
def o : OracleShape := { code := 0, mainRows := 2, mainDeg := 1, maskRows := 0, answers := 1 }
/-- Synthetic parameters: one segment: a message of moment 0 and one of moment 1. The second holds
two arrays, "A" in row 0 and "B" in the first half of row 1: off the pad's places, the last three of
row 1. -/
def q : Params.First :=
  { K1.qFull with
    codes := codes
    shape := { code := 0, maskCode := 0, answers := 1, last := [], choice := default, atStart := []
               link := [⟨0, [⟨o, 0, 0, 0⟩, ⟨o, 0, 1, 0⟩]⟩] }
    layout := ⟨[[⟨"A", 1, 4, 4, [⟨0, 0, 0, 0, 2, 2, 0, 4, true⟩]⟩,
                 ⟨"B", 1, 2, 4, [⟨0, 0, 1, 0, 1, 2, 0, 3, true⟩]⟩]]⟩ }
def gp : _root_.Desc.Plain.GPar := ⟨1, 0⟩
def sender : Addr := ⟨⟨1, some 0, 4, .K1⟩, 0⟩
def seat : MsgAddr → Option (Nat × Nat) := momentSeat q.shape sender 0 1 0
/-- Synthetic values: VA knows "A" alone, VB knows "B" alone. -/
def VA : ArrayVals :=
  { size := fun _ n => if n == "A" then some (4, 4) else none
    val := fun _ _ _ _ i c => .inl (OnBytes.Slice.toF (100 + 10 * i.toUInt64 + c.toUInt64)) }
def VB : ArrayVals :=
  { size := fun _ n => if n == "B" then some (2, 4) else none
    val := fun _ _ _ _ i c => .inl (OnBytes.Slice.toF (200 + 10 * i.toUInt64 + c.toUInt64)) }
def DA : RowData := laidData q.codes q.shape q.layout seat (fun _ => 0) VA
def DB : RowData := laidData q.codes q.shape q.layout seat (fun _ => 0) VB
/-- Synthetic readers of zeros (cells, weights, and Readers.rand's pads and tails): stand-ins: VA
and VB read no reader. -/
def Rd : Readers :=
  ⟨⟨fun _ _ _ _ => OnBytes.Slice.toF 0⟩, ⟨fun _ _ => OnBytes.Slice.toF 0⟩,
    fun _ => ⟨fun _ _ => OnBytes.Slice.toF 0, fun _ _ => OnBytes.Slice.toF 0⟩⟩

theorem toy_lengths : Own.lengthsFit q.codes = true := by
  simp only [Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : q.codes.base.size = 1 := rfl
    obtain rfl : i = 0 := by omega
    show Own.twoPower 16 = true
    decide
  · have h0 : q.codes.mask.size = 0 := rfl
    omega

theorem toy_sendFits : sendFits (K1.parLater q gp 0 4 1) (fun _ => none) = true := by
  unfold sendFits
  rw [show Own.lengthsFit (K1.parLater q gp 0 4 1).codes = true from toy_lengths, Bool.true_and]
  decide

/-- **A bare filling at moment 1**: every premise of later_sent_at holds: element (2, 3) of "A",
whatever the sender's coins. -/
example (cs : Cs (dueR (K1.parLater q gp 0 4 1) fun _ => none)) :
    ∃ r j, laidAt ⟨"A", 1, 4, 4, [⟨0, 0, 0, 0, 2, 2, 0, 4, true⟩]⟩ 2 3 = some (r, j) ∧
      (rowsR (K1.parLater q gp 0 4 1) (fun _ => none) (DA.forSend Rd sender []) cs 0).mainF r j =
        OnBytes.Slice.toF 123 := by
  obtain ⟨M, cd, r, j, h0, -, h2, -, -, -, -, -, h8, -⟩ :=
    later_sent_at q gp 0 4 1 0 (fun _ => 0) VA Rd [] (fun _ => none) cs 0 0 1 toy_sendFits
      (by decide) (by decide) ⟨"A", 1, 4, 4, [⟨0, 0, 0, 0, 2, 2, 0, 4, true⟩]⟩ (by decide) 2 3
      (by decide) (by decide) (4, 4) rfl (by decide)
  obtain rfl : (⟨o, 0, 1, 0⟩ : ReqMessage) = M := Option.some.inj h0
  exact ⟨r, j, h2, h8 rfl⟩

/-- **A joined filling**: DA.over DB at an element of "B", which DA does not know: the layout's half
at DB, not_lays at DA, the second arm of the joined filling, the sender's half at the joined
filling: element (1, 2) of "B", whatever the sender's coins. -/
example (cs : Cs (dueR (K1.parLater q gp 0 4 1) fun _ => none)) :
    ∃ r j, laidAt ⟨"B", 1, 2, 4, [⟨0, 0, 1, 0, 1, 2, 0, 3, true⟩]⟩ 1 2 = some (r, j) ∧
      (rowsR (K1.parLater q gp 0 4 1) (fun _ => none) ((DA.over DB).forSend Rd sender []) cs
        0).mainF r j = OnBytes.Slice.toF 212 := by
  have t1 : seat ⟨sender, 0⟩ = some (0, 1) := by decide
  obtain ⟨cd, r, j, e1, e2, e3, e4, e5, e6, e7, e8, e9, -⟩ :=
    laidData_place q.codes q.shape q.layout seat (fun _ => 0) VB ⟨sender, 0⟩ 0 1 ⟨o, 0, 1, 0⟩ t1
      (by decide) (by decide) toy_lengths ⟨"B", 1, 2, 4, [⟨0, 0, 1, 0, 1, 2, 0, 3, true⟩]⟩
      (by decide) 1 2 (by decide) (by decide) (2, 4) rfl (by decide)
  have hA : DA.lays ⟨sender, 0⟩ r j = false :=
    not_lays q.codes q.shape q.layout seat (fun _ => 0) VA t1 e3 rfl
  obtain ⟨hl, hent⟩ := over_right DA DB ⟨sender, 0⟩ r j hA e8
  have hs := sent_at_shape (DA.over DB) Rd [] (K1.parLater q gp 0 4 1) (fun _ => none) sender 0 cs
    q.codes ⟨o, 0, 1, 0⟩ cd r j (by decide) rfl e1 hl (by decide) e4 e5 e6 e7
  refine ⟨r, j, e2, ?_⟩
  rw [hs.2.2 rfl, hent, show DB.entry Rd _ ⟨sender, 0⟩ r j = _ from e9 Rd _]
  rfl

end PlaceSentToy

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.momentSeat_says
#print axioms ProofFile.Honest.K1.later_shape
#print axioms ProofFile.Honest.K1.fit_of_readyAt
#print axioms ProofFile.Honest.K1.laidData_place
#print axioms ProofFile.Honest.K1.sent_at_shape
#print axioms ProofFile.Honest.K1.over_left
#print axioms ProofFile.Honest.K1.over_right
#print axioms ProofFile.Honest.K1.not_lays
#print axioms ProofFile.Honest.K1.over_ready
#print axioms ProofFile.Honest.K1.later_sent_at
#print axioms ProofFile.Honest.K1.PlaceSentToy.toy_lengths
#print axioms ProofFile.Honest.K1.PlaceSentToy.toy_sendFits
#print axioms ProofFile.Honest.K1.PlaceSentToy.codes
#print axioms ProofFile.Honest.K1.PlaceSentToy.o
#print axioms ProofFile.Honest.K1.PlaceSentToy.q
#print axioms ProofFile.Honest.K1.PlaceSentToy.gp
#print axioms ProofFile.Honest.K1.PlaceSentToy.sender
#print axioms ProofFile.Honest.K1.PlaceSentToy.seat
#print axioms ProofFile.Honest.K1.PlaceSentToy.VA
#print axioms ProofFile.Honest.K1.PlaceSentToy.VB
#print axioms ProofFile.Honest.K1.PlaceSentToy.DA
#print axioms ProofFile.Honest.K1.PlaceSentToy.DB
#print axioms ProofFile.Honest.K1.PlaceSentToy.Rd
