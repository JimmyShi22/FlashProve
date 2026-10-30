-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/CellsQRaw.lean: CONDITIONAL: IT MOVES A DEBT, IT PAYS NONE: THE
SECOND OF THE TWO EQUATIONS THAT THE HONEST SIDE OF AN ATTENTION SEGMENT's OWN ROUNDS (kind K5)
SPENDS OF THE SCRIPT (K5ScriptQ.eCells, Honest/K5/Law/ScriptQ.lean; by a name: K5CellsQ,
Honest/K5/Law/EMaskAtHead.lean) FOLLOWS FROM AN EQUATION IN THE SCRIPT's OWN LETTERS, a sentence on
the trace's cells and two on public data. Definitions of propositions, and statements with their
proofs.

Why it is no unfolding. The verifier's side does not read a cell off a message. A message holds
SYMBOLS: three cells of one column, packed at the radix 2 ^ 20 (Alg.pack, Alg/Range.lean). The
library's reading of a cell (cellValS, Cb/Pv/Tail/InLink.lean) is: the small integer column whose
packing the symbols are, if there is one, and 0 if there is none. So the equation in the Script's
own letters speaks of symbols, and the way back to cells asks that the trace's cells are small.

  SymsRoom       on public data alone: each symbol of matrix number i has a seat in the list of
                 messages, the seat lies in its message's main rows' table, and it is no place of
                 that message's pad. It is the library's Seated
                 (Johnson/Desc/First/Look/K3CallerAtt.lean) at one matrix's symbols, and the clause
                 on the pad
  val_sym        what the witness's messages hold at a symbol's address: the witness's message of
                 the seat's member's number, main table, at the seat's row and place
  cell_of_packs  GENERAL: where one column's symbols are the packing of a small integer column, the
                 library's reading of a cell of that column is that integer. It is the library's
                 cellValS_pack (Johnson/Desc/First/Att/K05MsgOnto.lean) cut to one column, with
                 that theorem's proof
  mats_of_syms   GENERAL IN THE PUBLIC DATA AND THE WITNESS: no head, no Script: the matrices that
                 are read off a witness's messages hold, at a cell of a column whose symbols' seats
                 hold the packing of a small integer column, that integer
  msgNo5         the number, in the witness, of a member of the list of messages
  CellsSmallQ    on the trace alone: at an input that meets Vd each column of each matrix but the
                 lookup's planes' is the image of a small integer column
  ESymsRaw       the equation in the Script's own letters: at a symbol's seat the message holds the
                 packing of the trace's three cells
  eCells_of_raw  **K5CellsQ from these**

The premises of eCells_of_raw, all of them. h: the library's head (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean) · hNM: the plan's list of matrices is no longer than its number of
matrices (public) · R: SymsRoom at every matrix of the list but the planes' (public) · hS:
CellsSmallQ (the trace) · hE: ESymsRaw (the Script).

WHO PAYS THE TWO PUBLIC PREMISES: NOT THIS FILE. Honest/K5/Law/CellsQAtHead.lean has both under the
head, at a group's plan and the place of its lookup on the calls, from theorems of the library.

CAN ESymsRaw BE MET? THAT A SCRIPT MEETS IT IS SHOWN NOWHERE HERE. The nearest thing in the library
is a tuple of messages with prescribed symbols that is found by choice (msgOf,
Johnson/Desc/First/Att/K05MsgOnto.lean): no program, no honest prover. ESymsRaw asks one entry of
one message (the message's number in the witness, the row, the place) to be the packing that
(i, i', c) names. WITHIN ONE SEGMENT it asks no entry for two values, at a group's plan under the
head: two symbols of the plan's list at one entry are one symbol: syms_entry_apart_head
(Honest/K5/Law/CellsQAtHead.lean), over syms_apart_head (one seat, one symbol), which is by the
library's seatCalls_apart (Johnson/Desc/First/Look/K3CallerSeatsApart.lean) and entry_of_array
(Johnson/Goal/Meaning/ServedSeats.lean, whose head walks the ways in which it could fail). At a free
record nothing forbids a clash: where the list of trees hands one tree to two matrices the same
address is asked to hold both columns' packings. ACROSS SEGMENTS NOTHING IS SHUT: a matrix that an
earlier segment has committed to has its seat in the KEPT message of this segment's list, and by the
library's OneNumber (Johnson/Desc/First/Look/K3CopiesOne.lean) all copies of a message bear one
number in the witness: there ESymsRaw asks that one message to hold the packing of what the reader
of the trace answers under THIS segment's number and this segment's name for the matrix: it can be
met beside the like equation of the owner's segment only where that reader answers the same under
both.

Limits. Conditional. h is a hypothesis of every statement that names it. It can be met: at the
goals' two named sets of full-size public files, as Lean's written copies spell them, the head has a
member with no premise (at the first set the library's AtFullSide.Top.headMember_zFull; at the
second headMember_zGap; at either, under "Z is one of the two", headMember_named).
Of the files of the kind K5 only those under
lean/AtFullSide/K5/ call these; this one does not. At other public files in scope the library's
P5J.head_exists_at_name gives a member under premises on the files, of which the fourth follows from
the third (P5J.owed_of_live).
NO EQUATION IS SHOWN OF ANY SCRIPT, no trace is shown to be small, and neither public premise is
shown or evaluated at any plan in this file. One direction alone is shown; the converse is not
tried. NOT TRIED FOR EMPTINESS: no instance of the four premises together is exhibited; under the
head none can be evaluated. For cell_of_packs the library's packOf is an instance; for the
messages' side the library has a tuple with prescribed small cells (cells_msgOf, under SymsSit: both
Johnson/Desc/First/Att/K05MsgOnto.lean): neither is called here. The library's test for a pad's
place (padB, Johnson/Desc/SeatAt.lean) is typed at one answer. The bound of CellsSmallQ is the
library's own for the packing to be unique (twice 2 ^ 17), not the format's bound on a cell. The
matrix of the lookup's planes is left out, as in K5CellsQ. One kind's twelve members of the chain.
At the library's full size and the format's second hash function alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.EMaskAtHead
import Johnson.Desc.First.Att.K05MsgOnto

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading HTailF2)
open OnBytes.Road.Rows (Addr)
open Johnson.Pack (pMain)
open Cb.Pv.Tail (JCell Syms cellValS cellsOf symL Packs packs_unique packs_cellsOf uniq_gl)
open VerifiableInference.Desc (Chain padB Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (Sent Seat sigListCalls seatCalls valAt readAt finOf_some
  symAt msgAtt enCell cellJ szOf)
open VerifiableInference.Desc.First.Att.P (matsOfMsg seatCalls_main)
open VerifiableInference.OnPublicFiles (attMs)
open H2K5.Door (seatAll)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 On public data -/

/-- **The symbols' room.** i: a matrix's number in the smallness test's list. Each symbol of the
matrix (row of symbols i', column c) has a seat in the list of messages; the seat lies in its
message's main rows' table; it is no place of that message's pad. It is a definition: a premise's
form, on public data alone. -/
def SymsRoom (D : Sent) (rad : OnBytes.OracleShape → Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (i : Nat) : Prop :=
  ∀ i' c, i' < Alg.symRows (tl.mats.getD i {}).m → c < (tl.mats.getD i {}).k →
    ∃ (s : Seat) (hk : s.msg < (sigListCalls D rad x₁.link).length),
      seatCalls D x₁.link (.cell (tl.gtTree.getD i 0) i' c) = some s ∧
      s.row < ((sigListCalls D rad x₁.link).get ⟨s.msg, hk⟩).1.mainRows ∧
      s.place < (pMain D.codes ((sigListCalls D rad x₁.link).get ⟨s.msg, hk⟩).1).ell ∧
      padB D.codes ((sigListCalls D rad x₁.link).get ⟨s.msg, hk⟩).1 false s.row s.place = false

/-- **What the witness's messages hold at a symbol's address.** t: the symbol array's number in the
segment's list of arrays. CONDITIONAL: the address has the seat s; s lies in its message's main
rows' table; it is no place of the pad. -/
theorem val_sym {D : Sent} {rad : OnBytes.OracleShape → Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {t i' c : Nat} {s : Seat}
    {hk : s.msg < (sigListCalls D rad x₁.link).length}
    (hs : seatCalls D x₁.link (.cell t i' c) = some s)
    (h1 : s.row < ((sigListCalls D rad x₁.link).get ⟨s.msg, hk⟩).1.mainRows)
    (h2 : s.place < (pMain D.codes ((sigListCalls D rad x₁.link).get ⟨s.msg, hk⟩).1).ell)
    (hp : padB D.codes ((sigListCalls D rad x₁.link).get ⟨s.msg, hk⟩).1 false s.row s.place = false)
    (seatT : Fin (sigListCalls D rad x₁.link).length → Nat × Nat) (arr : Nat → Nat → Nat)
    {Cw Tok : Type} (w : Wit Cw Tok MsgT) :
    (valAt D.codes (sigListCalls D rad x₁.link) (seatCalls D x₁.link)
      (attMs x₁ D rad seatT arr w) (.cell t i' c)).getD 0 =
      w.msg (arr (seatT ⟨s.msg, hk⟩).1 (seatT ⟨s.msg, hk⟩).2) false s.row s.place := by
  have hm : s.mask = false := seatCalls_main x₁.link t i' c s hs
  unfold valAt
  rw [hs]
  show (readAt D.codes (sigListCalls D rad x₁.link) _ s).getD 0 = _
  unfold readAt
  rw [dif_pos hk, if_neg (by rw [hm]; exact Bool.false_ne_true), finOf_some h1, finOf_some h2]
  show (w.tab D.codes _ _ _ _ false s.row s.place) = _
  unfold VerifiableInference.Desc.Wit.tab
  rw [hp]
  rfl

/-! ## 2 From one column's symbols to its cells -/

/-- **Where one column's symbols are the packing of a small integer column, the library's reading of
a cell of that column is that integer.** General in the sizes. CONDITIONAL: the sizes' three
inequalities; P: the column's symbols are the packing of a, and a is small. -/
theorem cell_of_packs {s : Cb.Pv.Tail.Size} (hu : s.Uniq Cb.Gl.p) {y : Syms Cb.Gl.E s}
    (j : JCell s) {a : Fin (s.m j.1) → ℤ} (P : Packs (symL Cb.Gl.E s) y j.1 j.2.1 a) :
    cellValS y j = ((a j.2.2 : ℤ) : Cb.Gl.E) := by
  have e := packs_unique (symL Cb.Gl.E s) Cb.Gl.p hu (fun _ => rfl) P (packs_cellsOf _ ⟨_, P⟩)
  show ((cellsOf (symL Cb.Gl.E s) y j.1 j.2.1 j.2.2 : ℤ) : Cb.Gl.E) = _
  rw [← e]

/-- **The matrices that are read off a witness's messages, at a cell of a column whose symbols'
seats hold the packing of a small integer column.** General in the public data, the seats' table
and the witness. CONDITIONAL: the matrix, the row and the column lie within the record's sizes;
SymsRoom at the matrix; a is small; hw: at the seat of each of the column's symbols the witness's
message holds the packing of a. -/
theorem mats_of_syms {D : Sent} {rad : OnBytes.OracleShape → Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (seatT : Fin (sigListCalls D rad x₁.link).length → Nat × Nat) (arr : Nat → Nat → Nat)
    {Cw Tok : Type} (w : Wit Cw Tok MsgT) {i r c : Nat} (hiN : i < tl.NM)
    (hr : r < (tl.mats.getD i {}).m) (hc : c < (tl.mats.getD i {}).k)
    (R : SymsRoom D rad x₁ tl i) {a : Fin (tl.mats.getD i {}).m → ℤ}
    (ha : Alg.Small (((szOf tl).beta : Nat) : ℤ) a)
    (hw : ∀ i', i' < Alg.symRows (tl.mats.getD i {}).m →
      ∀ (s : Seat) (hk : s.msg < (sigListCalls D rad x₁.link).length),
        seatCalls D x₁.link (.cell (tl.gtTree.getD i 0) i' c) = some s →
        w.msg (arr (seatT ⟨s.msg, hk⟩).1 (seatT ⟨s.msg, hk⟩).2) false s.row s.place =
          ((Alg.pack (((szOf tl).rad : Nat) : ℤ) a i' : ℤ) : Cb.Gl.E)) :
    matsOfMsg x₁ tl D rad (attMs x₁ D rad seatT arr w) i r c = ((a ⟨r, hr⟩ : ℤ) : Cb.Gl.E) := by
  -- the column's symbols are the packing of a
  have P : Packs (symL Cb.Gl.E (szOf tl))
      (symAt D.codes (sigListCalls D rad x₁.link) (seatCalls D x₁.link) tl
        (attMs x₁ D rad seatT arr w))
      (⟨i, hiN⟩ : Fin (szOf tl).NM) (⟨c, hc⟩ : Fin ((szOf tl).k i)) a := by
    refine ⟨ha, fun i' => ?_⟩
    obtain ⟨s, hk, hs, h1, h2, hp⟩ := R i'.val c i'.isLt hc
    show (valAt D.codes (sigListCalls D rad x₁.link) (seatCalls D x₁.link)
      (attMs x₁ D rad seatT arr w) (.cell (tl.gtTree.getD i 0) i'.val c)).getD 0 = _
    rw [val_sym hs h1 h2 hp seatT arr w]
    exact hw i'.val i'.isLt s hk hs
  -- the reading of the cell
  have hj : cellJ (szOf tl) i r c = some ⟨⟨i, hiN⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩ := dif_pos ⟨hiN, hc, hr⟩
  show msgAtt D.codes (sigListCalls D rad x₁.link) (seatCalls D x₁.link) tl x₁.ns
    (attMs x₁ D rad seatT arr w) (enCell x₁.ns tl i r c) = _
  unfold enCell
  rw [hj]
  show cellValS _ (⟨⟨i, hiN⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩ : JCell (szOf tl)) = _
  exact cell_of_packs (uniq_gl (s := szOf tl) rfl rfl) _ P

/-! ## 3 The equation in the Script's own letters -/

variable {Z₀ : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z₀ D₀ r₀ Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **The number, in the witness, of member number kk of the list of messages.** It is a definition:
nothing is claimed of it. It has the text of maskNo5 (Honest/K5/Law/ScriptQRaw.lean), whose name
and docstring speak of the member with the mask row alone. -/
noncomputable def msgNo5 (x₁ : VerifiableInference.Desc.First.Look.Place) (kk : Nat)
    (hk : kk < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) : Nat :=
  h.𝔇.arr (seatAll h x₁ ⟨kk, hk⟩).1 (seatAll h x₁ ⟨kk, hk⟩).2

/-- **The trace's cells are small**: at an input that meets Vd each column of each matrix of the
smallness test's list but the lookup's planes' is the image of an integer column whose entries are
below twice 2 ^ 17 in absolute value. It is a definition: a premise's form, on the trace alone. -/
def CellsSmallQ (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (A : OnBytes.Attention.Plan)
    (cells : Tr → Cells) (Z5 : Seat5) : Prop :=
  ∀ v, Vd v → ∀ i c, i ≠ Z5.P.S.cf.NAs + 2 → c < (A.seam.tl.mats.getD i {}).k →
    ∃ a : Fin (A.seam.tl.mats.getD i {}).m → ℤ, Alg.Small (((szOf A.seam.tl).beta : Nat) : ℤ) a ∧
      ∀ r, ((a r : ℤ) : Cb.Gl.E) =
        Reading.gl.val (cellAt Z5.P.S Z5.link (cells v.trace) i r.val c)

/-- **The equation in the Script's own letters**: at the seat of symbol (row of symbols i', column
c) of matrix number i the message of the seat's member's number holds, in its main table, the
packing of the trace's cells of rows 3 i', 3 i' + 1 and 3 i' + 2 of that column. It is a
definition: a premise's form. Whether it can be met: see the head. -/
def ESymsRaw (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (A : OnBytes.Attention.Plan)
    (cells : Tr → Cells) (Z5 : Seat5) : Prop :=
  ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn), Vd v → N ≤ hd.length →
    ∀ i i' c, i ≠ Z5.P.S.cf.NAs + 2 → i' < Alg.symRows (A.seam.tl.mats.getD i {}).m →
    c < (A.seam.tl.mats.getD i {}).k →
    ∀ (s : Seat) (hk : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      seatCalls h.𝔇.sent x₁.link (.cell (A.seam.tl.gtTree.getD i 0) i' c) = some s →
      Q.msg (msgNo5 h x₁ s.msg hk) k v (hd.take (Q.fixedMsg (msgNo5 h x₁ s.msg hk))) false s.row
          s.place =
        Alg.pack (((szOf A.seam.tl).rad : Nat) : ℤ)
          (fun r : Fin (A.seam.tl.mats.getD i {}).m =>
            Reading.gl.val (cellAt Z5.P.S Z5.link (cells v.trace) i r.val c)) i'

variable {h Q}

/-- **THE SECOND EQUATION's TEXT FROM THE EQUATION IN THE SCRIPT's OWN LETTERS.** CONDITIONAL: under
the hypothesis h; hNM and R, on public data; hS, on the trace; hE, on the Script: see the head. It
moves the debt: none of these is shown here. -/
theorem eCells_of_raw {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {A : OnBytes.Attention.Plan}
    {cells : Tr → Cells} {Z5 : Seat5} (hNM : A.seam.tl.mats.size ≤ A.seam.tl.NM)
    (R : ∀ i, i ≠ Z5.P.S.cf.NAs + 2 → i < A.seam.tl.NM →
      SymsRoom h.𝔇.sent h.𝔇.l3.rad x₁ A.seam.tl i)
    (hS : CellsSmallQ Vd A cells Z5) (hE : ESymsRaw h Q Vd N x₁ A cells Z5) :
    K5CellsQ h Q Vd N x₁ A cells Z5 := by
  intro k v hd hv hN i r c hi hr hc
  -- the matrix stands in the list
  have hiN : i < A.seam.tl.NM := by
    refine Nat.lt_of_lt_of_le ?_ hNM
    by_contra hge
    have e : A.seam.tl.mats.getD i {} = {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hge)]
      rfl
    rw [e] at hr
    exact Nat.not_lt_zero _ hr
  obtain ⟨a, ha, hcast⟩ := hS v hv i c hi hc
  rw [mats_of_syms (seatAll h x₁) h.𝔇.arr (Q.wit k v hd) hiN hr hc (R i hi hiN) ha
    fun i' hi' s hk hs => by
      rw [← Alg.pack_intCast]
      refine (hE k v hd hv hN i i' c hi hi' hc s hk hs).trans ?_
      congr 1
      funext r'
      exact (hcast r').symm]
  exact hcast ⟨r, hr⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.val_sym
#print axioms ProofFile.Honest.K5.cell_of_packs
#print axioms ProofFile.Honest.K5.mats_of_syms
#print axioms ProofFile.Honest.K5.eCells_of_raw
