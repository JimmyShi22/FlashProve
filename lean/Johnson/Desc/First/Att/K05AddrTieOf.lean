-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05AddrTieOf.lean: kind K5: THE ONE TIE AT THE SEAM (AddrTie,
Johnson/Desc/First/Att/K05DataMats.lean: the law's reading of its tuple of messages, by address, is
the table of joints' data's) FROM ONE TIE ON THE WITNESS, message by message, and facts that are
public or stand on the live request: the two writings of one plan are put together: which message
(Johnson/Desc/First/Att/K05SeatsOne.lean), which place (Johnson/Desc/First/Att/K05CellAt.lean).

IS IT EMPTY HERE? NO MEMBER IS SHOWN. No premise is shown at any record or witness.

Main names:
  `tableOfSeat z`: the table that a seat lies in: the mask rows' or the main rows'.
  `ReadAddr tl fs`: the addresses that AddrTie speaks of.
  `MsgTie Rd D rad i f own st book rd m`: **THE ONE TIE ON THE WITNESS**: for every seat z that
    seatCalls gives AN ADDRESS OF Rd, and for no other: the live request has the oracle o of message
    number z.msg, and what the tuple m holds at z (0 where the seat lies in no table) is entry
    (z.row, z.place) of o's table, as the one accessor tabQ (Johnson/Desc/Sound/FormsQ.lean)
    reads it off the witness by the book's seat.
  `ceilLog2_one`: a table of one row has no row bits.
  `addrTie_of`: **AddrTie**, from:
    hF, hk: FrameIs; as many kept messages as entries of "born" (K05SeatsOne.lean);
    hlay, harr: the live request's rows' layout and the open link's list of arrays are the
      description's;
    hok: LaidOkAt: at the array of every symbol address inside the sizes, AND AT NO OTHER: where the
      layout has it and the live request finds its message, the programs' test laidMatrixOk says yes
      at the numbers of bits that THE RECORD's STATEMENT has for that message (paid, under public
      tests and a Bool on the record, in Johnson/Desc/First/Att/K05LayoutOk.lean);
    hS: every symbol address inside the sizes has a seat (`hS_of_seated`: from SymsOK: what the tie
    spends of
      AttReadsOK: its field keptSame, and seated at the symbols alone; `symsOK_of`);
    hM: MsgTie at ReadAddr tl fs;
    hmb: the oracle of the mask row has no row bits in its mask table (one mask row).
Limits. A rule over letters. That the pin's item's part of the witness meets MsgTie is not shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05DataMats
import Johnson.Desc.First.Att.K05SeatsOne
import Johnson.Desc.First.Att.K05CellAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.K9L (Bound dataOf maskOracle)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ tabQ)
open VerifiableInference.Desc.First.Look (Sent attSg sigListCalls seatCalls keptAt bornAt szOf valAt
  readAt laidPlace laidHolds)

/-- The table that a seat lies in. -/
def tableOfSeat (z : VerifiableInference.Desc.First.Look.Seat) : OnBytes.Part := if z.mask = true then .mask else .main

/-- The addresses that AddrTie speaks of: the symbols of the matrices' symbol arrays, inside their
sizes; the mask entries under the slots that the forms of fs name. -/
def ReadAddr (tl : HTailF2) (fs : List Aff) (a : Addr) : Prop :=
  (∃ (μ : Fin (szOf tl).NM) (i' : Fin (_root_.Alg.symRows ((szOf tl).m μ)))
    (c : Fin ((szOf tl).k μ)), a = .cell (tl.gtTree.getD μ.val 0) i'.val c.val) ∨
    ∃ f ∈ fs, ∃ y ∈ f.slots.toList, a = .mask y.1

/-- **The one tie on the witness**: message by message, AT THE SEATS OF THE ADDRESSES Rd, AND AT NO
OTHER. GENERAL IN THE LIST OF MEMBERS l, THE SEATS' FUNCTION sf AND THE NUMBER kept OF KEPT
MESSAGES. -/
def MsgTieOf (Rd : Addr → Prop) (cs : Codes) (l : List (OracleShape × ℕ))
    (sf : Addr → Option VerifiableInference.Desc.First.Look.Seat) (kept : ℕ) (f : ReqFrame)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (rd : ℕ × ℕ → MsgQ)
    (m : (Johnson.Pack.sigOf cs l).Msg) : Prop :=
  ∀ (a : Addr) (z : VerifiableInference.Desc.First.Look.Seat), Rd a → sf a = some z →
    ∃ o, oracleOfMsg f kept z.msg = some o ∧
      (readAt cs l m z).getD 0 =
        tabQ own st book rd o (tableOfSeat z) (tableIndex (st.rowBits o (tableOfSeat z)) (z.row, z.place))

/-- That tie at the list, the seats and the number of kept messages of link i's lookup on the calls.
-/
def MsgTie (Rd : Addr → Prop) (D : Sent) (rad : OracleShape → Nat) (i : ℕ) (f : ReqFrame)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (rd : ℕ × ℕ → MsgQ)
    (m : (Johnson.Pack.sigOf D.codes (sigListCalls D rad i)).Msg) : Prop :=
  MsgTieOf Rd D.codes (sigListCalls D rad i) (seatCalls D i) (keptAt D i).length f own st book rd m

theorem ceilLog2_one : ceilLog2 1 = 0 := rfl

/-- **The symbol arrays that are read are laid lawfully in their oracles' tables**, at the numbers
of bits that the statement st has for these oracles: at the array of a symbol address inside the
sizes, AND AT NO OTHER. -/
def LaidOkAt (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
    (f : ReqFrame) (st : OnBytes.Statement) : Prop :=
  ∀ (μ : Fin (szOf tl).NM) (_ : Fin (_root_.Alg.symRows ((szOf tl).m μ)))
    (_ : Fin ((szOf tl).k μ)) (bn : ℕ × String) (a : ReqArray) (o : ℕ),
    (D.arrayOf.getD x.link #[])[tl.gtTree.getD μ.val 0]? = some bn →
    OnBytes.reqArray D.layout bn.1 bn.2 = some a → f.whereIs bn.1 a.message = some o →
    laidMatrixOk a (st.rowBits o .main) (st.placeBits o .main) = true

/-- **What the tie spends of the guards of the caller's reading** (AttReadsOK,
Johnson/Desc/First/Look/K3CallerAtt.lean): of its four fields the second, and the third AT THE
SYMBOLS ALONE. -/
structure SymsOK (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) : Prop where
  /-- a kept message has the shape of the message whose rows it took -/
  keptSame : ∀ k (hk : k < (keptAt D x.link).length),
    (((VerifiableInference.Desc.First.Look.messagesAt D
      ((bornAt D x.link).getD k (0, 0)).1)[((bornAt D x.link).getD k (0, 0)).2]?).map
      (·.shape)) = some ((keptAt D x.link).get ⟨k, hk⟩).shape
  /-- every symbol address inside the sizes has a seat, and the seat lies in its table -/
  seated : ∀ (μ : Fin (szOf tl).NM) (i' : Fin (_root_.Alg.symRows ((szOf tl).m μ)))
    (c : Fin ((szOf tl).k μ)),
    ∃ z, seatCalls D x.link (.cell (tl.gtTree.getD μ.val 0) i'.val c.val) = some z ∧
      z.Fits D.codes (sigListCalls D rad x.link)

theorem symsOK_of {x : VerifiableInference.Desc.First.Look.Place} {S : Attention.Shape}
    {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat}
    (H : VerifiableInference.Desc.First.Look.AttReadsOK x S tl D rad) : SymsOK x tl D rad :=
  ⟨H.keptSame, fun μ i' c => H.seated _ (.sym μ i' c)⟩

/-- The premise hS of addrTie_of. -/
theorem hS_of_seated {x : VerifiableInference.Desc.First.Look.Place}
    {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} (H : SymsOK x tl D rad)
    (μ : Fin (szOf tl).NM) (i' : Fin (_root_.Alg.symRows ((szOf tl).m μ)))
    (c : Fin ((szOf tl).k μ)) :
    (seatCalls D x.link (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)).isSome = true := by
  obtain ⟨s, hs, _⟩ := H.seated μ i' c
  rw [hs]
  rfl

/-- **AddrTie from the tie message by message.** -/
theorem addrTie_of (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (own : List (ℕ × ℕ)) (pt : VerifiableInference.Desc.K9.Part)
    (rd : ℕ × ℕ → MsgQ) (m : (attSg x D rad).Msg) (fs : List Aff)
    (hF : FrameIs D x.link pt.L.check.frame)
    (hk : (keptAt D x.link).length = (bornAt D x.link).size)
    (hlay : pt.L.check.rows.layout = D.layout)
    (harr : pt.L.arrayOf = D.arrayOf.getD x.link #[])
    (hok : LaidOkAt x tl D pt.L.check.frame pt.d.st)
    (hS : ∀ (μ : Fin (szOf tl).NM) (i' : Fin (_root_.Alg.symRows ((szOf tl).m μ)))
      (c : Fin ((szOf tl).k μ)),
      (seatCalls D x.link (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)).isSome = true)
    (hM : MsgTie (ReadAddr tl fs) D rad x.link pt.L.check.frame own pt.d.st pt.d.book rd m)
    (hmb : ∀ o, maskOracle pt.L.check.frame = some o → pt.d.st.rowBits o .mask = 0) :
    AddrTie x tl D rad pt.L.arrayOf m (dataQ own pt rd) fs := by
  refine ⟨fun μ i' c => ?_, fun f hf y hy => ?_⟩
  · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (hS μ i' c)
    obtain ⟨bn, a, hbn, ha, hp, hzm, hw⟩ := whereIs_cell hF hk hz
    obtain ⟨o, ho, hr⟩ := hM _ z (Or.inl ⟨μ, i', c, rfl⟩) hz
    have hpz : tableOfSeat z = .main := by
      unfold tableOfSeat
      rw [hzm]
      rfl
    rw [hpz] at hr
    rw [ho] at hw
    show ((seatCalls D x.link (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)).bind
      (readAt D.codes (sigListCalls D rad x.link) m)).getD 0 = _
    rw [hz]
    show (readAt D.codes (sigListCalls D rad x.link) m z).getD 0 = _
    rw [hr]
    show _ = (match pt.L.arrayOf[tl.gtTree.getD μ.val 0]? with
      | some b => (dataQ own pt rd).cell b.1 b.2 i'.val c.val
      | none => 0)
    rw [harr, hbn]
    show _ = (dataOf pt.L.check.rows pt.L.check.frame pt.d.st
      (tabQ own pt.d.st pt.d.book rd)).cell bn.1 bn.2 i'.val c.val
    rw [dataOf_cell pt.L.check.rows pt.L.check.frame pt.d.st _ bn.1 bn.2 i'.val c.val
      (by rw [hlay]; exact ha) hw (hok μ i' c bn a o hbn ha hw), hp]
  · show ((seatCalls D x.link (.mask y.1)).bind
      (readAt D.codes (sigListCalls D rad x.link) m)).getD 0 = (dataQ own pt rd).mask y.1
    show _ = (match maskOracle pt.L.check.frame with
      | some o => tabQ own pt.d.st pt.d.book rd o .mask y.1
      | none => 0)
    cases hz : seatCalls D x.link (.mask y.1) with
    | none =>
      have hnone : maskOracle pt.L.check.frame = none := by
        unfold seatCalls at hz
        unfold maskOracle
        unfold VerifiableInference.Desc.First.Look.messagesAt at hz
        rw [hF.shape, hF.link]
        rw [Option.map_eq_none_iff] at hz
        rw [hz]
        rfl
      rw [hnone]
      rfl
    | some z =>
      obtain ⟨hzm, hz0, hzj, hw⟩ := maskOracle_mask hF hz
      obtain ⟨o, ho, hr⟩ := hM _ z (Or.inr ⟨f, hf, y, hy, rfl⟩) hz
      have hpz : tableOfSeat z = .mask := by
        unfold tableOfSeat
        rw [hzm]
        rfl
      rw [hpz, hz0, hzj] at hr
      rw [ho] at hw
      rw [hw]
      show (readAt D.codes (sigListCalls D rad x.link) m z).getD 0 = _
      rw [hr, hmb o hw]
      show tabQ own pt.d.st pt.d.book rd o .mask (0 + 2 ^ 0 * y.1) = _
      rw [pow_zero, Nat.one_mul, Nat.zero_add]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.ceilLog2_one
#print axioms VerifiableInference.Desc.First.Att.P.symsOK_of
#print axioms VerifiableInference.Desc.First.Att.P.hS_of_seated
#print axioms VerifiableInference.Desc.First.Att.P.addrTie_of
