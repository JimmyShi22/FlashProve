-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/CellsQAtHead.lean: CONDITIONAL: UNDER THE LIBRARY's HEAD
(P5J.AtMgA, Johnson/P5J/MgAtAll.lean) THE TWO PUBLIC PREMISES OF eCells_of_raw
(Honest/K5/Law/CellsQRaw.lean) HOLD AT A GROUP's PLAN AND THE PLACE OF ITS LOOKUP ON THE CALLS: so
the second of the two equations that the honest side of an attention segment's own rounds (kind K5)
spends of the Script (K5CellsQ, Honest/K5/Law/EMaskAtHead.lean) follows there from a sentence on the
trace's cells and an equation in the Script's own letters. Statements with their proofs. It pays two
public premises by theorems of the library; it shows nothing new on public data: it joins.

  nm_head         CONDITIONAL: the plan's list of matrices is no longer than its number of matrices:
                  K5Law.ofPlan_size (Johnson/Desc/First/Att/ArmAttPublic.lean), which has the two
                  equal, at what H2K5.Door.ofPlan_all
                  (Johnson/Desc/First/Att/Door/Law/K5RestPublic.lean) gives
  symsRoom_head   CONDITIONAL: **SymsRoom at every matrix of the plan's list**: the seat and that it
                  fits: Meaning.seat_of_tie (Johnson/Goal/Meaning/ReadingsOne.lean); off the pad:
                  the first half of OneNumber (Johnson/Desc/First/Look/K3CopiesOne.lean); both at
                  what H2K5.Door.cells_of_tie (Johnson/Desc/First/Att/Door/Law/K5KindOfHead.lean)
                  gives under the head and twelve closed tests, which H2K5.Door.tieWW_true
                  (Johnson/Desc/First/Att/Door/Law/K5WrittenTrue.lean) has
  syms_apart_head CONDITIONAL: two symbols of the plan's list with one seat are one symbol:
                  seatCalls_apart (Johnson/Desc/First/Look/K3CallerSeatsApart.lean) under the
                  programs' test on the layout (Meaning.K2.pub_layoutOk,
                  Johnson/IMR/LayoutOkPub.lean); entry_of_array, names_arrs_of_tie and owners_apart
                  (Johnson/Goal/Meaning/ServedSeats.lean)
  msgNo5_congr    a helper: a member's number does not hang on the proof that it is in the list
  syms_entry_apart_head   CONDITIONAL: two symbols of the plan's list whose seats' members bear one
                  number in the witness, with one row and one place, are one symbol: so ESymsRaw
                  asks no entry of a message for two values within the segment: the seat's member
                  is the one that the layout's number names (seat_of_tie) and bears that number
                  (the second half of OneNumber); then syms_apart_head
  eCells_head     CONDITIONAL: **K5CellsQ from CellsSmallQ and ESymsRaw**

ON WHAT symsRoom_head AND THE TWO ON SYMBOLS APART REST BESIDE THE HEAD: two closed facts that
Lean's kernel has decided by evaluation, at the library's WRITTEN values of the plans and lists: the
twelve groups' test of the tie (Johnson/Desc/First/Att/Door/Law/K5TieFTrue.lean, with a negative
test) and the 24 segments' test of the one number
(Johnson/Desc/First/Att/Door/Law/K5OneWritten.lean), which comes in through one_of_head
(Johnson/Desc/First/Att/Door/Law/K5OneOfHead.lean) inside cells_of_tie. The Limits in these files'
heads hold here too: they speak of the written values, and one_of_head stands over the entry tests
of its own version of the head alone.

The premises of eCells_head, all of them. h: the library's head · hg: g is below 12 · ha: a is the
group's plan · hx: x₁ is the place of the segment's lookup on the calls · hS: CellsSmallQ (the
trace) · hE: ESymsRaw (the Script).

Limits. Conditional. h is a hypothesis of every statement that names it. It can be met: at the
goals' two named sets of full-size public files, as Lean's written copies spell them, the head has a
member with no premise (at the first set the library's AtFullSide.Top.headMember_zFull; at the
second headMember_zGap; at either, under "Z is one of the two", headMember_named).
Of the files of the kind K5 only those under
lean/AtFullSide/K5/ call these; this one does not. At other public files in scope the library's
P5J.head_exists_at_name gives a member under premises on the files, of which the fourth follows from
the third (P5J.owed_of_live).
hS AND hE ARE SHOWN OF NO TRACE AND NO SCRIPT. Whether ESymsRaw can be met: see the head of
Honest/K5/Law/CellsQRaw.lean: syms_entry_apart_head shuts a clash of two symbols within one segment;
across segments, at a matrix that an earlier segment has committed to, nothing is shut. NOT TRIED
FOR EMPTINESS: no instance of hS and hE is exhibited. The matrix of the lookup's planes is
left out of eCells_head, as in K5CellsQ; symsRoom_head speaks of it too. One kind's twelve members
of the chain. At the library's full size and the format's second hash function alone. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.CellsQRaw
import Johnson.Desc.First.Att.ArmAttPublic
import Johnson.Desc.First.Att.Door.Law.K5KindOfHead
import Johnson.Desc.First.Att.Door.Law.K5WrittenTrue
import Johnson.Goal.Meaning.ServedSeats
import Johnson.IMR.LayoutOkPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (lookAt Seat seatCalls seatCalls_apart szOf sigListCalls)
open ProofFile.Honest.FirstThread (Script)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The plan's list of matrices is no longer than its number of matrices.** CONDITIONAL: under the
hypothesis h; a is the group's plan. The library has the two equal. -/
theorem nm_head {g : Nat} {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) :
    a.seam.tl.mats.size ≤ a.seam.tl.NM :=
  Nat.le_of_eq (K5Law.ofPlan_size (H2K5.Door.ofPlan_all h ha)).symm

/-- **THE SYMBOLS' ROOM AT EVERY MATRIX OF THE PLAN's LIST.** CONDITIONAL: under the hypothesis h; g
is below 12; a is the group's plan; x₁ is the place of the segment's lookup on the calls; i is below
the plan's number of matrices. -/
theorem symsRoom_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {i : Nat} (hiN : i < a.seam.tl.NM) :
    SymsRoom h.𝔇.sent h.𝔇.l3.rad x₁ a.seam.tl i := by
  obtain ⟨idx, C⟩ := H2K5.Door.cells_of_tie h (fun _ hg' => H2K5.Door.tieWW_true hg') g hg a x₁
    ha hx
  have e : _root_.Meaning.tlAt (P5J.At.X Zp) x₁.link = a.seam.tl := by
    rw [VerifiableInference.OnPublicFiles.lookAt_link hx]
    exact H2K5.Door.tlAt_att hg ha
  intro i' c hi' hc
  obtain ⟨hs, hk, hf⟩ := _root_.Meaning.seat_of_tie C.tie (μ := i) (i := i') (c := c) hiN hi' hc
  rw [if_neg (by simp)] at hf
  have O := C.one i i' c (by rw [e]; exact hiN) (by rw [e]; exact hi') (by rw [e]; exact hc) hk
  exact ⟨_, hk, hs, hf.1, hf.2, O.1⟩

/-- **TWO SYMBOLS OF THE PLAN's LIST WITH ONE SEAT ARE ONE SYMBOL.** CONDITIONAL: under the
hypothesis h; g is below 12; a is the group's plan; x₁ is the place of the segment's lookup on the
calls; i and j are below the plan's number of matrices; the two symbols' addresses have the seat
s. -/
theorem syms_apart_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {i j i' j' c c' : Nat}
    (hi : i < a.seam.tl.NM) (hj : j < a.seam.tl.NM) {s : Seat}
    (h1 : seatCalls h.𝔇.sent x₁.link (.cell (a.seam.tl.gtTree.getD i 0) i' c) = some s)
    (h2 : seatCalls h.𝔇.sent x₁.link (.cell (a.seam.tl.gtTree.getD j 0) j' c') = some s) :
    i = j ∧ i' = j' ∧ c = c' := by
  obtain ⟨idx, C⟩ := H2K5.Door.cells_of_tie h (fun _ hg' => H2K5.Door.tieWW_true hg') g hg a x₁
    ha hx
  have e : _root_.Meaning.tlAt (P5J.At.X Zp) x₁.link = a.seam.tl := by
    rw [VerifiableInference.OnPublicFiles.lookAt_link hx]
    exact H2K5.Door.tlAt_att hg ha
  have ok : OnBytes.reqLayoutOk h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout = true :=
    _root_.Meaning.K2.pub_layoutOk h.laid.pub
  obtain ⟨ea, er, ec⟩ := seatCalls_apart ok h1 h2
  have hk : x₁.link < 25 := by
    rw [VerifiableInference.OnPublicFiles.lookAt_link hx]
    omega
  have C0 := OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne
  have O : _root_.Meaning.OwnersApart (P5J.At.X Zp) x₁.link (szOf a.seam.tl).NM := by
    have e0 := _root_.Meaning.nm_of_core h.pubOne C0 hk
    have e1 : (szOf a.seam.tl).NM = (_root_.Meaning.matsAt (P5J.At.X Zp) x₁.link).size := by
      rw [← e]
      exact e0
    rw [e1]
    exact _root_.Meaning.owners_apart h.pubOne C0 hk
  exact ⟨_root_.Meaning.entry_of_array (_root_.Meaning.names_arrs_of_tie C.tie).1 O hi hj ea, er,
    ec⟩

/-- The number of a member does not hang on the proof that the member is in the list. -/
theorem msgNo5_congr {x₁ : VerifiableInference.Desc.First.Look.Place} {kk kk' : Nat} (e : kk = kk')
    {hk : kk < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    {hk' : kk' < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} :
    msgNo5 h x₁ kk hk = msgNo5 h x₁ kk' hk' := by
  subst e
  rfl

/-- **TWO SYMBOLS OF THE PLAN's LIST AT ONE ENTRY OF ONE MESSAGE ARE ONE SYMBOL.** CONDITIONAL:
under the hypothesis h; g is below 12; a is the group's plan; x₁ is the place of the segment's
lookup on the calls; both symbols lie within the plan's sizes; their addresses have the seats s and
t; the members at s and t bear one number in the witness; s and t have one row and one place. -/
theorem syms_entry_apart_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {i j i' j' c c' : Nat}
    (hi : i < a.seam.tl.NM) (hj : j < a.seam.tl.NM)
    (hi' : i' < Alg.symRows (a.seam.tl.mats.getD i {}).m) (hc : c < (a.seam.tl.mats.getD i {}).k)
    (hj' : j' < Alg.symRows (a.seam.tl.mats.getD j {}).m)
    (hc' : c' < (a.seam.tl.mats.getD j {}).k)
    {s t : Seat} {hs : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    {ht : t.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (h1 : seatCalls h.𝔇.sent x₁.link (.cell (a.seam.tl.gtTree.getD i 0) i' c) = some s)
    (h2 : seatCalls h.𝔇.sent x₁.link (.cell (a.seam.tl.gtTree.getD j 0) j' c') = some t)
    (en : msgNo5 h x₁ s.msg hs = msgNo5 h x₁ t.msg ht) (er : s.row = t.row)
    (ep : s.place = t.place) : i = j ∧ i' = j' ∧ c = c' := by
  obtain ⟨idx, C⟩ := H2K5.Door.cells_of_tie h (fun _ hg' => H2K5.Door.tieWW_true hg') g hg a x₁
    ha hx
  have e : _root_.Meaning.tlAt (P5J.At.X Zp) x₁.link = a.seam.tl := by
    rw [VerifiableInference.OnPublicFiles.lookAt_link hx]
    exact H2K5.Door.tlAt_att hg ha
  obtain ⟨a1, k1, -⟩ := _root_.Meaning.seat_of_tie C.tie (μ := i) (i := i') (c := c) hi hi' hc
  obtain ⟨a2, k2, -⟩ := _root_.Meaning.seat_of_tie C.tie (μ := j) (i := j') (c := c') hj hj' hc'
  have s1 := Option.some.inj (h1.symm.trans a1)
  have s2 := Option.some.inj (h2.symm.trans a2)
  have O1 := (C.one i i' c (by rw [e]; exact hi) (by rw [e]; exact hi') (by rw [e]; exact hc)
    k1).2
  have O2 := (C.one j j' c' (by rw [e]; exact hj) (by rw [e]; exact hj') (by rw [e]; exact hc')
    k2).2
  have N1 := (msgNo5_congr h (hk := hs) (hk' := k1) (congrArg Seat.msg s1)).trans O1
  have N2 := (msgNo5_congr h (hk := ht) (hk' := k2) (congrArg Seat.msg s2)).trans O2
  have en' := N1.symm.trans (en.trans N2)
  have hm : s.msg = t.msg :=
    (congrArg Seat.msg s1).trans ((congrArg idx en').trans (congrArg Seat.msg s2).symm)
  have hk0 : s.mask = t.mask := (congrArg Seat.mask s1).trans (congrArg Seat.mask s2).symm
  have es : s = t := by
    cases s
    cases t
    simp only [Seat.mk.injEq]
    exact ⟨hm, hk0, er, ep⟩
  exact syms_apart_head h hg ha hx hi hj h1 (h2.trans (congrArg some es.symm))

variable {h} {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- **THE SECOND EQUATION's TEXT, UNDER THE HEAD, FROM THE TRACE's AND THE SCRIPT's SENTENCES
ALONE.** CONDITIONAL: under the hypothesis h; g is below 12; which plan and place are meant; hS, on
the trace; hE, on the Script: neither is shown here. -/
theorem eCells_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat} {cells : Tr → Cells} {Z5 : Seat5}
    (hS : CellsSmallQ Vd a cells Z5) (hE : ESymsRaw h Q Vd N x₁ a cells Z5) :
    K5CellsQ h Q Vd N x₁ a cells Z5 :=
  eCells_of_raw (nm_head h ha) (fun _ _ hiN => symsRoom_head h hg ha hx hiN) hS hE

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.nm_head
#print axioms ProofFile.Honest.K5.symsRoom_head
#print axioms ProofFile.Honest.K5.syms_apart_head
#print axioms ProofFile.Honest.K5.msgNo5_congr
#print axioms ProofFile.Honest.K5.syms_entry_apart_head
#print axioms ProofFile.Honest.K5.eCells_head
