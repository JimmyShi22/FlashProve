-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SeatNumber.lean: AT THE SEAT OF A SYMBOL OF AN ATTENTION
SEGMENT's LIST OF MATRICES: WHICH ARRAY OF THE LAYOUT, WHICH ENTRY OF THE SEGMENT's LIST OF ARRAYS,
WHICH PLACE BY THE LAYOUT's RULE, AND WHICH NUMBER IN THE WITNESS. CONDITIONAL: under the hypothesis
h, the library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). One theorem, on
public data alone.

What it is for. The equation that this kind's cells ask of a script's messages (`ESymsRaw`,
CellsQRaw.lean in this folder) speaks at the message with the number `msgNo5 h x₁ s.msg hk`, at the
row and place of the seat s that the verifier's side reads (`seatCalls`). The laws on the layout's
rule (WayBack.lean, WayBackFill.lean) and on the frame's values (PackedVals.lean, PackedAtSeg.lean)
speak at the segment that owns an array, the array's own message and its name. This file ties the
first to the second.

Main name:
  `seat_number_head`: lab: the label of entry i of the plan's list. There is an array A with: the
    entry of the segment's list of arrays is (`Meaning.ownerK lab`, `Meaning.nameOf (Meaning.ownerA
    lab)`); A is the layout's array of that segment and name; the layout's rule lays (i', c) of A at
    the seat's row and place; and the seat's member has, in the witness, THE PLAN's NUMBER OF (the
    owner's segment, A's own message): `P5J.At.num Zp`.

How. `H2K5.Door.cells_of_tie` (Johnson/Desc/First/Att/Door/Law/K5KindOfHead.lean) with
`H2K5.Door.tieWW_true` (K5WrittenTrue.lean there) gives the public tie at the segment
(`Meaning.linkTieB`, Johnson/Goal/Meaning/ReadingsOne.lean) and "one number" (`OneNumber`,
Johnson/Desc/First/Look/K3CopiesOne.lean). The entry and the array: two clauses of the tie. The
place: `seatCalls`' own text. The number: `Meaning.seat_of_tie` (ReadingsOne.lean) and the second
half of "one number". Kin: `symsRoom_head` (CellsQAtHead.lean in this folder), which goes the same
way to the first half; `Meaning.seat_of_laidThere` (Johnson/Goal/Meaning/HidSeatsOf.lean), which has
the array, its sizes and the place under another public test.

Limits. All five entries of the list, the planes' too. lab is spelled at x₁.link, as the tie has it;
that is 2 g + 1 (`lookAt_link`, Johnson/IMR/K3Seat.lean). Of what a message holds nothing is said.
That an array's pair (segment, message) shares its number with no other pair is not shown here: see
`num_apart_head` (KeysCover.lean in this folder). It rests, beside the head, on closed facts that
Lean's kernel decided by evaluation at the library's written values (beneath `tieWW_true` and
`one_of_head`). Through its imports the file stands above Cb/Bridge/CodeListRSProved.lean, and so
above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.CellsQAtHead
import Johnson.Goal.Meaning.HidSeatsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (lookAt Seat seatCalls sigListCalls)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE ARRAY, THE ENTRY, THE PLACE AND THE NUMBER AT A SYMBOL's SEAT.** CONDITIONAL: under the
hypothesis h; g is below 12; a is the group's plan; x₁ is the place of the segment's lookup on the
calls; i is below the plan's number of matrices; i' and c lie inside the matrix's packed rows and
its columns; the symbol's address has the seat s, whose member is in the list. -/
theorem seat_number_head {g : ℕ} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {i i' c : ℕ}
    (hiN : i < a.seam.tl.NM) (hi' : i' < Alg.symRows (a.seam.tl.mats.getD i {}).m)
    (hc : c < (a.seam.tl.mats.getD i {}).k) {s : Seat}
    (hk : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length)
    (hs : seatCalls h.𝔇.sent x₁.link (.cell (a.seam.tl.gtTree.getD i 0) i' c) = some s) :
    ∃ A : OnBytes.Params.ReqArray,
      (h.𝔇.sent.arrayOf.getD x₁.link #[])[a.seam.tl.gtTree.getD i 0]? =
        some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) x₁.link i),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) x₁.link i))) ∧
      VerifiableInference.Desc.arrayOf h.𝔇.sent.layout
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) x₁.link i))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) x₁.link i))) = some A ∧
      VerifiableInference.Desc.laidAt A i' c = some (s.row, s.place) ∧
      msgNo5 h x₁ s.msg hk =
        P5J.At.num Zp (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) x₁.link i)) A.message := by
  obtain ⟨idx, C⟩ := H2K5.Door.cells_of_tie h (fun _ hg' => H2K5.Door.tieWW_true hg') g hg a x₁
    ha hx
  have e : _root_.Meaning.tlAt (P5J.At.X Zp) x₁.link = a.seam.tl := by
    rw [VerifiableInference.OnPublicFiles.lookAt_link hx]
    exact H2K5.Door.tlAt_att hg ha
  have t := List.all_eq_true.1 C.tie i (List.mem_range.2 hiN)
  unfold _root_.Meaning.entryTieB at t
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at t
  obtain ⟨⟨t1, -⟩, -⟩ := t
  obtain ⟨bn, hbn, h1⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨A, hA, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨rp, hrp, h3⟩ := Option.bind_eq_some_iff.1 h2
  obtain rfl := Option.some.inj (hbn.symm.trans t1)
  have hA' : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout
      (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x₁.link i))
      (_root_.Meaning.nameOf (_root_.Meaning.ownerA
        (_root_.Meaning.labAt (P5J.At.X Zp) x₁.link i))) = some A := hA
  have hrp' : VerifiableInference.Desc.laidAt A i' c = some rp := by
    rw [← _root_.Meaning.laidPlace_eq_laidAt]
    exact hrp
  have hrow : rp = (s.row, s.place) := by
    split at h3
    · obtain rfl := Option.some.inj h3
      rfl
    · obtain ⟨j, -, rfl⟩ := Option.map_eq_some_iff.1 h3
      rfl
  have eF : _root_.Meaning.fLay h.𝔇.sent.layout (P5J.At.num Zp)
      (_root_.Meaning.labAt (P5J.At.X Zp) x₁.link i) i' c =
      (P5J.At.num Zp (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x₁.link i))
        A.message, rp.1, rp.2) := by
    unfold _root_.Meaning.fLay VerifiableInference.Desc.seatIn
    rw [hA']
    show ((VerifiableInference.Desc.laidAt A i' c).map fun y =>
      (P5J.At.num Zp (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x₁.link i))
        A.message, y.1, y.2)).getD (0, 0, 0) = _
    rw [hrp']
    rfl
  obtain ⟨hs2, hk2, -⟩ := _root_.Meaning.seat_of_tie C.tie (μ := i) (i := i') (c := c) hiN hi' hc
  have es := Option.some.inj (hs.symm.trans hs2)
  have O := (C.one i i' c (by rw [e]; exact hiN) (by rw [e]; exact hi') (by rw [e]; exact hc)
    hk2).2
  refine ⟨A, t1, hA', by rw [hrp', hrow], ?_⟩
  have em : s.msg = idx (_root_.Meaning.fLay h.𝔇.sent.layout (P5J.At.num Zp)
      (_root_.Meaning.labAt (P5J.At.X Zp) x₁.link i) i' c).1 := by
    rw [es]
  refine (msgNo5_congr h em (hk' := hk2)).trans (O.trans ?_)
  rw [eF]
  rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.seat_number_head
