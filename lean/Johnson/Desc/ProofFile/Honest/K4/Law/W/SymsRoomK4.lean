-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SymsRoomK4.lean: CONDITIONAL: on h, Lh and hx. On
public data alone.

What is here. ANOTHER HOUSE's PREMISE's FORM `SymsRoom` (Honest/K5/Law/CellsQRaw.lean: each symbol
of a matrix has a seat in the list of messages, inside its message's main table, off that message's
pad) HOLDS AT EVERY MATRIX OF THE LIST OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), AT
EACH OF THE TWELVE GROUPS, UNDER THE LIBRARY's HEAD ALONE. That house pays its form at the attention
links over a closed test at the odd links (`symsRoom_head`, Honest/K5/Law/CellsQAtHead.lean). Here
nothing new is decided by evaluation. The seat and the two bounds are three clauses of the library's
`SymsOne` (`symsOne_head`, Law/W/SeatNumberK4.lean). The pad's clause: the library's `PlacesOffPad`
(Johnson/P5J/HidBears.lean: every place that a segment's seats name is off the pad of whichever
member of the segment's group bears the number) holds under the head (`AtMg.placesOff`,
Johnson/P5J/HidBearsAtMg.lean, at `offC_head`, Johnson/Top/H0/K2Ties/OffHead.lean, at the first
pin); the member with the number is the seat's (the last clause of `SymsOne`); and that member has
the shape of the list's entry (`SitsIn`, by `sitsIn_head`, Law/W/ReadersHead.lean). One statement
with its proof, and its form for a caller.

  `symsRoom_k4`   **the symbols' room at every matrix of the plan's list**, the planes' too.
  `symsRoom_k4_all`   the same in the form in which Law/W/CellsOfSyms.lean asks it (R).

Not shown here. Of what a message holds nothing is said. h: the library's hypothesis `P5J.AtMgA` on
the public files; Lh (`LaidK4`, Law/SeatedHead.lean) and hx follow from it at each of the twelve
groups, as Law/W/MatsAreHead.lean's head says. Beneath it stand closed facts that Lean's kernel
decided by evaluation at the library's written values (beneath `offC_head`, and what the heads of
Law/W/SeatNumberK4.lean and Law/W/ReadersHead.lean name); no independent checker that its writers
know of has replayed them. THE STATEMENT RESTS ON DEFINITIONS OF FILES UNDER Johnson/Goal/, CALLED
BY NAME, as Law/W/SeatNumberK4.lean's head says. `padB` is typed at one answer
(Johnson/Desc/SeatAt.lean). THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SeatNumberK4
import Johnson.Top.H0.K2Ties.OffHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (memAt_some)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt)
open VerifiableInference.Desc.Sound (seatOf)
open ProofFile.Honest.K5 (SymsRoom)
open P5J (AtMgA TS PlacesOffPad)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh and hx; i is below the plan's number of matrices. **THE SYMBOLS' ROOM AT
MATRIX NUMBER i OF THE PLAN's LIST.** xl: the lookup's place at the segment. -/
theorem symsRoom_k4 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {i : ℕ} (hiN : i < x.2.hp.tl.NM) : SymsRoom h.𝔇.sent h.𝔇.l3.rad xl x.2.hp.tl i := by
  obtain ⟨hσ, h1, -, -⟩ := symsOne_head h Lh hx
  have hS := sitsIn_head h Lh hx
  have PO : PlacesOffPad h.𝔇.sent.codes h.𝔇.l3.arr h.𝔇.ms h.𝔇.N (_root_.Meaning.sizesOf Zp.p.X)
      (_root_.Meaning.seatBy
        (_root_.Meaning.fLay (OnBytes.Road.K4.sentAt Zp).layout (OnBytes.Road.K4.numAt Zp))
        Zp.p.X (_root_.Meaning.sizesOf Zp.p.X)) :=
    h.toAtMg.placesOff (VerifiableInference.Desc.First.K2Ties.offC_head h.toAtMg
      (P5J.pins_of_laid h.scope h.laid).1)
  have hi1 : i < (_root_.Meaning.sizesOf Zp.p.X (2 * g)).NM := by
    rw [← hσ]
    exact hiN
  intro i' c hi' hc
  have hr1 : i' < Alg.symRows ((_root_.Meaning.sizesOf Zp.p.X (2 * g)).m i) := by
    rw [← hσ]
    exact hi'
  have hc1 : c < (_root_.Meaning.sizesOf Zp.p.X (2 * g)).k i := by
    rw [← hσ]
    exact hc
  obtain ⟨s, hk, q0, -, q2, q3, q4, q5⟩ := h1 ⟨i, hi1⟩ ⟨i', hr1⟩ ⟨c, hc1⟩
  obtain ⟨-, u, hu, esh⟩ := hS ⟨s.msg, hk⟩
  obtain ⟨um, us⟩ := memAt_some hu
  have hmem : seatOf u ∈ h.𝔇.N.group (2 * g) := by
    rw [us]
    exact List.mem_of_find?_eq_some q5
  have hnum' := List.find?_some q5
  have hnum := eq_of_beq hnum'
  have off := PO (2 * g) ⟨i, hi1⟩ i' c hr1 hc1 u um hmem (by
    show h.𝔇.l3.arr (seatOf u).1 (seatOf u).2 = _
    rw [us]
    exact hnum)
  rw [esh] at off
  have e1 : _ = s.row := congrArg Prod.fst q4
  have e2 : _ = s.place := congrArg Prod.snd q4
  refine ⟨s, hk, q0, q2, q3, ?_⟩
  rw [← e1, ← e2]
  exact off

/-- CONDITIONAL: on h, Lh and hx. The same at every matrix but the planes', as a caller asks it. -/
theorem symsRoom_k4_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (Qp : K4Pub) : ∀ i, i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB → i < x.2.hp.tl.NM →
      SymsRoom h.𝔇.sent h.𝔇.l3.rad xl x.2.hp.tl i :=
  fun _ _ hiN => symsRoom_k4 h Lh hx hiN

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.symsRoom_k4
#print axioms ProofFile.Honest.K4.W.symsRoom_k4_all
