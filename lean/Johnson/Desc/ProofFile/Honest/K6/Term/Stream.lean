--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/Stream.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the
online proof): THE PROOFS OF THE STATEMENTS OF Honest/K6/Term/StreamStatements.lean: the stream that
the head borrows is read at its owner's seats, in segment 22's array; so where the Script lays the
filling at segment 22, the stream's symbols are the packing of the input's cells.

WHAT IT IS NOT. What that file's head says: an exchange, nothing is paid; the sentence that comes
(LaysFilling at segment 22) is shown of no Script; nothing is said of a kept copy or of the code
switch into link 24; it speaks only of states at which the thread stands at border 341. Four closed
facts on the reference sizes are decided by evaluation (streamNamesAndShapes). It imports one file
of another house that lies in no sealed tree (Honest/K3/Term/BorrowedMatricesBearOneNumber.lean),
and stands over this kind's elder files, which lie in none either. Nothing on soundness, on
completeness or on what a proof hides.

WHAT IT IS. Calls and ties; no new mathematics.
  THE OWNER. Meaning.owner_label (Johnson/Goal/Meaning/HidSeatsOf.lean) at (24, 7), on the branch
  "a = NHf + 3"; NHf = 4 (k6_sizes_own), the out-stream's number is 7 (Meaning.ix_of_core).
  THE SEATS. Meaning.seat_of_laidThere at (24, 7): general in the matrix.
  THE SYMBOL. P5J.symAt_readAt: off the pads what segment 24 reads is the witness's shared message
  at the seat. msg_of_lays (Honest/K5/Law/LaysFilling.lean) at segment 22 and the array "M7": that
  message holds the value of the array; cellsVals reads it as the packing of the readers' cells
  under (22, 7).
  THE TRACE. The two matrices have one shape at the reference sizes; the cells are one by the
  premise on the trace.
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.StreamStatements
import Johnson.Desc.ProofFile.Honest.K6.Cells.SeatsInside
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.Desc.ProofFile.Honest.K5.Law.ReachAtHead
import Johnson.Desc.ProofFile.Honest.K3.Term.BorrowedMatricesBearOneNumber
import Johnson.P5J.HidBearsAtMg
import Johnson.Top.H0.K2Ties.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open Inst.Model (ppref Instance)
open OnBytes.HonestTrace (Sz Seg MatName planeOf planMats packedCells ServesAt shapeNo_in_scope)
open VerifiableInference.Desc (Chain Place Strs arrayOf laidAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Law (seatLay)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (k6_sizes_own)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K1 (labelNo cellsVals)
open ProofFile.Honest.K5 (LaysFilling msg_of_lays cellsVals_size labelNo_arrayLabel asE_inl)

/-- FOUR CLOSED FACTS on the reference sizes: number 7 is the stream's name at the head's segment
and the out-stream's name at the last group's; the second has an array of its own segment; the two
have one shape. -/
theorem streamNamesAndShapes :
    Sz.ref.matAt 24 7 = some (.head, .xbL) ∧ Sz.ref.matAt 22 7 = some (.ff 11, .xbO) ∧
      (Sz.ref.arrayNo (.ff 11) .xbO).isSome = true ∧
      Sz.ref.shape (.ff 11) .xbO = Sz.ref.shape .head .xbL :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem streamIsOwnedByTheLastGroup : StreamIsOwnedByTheLastGroup := by
  intro Z D r Zp Np cF x h
  have hP := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hP
  obtain ⟨hNM, hN4, -, -, -⟩ := k6_sizes_own h
  have F := Meaning.follows_of_core hP C
  have e := Meaning.owner_label hP C (k := 24) (a := 7) (by norm_num)
    (by rw [← F.NM 24 (by norm_num), hNM]; omega)
  unfold Meaning.ownerOf at e
  rw [if_pos rfl, if_pos (by rw [hN4]), (Meaning.ix_of_core hP C).2.1] at e
  exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩

theorem streamSeatsLieInTheLastGroupsArray : StreamSeatsLieInTheLastGroupsArray := by
  intro Z D r Zp Np cF x h inList i c hi hc
  obtain ⟨o1, o2⟩ := streamIsOwnedByTheLastGroup Z D r Zp Np cF x h
  obtain ⟨A, y, hA, z1, z2, hat, hseat⟩ :=
    Meaning.seat_of_laidThere h.plan.laid (At.num Zp) (k := 24) (by norm_num) ⟨7, inList⟩ hi hc
  have hA' : arrayOf (At.layout Zp) (Meaning.ownerK (Meaning.labAt (At.X Zp) 24 7))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (At.X Zp) 24 7))) = some A := hA
  have hseat' : (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, inList⟩ i c) =
      (At.num Zp (Meaning.ownerK (Meaning.labAt (At.X Zp) 24 7)) A.message, y.1, y.2) := hseat
  rw [o1, o2] at hA'
  rw [o1] at hseat'
  refine ⟨A, hA', z1, z2, ?_, ?_⟩
  · rw [hseat']
    exact hat
  · rw [hseat']

theorem streamCellsAreTheLastGroupsAtTheModelsTrace :
    StreamCellsAreTheLastGroupsAtTheModelsTrace := by
  intro W₀ Rc Tr Z D r Zp Np cF x h Vd w cells hTrace hVd row column
  obtain ⟨i, xI, -, hcell⟩ := hTrace hVd
  rw [hcell]
  exact ProofFile.Honest.K3.Term.headReadsTheStreamOfTheLastGroup h.scope h.reads h.pubOne i xI row column

theorem streamSymbolsArePackedWhereTheScriptLaysTheLastGroup :
    StreamSymbolsArePackedWhereTheScriptLaysTheLastGroup := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said cells readers N seat heard hN L hRd hC k s m E hT ds ha' i' c
  have hval : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  have hfit : drawsFit ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341)
      m.st.heard = true := hT.1.2.1
  have hlen : N ≤ (m.st.heard ++ ds).length := by
    have e := drawsFit_length _ _ hfit
    rw [List.length_append, e]
    exact Nat.le_trans hN (Nat.le_add_right _ _)
  obtain ⟨hM24, hM22, ho, hShape⟩ := streamNamesAndShapes
  obtain ⟨A, hA, -, -, hat, q1⟩ :=
    streamSeatsLieInTheLastGroupsArray Z D r Zp Np cF x h ha' i'.val c.val i'.isLt c.isLt
  -- the reference sizes' shape of the stream is the plan's rows of cells and columns
  have hP := h.pubOne
  obtain ⟨-, -, sm, sk⟩ := shapeNo_in_scope h.scope h.reads hP hM24
    (by decide : MatName.xbL ≠ planeOf .head)
  have ep : planMats (At.X Zp) 24 = (At.X Zp).H.tl.mats := by simp [planMats]
  have et : Meaning.tlAt (At.X Zp) 24 = (At.X Zp).H.tl := by
    unfold Meaning.tlAt
    simp
  have eN24 : Sz.ref.shapeNo 24 7 = Sz.ref.shape .head .xbL := by
    unfold Sz.shapeNo
    rw [hM24]
  have eN22 : Sz.ref.shapeNo 22 7 = Sz.ref.shape .head .xbL := by
    unfold Sz.shapeNo
    rw [hM22]
    exact hShape
  have hm' : (Meaning.sizesOf (At.X Zp) 24).m 7 = (Sz.ref.shape .head .xbL).1 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD 7 {}).m = _
    rw [et, ← ep, sm, eN24]
  have hk' : (Meaning.sizesOf (At.X Zp) 24).k 7 = (Sz.ref.shape .head .xbL).2 := by
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD 7 {}).k = _
    rw [et, ← ep, sk, eN24]
  have hi22 : i'.val < (Sz.ref.packedShape 22 7).1 := by
    show i'.val < Alg.symRows (Sz.ref.shapeNo 22 7).1
    rw [eN22, ← hm']
    exact i'.isLt
  have hc22 : c.val < (Sz.ref.packedShape 22 7).2 := by
    show c.val < (Sz.ref.shapeNo 22 7).2
    rw [eN22, ← hk']
    exact c.isLt
  -- the array's name is read as 7
  have hname : A.name = Meaning.nameOf 7 := by
    obtain ⟨as, -, hf⟩ := Option.bind_eq_some_iff.1 hA
    simpa using List.find?_some hf
  have hn : labelNo A.name = some 7 := by
    rw [hname]
    exact labelNo_arrayLabel (by omega)
  have hz := cellsVals_size Sz.ref hn hM22 ho
  -- off the pads of the copies the symbols that the reader yields are the witness's own messages'
  refine (congrFun (congrFun (congrFun (P5J.symAt_readAt h.plan.hN h.plan.hG
    (h.toAtMg.placesOff (VerifiableInference.Desc.First.K2Ties.offC_ofHead h.toAtMg))
    (Q.wit k m.st.input (m.st.heard ++ ds)) 24) ⟨7, ha'⟩) i') c).trans ?_
  show Q.msg (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, ha'⟩ i'.val c.val).1 k
    m.st.input ((m.st.heard ++ ds).take (Q.fixedMsg
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, ha'⟩ i'.val c.val).1)) false
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, ha'⟩ i'.val c.val).2.1
    (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, ha'⟩ i'.val c.val).2.2 = _
  rw [q1]
  -- the Script's message of segment 22 holds the array's value there
  have hA'' : arrayOf h.𝔇.sent.layout 22 (Meaning.nameOf 7) = some A := hA
  obtain ⟨hd', q⟩ := msg_of_lays L hA'' hat hz hi22 hc22 k hval hlen
  refine q.trans ?_
  have e : (cellsVals Sz.ref).val (readers m.st.input) hd' 22 A.name i'.val c.val =
      .inl (packedCells Sz.ref (readers m.st.input).cells.cell 22 7 i'.val c.val) := by
    simp only [cellsVals, hn]
  rw [e, asE_inl]
  congr 1
  -- one shape, and the same cells
  obtain ⟨ew, hVd⟩ := hval
  rw [ew] at hVd ⊢
  rw [hRd]
  unfold packedCells
  rw [hM22, hM24]
  show (if c.val < (Sz.ref.shape (.ff 11) .xbO).2 then
      OnBytes.HonestTrace.pack3 (Sz.ref.shape (.ff 11) .xbO).1
        (fun r => (cells w.trace).cell 22 MatName.xbO.label r c.val) i'.val else 0) =
    (if c.val < (Sz.ref.shape .head .xbL).2 then
      OnBytes.HonestTrace.pack3 (Sz.ref.shape .head .xbL).1
        (fun r => (cells w.trace).cell 24 MatName.xbL.label r c.val) i'.val else 0)
  rw [hShape, funext fun r => (hC hVd r c.val).symm]

theorem streamSymbolsArePackedWhereTheScriptHoldsTheSwitchesData :
    StreamSymbolsArePackedWhereTheScriptHoldsTheSwitchesData := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said cells readers N G hG hN hLays hRd hC
  obtain ⟨G', hG', reach⟩ := ProofFile.Honest.K5.reach_switchSeat h
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  exact streamSymbolsArePackedWhereTheScriptLaysTheLastGroup W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H
    Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells readers N (K2.switchSeat Zp G')
    (fun _ => 0) hN
    ⟨fun As A hl hA hz => reach N 22 (by norm_num) (by norm_num) As A hl hA hz, hLays⟩ hRd hC

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.streamNamesAndShapes
#print axioms ProofFile.Honest.K6.Term.streamIsOwnedByTheLastGroup
#print axioms ProofFile.Honest.K6.Term.streamSeatsLieInTheLastGroupsArray
#print axioms ProofFile.Honest.K6.Term.streamCellsAreTheLastGroupsAtTheModelsTrace
#print axioms ProofFile.Honest.K6.Term.streamSymbolsArePackedWhereTheScriptLaysTheLastGroup
#print axioms ProofFile.Honest.K6.Term.streamSymbolsArePackedWhereTheScriptHoldsTheSwitchesData
