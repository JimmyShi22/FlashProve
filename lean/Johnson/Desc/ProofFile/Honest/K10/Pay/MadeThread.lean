-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeThread.lean: the closing of a segment (K10), at the first chain's thread under the
library's head: wherever the invariant holds at the border in front of the closing of segment l, the lot's job makes the
group's rows and they pass the public test `rowsFit`. This is the field made of `CarryOwed` (Honest/K10/Xch/CarryTop.lean).

  `place_written`   by Lean's kernel: behind each of the 25 segments the written plan has a place of the code switch
  `made_at_thr`     the field, from the code switch's public test at a place behind the segment, and `ownHeard`: the data of
                    the own messages of these segments is ready at what was heard
  `made_of_reads`   the same at the filling `widerRows` at the reference sizes and at the opening's ground, with `ReadsLight` in
                    the stead of the public test

Limits. `publicOk`, `ReadsLight` and `ownHeard` are premises here. That a run stands at the border is not shown. The full size
and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeReady
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeStand
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads
import Johnson.Desc.ProofFile.Honest.AtPureWider

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (SwitchPlace ownHeard publicOk switchPlaces segmentsOf)
open ProofFile.Honest.K2.Law (segsW placesW ReadsLight places_at_head segments_at_head publicOk_of_reads)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)
open _root_.Desc.K14.Law (secondAt seatZ)

set_option maxRecDepth 10000000 in
/-- Behind each of the 25 segments the written plan has a place of the code switch. -/
theorem place_written : ((List.range 25).all fun l => placesW.any fun p => p.link == l + 1) = true := by
  decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **Wherever the invariant holds at the border in front of a closing, the lot's job makes the group's rows and they pass
the public test.** -/
theorem made_at_thr {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) {Gr : ProofFile.Ground} (hS : segmentsOf Zp Gr = segsW)
    {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Zp Gr Qc).pub))
    {pl : SwitchPlace} (hp : pl ∈ switchPlaces Zp Gr)
    (hPub : publicOk rows Gr.first.layout pl (lotSegs Zp Gr Qc) m.st.input.x = true)
    (hOwn : ownHeard (rows m.st.input.x) (askPlace (addrsAt Zp Gr)) (lotSegs Zp Gr Qc) m.st.heard = true) :
    ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard ca = .ok R ∧ rowsFit s.st D.G R = true := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hl : l < 25 := link_lt h hlt
  have hr := thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, hFit, hP, -, -, -, -⟩ := hT'
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hd : drawsFit (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)) m.st.heard = true := hFit
  exact made_reached h hl hr hf hQ hS Hb readers rows stAt m.st.input m.st.heard ca
    (ownReady_of_place hp hPub hOwn) (heard_reached h hl hQ hS hd)

/-- **The same at the filling `widerRows` at the reference sizes and at the opening's ground**: the code switch's public test
is paid by `publicOk_of_reads` (Honest/K2/Law/PublicOkOfReads.lean), which asks `ReadsLight` at the input's instance. -/
theorem made_of_reads {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np))
    {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (stAt : StAtOf ProofFile.Inst)
    (ca : CsAll (closeCarries (lotJob readers (widerRows Sz.ref Zp Bs.G₀) stAt Zp Bs.G₀ Qc).pub))
    (hReads : ReadsLight Zp Bs.G₀ m.st.input.x)
    (hOwn : ownHeard (widerRows Sz.ref Zp Bs.G₀ m.st.input.x) (askPlace (addrsAt Zp Bs.G₀))
      (lotSegs Zp Bs.G₀ Qc) m.st.heard = true) :
    ∃ R, (lotJob readers (widerRows Sz.ref Zp Bs.G₀) stAt Zp Bs.G₀ Qc).rows m.st.input m.st.heard ca = .ok R ∧
      rowsFit s.st D.G R = true := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h (List.getElem?_eq_some_iff.1 hblk).1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  obtain ⟨pl, hpl, hlink⟩ : ∃ pl ∈ placesW, pl.link = l + 1 := by
    obtain ⟨pl, hm, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 place_written l (List.mem_range.2 hl))
    exact ⟨pl, hm, eq_of_beq e⟩
  have hp : pl ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hpl
  have hPub := publicOk_of_reads h O hReads pl hp
  rw [hlink, ← hQ] at hPub
  exact made_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT (segments_at_head h.toAtMg O) Hb readers
    (widerRows Sz.ref Zp Bs.G₀) stAt ca hp hPub hOwn

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.place_written
#print axioms ProofFile.Honest.K10.made_at_thr
#print axioms ProofFile.Honest.K10.made_of_reads
