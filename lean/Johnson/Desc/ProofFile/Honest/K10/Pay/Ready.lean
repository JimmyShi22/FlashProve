-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/Ready.lean: the closing of a segment (K10): at every stand of the first chain's
thread in front of a closing, the twenty facts of `CloseBase` (Johnson/Desc/K10/Honest/Base.lean) hold of the record of
the verifier's state; so the closing's block accepts whatever the closing's part sends there (`AcceptedS`,
Honest/Thread/PaysS.lean), at all 25 closings. No acceptance is among the premises.

The words. The head: the library's hypothesis `P5J.AtMgA`, at the older hash. The head's thread: the field `thread` of
`lettersHead` (Honest/Thread/FirstHead.lean). A stand: `ThrS 𝕋 Said b k s m E`: the thread's invariant at border b with a
second condition Said. `SaidOk` (Honest/Thread/SaidOk.lean): the words shown so far were below the prime.

  `MaskFresh s`           a premise by name: the message that the record's frame names as the fresh mask is neither sampled
                      nor spent as a mask
  **`closeBase_at_stand`**   at a stand at `SaidOk` in front of the closing of segment l, under `MaskFresh s`:
                      ∃ B, `CloseBase Qc (recOf s) B`
  `ready_at_stand`      so the test `closeBaseB Qc` says yes of the record
  **`acceptedS_of_fresh`**  so `AcceptedS 𝕋 Said fall b` at each of the 25 closings, at every fall and at every Said that
                      gives `SaidOk`, from `ClosingsFirst` of the prover's list of halves and `MaskFresh` at the stands

Where the twenty come from. owed, link, group, due, mask, there, stretch, kh, bits, power, code: Pay/FrameFacts.lean.
beginRun, rows, inOrder, rowsIn: Pay/Run.lean. termsOk: Pay/Terms.lean. maskCode: `mask_at_thr` (Xch/Mask.lean). shape,
maskfits, spendAsMask: Pay/FoldAt.lean.

Limits. `ClosingsFirst` and `MaskFresh` are premises here. That the thread's invariant holds at any run is not said: where it
holds at no stand of a border, `AcceptedS` holds there for nothing. Whether the head can be had at any files is not shown
here. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.FrameFacts
import Johnson.Desc.ProofFile.Honest.K10.Pay.Run
import Johnson.Desc.ProofFile.Honest.K10.Pay.Terms
import Johnson.Desc.ProofFile.Honest.K10.Pay.FoldAt
import Johnson.Desc.ProofFile.Honest.K10.Thr.AtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- **A premise by name**: the message that the record's frame names as the fresh mask is neither sampled nor spent as a
mask. -/
def MaskFresh (s : TS) : Prop :=
  ∀ mk y, (recOf s).frame.mask = some mk → (recOf s).st.oracles[mk]? = some y →
    y.sampled = false ∧ y.spentAsMask = false

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head, written out once. The option turns off one early look of the notation
-- command, which has no case for a field access; each use is elaborated and type-checked as any term is.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a stand in front of a closing the twenty facts hold of the record of the verifier's state**, given that the
fresh mask's message is neither sampled nor spent. -/
theorem closeBase_at_stand {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : ThrS 𝕋 SaidOk (14 * l + IM.nAt l + 5) k s m En) (hfresh : MaskFresh s) :
    ∃ B : BaseData, CloseBase Qc (recOf s) B := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hb : 14 * l + IM.nAt l + 5 ≤ cF.blocksInOrder.length := Nat.le_of_lt hlt
  have hl : l < 25 := link_lt h hlt
  have hf : s.failed = none := (run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1).1
  have hrb := thrS_reach_below h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hr := reach_raw hrb
  obtain ⟨L, hL, hmo⟩ := frame_link h hl hr hf
  obtain ⟨Gq, hq⟩ := frame_group h hl hr hf
  obtain ⟨mk, hm⟩ := frame_mask h hl hr
  obtain ⟨G, hG⟩ := frame_there h hl hr
  have hcode := frame_code h hl hr hf G hG
  have hkh := frame_kh h hl hr hf G Gq hG hq
  have hfr : ∀ y, (recOf s).st.oracles[mk]? = some y → y.sampled = false ∧ y.spentAsMask = false :=
    fun y hy => hfresh mk y hm hy
  exact ⟨⟨L, Gq, mk, G⟩,
    { owed := frame_owed h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hT.1
      link := hL
      group := hq
      due := ⟨frame_next h hl hr hf, hmo⟩
      mask := hm
      beginRun := run_begin h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT.1 ⟨G, hG⟩
      there := hG
      inOrder := run_inOrder_reached h hr hf G hG
      rowsIn := run_rowsIn_reached h hr hf G hG
      termsOk := terms_reached h hl hrb hf G hG
      rows := run_rows h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT G hG
      kh := hkh
      stretch := frame_stretch h Td hr hf Gq hq
      code := hcode
      maskCode := mask_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT.1 G hG
      power := frame_power h hr hf
      bits := frame_bits h hl hr hf G hG
      shape := fold_shape h hl hr hf (B := ⟨L, Gq, mk, G⟩) hq hG hcode hkh
      maskfits := fold_mask h hl hr hf (B := ⟨L, Gq, mk, G⟩) hq hm hG hfr
      spendAsMask := fold_spend h hl hr hf (B := ⟨L, Gq, mk, G⟩) hq hm hG hfr }⟩

/-- So the test on the record says yes. -/
theorem ready_at_stand {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : ThrS 𝕋 SaidOk (14 * l + IM.nAt l + 5) k s m En) (hfresh : MaskFresh s) :
    YesFree.closeBaseB Qc (recOf s) = true := by
  obtain ⟨B, HB⟩ := closeBase_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT hfresh
  exact YesFree.closeBaseB_of HB

/-- **The closing's block accepts at each of the 25 closings**, at every fall and at every Said that gives `SaidOk`,
given the premise on the prover's list of halves and that the fresh mask is fresh at the stands. -/
theorem acceptedS_of_fresh (l : Nat) (hl : l < 25) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hfresh : ∀ k s m En, ThrS 𝕋 SaidOk (14 * l + IM.nAt l + 5) k s m En → MaskFresh s) :
    AcceptedS 𝕋 Said fall (14 * l + IM.nAt l + 5) :=
  accepted_base_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl rfl readers rows stAt Gr hF fall
    fun _ _ _ Td k s m En _ hT _ =>
      ready_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td ⟨hT.1, hSaid _ _ _ hT.2⟩
        (hfresh k s m En ⟨hT.1, hSaid _ _ _ hT.2⟩)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.MaskFresh
#print axioms ProofFile.Honest.K10.closeBase_at_stand
#print axioms ProofFile.Honest.K10.ready_at_stand
#print axioms ProofFile.Honest.K10.acceptedS_of_fresh
