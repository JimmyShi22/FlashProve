-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/WTextAtDoor.lean: kind K13 (the members' batching): what the last chain's start reads
as W (`wvW`, Johnson/Desc/Third/Law/Row0AtWords.lean), at the first chain's last state and of the
last chain's witness (`lastWitness`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean), in
terms of the first chain's Script's witness. The full size, and the hash function `OnBytes.secondHashFunction`,
alone. Statements with their proofs; no definition.

Main names.
  `k13_codes_at_end`: wherever the first chain's thread holds at its last border, the state's table
    of codes is the plan's.
  `k13_wvW_at_lastWitness`: there, W's reader at the last chain's witness gives the word that the
    first Script's witness has, read through the state's own book, in the main table of the message
    number `w₁Of`, at the place that W's layout gives the entry, the layout taken at the plan's
    codes and the first chain's shape.

How. The last chain's shape is the first chain's (`P5J.linOne`, Johnson/P5J/Cols13Paid.lean). A
message of the first chain's book sits in a tree below the first chain's count of trees
(`head_seats_below`, Johnson/Desc/ProofFile/Honest/K14/FirstSeatsBelow.lean), where the overlay
leaves table and pad (`wordsBy_first`, Johnson/Desc/ProofFile/Honest/K14/FirstAtLastWitness.lean).

Limits. Conditional on the head at the return and on the thread's invariant at border 358; that it
holds there at any run is not shown here. What the word is, is not said here.

What is not claimed. Neither is one of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.EvalAloneAtEnd
import AtFullSide.K13.WTextAtEnd
import Johnson.Desc.ProofFile.Honest.K14.FirstAtLastWitness
import Johnson.Desc.ProofFile.Honest.K14.FirstSeatsBelow
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexFactsThr
import Johnson.P5J.Cols13Paid
import Johnson.ToldDescR.RcLastCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.K13.Law (pin_at)
open VerifiableInference.Desc.Sound (MsgT wordsFirst seatBy noFirst)
open VerifiableInference.Desc.Third.Law (wvW w₁Of)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead HeadAtReturn FirstThreadParts IndexReaders
  firstThread lastWitness)
open ProofFile.Honest.K4.W (indexFacts_thr)
open ProofFile.Honest.K14 (wordsBy_first head_seats_below)

/-- **Wherever the first chain's thread holds at its last border, the state's table of codes is the
plan's.** -/
theorem k13_codes_at_end {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k s m En) :
    s.st.codes = Zp.first.codes := by
  obtain ⟨sh, F⟩ := indexFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (le_of_eq (len358 h).symm) (by decide) (pin_at (k := 358) (by decide) (by decide)) hT
  exact F.hc

/-- **W's reader at the last chain's witness, in terms of the first Script's witness.** hd': any
list of challenges. -/
theorem k13_wvW_at_lastWitness {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins A.B} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (firstThread hd first w) 358 k s m En) (z : ProofFile.InstPub) (hd' : List Fmt.Drawn)
    (c : ℕ) :
    wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) (z, s)
        (lastWitness hd first reads k m.st.input hd') c =
      wordsFirst (P5J.At.arr A.Z) s.st s.book (first.script.wit k m.st.input hd') (w₁Of s) .main
        ((linLayW A.Z.first.codes A.Z.first.lin).index c) := by
  have hc : s.st.codes = A.Z.first.codes :=
    k13_codes_at_end hd.head A.H first.script _ _ _ _ _ _ _ _ _ w hT
  have hS : (ToldDesc.p14At A.Z).S = A.Z.first.lin := (P5J.linOne hd.head.laid).symm
  show wordsFirst (P5J.At.arr A.Z) s.st s.book (lastWitness hd first reads k m.st.input hd')
    (w₁Of s) .main ((linLayW s.st.codes (ToldDesc.p14At A.Z).S).index c) = _
  rw [hc, hS]
  exact wordsBy_first hd first reads k m.st.input hd' (seatBy noFirst s.book) s.st (w₁Of s)
    (head_seats_below hd.head A.H first.script _ _ _ _ _ _ _ _ _ w
      (le_of_eq (len358 hd.head).symm) hT (w₁Of s)) .main _

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_codes_at_end
#print axioms AtFullSide.K13.k13_wvW_at_lastWitness
