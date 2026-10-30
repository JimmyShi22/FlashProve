-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EvAllAtEnd.lean: kind K13 (the members' batching): wherever the thread of the proof
file's first chain holds at its last border, every open row of the request's own group holds of the
words of the Script's witness: the meaning `evAll`
(Johnson/Desc/ProofFile/Honest/K14/EvAtLastStart.lean) of the last chain's item "ev", at the first
chain's last state. The full size, and the hash function `OnBytes.secondHashFunction`, alone. Statements with
their proofs; no definition.

Main names.
  `end_wrow_open`: the item "wrow" is open at border 358 of the first chain's table of items: a
    closed fact, by evaluation in Lean's kernel.
  `k13_wRow_at_end`: at that border the row (Eval) says its claim (`WRow`,
    Johnson/Desc/K13/Law/Letters.lean) of the witness's words read through the state's own book, at
    every continuation of the challenges.
  `k13_evAll_of_thread`: **`evAll` there**, from h (`P5J.AtMgA`) and the thread alone.

How. The thread's invariant says of every item that is open at its border that it holds of the
Script's witness, at every continuation; at "wrow" the item's meaning is `WRow`, by unfolding (the
library states the equation as the field wrow of `tied_at_letters`,
Johnson/Desc/ProofFile/Honest/K13/ExchangeM4At.lean, which is not imported here). The item is opened
behind member 356 (`k13_wrowS_at_356`, Johnson/Desc/ProofFile/Honest/K13/WRowAt356.lean) and has to
pass member 357. (Eval) is the own group's one open row there (`k13_evalAlone_at_end`,
EvalAloneAtEnd.lean of this folder).

Limits. Conditional on h and on the thread's invariant at border 358, at the thread as `lettersHead`
makes it (Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean), every argument a variable. THAT THE
INVARIANT HOLDS AT BORDER 358 AT ANY RUN IS NOT SHOWN HERE: the statements unpack it; where it holds
at no run they say nothing. The witness is the FIRST chain's Script's. A last chain's thread may
read another witness, in which later messages are laid over this one's: that `evAll` goes over to
such a witness is not shown here. The words hold values of the index's own entries: these statements
are not to stand in front of a law over coins.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.K13.EvalAloneAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (WRow)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K14 (evAll)

set_option maxRecDepth 100000 in
/-- The item "wrow" is open at the first chain's last border. -/
theorem end_wrow_open :
    Item.wrow ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 358 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **Wherever the first chain's thread holds at its last border, (Eval) says its claim of the
Script's witness's words**, at every continuation of the challenges: the thread's clause on its open
items, at "wrow". -/
theorem k13_wRow_at_end {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k s m En)
    (ds' : List Fmt.Drawn) :
    WRow (whereOf Zp) s
      (wordsFirst (P5J.At.arr Zp) s.st s.book (Q.wit k m.st.input (m.st.heard ++ ds'))) := by
  have hT' := hT
  unfold Thr at hT'
  have q : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).Mg m.st.input).wrow
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf m.st.input.x, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs En)
      (Q.wit k m.st.input (m.st.heard ++ ds')) := hT'.2.2.2.1 ds' Item.wrow end_wrow_open
  exact q

/-- **Wherever the first chain's thread holds at its last border, every open row of the own group
holds of the Script's witness's words**, at every continuation of the challenges: the meaning
`evAll` of the last chain's item "ev", at the first chain's last state. No premise but h and the
thread's invariant at that border, which holds (Eval)'s sentence among its clauses. -/
theorem k13_evAll_of_thread {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k s m En)
    (ds' : List Fmt.Drawn) (z : ProofFile.InstPub) (y : Strs) :
    evAll (P5J.At.arr Zp) (fun q : ProofFile.InstPub × TS => q.2) (z, s) y
      (Q.wit k m.st.input (m.st.heard ++ ds')) :=
  k13_evAll_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT (P5J.At.arr Zp) z y _
    (k13_wRow_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT ds')

end AtFullSide.K13

#print axioms AtFullSide.K13.end_wrow_open
#print axioms AtFullSide.K13.k13_wRow_at_end
#print axioms AtFullSide.K13.k13_evAll_of_thread
