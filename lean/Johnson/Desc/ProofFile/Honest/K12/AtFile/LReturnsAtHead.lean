-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LReturnsAtHead.lean: the sender's text in the job of the
first chain's closing proximity test (`carryRows`, K12/AtProof/JobL.lean) returns, under the
library's head (`P5J.AtMgA` at `OnBytes.secondHashFunction`), at the letters at which the wider filling lays
that job (`proxLotOf`, Honest/AtPureWiderK12.lean) where its sizes are `Sz.ref`, at every input
whose instance passes the description's test on the instance, at every list of challenges and every
stretch of coins. So at every stand of a thread whose valid inputs pass that test.

  `carryRows_returns_at_head`    the law at an input
  `carryRows_returns_at_stand`   at every stand of the first chain's thread, at every number

Hypotheses.
  h, hG, hf   the head; G is the blank ground; pl is the finish that `finishAt` returns there
  hClosing    the closing returns at zeros at pl, at the segments in front of it (`K2.closingOk`): a
              test with code on public data
  hStart      the instance passes the description's test on the instance (`okStart`)
  hValid      (at a stand) the thread's valid inputs pass that test

By what. `carryRows_returns` (ClosingReturns.lean), `carryShape_at_head` (LReturnsLines.lean),
`publicOk_of_okStart` (Johnson/HonestTrace/Joint/ReadsLightPaid.lean).

Limits.
- hClosing IS A PREMISE. It is shown at no place here.
- hStart and hValid are premises. That some instance passes the test is not shown here.
- At the sizes `Sz.ref` alone. The full size; the format's second hash function.
- Nothing says what the rows are.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `carryRows_returns_at_stand` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from `Thr` as a
premise; hValid is on the letter for "valid". `carryRows_returns_at_head` names no coin in a
premise: it holds at every list of challenges and every stretch of coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LReturnsLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingReturns
import Johnson.HonestTrace.Joint.ReadsLightPaid
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA F0T)

variable {W₀ Rc Tr : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The sender's text returns at every input whose instance passes the test on the instance.** -/
theorem carryRows_returns_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl)
    (hClosing : K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hStart : (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true) (heard : List Fmt.Drawn)
    (mem : ℕ → Stretch) :
    ∃ R, carryRows (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl w heard mem = .ok R := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hm : pl ∈ K2.switchPlaces Zp Bs.G₀ := List.mem_of_find?_eq_some hf
  exact carryRows_returns _ readers _ _ pl w heard mem hClosing
    (OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart h O hStart pl hm)
    (carryShape_at_head h.toAtMg hG hf)

variable {Bk : ProverCoinCounts} {Cl X P Cells Tok M : Type}

/-- **So at every stand of the first chain's thread**, where the thread's valid inputs pass the test
on the instance. -/
theorem carryRows_returns_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl)
    (hClosing : K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc ProofFile.Inst Tr X P Cells Tok M)
    (hValid : ∀ w, L.valid w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true) {b : ℕ}
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr L.thread b k s m E) (heard : List Fmt.Drawn) (mem : ℕ → Stretch) :
    ∃ R, carryRows (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl m.st.input heard mem = .ok R :=
  carryRows_returns_at_head h hG hf hClosing readers m.st.input (hValid _ hT.2.2.2.2.2.2) heard mem

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carryRows_returns_at_head
#print axioms ProofFile.Honest.K12.AtProof.carryRows_returns_at_stand
