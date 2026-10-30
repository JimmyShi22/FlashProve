-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LReturnsClosing.lean: the premise hClosing of
`carryRows_returns_at_head` and `carryRows_returns_at_stand` (LReturnsAtHead.lean) and of
`acceptedS_of_shape` (LShapeAccepted.lean), under the library's head (`P5J.AtMgA` at
`OnBytes.secondHashFunction`): at the finish of the code switch the closing returns at zeros. And the first two
laws without that premise.

  `closingOk_at_finish`            the premise, in its own letters
  `carryRows_returns_at_input`     `carryRows_returns_at_head` without it
  `carryRows_returns_at_thread`    `carryRows_returns_at_stand` without it

By what. `closing_at_head` (Johnson/Desc/ProofFile/Honest/K2/Law/ClosingAtHead.lean): at every place
of the kind. 25 closed facts by Lean's kernel lie beneath it.

Limits.
- All limits of LReturnsAtHead.lean but the first hold here.
- It says that a public test passes: the closing returns at zeros. Nothing on what it leaves.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `carryRows_returns_at_thread` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from `Thr` as a
premise; hValid is on the letter for "valid".
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LReturnsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

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

/-- **At the finish the closing returns at zeros.** -/
theorem closingOk_at_finish (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) :
    K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact K2.Law.closing_at_head h.toAtMg O pl (List.mem_of_find?_eq_some hf)

/-- **The sender's text returns at every input whose instance passes the test on the instance.** -/
theorem carryRows_returns_at_input (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (w : Local W₀ Rc ProofFile.Inst Tr) (hStart : (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (heard : List Fmt.Drawn) (mem : ℕ → Stretch) :
    ∃ R, carryRows (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl w heard mem = .ok R :=
  carryRows_returns_at_head h hG hf (closingOk_at_finish h hG hf) readers w hStart heard mem

variable {Bk : ProverCoinCounts} {Cl X P Cells Tok M : Type}

/-- **So at every stand of the first chain's thread**, where the thread's valid inputs pass the test
on the instance. -/
theorem carryRows_returns_at_thread (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc ProofFile.Inst Tr X P Cells Tok M)
    (hValid : ∀ w, L.valid w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true) {b : ℕ}
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr L.thread b k s m E) (heard : List Fmt.Drawn) (mem : ℕ → Stretch) :
    ∃ R, carryRows (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers
      (K2.lotClosingAt G.first.layout (K2.segmentsOf Zp G)) pl m.st.input heard mem = .ok R :=
  carryRows_returns_at_stand h hG hf (closingOk_at_finish h hG hf) readers L hValid hT heard mem

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closingOk_at_finish
#print axioms ProofFile.Honest.K12.AtProof.carryRows_returns_at_input
#print axioms ProofFile.Honest.K12.AtProof.carryRows_returns_at_thread
