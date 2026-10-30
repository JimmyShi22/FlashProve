-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/PlanAtSendB.lean: no soundness is claimed.
PlanAtSend (SampleTwoOpen.lean: the closed facts on a sending's parameters that sampleTwoB_h4_paid asks twice) as a test with code, so that a run can evaluate it.
  planAtSendB P cs sh k rad   K1.condPort P rad && P.codes = cs && the place k is there, sampled, with the shape sh
  **planAtSend_of_B**         planAtSendB P cs sh k rad = true → PlanAtSend P cs sh k
  sendsPlanB Z                one test on the public part for both sendings, at the last table's letters and the radius 0
  **hP_of_sendsPlanB**        sendsPlanB Z = true, at the opening IM.Open (Johnson/IMR/SeatOpen.lean) ⇒ hP₁ ∧ hP₂, to the letter (Bs.G₀.first = Z.first by Open.first)

No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SampleTwoOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc

def planAtSendB (P : K1.Par) (cs : Codes) (sh : OracleShape) (k : ℕ) (rad : ℕ → ℕ) : Bool :=
  K1.condPort P rad && decide (P.codes = cs) &&
    if h : k < (K1.shapesOf P).length then
      decide (K1.sampledAt P ⟨k, h⟩) && decide (K1.shapeAt P ⟨k, h⟩ = sh)
    else false

theorem planAtSend_of_B {P : K1.Par} {cs : Codes} {sh : OracleShape} {k : ℕ} {rad : ℕ → ℕ}
    (h : planAtSendB P cs sh k rad = true) : PlanAtSend P cs sh k := by
  unfold planAtSendB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  split at h3
  · next hk =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    exact ⟨⟨rad, h1⟩, h2, ⟨k, hk⟩, rfl, h3.1, h3.2⟩
  · cases h3

/-- **ONE TEST ON THE PUBLIC PART for both sendings**, at the letters at which the last table spends
`sampleTwoB`: cs := (p14At Z).codes; the index masks' message is the place 4 of the first sending,
with the shape of the first notice of request.atStart; W's is the place 0 of its own, with the shape
(p14At Z).S.w; the radius 0. Where `linMessageW` gives nothing the second half passes idly. -/
def sendsPlanB (Z : ProofFile.Pub) : Bool :=
  planAtSendB (K1.firstPar Z.first (K1.gpOf Z)) (p14At Z).codes
      ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) 4
      (fun _ => 0) &&
    match linMessageW Z.first.lin with
    | some msg => planAtSendB
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)
        (p14At Z).codes (p14At Z).S.w 0 (fun _ => 0)
    | none => true

/-- **hP₁ and hP₂ of `sampleTwoB_h4_paid`, from that one test, at the opening.** -/
theorem hP_of_sendsPlanB {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (h : sendsPlanB Z = true) :
    PlanAtSend (K1.firstPar Bs.G₀.first (K1.gpOf Z)) (p14At Z).codes
        ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) 4 ∧
      ∀ msg, linMessageW Z.first.lin = some msg → PlanAtSend
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)
        (p14At Z).codes (p14At Z).S.w 0 := by
  unfold sendsPlanB at h
  rw [Bool.and_eq_true] at h
  refine ⟨?_, fun msg hm => ?_⟩
  · rw [O.first]
    exact planAtSend_of_B h.1
  · have h2 := h.2
    rw [hm] at h2
    exact planAtSend_of_B h2

end ToldDesc

#print axioms ToldDesc.planAtSend_of_B
#print axioms ToldDesc.hP_of_sendsPlanB
