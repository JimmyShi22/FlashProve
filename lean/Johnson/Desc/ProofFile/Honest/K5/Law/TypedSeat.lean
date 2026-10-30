-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TypedSeat.lean: CONDITIONAL: THE TYPED SEATS OF THE MESSAGES,
AND THE FORM's reach AT THEM, under the library's head on the public input (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean). No filling, no prover, no thread. One definition; one statement with its
proof.

  typedSeat           a definition: the opening's seat at segment 0, the switches' at every other
  reach_typedSeat     CONDITIONAL: the form's reach at the typed seats, at every segment but the
                      head's, at every N, with no challenge heard

The premises. h: the head · hG: G is the maker's own ground · hl: l is below 24.

How. reach_firstSeat, reach_switchSeat (ReachAtHead.lean in this folder), one premise forgotten.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. That there is a ground G with hG under h is not said here. What is laid at a
typed seat is not said. At the earlier hash OnBytes.secondHashFunction, a fixed function. Through its imports it
stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/
(lean/LIMITS.md, L15): a fact on import lines. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsK5
import Johnson.Desc.ProofFile.Honest.K5.Law.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The typed seats**: the opening's at segment 0, the switches' at every other. -/
noncomputable def typedSeat (G : Ground) (l : ℕ) : MsgAddr → Option (ℕ × ℕ) :=
  if l = 0 then K1.firstSeat h.𝔇.sent.shape 0 else K2.switchSeat Zp G

/-- **THE FORM's reach AT THE TYPED SEATS**, at every segment but the head's, at every N, with no
challenge heard. CONDITIONAL: under the hypothesis h; hG: G is the maker's own ground. -/
theorem reach_typedSeat {G : Ground} (hG : blankBy pureRoad.links Zp = some G) (N : ℕ) {l : ℕ}
    (hl : l < 24) :
    ∀ (As : List OnBytes.Params.ReqArray) (Ar : OnBytes.Params.ReqArray),
      h.𝔇.sent.layout.link[l]? = some As → Ar ∈ As → offPlanes l Ar.name = true →
      ((cellsVals Sz.ref).size l Ar.name).isSome = true →
      ∃ Ad : MsgAddr, typedSeat h G l Ad = some (l, Ar.message) ∧
        (fun _ : MsgAddr => 0) Ad ≤ N := by
  intro As Ar hAs hAr _ hz
  unfold typedSeat
  by_cases h0 : l = 0
  · subst h0
    rw [if_pos rfl]
    exact reach_firstSeat h N hAs hAr hz
  · rw [if_neg h0]
    obtain ⟨G', hG', R⟩ := reach_switchSeat h
    have eG : G' = G := Option.some.inj (hG'.symm.trans hG)
    rw [eG] at R
    exact R N l (by omega) hl As Ar hAs hAr hz

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.typedSeat
#print axioms ProofFile.Honest.K5.reach_typedSeat
