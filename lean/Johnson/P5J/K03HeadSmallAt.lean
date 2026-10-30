-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03HeadSmallAt.lean: the kind "lookup" (K3): THE PREMISE hHead OF `k03_head_at` AND
`k03_cond_due` (Johnson/P5J/K03HeadAt.lean, K03Due.lean) AT THE CLOSED CONSTANT: "the output head's
part 'small' goes back over what an accept of the lookup leaves", at all strings.

Main name: `k03_hHead`: from the head alone: one call of the output head's authors'
`headPart_atAll_blind` (Johnson/Desc/Kinds/Law/HeadCutsAtAll.lean): the constant's headPart reads
nothing of the strings, and of the verifier's state the heard reply's token at the part
lookCallsHeard alone; "small" is another part. So the question "can hHead be met?" that stands in
the heads of those two files is answered: yes, by a theorem; `SameBut` is not even spent.

Limits: nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03HeadAt
import Johnson.Desc.Kinds.Law.HeadCutsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **hHead, at the constant.** -/
theorem k03_hHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ (z : ProofFile.InstPub) (s s' : VerifiableInference.Desc.First.S) i y y' w, SameBut s s' →
      (h.toAtMg.𝔇 h.𝔇).headPart .small i (z, s') y' w →
      (h.toAtMg.𝔇 h.𝔇).headPart .small i (z, s) y w :=
  fun z s s' i y y' w _ hp =>
    Eq.mp (VerifiableInference.Desc.Kinds.Head.Law.headPart_atAll_blind h .small i z s s' y y' w
      (fun e => by cases e)) hp

end P5J

#print axioms P5J.k03_hHead
