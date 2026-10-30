-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLPublicThread.lean

It states no goal. No property of the protocol is claimed.

hok and hpub of
`acceptedS_stands_L` (the middle conjunct, hS, is what `shapeFits_head_L` pays inside it)
at the first thread's own letters (`firstLetters`,
Honest/Thread/TheFirstThread.lean): there Vd is `ReadyInput`, whose first clause is the first test.

  `closing_public_at_ready`       hpub to the letter at Vd := ReadyInput
  `closing_public_at_first_thread`  the same at every input that the first thread calls valid
  `closing_premises_at_first_thread`  hok, hS and hpub at the return's ground

By what. `closing_premises_at_finish`, `closing_public_of_okStart` (LotLPublicClosing.lean),
`ground_of_return` (LotLPublicFilling.lean), `head_valid` (Honest/Thread/FirstHead.lean).

Hypotheses. h: the head at a return of the maker. hf: pl is the finish at the return's ground. hc:
the statement of `closing_at_head`. The data are `widerRows Sz.ref` at the return: which filling the return
came of is not read here, so that these are its rows is for the one who lays hh to say.

Limits.
- Public tests alone: nothing on what a prover sends, nothing on a run.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicFilling
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstLetters head_valid)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {pl : K2.SwitchPlace}

/-- The return's ground is the blank ground, at the head at a return. -/
theorem ground_at_return (h : HeadAtReturn files A) :
    ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G := by
  obtain ⟨P, hA⟩ := h.returned
  exact ground_of_return h.head hA

/-- **hpub to the letter at the first thread's Vd.** -/
theorem closing_public_at_ready (h : HeadAtReturn files A) (hf : finishAt A.Z A.G = some pl) :
    ∀ v, ReadyInput h.description A.H v →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout pl
        ((K2.segmentsOf A.Z A.G).take pl.link) v.x = true :=
  fun _ hv => closing_public_of_okStart h.head (ground_at_return h) hf hv.1

/-- **The same at every input that the first thread calls valid.** -/
theorem closing_public_at_first_thread (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hf : finishAt A.Z A.G = some pl) :
    ∀ v, (firstLetters h parts w).valid v →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout pl
        ((K2.segmentsOf A.Z A.G).take pl.link) v.x = true :=
  fun v hv => closing_public_at_ready h hf v hv.2

/-- **hok, hS and hpub at the first thread's letters.** -/
theorem closing_premises_at_first_thread (h : HeadAtReturn files A)
    (hf : finishAt A.Z A.G = some pl)
    (hc : ClosingAtEveryPlace files A.Z h.places h.firstChain) :
    K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ v, ReadyInput h.description A.H v →
        K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout pl
          ((K2.segmentsOf A.Z A.G).take pl.link) v.x = true := by
  obtain ⟨hok, hS, -⟩ := closing_premises_at_finish h.head (ground_at_return h) hf hc
  exact ⟨hok, hS, closing_public_at_ready h hf⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.ground_at_return
#print axioms ProofFile.Honest.K12.AtProof.closing_public_at_ready
#print axioms ProofFile.Honest.K12.AtProof.closing_public_at_first_thread
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_at_first_thread
