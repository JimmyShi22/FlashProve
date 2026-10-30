-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5SentOfK3.lean: kind K5 (an attention segment's own rounds): TWO FIELDS OF K5Rest (K5AtMgPaid.lean: sent · someMem) AT THE COMPOSED MEANING's CLOSED CONSTANT, FROM THE HEAD's OWN NAMED TEST k3 (Johnson/P5J/MgAtAll.lean: AtMgA.k3 : At.k3SeatsB Zp cF Z.lay = true).
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

Typed by reading P5J/MgAtAll.lean · Rad3Seat3Tests.lean · Rad3Seat3At.lean · LettersAll.lean · LettersAt4.lean ·
Desc/Sound/MgAll.lean · First/Look/K3LettersAt.lean · K3CallsFill.lean · K3CallsAddress.lean · Door/Law/K5AtMgPaid.lean.

Why. The test k3SeatsB (Johnson/P5J/Rad3Seat3Tests.lean) asks, at every link, that each member of the calls' list has a member of the table's own list alike (callsSomeB) and that its seat stands in the link's first sending (callsSentB); its laws calls_some | calls_sent end in the lookup argument's fields.
The kind's two fields are these at the link x₁.link = 2 g + 1, at the constant's letters: rad := h.𝔇.l3.rad · seat := h.𝔇.l3.seat x₁.link false · Dn := h.𝔇.sent · ms := h.𝔇.ms · N := h.𝔇.pubD.N, which unfold to the test's own terms.

Main names:
  `k3_at`: the test's six parts at the calls' place of an attention segment.
  `sent_all`: K5Rest's field sent. `someMem_all`: K5Rest's field someMem. Each in the field's own text at the closed letters.
Is it empty here? Under the head: A MEMBER OF THAT HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). Of its field k3: EVALUATED, NOT PROVED (Johnson/P5J/Rad3Seat3Tests.lean, Limits); by report (a text of this project that is not in this repository): k3SeatsB said true at all 25 links, and every negative test false, at the release's three public files, at another form's letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.First.Look.K3CallsAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open P5J (AtMgA TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

theorem links_25 : P5J.At.links.length = 25 := by decide

include h in
/-- The head's test on the lookup arguments' seats, at the calls' place of an attention segment. -/
theorem k3_at {g : ℕ} (hg : g < 12) {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    x₁.link = 2 * g + 1 ∧ P5J.At.callsSomeB Zp Z.lay x₁.link = true ∧ P5J.At.callsSentB Zp cF Z.lay x₁.link x₁.link = true := by
  have e : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  obtain ⟨-, -, h3, h4, -, -⟩ := P5J.At.k3SeatsB_at Zp cF Z.lay h.k3 x₁.link (by rw [e, links_25]; omega)
  exact ⟨e, h3, h4⟩

/-- **K5Rest's field sent, at the closed letters.** -/
theorem sent_all {g : ℕ} (hg : g < 12) {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    ∀ i : Fin (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length, h.𝔇.l3.seat x₁.link false i.1 ∈ h.𝔇.pubD.N.sent (2 * g + 1) 0 := by
  obtain ⟨e, -, h4⟩ := k3_at h hg hx
  intro i
  have h1 : P5J.At.seat3At Zp x₁.link false i.1 ∈ (P5J.At.N Zp cF).sent x₁.link 0 := P5J.At.calls_sent Zp cF Z.lay x₁ x₁.link h4 i
  have h2 : (P5J.At.N Zp cF).sent x₁.link 0 = (P5J.At.N Zp cF).sent (2 * g + 1) 0 := by rw [e]
  rw [h2] at h1
  exact h1

/-- **K5Rest's field someMem, at the closed letters.** -/
theorem someMem_all {g : ℕ} (hg : g < 12) {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    ∀ i, ∃ y ∈ h.𝔇.ms, Alike y (⟨⟨sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link, fun j => h.𝔇.l3.seat x₁.link false j.1⟩, i⟩ : Mem) :=
  P5J.At.calls_some Zp Z.lay x₁ (k3_at h hg hx).2.1

end

end H2K5.Door

#print axioms H2K5.Door.k3_at
#print axioms H2K5.Door.sent_all
#print axioms H2K5.Door.someMem_all
