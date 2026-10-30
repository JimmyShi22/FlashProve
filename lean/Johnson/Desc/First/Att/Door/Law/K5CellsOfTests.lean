-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CellsOfTests.lean: kind K5: A PAYMENT BENEATH THE KIND's FROZEN NAMED CONDITION (K5CondAt, K5LeftOfCond.lean): ITS PER-GROUP FIELD cells := ∃ idx, K5CellsCond h a x₁ idx (K5RestCells.lean), AND K5Rest's FIELD cells ITSELF, FROM TESTS WITH CODE ON PUBLIC DATA ALONE.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Why. K5CellsOfAt.lean took the ends of the two theorems AtMgA.one_at | own_at (Johnson/P5J/K03OneOwnAt.lean) as premises. Here these theorems are CALLED: one line each.

Main names (T: the row "K3 tie" (on where its text comes from: K5CellsOfAt.lean's head) at l := 2 * g + 1: a Bool as it stands; oneC · namedC (K03OneOwnAt.lean) · offC (Johnson/P5J/HidBearsAtMg.lean): named tests):
  `cellsCond_of_tests`: T · h.oneC (2 * g + 1) = true → ∃ idx, K5CellsCond h a x₁ idx.
  `cellsOwn_of_tests`: T · h.oneC (2 * g + 1) · h.namedC (2 * g + 1) · h.namedC (2 * g) · h.toAtMg.offC → ∃ idx, K5CellsOwn h g a x₁ idx.
  `cells_of_tests`: **so K5Rest's field cells (the kind's one law over witnesses) follows from five Bools on public data.**
Is it empty here? THE FIVE ARE SHOWN AT NOTHING IN LEAN: a run's matter. As reported, by prints (evaluations at a stored full-size set's three public files; evidence, no proof): oneC true at l < 24, namedC at l < 25, offC true, each with negative tests that say no; tie
true at all 25 over the files of another build.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5CellsOfAt
import Johnson.P5J.K03OneOwnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls idxAt CellsAre)
open P5J (AtMgA TS At.X At.num At.sentAt At.rad3At)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- **The frozen per-group field, from two tests.** -/
theorem cellsCond_of_tests {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (At.X Zp) (2 * g + 1) false = some x₁)
    (T : _root_.Meaning.linkTieB (At.X Zp) (At.sentAt Zp) (At.rad3At Zp Z.lay) (At.num Zp) (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (2 * g + 1) (_root_.Meaning.tlAt (At.X Zp) (2 * g + 1)) = true)
    (hB : h.oneC (2 * g + 1) = true) :
    ∃ idx, K5CellsCond h a x₁ idx :=
  cellsCond_of_at h hg ha hx T (h.one_at (by omega) hB)

/-- **What K5Rest's field cells spends, from five tests.** -/
theorem cellsOwn_of_tests {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (At.X Zp) (2 * g + 1) false = some x₁)
    (T : _root_.Meaning.linkTieB (At.X Zp) (At.sentAt Zp) (At.rad3At Zp Z.lay) (At.num Zp) (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (2 * g + 1) (_root_.Meaning.tlAt (At.X Zp) (2 * g + 1)) = true)
    (hB : h.oneC (2 * g + 1) = true) (hN₁ : h.namedC (2 * g + 1) = true) (hN₀ : h.namedC (2 * g) = true)
    (hC : h.toAtMg.offC = true) :
    ∃ idx, K5CellsOwn h g a x₁ idx :=
  cellsOwn_of_at h hg ha hx T (h.one_at (by omega) hB) (h.own_at (by omega) hN₁ hC) (h.own_at (by omega) hN₀ hC)

/-- **K5Rest's field cells, from five tests on public data.** -/
theorem cells_of_tests {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (At.X Zp) (2 * g + 1) false = some x₁)
    (T : _root_.Meaning.linkTieB (At.X Zp) (At.sentAt Zp) (At.rad3At Zp Z.lay) (At.num Zp) (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (2 * g + 1) (_root_.Meaning.tlAt (At.X Zp) (2 * g + 1)) = true)
    (hB : h.oneC (2 * g + 1) = true) (hN₁ : h.namedC (2 * g + 1) = true) (hN₀ : h.namedC (2 * g) = true)
    (hC : h.toAtMg.offC = true) :
    ∀ w, h.𝔇.H.base (2 * g + 1) w →
      CellsAre x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (msgsOf h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁) h.𝔇.arr w) (zofAll h g w) :=
  cellsOwn_all h hg ha hx (cellsOwn_of_tests h hg ha hx T hB hN₁ hN₀ hC)

end

end H2K5.Door

#print axioms H2K5.Door.cellsCond_of_tests
#print axioms H2K5.Door.cellsOwn_of_tests
#print axioms H2K5.Door.cells_of_tests
