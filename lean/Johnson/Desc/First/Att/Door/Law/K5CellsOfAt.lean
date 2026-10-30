-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CellsOfAt.lean: kind K5: A PAYMENT BENEATH THE KIND's FROZEN NAMED CONDITION (K5CondAt, K5LeftOfCond.lean): ITS PER-GROUP FIELD cells := ∃ idx, K5CellsCond h a x₁ idx (K5RestCells.lean) FROM OTHER FILES' (Johnson/P5J/) OWN SENTENCES ON THE LOOKUP ARGUMENT AT SEGMENT 2 g + 1, AT A CLOSED
idx.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Why. Another file has theorems AtMgA.one_at | own_at (Johnson/P5J/K03OneOwnAt.lean) that end in the lookup argument's ledger's fields one | own at a segment l, from tests with code (oneC l · namedC l · offC) which runs have evaluated.
THIS FILE TAKES THE TWO THEOREMS' ENDS AS PREMISES: so Lean says that these ends meet this kind's fields; the last step (this file's theorems after one_at | own_at) is one line where both lie.
THE PREMISES' TEXTS: O · W₁ · W₀ ARE CUT BY PROGRAM out of K03OneOwnAt.lean's two statements, sign for sign, with l := 2 * g + 1 (W₀: 2 * g) · T IS TYPED AFTER the line for the row "K3 tie" in a text of ours, not in this repository, and held by program against that text, with
l := 2 * g + 1 and lay := Z.lay.

Main names:
  `cellsCond_of_at`: T · O → ∃ idx, K5CellsCond h a x₁ idx, at idx := idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1) (Johnson/Desc/First/Look/K3IdxAt.lean): A CLOSED TERM OF g.
  `cellsOwn_of_at`: T · O · W₁ · W₀ → ∃ idx, K5CellsOwn h g a x₁ idx (K5CellsOfOwn.lean): what K5Rest's field cells spends.
WHAT LEAN's YES SAYS BESIDE: (h.toAtMg.𝔇 h.𝔇)'s sent · rad3 · seat3 · arr · ms · N are h.𝔇's, and h.𝔇's sent · rad3 are At.sentAt Zp · At.rad3At Zp Z.lay, by unfolding; x₁.link = 2 g + 1; a.seam.tl = Meaning.tlAt (At.X Zp) (2 g + 1).
Is it empty here? T · O · W₁ · W₀ ARE SHOWN AT NOTHING IN LEAN. As reported, by prints (evaluations at a stored full-size set's three public files; evidence, no proof): oneC true at l < 24, namedC at l < 25, offC true, each with negative tests that say no; tie true at
all 25 over the files of another build.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5CellsOfOwn
import Johnson.Desc.First.Look.K3IdxAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls idxAt)
open VerifiableInference.Desc.First.Att.P (place_calls)
open VerifiableInference.OnPublicFiles (OneNumber OwnNamed)
open P5J (AtMgA TS At.X At.num At.sentAt At.rad3At)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- **The frozen per-group field, at a closed idx.** -/
theorem cellsCond_of_at {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (At.X Zp) (2 * g + 1) false = some x₁)
    (T : _root_.Meaning.linkTieB (At.X Zp) (At.sentAt Zp) (At.rad3At Zp Z.lay) (At.num Zp) (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (2 * g + 1) (_root_.Meaning.tlAt (At.X Zp) (2 * g + 1)) = true)
    (O : OneNumber (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
      (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (_root_.Meaning.tlAt (At.X Zp)) (2 * g + 1)
      (fun j : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (2 * g + 1)).length =>
      (h.toAtMg.𝔇 h.𝔇).seat3 (2 * g + 1) false j.1) (h.toAtMg.𝔇 h.𝔇).arr id) :
    ∃ idx, K5CellsCond h a x₁ idx := by
  have hxl : x₁.link = 2 * g + 1 := (place_calls (scope_all h).1 ha hx).2.2.1
  refine ⟨idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1), ?_, ?_⟩
  · rw [hxl, ← tlAt_att hg ha]
    exact T
  · rw [hxl]
    exact O

/-- **What K5Rest's field cells spends, at the same idx.** -/
theorem cellsOwn_of_at {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (At.X Zp) (2 * g + 1) false = some x₁)
    (T : _root_.Meaning.linkTieB (At.X Zp) (At.sentAt Zp) (At.rad3At Zp Z.lay) (At.num Zp) (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (2 * g + 1) (_root_.Meaning.tlAt (At.X Zp) (2 * g + 1)) = true)
    (O : OneNumber (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
      (idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)) (_root_.Meaning.tlAt (At.X Zp)) (2 * g + 1)
      (fun j : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (2 * g + 1)).length =>
      (h.toAtMg.𝔇 h.𝔇).seat3 (2 * g + 1) false j.1) (h.toAtMg.𝔇 h.𝔇).arr id)
    (W₁ : OwnNamed (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (At.num Zp) (_root_.Meaning.tlAt (At.X Zp)) (2 * g + 1)
      (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms (h.toAtMg.𝔇 h.𝔇).N)
    (W₀ : OwnNamed (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (At.num Zp) (_root_.Meaning.tlAt (At.X Zp)) (2 * g)
      (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms (h.toAtMg.𝔇 h.𝔇).N) :
    ∃ idx, K5CellsOwn h g a x₁ idx := by
  have hxl : x₁.link = 2 * g + 1 := (place_calls (scope_all h).1 ha hx).2.2.1
  refine ⟨idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1), ?_, ?_, ?_, W₀⟩
  · rw [hxl, ← tlAt_att hg ha]
    exact T
  · rw [hxl]
    exact O
  · rw [hxl]
    exact W₁

end

end H2K5.Door

#print axioms H2K5.Door.cellsCond_of_at
#print axioms H2K5.Door.cellsOwn_of_at
