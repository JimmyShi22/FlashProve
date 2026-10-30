-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM4At.lean: the proof of the statement `OwedFillM4`
(Johnson/Desc/K13/Law/OwedFillM4.lean): what the tie at W's commitment asks of the table's letters
(`FillM4`, Johnson/Desc/K13/Law/AtTableW.lean) out of kind K13's premises on the letter Mg
(`MgK13`), the tests on the plan (`PlanK13`, `PlanM4`) and what is owed beside. Two theorems: calls
alone.
Main names:
  `rider4_kept`: an item whose Bool is a test on the record that rides over the step at W's
    commitment (the second half of `OwedKeeps`, OwedSig.lean), and whose `pubP` says nothing, is a
    rider there.
  `fillM4_at`: **the statement.** `fillM4_of` (FillFromSentences.lean) CALLED at hS := the
    structure's `ours` · hO := the premise `OwedOthers4` at the structure's `sig`, `masks`, `seats`,
    `ours.indexThere` and the plan's `below` · the riders: `rider4_book` (the structure's `book`
    counts from 0, and the plan's hft says that 0 is the commitment's first tree), `rider4_seats`,
    `rider4_shapes`, `rider4_pileMasks`, `rider4_frontOk`, `rider4_kept`.
What is not claimed. A member of `MgK13`, `PlanK13` or `PlanM4`. `OwedOthers4` and `OwedKeeps wB`
are premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OwedFillM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame bookStepB)
open VerifiableInference.Desc.K12.Door (toTree)

/-- An item whose Bool is a test on the record that rides over the step, and whose `pubP` says
nothing, is a rider at W's commitment. -/
theorem rider4_kept {Pp W Cl : Type} {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W}
    {Q : List Pub} {p : Option Place} {q : Pub} {wB : S → Bool} (hm : q ∈ Q) (hK : OwedKeeps wB)
    (hW : ∀ x, Mg.pub q x = wB x.2) (hWP : ∀ x, Mg.pubP q x) : Rider4 Cl P P' N Mg Q p q :=
  fun x x' h hQ _ => by
    have h0 := hQ _ hm
    rw [hW] at h0
    refine ⟨?_, fun _ => hWP x'⟩
    rw [hW]
    exact hK.2 P P' x x' h h0

/-- **`FillM4` out of the structure, the tests on the plan and what is owed beside.** -/
theorem fillM4_at : OwedFillM4 := by
  intro Pp Cl Xi Cells Tok nR F y₀ P P' N Mg sh ly rest arr mat G smp ms decT M L wB Q p hMg hPl
    h4 hplan hW hWP hQ hIn _ hO hK hsmp hdec hrest
  have hB : ∀ x, Mg.pub bookItem x = bookStepB P'.gp.firstTree x.2.book x.2.roots := fun x =>
    (hMg.book x).trans (congrArg (fun ft => bookStepB ft x.2.book x.2.roots) h4.hft)
  refine fillM4_of Q p hMg.ours
    (hO P P' arr mat N Mg Q p P'.codes G smp ms decT L hMg.sig
      (hIn _ (by simp [knownK13])) (hIn _ (by simp [knownK13])) hMg.masks hMg.seats
      (fun x h => by rw [hMg.ours.indexThere] at h; exact h) hPl.below hsmp hdec)
    hrest hplan fun q hq => ?_
  rcases hQ q hq with hk | rfl | rfl
  · have hP := hMg.quiet q hk
    simp only [knownK13, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact rider4_book hq hB hP
    · exact rider4_seats (L := toTree L) hq hMg.seats hP h4.hp h4.hs
    · exact rider4_shapes hq hMg.shapes hP h4.hx
    · exact rider4_pileMasks hq hMg.masks hP
  · exact rider4_frontOk y₀ hMg.ours hq
  · exact rider4_kept hq hK hW hWP

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.rider4_kept
#print axioms VerifiableInference.Desc.K13.Law.fillM4_at
