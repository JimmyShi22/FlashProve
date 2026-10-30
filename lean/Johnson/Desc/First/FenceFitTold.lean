-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FenceFitTold.lean: WHAT THE TABLE's TEST fenceFit ASKS AT THE NUMBERS THAT ARE
FILLED OFF WHAT THE BLOCKS TELL: with the look-up by place taken away: at every border k, each
sampled tenant of an open pin sits in a tree whose number is below the number of trees that the
first k blocks tell. Two theorems. A file beside the table: it turns nothing of it.
Why. Several kinds' laws at the first chain's table take `fenceFit N links ps = true` as a
premise: whoever spends `fenced_at` (Johnson/Desc/Sound/PieceFence.lean): K4's row's line "below"
among them. UNLIKE `bookFit` (Johnson/Desc/First/BookFitTold.lean) IT IS NOT TRUE AT THE FILLED N
BY THAT FILLING's MAKE: its left side is read off four fields that `withTold` leaves as they were
(`sent`, `keptOf`, `index`, `w`: the plan's seats), its right side off the telling: two sources.
What can be taken away is the look-up: so that what is left to show, or to test, stands in the
open, without `treesAt` and without the list's index.
  `sampledIn_withTold`: the sampled tenants of the open pins are those of the numbers beneath: by
  rfl.
  `fenceFit_withTold`: **the test's yes at the filled numbers says just this**: an equivalence.
Silly members. Where no pin is open at any border the right side holds of nothing, and the test
says yes.
Limits. (1) `ps.Nodup` is asked, as in BookFitTold.lean; at the table's own list it is a theorem:
`ProofFile.Law.flatPlaces_nodup` (Johnson/Desc/ProofFile/Law/KindPlaces.lean).
(2) THE RIGHT SIDE IS SHOWN NOWHERE HERE: it has content: it ties the plan's
seats to the description's telling. It has been evaluated true at one honest proof a size, with
controls that failed (as reported; not shown here). (3) No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.BookFitTold
import Johnson.Desc.First.FenceFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- The sampled tenants of the open pins are those of the numbers beneath. -/
theorem sampledIn_withTold (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (O : List Item) : sampledIn (N.withTold ps told) O = sampledIn N O := rfl

/-- **What the test's yes says at the numbers that are filled off the telling.** -/
theorem fenceFit_withTold (N : Numbers) (links : List ModelPart) (ps : List Place)
    (told : List (List Oracle)) (hn : ps.Nodup) :
    fenceFit (N.withTold ps told) links ps = true ↔
      ∀ k, k ≤ ps.length → ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        x.1 < treesTold told k := by
  constructor
  · intro h k hk x hx
    have t : x.1 < treesTold told (borderOf ps ps[k]?) :=
      fenceFit_at (N.withTold ps told) links ps h k hk x hx
    rwa [borderOf_getElem ps hn k hk] at t
  · intro h
    unfold fenceFit
    refine List.all_eq_true.2 fun k hk => List.all_eq_true.2 fun x hx => decide_eq_true ?_
    have hk' : k ≤ ps.length := Nat.le_of_lt_succ (List.mem_range.1 hk)
    show x.1 < treesTold told (borderOf ps ps[k]?)
    rw [borderOf_getElem ps hn k hk']
    exact h k hk' x hx

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.sampledIn_withTold
#print axioms VerifiableInference.Desc.First.fenceFit_withTold
