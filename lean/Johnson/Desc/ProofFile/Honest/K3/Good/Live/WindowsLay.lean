-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/WindowsLay.lean: the kind "lookup" (K3): shape and first
slot of the lookup on the digits at a layers' link, in the numbers of the link's plan. A theorem.

Terms. Honest/K3/GLOSSARY.md ("slot", "face"). In this file: W is the verifier's public structure,
hp the plan of the layers' link i (`Layer.HPlan2`), p the public parameters of the lookup's place
(`placeAt`, Johnson/Desc/First/Look/LookKind.lean).

What is shown.
  `digits_lay`: at a layers' link: the plan is there; the shape is hp.tl.f9; the first slot and
    `Forest.elems hp.tl.f9` add up to hp.ns: the lookup's stretch is the last slots below hp.ns.
The like for the lookup on the calls is the library's `place_lay`
(Johnson/Desc/First/Look/K3PlaceLetters.lean) as it stands: the shape is W.y.fo and the first slot
0.

Hypotheses that remain. W is what `Verify.publicOf` returns (`hX`); i is not the head's link and is
a layers' link (`hn`, `h0`, in the form of `place_lay`); the place's parameters are there (`e`):
that holds `Forest.elems hp.tl.f9 ≤ hp.ns` within it: else `placeAt` returns nothing.

How the proof goes. The text of `lookAt` (Johnson/Desc/First/Look/LookAt.lean) is taken apart, by
the steps by which the proof of the library's `lookAt_dig`
(Johnson/Road/K4/Riders/LookInByMake.lean) opens it too; the shape by the library's
`digits_shape_at` and `shapeZAll_of_public` (Johnson/Desc/First/Look/DigitsShapeAt.lean).

Related. `lookAt_dig` states the other direction of the clause on the first slot: from the plan at
the link and `Forest.elems hp.tl.f9 ≤ hp.ns`: the place is there, and its ledger's next slot is
hp.ns - 0 - `Forest.elems hp.tl.f9`.

Limits. Numbers alone. hp.ns is not told here as a sum of the link's stretches. The library tells
it: `planG_slots` (LookInByMake.lean): what `Layer.planG` returns has hp.ns = `slotsOf` at the
group, with `Forest.elems hp.tl.f9` as its last argument; `slotsOf` (OnBytes/Model/LayerPlan.lean)
is the sum of the group's numbers of slots in the order of the messages, the smallness test's last.
It is not joined with `digits_lay` here. No instance of the hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.Desc.First.Look.K3PlaceAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (P placeAt placeAt_iff lookAt tlAt digitsNext
  digits_shape_at shapeZAll_of_public)

/-- **The lookup on the digits of a layers' link**: its shape and its first slot, in the plan's
numbers. Conditional on the hypotheses that the head of this file lists. No instance of these
hypotheses is exhibited in this file. -/
theorem digits_lay {pol KL : ByteArray} {layout : Option ByteArray} {W : Verify.Public} {i : ℕ}
    {p : P} (hX : Verify.publicOf pol KL layout = .ok W) (e : placeAt W i true = some p)
    (hn : i ≠ (if W.p4 then 2 else 1) * W.NGr) (h0 : i % (if W.p4 then 2 else 1) = 0) :
    ∃ hp, W.G[i / (if W.p4 then 2 else 1)]? = some hp ∧ p.shape = some hp.tl.f9 ∧
      p.first + Forest.elems hp.tl.f9 = hp.ns := by
  obtain ⟨x, hx, rfl⟩ := placeAt_iff.1 e
  have hx0 := hx
  unfold lookAt at hx
  dsimp only at hx
  rw [if_neg (by simpa using hn), if_pos (by simpa using h0)] at hx
  obtain ⟨hp, hg, hx⟩ := Option.bind_eq_some_iff.1 hx
  simp only [if_true] at hx
  obtain ⟨nx, hnx, rfl⟩ := Option.map_eq_some_iff.1 hx
  have ht : tlAt W i = some hp.tl := by
    unfold tlAt
    dsimp only
    rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hg]
    rfl
  refine ⟨hp, hg, digits_shape_at (shapeZAll_of_public hX) hx0 ht _, ?_⟩
  unfold digitsNext at hnx
  split at hnx
  · obtain rfl := Option.some.inj hnx
    show hp.ns - 0 - Forest.elems hp.tl.f9 + Forest.elems hp.tl.f9 = hp.ns
    omega
  · exact nomatch hnx

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.digits_lay
