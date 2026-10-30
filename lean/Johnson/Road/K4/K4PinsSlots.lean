-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsSlots.lean: THE PLAN's NUMBER OF SLOTS OF A FEED-FORWARD SEGMENT IS AT MOST
8192,
WHERE THE PUBLIC PARAMETERS' CODES AND SHAPE ARE THE WRITTEN ONES: not by the scope's numerals, but
by a test that the maker of the built segments makes itself: it refuses unless a segment's slots
and the answers' pads have room in the segments' mask row (`linkLaid`,
OnBytes/Model/StagesLinks.lean; `built_ns_le`,
Johnson/Road/K4/Rec/BuiltTests.lean, called). Four theorems: two by Lean's kernel.

  `maskEll_written`: BY THE KERNEL: the written code of the segments' mask rows has length 8192.
    NEGATIVE: `maskEll_written_no`: another code of the list, the index masks' message's, has 256.
  `slots_plain`: where the plain road returns Z, under `WrittenAt Z`, with attention's segments, at
    a group with its two plans: hp.ns ≤ 8192.
  **`slots_paid`**: in the goals' scope, at an opening, under `WrittenAt Z`: at each of the twelve
    groups. IT IS THE PREMISE slots OF `pins_paid` (Johnson/Road/K4/K4PinsPaid.lean).

Limits. K04_law IS NOT PROVED BY THIS. `WrittenAt Z` IS A PREMISE: a condition on the three public
files alone. That there is an opening is shown by no theorem here. The full size alone.

-/
import Johnson.Road.K4.Rec.BuiltTests
import Johnson.Road.K4.K4PlanTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)

/-- By the kernel: the written code of the segments' mask rows has length 8192. -/
theorem maskEll_written :
    (proofSizedFull.codes.mask[proofSizedFull.request.maskCode]?).map (·.ell) = some 8192 := by
  decide +kernel

/-- A negative test: another code of the list, the index masks' message's, has another length. -/
theorem maskEll_written_no : (proofSizedFull.codes.mask[12]?).map (·.ell) = some 256 := by
  decide +kernel

/-- **Where the plain road returns Z with the written codes and shape: a layers' plan's slots have
room.** -/
theorem slots_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (W : WrittenAt Z) (h4 : Z.p.X.p4 = true) {g : ℕ}
    {hp : OnBytes.Model.Layer.HPlan2} {a : OnBytes.Attention.Plan}
    (hG : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) : hp.ns ≤ 8192 := by
  obtain ⟨X, hX, e⟩ := Option.map_eq_some_iff.1 (Riders.built_ns_plain hZ h4 hG ha)
  obtain ⟨zk, hz, hle⟩ := Rec.built_ns_le hZ hX
  rw [W.codes, W.shape, shape_one] at hz
  have h8 := maskEll_written
  rw [hz] at h8
  have e8 : zk.ell = 8192 := Option.some.inj h8
  omega

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In the goals' scope, at an opening, under the written values: at each of the twelve
groups.** -/
theorem slots_paid (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (W : WrittenAt Z) :
    ∀ g, g < 12 → ∀ hp, Z.p.X.G[g]? = some hp → hp.ns ≤ 8192 := by
  intro g hg hp hG
  obtain ⟨k4, _, _, hA⟩ := _root_.Meaning.scope_plans hS hR O.public
  obtain ⟨a, ha, _⟩ := hA g hg
  rw [O.W] at k4 ha
  exact slots_plain O.pub W k4 hG ha

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.maskEll_written
#print axioms OnBytes.Road.K4.maskEll_written_no
#print axioms OnBytes.Road.K4.slots_plain
#print axioms OnBytes.Road.K4.slots_paid
