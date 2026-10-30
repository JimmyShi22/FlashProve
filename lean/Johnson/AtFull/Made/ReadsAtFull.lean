-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReadsAtFull.lean: where the planner returns and its sizes and shapes are the
written full-size values, the readers of a key's and of a proof's three chains return on the
planner's parameter bytes, at written-out values, under tests on the plans alone.

THE PREMISES ARE NOT SHOWN TOGETHER. Each law takes the planner's return, and equations that say
that parts of what it returns, or of what it was handed, are the written values. To show these is
other files' business.

The two main laws of Johnson/AtFull/Made/ReadsOfConfigure.lean ask tests with code on the values
that were spelled, and a bound on each item's length. Here these are paid by closed facts at the
written values: the key's sizes `keyFull` (Johnson/HB/LLHARD/KB9/ItemsFull.lean,
Johnson/AtFull/Made/LengthsAtFull.lean); the proof's sizes `proofSizedFull`, the layout
`layoutFull`, 13 pending rows and the binding tree's shape ⟨6, 40⟩ (ProofItemsAtFull.lean,
ReqAtFull.lean, LayoutAtFull.lean, LengthsAtFull.lean).

`key_read_full`, `proof_read_full`: the two laws. What stays of the premises: the planner's return;
the digest's 32 bytes; the equations; the tests on the plans; and that each of the links'
identifiers is below 2 ^ 64. `firstWritten_of`: the six equations of `FirstWritten`
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) hold of the first chain in `proofOf`.
`binding_of_two`: the binding tree's shape from its two numbers. `links_full`, `codesSize_full`,
`linSize_full`: three closed facts on numbers.

Limits. `proof_read_full` ends in `proofOf cfg l x made.sized ...`, which still holds the letters l,
x and made.sized; of its first chain six fields are written values, by `firstWritten_of`.
Nothing on soundness.
-/
import Johnson.AtFull.Made.ReadsOfConfigure
import Johnson.AtFull.Made.ProofItemsAtFull
import Johnson.AtFull.Made.ReqAtFull
import Johnson.AtFull.Made.LayoutAtFull
import Johnson.AtFull.Made.LengthsAtFull
import Johnson.HB.LLHARD.KB9.ItemsFull
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.KB9
open Johnson.G (layoutFull)
open VerifiableInference.PlanWritten (proofSizedFull FirstWritten)
open Lk6.AtPlan (keyFull)

/-- The binding tree's shape from its two numbers. -/
theorem binding_of_two {l : Lines} {z : Sized} (h1 : clog2 l.slots = 6)
    (h2 : z.set.saltBytes = 40) :
    (⟨clog2 l.slots, z.set.saltBytes⟩ : LinBindingShape) = ⟨6, 40⟩ := by
  rw [h1, h2]

/-- **A key's three chains at the written sizes.** -/
theorem key_read_full {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure l x cfg bits = .ok made) {P1 P2 P3 : Planned} (hk : made.key = [P1, P2, P3])
    (h32 : cfg.size = 32) (hz : made.sized.key = keyFull) (p1 : planB P1.plan = true)
    (p2 : planB P2.plan = true) (p3 : planB P3.plan = true)
    (w2 : sameWords P1.plan P2.plan = true) (w3 : sameWords P1.plan P3.plan = true)
    (n2 : noSample P2.plan = true) (n3 : noSample P3.plan = true) :
    KeyChains.read made.keyOneTime made.keyShared made.keySecond =
      some (keyOf cfg keyFull P1.plan P2.plan P3.plan) := by
  have hi : itemsB made.sized.key = true := by
    rw [hz]
    exact itemsB_full
  have hs : Short (Plan.oneTimeItems made.sized.key) := by
    rw [hz]
    exact short_key_full
  have k := key_read_of_configure hc hk h32 p1 p2 p3 hi hs w2 w3 n2 n3
  rw [hz] at k
  exact k

/-- The written layout has one entry for each link of the written shape of a request. -/
theorem links_full : layoutFull.link.length = proofSizedFull.request.link.length := by
  decide +kernel

theorem codesSize_full :
    16 + 24 * proofSizedFull.codes.base.size + 24 * proofSizedFull.codes.mask.size < 2 ^ 64 := by
  decide +kernel

theorem linSize_full :
    1024 + 32 * (proofSizedFull.batch.shape.testU.length +
      proofSizedFull.batch.shape.testOmega.length + proofSizedFull.batch.shape.testOwn.length +
      proofSizedFull.batch.shape.testOwnOmega.length) < 2 ^ 64 := by
  decide +kernel

/-- **A proof's three chains at the written sizes, layout and numbers.** -/
theorem proof_read_full {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure l x cfg bits = .ok made) {F S2 S3 : Planned}
    (hp : made.proof = [F, S2, S3]) (h32 : cfg.size = 32)
    (hz : made.sized.proof = proofSizedFull)
    (hb : (⟨clog2 l.slots, made.sized.set.saltBytes⟩ : LinBindingShape) = ⟨6, 40⟩)
    (hy : x.layout = layoutFull) (hn : x.sub.pendingRows = 13)
    (hI : wordsB x.identifiers = true) (p1 : planB F.plan = true) (p2 : planB S2.plan = true)
    (p3 : planB S3.plan = true) (w2 : sameWords F.plan S2.plan = true)
    (w3 : sameWords F.plan S3.plan = true) (n1 : noSample F.plan = true)
    (n2 : noSample S2.plan = true) (n3 : noSample S3.plan = true) :
    ProofChains.read made.first made.shared made.second =
      some (proofOf cfg l x made.sized F.plan S2.plan S3.plan) := by
  have hC : codesB made.sized.proof.codes = true := by
    rw [hz]
    exact codesB_proofFull
  have hL : linB made.sized.proof.batch.shape = true := by
    rw [hz]
    exact linB_proofFull
  have hR : reqB made.sized.proof.request = true := by
    rw [hz]
    exact reqB_proofFull
  have hY : layoutB x.layout = true := by
    rw [hy]
    exact layoutB_full
  have hN : wB x.sub.pendingRows = true := by
    rw [hn]
    exact wB_thirteen
  have hB : bindingB ⟨clog2 l.slots, made.sized.set.saltBytes⟩ = true := by
    rw [hb]
    exact bindingB_six_forty
  have hl : x.layout.link.length = made.sized.proof.request.link.length := by
    rw [hy, hz]
    exact links_full
  have hk := Johnson.G.MadeFree.configure_kept hc
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, not_or, ne_eq, not_not] at hk
  have h5 : 8 + 8 * x.identifiers.length < 2 ^ 64 := by
    have e : x.identifiers.length = layoutFull.link.length := by
      rw [hk.1.1.1, ← hl, hy]
    have c : layoutFull.link.length = 25 := by decide +kernel
    omega
  have hs : Short (madeFirstItems l x made.sized) := by
    refine short_first ?_ ?_ ?_ ?_ h5
    · rw [hz]
      exact codesSize_full
    · rw [hz]
      exact linSize_full
    · rw [hz, reqSize_full]
      omega
    · rw [hy, layoutSize_full]
      omega
  exact proof_read_of_configure hc hp h32 p1 p2 p3 hC hL hR hY hI hN hB hs hl w2 w3 n1 n2 n3

/-- The six equations on a proof's first chain as read back hold of the first chain in `proofOf`,
where the sizes, the layout and the two numbers are the written ones. -/
theorem firstWritten_of {cfg : ByteArray} {l : Lines} {x : Shapes} {z : Sized}
    {F S2 S3 : Fmt.Plan} (hz : z.proof = proofSizedFull)
    (hb : (⟨clog2 l.slots, z.set.saltBytes⟩ : LinBindingShape) = ⟨6, 40⟩)
    (hy : x.layout = layoutFull) (hn : x.sub.pendingRows = 13) :
    FirstWritten (proofOf cfg l x z F S2 S3).first := by
  refine ⟨?_, ?_, ?_, hn, hb, hy⟩
  · show z.proof.codes = proofSizedFull.codes
    rw [hz]
  · show z.proof.batch.shape = proofSizedFull.batch.shape
    rw [hz]
  · show z.proof.request = proofSizedFull.request
    rw [hz]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.binding_of_two
#print axioms Johnson.AtFull.Made.key_read_full
#print axioms Johnson.AtFull.Made.links_full
#print axioms Johnson.AtFull.Made.codesSize_full
#print axioms Johnson.AtFull.Made.linSize_full
#print axioms Johnson.AtFull.Made.proof_read_full
#print axioms Johnson.AtFull.Made.firstWritten_of
