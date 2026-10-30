-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SampleFitsOfShapes.lean: `SampleFits` (Close/Law/SampleTie.lean) OF KIND K1's SAMPLE ROW, AT A
GROUP THAT HOLDS A WRITTEN LIST's MEMBERS: ITS TWO DEBTS, JOINED. Theorems.

What is said.
  `keep_slot_kept`: where whole members are kept, a slot's row names that slot.
  `sampleFits_of_shapes`: `(groupLayK ..).Good`; T.groups[g]? = some G; T.layout g = some L; `GroupOk T G`;
    `ShapesAre T G lo kb no`; `AgreesWith lo kb L`; hinj; L.k = s.h + s.g; s.h = 0; at a member a: `K1.Tie` of its
    shape; a seed (z, β) that reads as ρ (`K1.ReadsOne`): THEN `SampleFits (namesOf ..) T L w (no a.1) a u` at
    w := kind K1's sample row of the message no a.1 at (z, β, 0, y) and u := the member's row's form at ρ, on a alone.
By: `sampleFits_of` · `blockAt_of_shapes` (Close/Law/BlockOfShapes.lean) · `middle_of` (MiddleAtK10.lean) ·
`backAt_of_shapes` (BackOfShapes.lean) · `namesOne_sampleRow` (SampleAtK10.lean) · `atMem_other`.

Limits. `ShapesAre`, hinj, `K1.Tie` and `K1.ReadsOne` are shown of no verifier's state here. That a state's sample row IS
this row is not here. No member is shown. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.BackOfShapes
import Johnson.Desc.First.Link.Law.SampleAtK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G
open Cb Cb.Pv KObj
open VerifiableInference.Desc.First.Close

/-- Where whole members are kept, a slot's row names that slot. -/
theorem keep_slot_kept {S : Sig GE} (R : Rows S) (kp : {o // R.mem o} → Prop) [DecidablePred kp]
    (q : (R.keep kp).Kp) : (R.keep kp).slot ((R.keep kp).kept q) = some q := by
  show (if h : kp q.1.1 then some (⟨⟨q.1.1, h⟩, q.2⟩ : Σ a : {a // kp a}, Fin (R.nM a.1))
    else none) = some q
  rw [dif_pos q.1.2]

variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {e : ℕ} {kb : Fin lo.length → Bool}
  {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C}
  {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z}
  {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {g : ℕ} {L : GroupLayout}

/-- **SampleFits OF KIND K1's SAMPLE ROW, FROM ShapesAre.** -/
theorem sampleFits_of_shapes (hg : (groupLayK cs lo s e kb hM hZ).Good)
    (hG : T.groups[g]? = some G) (hL : T.layout g = some L) (hOk : GroupOk T G)
    (H : ShapesAre T G lo kb no) (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : L.k = s.h + s.g) (hh : s.h = 0) (a : {i // memMain lo i})
    (hT : K1.Tie cs (lo.get a.1).1) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ cs (lo.get a.1).1) → GE) × GEˣ) (rd : K1.ReadsOne cs (lo.get a.1).1 z β ρ)
    (u : ((sigOf cs lo).om a.1).Z.S) :
    SampleFits (namesOf cs lo s e kb hM hZ no) T L
      (K1.sampleRow (K1.Msg.of cs (lo.get a.1).1) (no a.1) z β 0 y) (no a.1) a
      (Slf.atMem (Jf := fun a : (groupLayK cs lo s e kb hM hZ).G.A => ((sigOf cs lo).om a.1).C.J) a
        (((sigOf cs lo).om a.1).row u) ρ) :=
  sampleFits_of _ T L _ _ a _ (namesOne_sampleRow _ _ _ _ _ _)
    (fun _ hm => atMem_other
      (Jf := fun a : (groupLayK cs lo s e kb hM hZ).G.A => ((sigOf cs lo).om a.1).C.J) a
      (((sigOf cs lo).om a.1).row u) ρ hm) hg.view (fun q => keep_slot_kept _ _ q)
    (blockAt_of_shapes hG hL hOk H hA hinj hk a)
    (middle_of cs lo (memMain lo) s e _ _ hM hZ _ _ T L (no a.1) a hT z β y ρ rd u
      (backAt_of_shapes hG hL hOk H hA hinj hk hh a))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keep_slot_kept
#print axioms VerifiableInference.Desc.LinkJoin.sampleFits_of_shapes
