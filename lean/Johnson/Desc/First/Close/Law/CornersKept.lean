-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CornersKept.lean: THE TEST ON WHERE THE ROWS STAND SAYS YES, BY THE
KERNEL, AT THE PROGRAM's OWN LAYOUT OF EVERY WRITTEN LIST, WHICHEVER MEMBERS ARE KEPT, AT BOTH
SIZES. Statements and proofs. NO TEXT OF THE DESCRIPTION STANDS BENEATH THIS FILE.

Corners.lean (beside this file) evaluates its test `Corners` at the program's own layout with
nothing kept: which members a plan's group keeps is not in the written lists. Here the flags are a
letter.
  `linksFull_corners_all`, `linksSmall_corners_all`: at each of the 26 and the 6 written lists and
    at EVERY choice kb of kept members, the test says yes at the layout that `layBlocks` gives for
    these flags, at the number of row variables that the program's formula gives for them (`kLay lo
    kb`). By evaluation in the kernel over all choices, a list at a time (`CornersAll`; the lists
    without repeats are five at each size).
  `groupFullLayK`, `groupFullLayK_good`, `k10_condition_full_layK`, and the like at the small size:
    `BatFoldOKAt` at the caller of the group at that layout with these members kept, the
    coefficients the powers of one element along any numbering, from ONE premise: the group in front
    has the formula's number of row variables for these flags.
  `corners_no_masks`, `corners_no_overlap`, `corners_no_room`: THE TEST CAN SAY NO: three made-up
    controls: two members with a mask row each; two blocks of main rows that overlap; main rows
    beyond the cube (which pass once the member is kept).
Limits. HOW LITTLE THE EVALUATIONS TEST: `Corners`' third and
fourth clause name neither the flags nor the main rows; and at `layBlocks`' own first rows and the
formula's own number the first two clauses are not seen to fail (a run: 200,000 made-up lists
and flags: yes just if the members' mask blocks take at most one row): so the many evaluations hold
about one bit a list: that at most one member bears a mask row, and that one a single row. That is
what the group's data's being in order needs here; it is no test of a layout that somebody else has
made. Two letters speak of keeping and nothing ties them: kb (the group's kept members) and keep
(the caller's kept messages). Those of Corners.lean but the one on kept members. For which flags a
group in front has the formula's number is not said. Nothing on soundness of the protocol.

-/
import Johnson.Desc.First.Close.Law.Kept.Full0
import Johnson.Desc.First.Close.Law.Kept.Full1a
import Johnson.Desc.First.Close.Law.Kept.Full1b
import Johnson.Desc.First.Close.Law.Kept.Full2
import Johnson.Desc.First.Close.Law.Kept.Full34
import Johnson.Desc.First.Close.Law.Kept.Small0
import Johnson.Desc.First.Close.Law.Kept.Small1a
import Johnson.Desc.First.Close.Law.Kept.Small1b
import Johnson.Desc.First.Close.Law.Kept.Small2
import Johnson.Desc.First.Close.Law.Kept.Small34

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb Iop IOR
open VerifiableInference.OnPublicFiles

/-! The written lists without repeats are five at each size: the evaluations stand in the files of
the folder Kept/, so that none is heavy. -/

theorem cornersFull_1 : CornersAll (linksFullLit.dedup.getD 1 []) :=
  cornersAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact cornersFull_1_0
    · exact cornersFull_1_1
    · exact cornersFull_1_2
    · exact cornersFull_1_3

theorem cornersFull_len : linksFullLit.dedup.length = 5 := by
  decide +kernel

theorem cornersFull_each (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) :
    CornersAll lo := by
  refine each_of_getD CornersAll _ [] 5 cornersFull_len (fun i hi => ?_) lo (List.mem_dedup.2 hlo)
  interval_cases i
  · exact cornersFull_0
  · exact cornersFull_1
  · exact cornersFull_2
  · exact cornersFull_3
  · exact cornersFull_4

theorem cornersSmall_1 : CornersAll (linksSmallLit.dedup.getD 1 []) :=
  cornersAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact cornersSmall_1_0
    · exact cornersSmall_1_1
    · exact cornersSmall_1_2
    · exact cornersSmall_1_3

theorem cornersSmall_len : linksSmallLit.dedup.length = 5 := by
  decide +kernel

theorem cornersSmall_each (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) :
    CornersAll lo := by
  refine each_of_getD CornersAll _ [] 5 cornersSmall_len (fun i hi => ?_) lo (List.mem_dedup.2 hlo)
  interval_cases i
  · exact cornersSmall_0
  · exact cornersSmall_1
  · exact cornersSmall_2
  · exact cornersSmall_3
  · exact cornersSmall_4

theorem linksFull_corners_all : ∀ lo ∈ linksFullLit, ∀ kb : Fin lo.length → Bool,
    Corners lo (kLay lo kb) (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) kb :=
  cornersFull_each

theorem linksSmall_corners_all : ∀ lo ∈ linksSmallLit, ∀ kb : Fin lo.length → Bool,
    Corners lo (kLay lo kb) (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) kb :=
  cornersSmall_each

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)

/-- The group at the program's own layout, the members with the flag kept. -/
noncomputable abbrev groupFullLayK : RowsK (sigOf codesFull2 lo) :=
  groupFull lo hlo gs hgs (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
    fun a => kb a.1 = true

theorem groupFullLayK_good (hk : gs.k = kLay lo kb) : (groupFullLayK lo hlo gs hgs kb).Good :=
  full_good_of_corners lo hlo gs hgs _ _ _ (hk ▸ linksFull_corners_all lo hlo kb)

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupFullLayK lo hlo gs hgs kb).G.C.J) (n : ℕ)
  (num : (groupFullLayK lo hlo gs hgs kb).G.Row B ≃ Fin n)
  (fx : Fin (((groupFullLayK lo hlo gs hgs kb).Sh.fold Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupFullLayK lo hlo gs hgs kb).sizeB keep Sb
      sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFullLayK lo hlo gs hgs kb).G ((groupFullLayK lo hlo gs hgs kb).sizeB keep Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp)

/-- **THE PROVED BLOCK's CONDITION AT THE PROGRAM's OWN LAYOUT, WHICHEVER MEMBERS ARE KEPT.** -/
theorem k10_condition_full_layK (hk : gs.k = kLay lo kb) :
    BatFoldOKAt ((groupFullLayK lo hlo gs hgs kb).foldCaller keep Sb sl
      (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) :=
  k10_condition_full lo hlo gs hgs _ _ _ keep Sb sl _ fx A₀ w₀ w₁
    (Cb.Pv.Bat.powersZ_ok n num num.injective) (groupFullLayK_good lo hlo gs hgs kb hk)

end

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (kb : Fin lo.length → Bool)

/-- The group at the program's own layout, the members with the flag kept. -/
noncomputable abbrev groupSmallLayK : RowsK (sigOf codesSmall2 lo) :=
  groupSmall lo hlo gs hgs (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
    fun a => kb a.1 = true

theorem groupSmallLayK_good (hk : gs.k = kLay lo kb) : (groupSmallLayK lo hlo gs hgs kb).Good :=
  small_good_of_corners lo hlo gs hgs _ _ _ (hk ▸ linksSmall_corners_all lo hlo kb)

variable (keep : (sigOf codesSmall2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupSmallLayK lo hlo gs hgs kb).G.C.J) (n : ℕ)
  (num : (groupSmallLayK lo hlo gs hgs kb).G.Row B ≃ Fin n)
  (fx : Fin (((groupSmallLayK lo hlo gs hgs kb).Sh.fold Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub ((groupSmallLayK lo hlo gs hgs kb).sizeB keep Sb
      sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesSmall2 lo).Wit × Wp)
  (w₁ : LdBrW (groupSmallLayK lo hlo gs hgs kb).G ((groupSmallLayK lo hlo gs hgs kb).sizeB keep Sb
      sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp)

/-- **THE PROVED BLOCK's CONDITION AT THE PROGRAM's OWN LAYOUT, WHICHEVER MEMBERS ARE KEPT.** -/
theorem k10_condition_small_layK (hk : gs.k = kLay lo kb) :
    BatFoldOKAt ((groupSmallLayK lo hlo gs hgs kb).foldCaller keep Sb sl
      (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁) :=
  k10_condition_small lo hlo gs hgs _ _ _ keep Sb sl _ fx A₀ w₀ w₁
    (Cb.Pv.Bat.powersZ_ok n num num.injective) (groupSmallLayK_good lo hlo gs hgs kb hk)

end

/-! ## The test can say no: three controls -/

/-- Two members with a mask row each: the mask rows do not fit one corner apart. -/
theorem corners_no_masks : ¬ Corners
    [({ mainRows := 1, maskRows := 1 }, 0), ({ mainRows := 1, maskRows := 1 }, 0)] 1
    (fun i => i.val) (fun _ => 0) (fun _ => false) := by
  decide

/-- Two members' blocks of main rows overlap. -/
theorem corners_no_overlap : ¬ Corners [({ mainRows := 2 }, 0), ({ mainRows := 2 }, 0)] 2
    (fun i => i.val) (fun _ => 0) (fun _ => false) := by
  decide

/-- A member's main rows reach beyond the cube; kept, they do not count. -/
theorem corners_no_room : ¬ Corners [({ mainRows := 3 }, 0)] 1 (fun _ => 0) (fun _ => 0)
      (fun _ => false) ∧
    Corners [({ mainRows := 3 }, 0)] 1 (fun _ => 0) (fun _ => 0) (fun _ => true) := by
  decide

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.corners_no_masks
#print axioms VerifiableInference.Desc.First.Close.corners_no_overlap
#print axioms VerifiableInference.Desc.First.Close.corners_no_room
#print axioms VerifiableInference.Desc.First.Close.linksFull_corners_all
#print axioms VerifiableInference.Desc.First.Close.linksSmall_corners_all
#print axioms VerifiableInference.Desc.First.Close.k10_condition_full_layK
#print axioms VerifiableInference.Desc.First.Close.k10_condition_small_layK
