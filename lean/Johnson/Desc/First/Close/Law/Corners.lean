-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Corners.lean: THE PROVED BLOCK's CONDITION FOR THE CLOSING OF A LINK
(KIND K10) AT EVERY LAYOUT THAT PASSES ONE TEST; AND THE TEST SAYS YES, BY THE KERNEL, AT THE
PROGRAM's OWN LAYOUT OF EVERY WRITTEN LIST, AT BOTH SIZES. Definitions, statements and proofs. NO
TEXT OF THE DESCRIPTION STANDS BENEATH THIS FILE.

`k10_condition_full` and `k10_condition_small` (GroupFull.lean, GroupSmall.lean, beside this file)
leave one premise on numbers: the group's data are in order.
  `Corners lo k oM oZ kb`: a decidable test on where the rows stand: the main rows of a member that
    is not kept fit the cube of k row variables; no two such members' blocks overlap; the mask rows
    fit one corner; no two members' blocks of mask rows overlap.
  `apart_inj_on`, `full_good_of_corners`, `small_good_of_corners`: where the test says yes the
    group's data are in order: at every list, group in front, oM, oZ and flags kb of kept members.
  `layAt`, `sizesM`, `sizesZ`, `kLay`: the program's own layout, off `layBlocks`
    (OnBytes/Iop/Ground.lean:1108: blocks of 2^bits rows from row 0 by decreasing size; a kept
    member takes none) with the bits as `Statement.rowBits` counts them (:405: `ceilLog2` of the
    rows), and the number of row variables by the formula of `Statement.layout` (:1118 ff.).
  `linksFull_corners`, `linksSmall_corners`: THE TEST SAYS YES at each of the 26 and the 6 written
    lists, at that layout with nothing kept. `linksFull_k`, `linksSmall_k`: the formula's numbers
    there: 8, 7 in turn, then 8, 1; and 9, 7, 9, 7, 8, 1. `linksFull_has_group`,
    `linksSmall_has_group`: every list but the last has a group in front with that number.
  `groupFullLay`, `groupFullLay_good`, `k10_condition_full_lay`, and the like at the small size:
    `BatFoldOKAt` at the caller of the group at the program's own layout, the coefficients the
    powers of one element along any numbering, from ONE premise: the group in front has the
    formula's number of row variables.
Limits. NOTHING IS KEPT in the layouts at which the test is evaluated: which members a plan's group
keeps is not in the written lists; at other flags the test is a premise. `sizesM`, `sizesZ` and
`kLay` are typed after `Statement.layout`, not drawn from it: no statement is built here, and no
lemma says that a statement with these shapes has this layout. `layBlocks` is the program's; that
the description's own layout (Johnson/Desc/Own/Layout.lean) agrees with it is other files' to show.
The last written list (2 main rows; the formula gives 1) has no group in front: it is not treated.
That the written lists and groups are those of a file's plan is not shown. No block's decision calls
this test. L15, through GroupFull.lean. Nothing on soundness of the protocol.

-/
import Johnson.Desc.First.Close.Law.GroupSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb Iop IOR
open VerifiableInference.OnPublicFiles

/-- **THE TEST ON WHERE THE ROWS STAND**: of a list of messages' shapes, a number k of row
variables, the first rows oM and oZ of the members' blocks, and the flags kb of the kept members.
A member is a message with a main row. The main rows of a member that is not kept fit the cube; no
two such members' blocks overlap; the mask rows fit one corner; no two members' blocks of mask
rows overlap. -/
def Corners (lo : List (OracleShape × ℕ)) (k : ℕ) (oM oZ : Fin lo.length → ℕ)
    (kb : Fin lo.length → Bool) : Prop :=
  (∀ i, (lo.get i).1.mainRows ≠ 0 → kb i = false → oM i + (lo.get i).1.mainRows ≤ 2 ^ k) ∧
  (∀ i j, (lo.get i).1.mainRows ≠ 0 → (lo.get j).1.mainRows ≠ 0 → kb i = false → kb j = false →
    i ≠ j → oM i + (lo.get i).1.mainRows ≤ oM j ∨ oM j + (lo.get j).1.mainRows ≤ oM i) ∧
  (∀ i, (lo.get i).1.mainRows ≠ 0 → oZ i + (lo.get i).1.maskRows ≤ 1) ∧
  (∀ i j, (lo.get i).1.mainRows ≠ 0 → (lo.get j).1.mainRows ≠ 0 → i ≠ j →
    oZ i + (lo.get i).1.maskRows ≤ oZ j ∨ oZ j + (lo.get j).1.maskRows ≤ oZ i)

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
instance (lo : List (OracleShape × ℕ)) (k : ℕ) (oM oZ : Fin lo.length → ℕ)
    (kb : Fin lo.length → Bool) : Decidable (Corners lo k oM oZ kb) := by
  unfold Corners
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_))
  · exact Nat.decidableForallFin _
  · exact @Nat.decidableForallFin _ _ fun i => Nat.decidableForallFin _
  · exact Nat.decidableForallFin _
  · exact @Nat.decidableForallFin _ _ fun i => Nat.decidableForallFin _

/-- Rows have different corners if the blocks of the members that count do not overlap. -/
theorem apart_inj_on {A : Type} (n o : A → ℕ) (ok : A → Prop)
    (h : ∀ a b, ok a → ok b → a ≠ b → o a + n a ≤ o b ∨ o b + n b ≤ o a)
    (r r' : Σ a, Fin (n a)) (h1 : ok r.1) (h2 : ok r'.1)
    (k : o r.1 + r.2.val = o r'.1 + r'.2.val) : r = r' := by
  obtain ⟨a, i⟩ := r
  obtain ⟨b, j⟩ := r'
  have k' : o a + i.val = o b + j.val := k
  by_cases e : a = b
  · subst e
    have : i = j := Fin.ext (by omega)
    rw [this]
  · have hi := i.isLt
    have hj := j.isLt
    rcases h a b h1 h2 e with g | g <;> omega

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ) (kb : Fin lo.length → Bool)

/-- **hg AT EVERY LAYOUT THAT PASSES THE TEST**, at the full size. -/
theorem full_good_of_corners (h : Corners lo gs.k oM oZ kb) :
    (groupFull lo hlo gs hgs oM oZ fun a => kb a.1 = true).Good := by
  obtain ⟨c1, c2, c3, c4⟩ := h
  have e : (stageOf gs 219).h + (stageOf gs 219).g = gs.k := by
    rw [← (frontFull_place gs hgs).2]
    show 0 + gs.k = gs.k
    omega
  have e0 : (stageOf gs 219).h = 0 := by
    rw [← (frontFull_place gs hgs).2]
    rfl
  refine full_good lo hlo gs hgs _ _ _ (fun r hr => ?_) (fun r r' hr hr' k => ?_) (fun r => ?_)
    fun r r' k => ?_
  · rw [e]
    have h1 := c1 r.1.1 r.1.2 (by simpa using hr)
    have h2 : r.2.val < (lo.get r.1.1).1.mainRows := r.2.isLt
    show oM r.1.1 + r.2.val < 2 ^ gs.k
    omega
  · exact apart_inj_on (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.mainRows)
      (fun a => oM a.1) (fun a => kb a.1 = false)
      (fun a b ha hb hab => c2 a.1 b.1 a.2 b.2 ha hb fun q => hab (Subtype.ext q)) r r'
      (by simpa using hr) (by simpa using hr') k
  · rw [e0]
    have h1 := c3 r.1.1 r.1.2
    have h2 : r.2.val < (lo.get r.1.1).1.maskRows := r.2.isLt
    show oZ r.1.1 + r.2.val < 2 ^ 0
    omega
  · exact apart_inj_on (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.maskRows)
      (fun a => oZ a.1) (fun _ => True)
      (fun a b _ _ hab => c4 a.1 b.1 a.2 b.2 fun q => hab (Subtype.ext q)) r r' trivial trivial k

end

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (oM oZ : Fin lo.length → ℕ) (kb : Fin lo.length → Bool)

/-- **hg AT EVERY LAYOUT THAT PASSES THE TEST**, at the small size. -/
theorem small_good_of_corners (h : Corners lo gs.k oM oZ kb) :
    (groupSmall lo hlo gs hgs oM oZ fun a => kb a.1 = true).Good := by
  obtain ⟨c1, c2, c3, c4⟩ := h
  have e : (stageOf gs 218).h + (stageOf gs 218).g = gs.k := by
    rw [← (frontSmall_place gs hgs).2]
    show 0 + gs.k = gs.k
    omega
  have e0 : (stageOf gs 218).h = 0 := by
    rw [← (frontSmall_place gs hgs).2]
    rfl
  refine small_good lo hlo gs hgs _ _ _ (fun r hr => ?_) (fun r r' hr hr' k => ?_) (fun r => ?_)
    fun r r' k => ?_
  · rw [e]
    have h1 := c1 r.1.1 r.1.2 (by simpa using hr)
    have h2 : r.2.val < (lo.get r.1.1).1.mainRows := r.2.isLt
    show oM r.1.1 + r.2.val < 2 ^ gs.k
    omega
  · exact apart_inj_on (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.mainRows)
      (fun a => oM a.1) (fun a => kb a.1 = false)
      (fun a b ha hb hab => c2 a.1 b.1 a.2 b.2 ha hb fun q => hab (Subtype.ext q)) r r'
      (by simpa using hr) (by simpa using hr') k
  · rw [e0]
    have h1 := c3 r.1.1 r.1.2
    have h2 : r.2.val < (lo.get r.1.1).1.maskRows := r.2.isLt
    show oZ r.1.1 + r.2.val < 2 ^ 0
    omega
  · exact apart_inj_on (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.maskRows)
      (fun a => oZ a.1) (fun _ => True)
      (fun a b _ _ hab => c4 a.1 b.1 a.2 b.2 fun q => hab (Subtype.ext q)) r r' trivial trivial k

end

/-! ## The program's own layout -/

/-- The first row of block i as the program's `layBlocks` places it; 0 where it places none. -/
def layAt (sizes : List (Option ℕ)) (i : ℕ) : ℕ :=
  (((layBlocks sizes.toArray).1.getD i none).getD 0)

/-- The sizes of the main blocks: of every member that is not kept, the bits of its rows. -/
def sizesM (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : List (Option ℕ) :=
  List.ofFn fun i : Fin lo.length =>
    if (lo.get i).1.mainRows ≠ 0 ∧ kb i = false then some (ceilLog2 (lo.get i).1.mainRows) else none

/-- The sizes of the mask blocks: of every member with a mask row. -/
def sizesZ (lo : List (OracleShape × ℕ)) : List (Option ℕ) :=
  List.ofFn fun i : Fin lo.length =>
    if (lo.get i).1.mainRows ≠ 0 ∧ (lo.get i).1.maskRows ≠ 0 then
      some (ceilLog2 (lo.get i).1.maskRows) else none

/-- The number of row variables by the program's own formula. -/
def kLay (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : ℕ :=
  max (max (ceilLog2 (layBlocks (sizesM lo kb).toArray).2)
    (ceilLog2 (layBlocks (sizesZ lo).toArray).2)) 1

set_option maxRecDepth 1000000 in
/-- **THE TEST SAYS YES AT EVERY WRITTEN LIST OF THE FULL SIZE**, at the program's own layout with
nothing kept. -/
theorem linksFull_corners : ∀ lo ∈ linksFullLit,
    Corners lo (kLay lo fun _ => false) (fun i => layAt (sizesM lo fun _ => false) i.val)
      (fun i => layAt (sizesZ lo) i.val) (fun _ => false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The like at the small size. -/
theorem linksSmall_corners : ∀ lo ∈ linksSmallLit,
    Corners lo (kLay lo fun _ => false) (fun i => layAt (sizesM lo fun _ => false) i.val)
      (fun i => layAt (sizesZ lo) i.val) (fun _ => false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The numbers of row variables that the program's formula gives at the written lists. -/
theorem linksFull_k : (linksFullLit.map fun lo => kLay lo fun _ => false) =
    [8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 1] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem linksSmall_k :
    (linksSmallLit.map fun lo => kLay lo fun _ => false) = [9, 7, 9, 7, 8, 1] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Every written list but the last has a group in front with the program's number of row
variables. (The last list's number is 1: no group in front has it.) -/
theorem linksFull_has_group : ∀ lo ∈ linksFullLit.dropLast,
    ∃ gs ∈ frontFull, gs.k = kLay lo fun _ => false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem linksSmall_has_group : ∀ lo ∈ linksSmallLit.dropLast,
    ∃ gs ∈ frontSmall, gs.k = kLay lo fun _ => false := by
  decide +kernel

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull)

/-- The group at the program's own layout, nothing kept. -/
noncomputable abbrev groupFullLay : RowsK (sigOf codesFull2 lo) :=
  groupFull lo hlo gs hgs (fun i => layAt (sizesM lo fun _ => false) i.val)
    (fun i => layAt (sizesZ lo) i.val) fun a => (fun _ : Fin lo.length => false) a.1 = true

theorem groupFullLay_good (hk : gs.k = kLay lo fun _ => false) :
    (groupFullLay lo hlo gs hgs).Good :=
  full_good_of_corners lo hlo gs hgs _ _ _ (hk ▸ linksFull_corners lo hlo)

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupFullLay lo hlo gs hgs).G.C.J) (n : ℕ)
  (num : (groupFullLay lo hlo gs hgs).G.Row B ≃ Fin n)
  (fx : Fin (((groupFullLay lo hlo gs hgs).Sh.fold Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupFullLay lo hlo gs hgs).sizeB keep Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFullLay lo hlo gs hgs).G ((groupFullLay lo hlo gs hgs).sizeB keep Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp)

/-- **THE PROVED BLOCK's CONDITION AT THE PROGRAM's OWN LAYOUT**: at a written list and the group in
front whose number of row variables is the one that the program's formula gives. -/
theorem k10_condition_full_lay (hk : gs.k = kLay lo fun _ => false) :
    BatFoldOKAt ((groupFullLay lo hlo gs hgs).foldCaller keep Sb sl
      (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) :=
  k10_condition_full lo hlo gs hgs _ _ _ keep Sb sl _ fx A₀ w₀ w₁
    (Cb.Pv.Bat.powersZ_ok n num num.injective) (groupFullLay_good lo hlo gs hgs hk)

end

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall)

/-- The group at the program's own layout, nothing kept. -/
noncomputable abbrev groupSmallLay : RowsK (sigOf codesSmall2 lo) :=
  groupSmall lo hlo gs hgs (fun i => layAt (sizesM lo fun _ => false) i.val)
    (fun i => layAt (sizesZ lo) i.val) fun a => (fun _ : Fin lo.length => false) a.1 = true

theorem groupSmallLay_good (hk : gs.k = kLay lo fun _ => false) :
    (groupSmallLay lo hlo gs hgs).Good :=
  small_good_of_corners lo hlo gs hgs _ _ _ (hk ▸ linksSmall_corners lo hlo)

variable (keep : (sigOf codesSmall2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupSmallLay lo hlo gs hgs).G.C.J) (n : ℕ)
  (num : (groupSmallLay lo hlo gs hgs).G.Row B ≃ Fin n)
  (fx : Fin (((groupSmallLay lo hlo gs hgs).Sh.fold Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub ((groupSmallLay lo hlo gs hgs).sizeB keep Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesSmall2 lo).Wit × Wp)
  (w₁ : LdBrW (groupSmallLay lo hlo gs hgs).G ((groupSmallLay lo hlo gs hgs).sizeB keep Sb sl
    (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp)

/-- **THE PROVED BLOCK's CONDITION AT THE PROGRAM's OWN LAYOUT**: at a written list and the group in
front whose number of row variables is the one that the program's formula gives. -/
theorem k10_condition_small_lay (hk : gs.k = kLay lo fun _ => false) :
    BatFoldOKAt ((groupSmallLay lo hlo gs hgs).foldCaller keep Sb sl
      (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁) :=
  k10_condition_small lo hlo gs hgs _ _ _ keep Sb sl _ fx A₀ w₀ w₁
    (Cb.Pv.Bat.powersZ_ok n num num.injective) (groupSmallLay_good lo hlo gs hgs hk)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.full_good_of_corners
#print axioms VerifiableInference.Desc.First.Close.linksFull_corners
#print axioms VerifiableInference.Desc.First.Close.linksSmall_corners
#print axioms VerifiableInference.Desc.First.Close.linksFull_k
#print axioms VerifiableInference.Desc.First.Close.linksFull_has_group
#print axioms VerifiableInference.Desc.First.Close.linksSmall_has_group
#print axioms VerifiableInference.Desc.First.Close.k10_condition_full_lay
#print axioms VerifiableInference.Desc.First.Close.k10_condition_small_lay
