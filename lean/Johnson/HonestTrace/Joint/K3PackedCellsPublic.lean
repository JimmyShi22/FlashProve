-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/K3PackedCellsPublic.lean

«THE SCRIPT HOLDS THE PACKED TRACE CELLS», THE PUBLIC HALF, AT ANY OF THE 25 SEGMENTS: the four laws of
Johnson/Desc/ProofFile/Honest/K5/Law/PackedAtSeg.lean (mu_att, owner_numbers_att, shape_at_plan, cells_pack_label),
which stand at an attention segment, typed once for a segment σ of the full size, in the letters of Meaning.tlAt.
Nothing is claimed on soundness, completeness or hiding.

Limits. In the goals' scope alone; at "Sz.ref" and 12 groups. "shape_at_tail" and "cells_pack_at"
stand off the planes' matrices; "cells_pack_at" takes as a premise that the reader answers the same
under the owner's number and label.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedAtSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.PackedCells
open OnBytes.HonestTrace (Sz Seg MatName planeOf pack3 pack3_eq_pack arrayLabel nameNo_eq_some_iff
  matAt_eq_some_iff no?_lt shapeNo_in_scope planMats planMats_eq parts_in_scope shape_owner
  below_of_mu ref_ok)
open ProofFile.Honest (Readers asE)
open ProofFile.Honest.K1 (labelNo cellsVals)
open ProofFile.Honest.K5 (cellsVals_pack labelNo_arrayLabel owner_numbers_att)
open VerifiableInference.Desc.First.Look (szOf)

/-- The number of a name in a segment's list, in the sizes' two spellings. -/
theorem number_of_name {σ : Seg} (hσ : σ.Below 12) {i : ℕ} {μ : MatName}
    (hi : Sz.ref.nameNo σ i = some μ) : Sz.ref.mu σ μ = some i := by
  unfold Sz.mu
  rw [if_pos (show Seg.Below Sz.ref.nGr σ from hσ)]
  exact (nameNo_eq_some_iff Sz.ref _ _ _).1 hi

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- The label's two numbers are those of Sz.ref's owner, at a group's feed-forward segment. -/
theorem owner_numbers_layers (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {i : ℕ}
    {μ : MatName} (hi : Sz.ref.nameNo (.ff g) i = some μ) :
    Meaning.ownerK (Meaning.labAt X (2 * g) i) = (Sz.ref.owner (.ff g) μ).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner (.ff g) μ).1 (Sz.ref.owner (.ff g) μ).2 =
        some (Meaning.ownerA (Meaning.labAt X (2 * g) i)) := by
  have C := OnBytes.Road.Hd.core_of_scope hZ hR hX
  have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hi
  have hlt : i < 9 := no?_lt Sz.ref hno
  have hl := Meaning.owner_label hX C (k := 2 * g) (a := i) (by omega)
    (by rw [Meaning.size_even hX C hg]; exact hlt)
  obtain ⟨-, i7, i8⟩ := Meaning.ix_of_core hX C
  unfold Meaning.ownerOf at hl
  rw [if_neg (by omega), if_neg (by omega), i8, i7] at hl
  by_cases e : i = 8 ∧ 0 < 2 * g
  · rw [if_pos e] at hl
    obtain ⟨k1, k2⟩ := Prod.mk.inj hl
    have hq : μ = .xbI := MatName.no?_inj hno (by rw [e.1]; rfl)
    subst hq
    have hg0 : g ≠ 0 := by omega
    have ho : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg hg0
    rw [ho, k1, k2]
    refine ⟨?_, ?_⟩
    · show 2 * g - 2 = 2 * (g - 1)
      omega
    · show Sz.ref.mu (.ff (g - 1)) .xbO = some 7
      unfold Sz.mu
      rw [if_pos (show Seg.Below Sz.ref.nGr (.ff (g - 1)) from (show g - 1 < 12 by omega))]
      rfl
  · rw [if_neg e] at hl
    obtain ⟨k1, k2⟩ := Prod.mk.inj hl
    have ho : Sz.ref.owner (.ff g) μ = (.ff g, μ) := by
      cases μ with
      | xbI =>
        have e8 : i = 8 := (Option.some.inj hno).symm
        have g0 : g = 0 := by
          by_contra h0
          exact e ⟨e8, by omega⟩
        exact if_pos g0
      | _ => rfl
    rw [ho, k1, k2]
    exact ⟨rfl, number_of_name (σ := .ff g) hg hi⟩

/-- The same at the output head. -/
theorem owner_numbers_head (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {i : ℕ}
    {μ : MatName} (hi : Sz.ref.nameNo .head i = some μ) :
    Meaning.ownerK (Meaning.labAt X 24 i) = (Sz.ref.owner .head μ).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner .head μ).1 (Sz.ref.owner .head μ).2 =
        some (Meaning.ownerA (Meaning.labAt X 24 i)) := by
  have C := OnBytes.Road.Hd.core_of_scope hZ hR hX
  have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hi
  have hlt : i < 8 := no?_lt Sz.ref hno
  have hl := Meaning.owner_label hX C (k := 24) (a := i) (by omega)
    (by rw [Meaning.size_head hX C]; exact hlt)
  obtain ⟨-, i7, -⟩ := Meaning.ix_of_core hX C
  have n4 := (parts_in_scope hZ hR hX).2.2.2
  unfold Meaning.ownerOf at hl
  rw [if_pos rfl, n4, i7] at hl
  by_cases e : i = 4 + 3
  · rw [if_pos e] at hl
    obtain ⟨k1, k2⟩ := Prod.mk.inj hl
    have hq : μ = .xbL := MatName.no?_inj hno (by rw [e]; rfl)
    subst hq
    rw [k1, k2]
    refine ⟨rfl, ?_⟩
    show Sz.ref.mu (.ff 11) .xbO = some 7
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr (.ff 11) from (show 11 < 12 by omega))]
    rfl
  · rw [if_neg e] at hl
    obtain ⟨k1, k2⟩ := Prod.mk.inj hl
    have ho : Sz.ref.owner .head μ = (.head, μ) := by
      cases μ with
      | xbL => exact absurd (Option.some.inj hno).symm e
      | _ => rfl
    rw [ho, k1, k2]
    exact ⟨rfl, number_of_name (σ := .head) trivial hi⟩

/-- **The label's two numbers are those of Sz.ref's owner, at any of the 25 segments.** -/
theorem owner_numbers (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {σ : Seg} (hσ : σ.Below 12) {i : ℕ}
    {μ : MatName} (hi : Sz.ref.nameNo σ i = some μ) :
    Meaning.ownerK (Meaning.labAt X (σ.no 12) i) = (Sz.ref.owner σ μ).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 =
        some (Meaning.ownerA (Meaning.labAt X (σ.no 12) i)) := by
  cases σ with
  | ff g => exact owner_numbers_layers hZ hR hX hσ hi
  | att g => exact owner_numbers_att hZ hR hX hσ hi
  | head => exact owner_numbers_head hZ hR hX hi

/-- **The plan's record has Sz.ref's rows and columns**, at a matrix that is not the planes'. -/
theorem shape_at_tail (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {σ : Seg} (hσ : σ.Below 12) {i : ℕ}
    {μ : MatName} (hi : Sz.ref.nameNo σ i = some μ) (hp : μ ≠ planeOf σ) :
    ((Meaning.tlAt X (σ.no 12)).mats.getD i {}).m = (Sz.ref.shape σ μ).1 ∧
      ((Meaning.tlAt X (σ.no 12)).mats.getD i {}).k = (Sz.ref.shape σ μ).2 := by
  have hM : Sz.ref.matAt (σ.no 12) i = some (σ, μ) :=
    (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hσ, rfl, number_of_name hσ hi⟩
  obtain ⟨-, -, hm, hk⟩ := shapeNo_in_scope hZ hR hX hM hp
  have eT : planMats X (σ.no 12) = (Meaning.tlAt X (σ.no 12)).mats := planMats_eq X _
  have eS : Sz.ref.shapeNo (σ.no 12) i = Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [hM]
  rw [eT, eS] at hm hk
  exact ⟨hm, hk⟩

/-- The owner's number in its own list is below 26. -/
theorem owner_number_small {σ : Seg} {μ : MatName} {a : ℕ} (h : Sz.ref.mu σ μ = some a) :
    a < 26 := by
  have h9 : ∀ τ : Seg, Sz.ref.len τ ≤ 9 := fun τ => by
    cases τ with
    | ff _ => exact (by decide : 3 + 1 + 5 ≤ 9)
    | att _ => exact (by decide : 1 + 4 ≤ 9)
    | head => exact (by decide : 4 + 4 ≤ 9)
  unfold Sz.mu at h
  split_ifs at h
  exact Nat.lt_of_lt_of_le (no?_lt Sz.ref h) (Nat.le_trans (h9 _) (by decide))

/-- **THE LAW, AT ANY OF THE 25 SEGMENTS, IN THE LETTERS OF THE PLAN's LABEL**: what the frame's values lay for the
array of matrix number i of the segment's list is the packing of the reader's cells of that column, read under the
segment's own number and the matrix's label. hC: THE READER ANSWERS THE SAME under the owner's number and label. -/
theorem cells_pack_at (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {σ : Seg} (hσ : σ.Below 12) {i : ℕ}
    {μ : MatName} (hi : Sz.ref.nameNo σ i = some μ) (hp : μ ≠ planeOf σ) (R : Readers)
    (hd : List Fmt.Drawn) {c : ℕ} (hc : c < ((Meaning.tlAt X (σ.no 12)).mats.getD i {}).k)
    (hC : ∀ r, R.cells.cell ((Sz.ref.owner σ μ).1.no 12) (Sz.ref.owner σ μ).2.label r c =
      R.cells.cell (σ.no 12) μ.label r c) (i' : ℕ) :
    asE (some ((cellsVals Sz.ref).val R hd (Meaning.ownerK (Meaning.labAt X (σ.no 12) i))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X (σ.no 12) i))) i' c)) =
      Alg.pack (((szOf (Meaning.tlAt X (σ.no 12))).rad : ℕ) : ℤ)
        (fun r : Fin ((Meaning.tlAt X (σ.no 12)).mats.getD i {}).m =>
          algebraMap Cb.Gl.F Cb.Gl.E (R.cells.cell (σ.no 12) μ.label r.val c)) i' := by
  obtain ⟨k1, k2⟩ := owner_numbers hZ hR hX hσ hi
  obtain ⟨hm, hk⟩ := shape_at_tail hZ hR hX hσ hi hp
  have hmu := number_of_name hσ hi
  have eO : Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = Sz.ref.shape σ μ :=
    shape_owner Sz.ref ref_ok.1 σ μ (by rw [hmu]; rfl)
  have hM₀ : Sz.ref.matAt ((Sz.ref.owner σ μ).1.no 12)
      (Meaning.ownerA (Meaning.labAt X (σ.no 12) i)) =
      some ((Sz.ref.owner σ μ).1, (Sz.ref.owner σ μ).2) :=
    (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨below_of_mu (by rw [k2]; rfl), rfl, k2⟩
  have hc₀ : c < (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).2 := by
    rw [eO, ← hk]
    exact hc
  have eR : (((szOf (Meaning.tlAt X (σ.no 12))).rad : ℕ) : ℤ) = 2 ^ 20 := by
    show ((2 ^ 20 : ℕ) : ℤ) = 2 ^ 20
    norm_num
  have em : (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).1 =
      ((Meaning.tlAt X (σ.no 12)).mats.getD i {}).m := by rw [eO, ← hm]
  have mid : pack3 (Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).1
      (fun r => algebraMap Cb.Gl.F Cb.Gl.E (R.cells.cell ((Sz.ref.owner σ μ).1.no 12)
        (Sz.ref.owner σ μ).2.label r c)) i' =
      pack3 ((Meaning.tlAt X (σ.no 12)).mats.getD i {}).m
        (fun r => algebraMap Cb.Gl.F Cb.Gl.E (R.cells.cell (σ.no 12) μ.label r c)) i' := by
    rw [em]
    congr 1
    funext r
    rw [hC r]
  have hn : labelNo (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X (σ.no 12) i))) =
      some (Meaning.ownerA (Meaning.labAt X (σ.no 12) i)) :=
    labelNo_arrayLabel (owner_number_small k2)
  rw [k1, cellsVals_pack Sz.ref R hd hn hM₀ hc₀ i', eR]
  exact ((pack3_eq_pack _ _ i').symm.trans mid).trans (pack3_eq_pack _ _ i')

end

end OnBytes.HonestTrace.PackedCells

#print axioms OnBytes.HonestTrace.PackedCells.number_of_name
#print axioms OnBytes.HonestTrace.PackedCells.owner_numbers_layers
#print axioms OnBytes.HonestTrace.PackedCells.owner_numbers_head
#print axioms OnBytes.HonestTrace.PackedCells.owner_numbers
#print axioms OnBytes.HonestTrace.PackedCells.shape_at_tail
#print axioms OnBytes.HonestTrace.PackedCells.owner_number_small
#print axioms OnBytes.HonestTrace.PackedCells.cells_pack_at
