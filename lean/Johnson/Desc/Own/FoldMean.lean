-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/FoldMean.lean: what the three tests of Johnson/Desc/Own/Fold.lean check, each as a
proposition in plain terms, with the proof that the test says yes exactly where it holds.
Definitions of type Prop, statements and proofs. No block's text imports this file.
  `MemberFit S F i`, `ShapeFitAt S F c zk`, `FoldShapeFit S F`, `foldShapeFits_iff`: the shape fits.
  `FoldMaskFit S F fresh`, `foldMaskFits_iff`: the message number fresh can be the fresh mask.
  `FoldRowFit S F row`, `foldRowFits_iff`: the row has the sizes of the group's tables.
`formFits` stays a name here: what it checks is said beside its own text (Johnson/Desc/Own/).

-/
import Johnson.Desc.Own.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- Member number i of the layout is there, has the fold's codes where it has rows, has a block of
main rows, inside the cube, exactly if it has main rows and is not kept, and a block of mask rows,
inside the cube, exactly if it has mask rows. -/
def MemberFit (S : Statement) (F : FoldShape) (i : Nat) : Prop :=
  ∃ x, S.oracles[F.layout.members.getD i noId]? = some x ∧
    (x.shape.mainRows = 0 ∨ x.shape.code = F.code) ∧
    (x.shape.maskRows = 0 ∨ x.shape.maskCode = F.maskCode) ∧
    (match F.layout.mainFirst.getD i none with
      | some f => (0 < x.shape.mainRows ∧ F.layout.kept.getD i false = false) ∧
          f + x.shape.mainRows ≤ 2 ^ F.layout.k
      | none => ¬ (0 < x.shape.mainRows ∧ F.layout.kept.getD i false = false)) ∧
    (match F.layout.maskFirst.getD i none with
      | some f => 0 < x.shape.maskRows ∧ f + x.shape.maskRows ≤ 2 ^ F.layout.h
      | none => x.shape.maskRows = 0)

/-- The shape fits, at the main code c and the mask code zk. -/
def ShapeFitAt (S : Statement) (F : FoldShape) (c zk : Code) : Prop :=
  1 ≤ F.layout.k ∧ F.layout.h ≤ F.layout.k ∧ zk.logN ≤ c.logN ∧
    2 * F.layout.k + 1 - F.layout.h ≤ zk.ell ∧
    F.layout.kept.size = F.layout.members.size ∧
    F.layout.mainFirst.size = F.layout.members.size ∧
    F.layout.maskFirst.size = F.layout.members.size ∧
    (∀ i < F.layout.members.size, MemberFit S F i) ∧
    ∃ i < F.layout.members.size, ∃ x, S.oracles[F.layout.members.getD i noId]? = some x ∧
      0 < x.shape.mainRows ∧ F.layout.kept.getD i false = false

/-- The shape of a fold fits the statement: its two codes are there, and it fits at them. -/
def FoldShapeFit (S : Statement) (F : FoldShape) : Prop :=
  ∃ c zk, S.codes.base[F.code]? = some c ∧ S.codes.mask[F.maskCode]? = some zk ∧
    ShapeFitAt S F c zk

theorem foldShapeFits_iff (S : Statement) (F : FoldShape) :
    foldShapeFits S F = true ↔ FoldShapeFit S F := by
  unfold foldShapeFits FoldShapeFit
  cases S.codes.base[F.code]? with
  | none => simp
  | some c =>
    cases S.codes.mask[F.maskCode]? with
    | none => simp
    | some zk =>
      refine Iff.trans ?_ (⟨fun h => ⟨c, zk, rfl, rfl, h⟩, fun ⟨_, _, h1, h2, h⟩ => by
        cases h1; cases h2; exact h⟩ : ShapeFitAt S F c zk ↔ _)
      unfold ShapeFitAt
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
        List.any_eq_true, List.mem_range, and_assoc]
      refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr ?_ ?_
      · refine forall_congr' fun i => imp_congr_right fun _ => ?_
        unfold MemberFit
        cases S.oracles[F.layout.members.getD i noId]? with
        | none => simp
        | some x =>
          cases F.layout.mainFirst.getD i none <;> cases F.layout.maskFirst.getD i none <;>
            simp [and_assoc] <;> intros <;>
            exact ⟨fun h hp => h.elim (fun h0 => absurd hp (by omega)) id,
              fun h => (Nat.eq_zero_or_pos _).elim Or.inl fun hp => Or.inr (h hp)⟩
      · refine exists_congr fun i => and_congr_right fun _ => ?_
        cases S.oracles[F.layout.members.getD i noId]? with
        | none => simp
        | some x => simp

/-- The oracle message number fresh can be the fold's fresh mask. -/
def FoldMaskFit (S : Statement) (F : FoldShape) (fresh : Nat) : Prop :=
  ∃ o, S.oracles[fresh]? = some o ∧ o.shape.mainRows = 0 ∧ o.shape.maskRows = 2 ^ F.layout.h ∧
    o.shape.maskCode = F.maskCode ∧ o.sampled = false ∧ o.shape.answers = 0 ∧
    fresh ∉ F.layout.members

theorem foldMaskFits_iff (S : Statement) (F : FoldShape) (fresh : Nat) :
    foldMaskFits S F fresh = true ↔ FoldMaskFit S F fresh := by
  unfold foldMaskFits FoldMaskFit
  cases S.oracles[fresh]? with
  | none => simp
  | some o => simp [and_assoc]

/-- The row has the sizes of the group's tables. -/
def FoldRowFit (S : Statement) (F : FoldShape) (row : GroupRow) : Prop :=
  formFits row.c (F.layout.k + ceilLog2 (S.codes.base.getD F.code default).ell) = true ∧
    row.d.size = (S.codes.mask.getD F.maskCode default).ell * 2 ^ F.layout.h ∧
    ∀ f ∈ row.kept,
      (∃ i, F.layout.members.idxOf? f.oracle = some i ∧ F.layout.kept.getD i false = true) ∧
        formFits f.c (S.tableBits f.oracle .main) = true

theorem foldRowFits_iff (S : Statement) (F : FoldShape) (row : GroupRow) :
    foldRowFits S F row = true ↔ FoldRowFit S F row := by
  unfold foldRowFits FoldRowFit
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun f =>
    imp_congr_right fun _ => and_congr_left fun _ => ?_
  cases F.layout.members.idxOf? f.oracle with
  | none => simp
  | some i => simp

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.foldShapeFits_iff
#print axioms VerifiableInference.Desc.Own.foldMaskFits_iff
#print axioms VerifiableInference.Desc.Own.foldRowFits_iff
