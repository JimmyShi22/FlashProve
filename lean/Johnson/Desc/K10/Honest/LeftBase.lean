-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/LeftBase.lean: the public premises of LeftIs.lean hold at the single rows that a closing
returns.

What is proved.
  `rows_layout`     the single rows that the fold returns carry the description's own layout of the group
  **`leftFits_of_base`**   from `CloseBase P s D`: `LeftFits` (Johnson/Desc/K10/Honest/LeftIs.lean) holds at the
                   statement behind the beginning of the test, the group as that beginning leaves it, and the single
                   rows `foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)`, for every row and all rounds
  `toy_padded`      the words of the kind's first toy example (Johnson/Desc/K10/Honest/HoldsToy.lean) are 0 on the rows
                   beyond the real ones
  **`toy_fits`**     at that example's single rows `LeftFits` and `Padded` hold together, so the premises of
                   LeftIs.lean's two theorems can be met. The example has three members; one is kept; one has three real
                   rows in a block of four, so there is a row beyond the real ones
  `toy_iff`         `claimTrue_iff_tables` applied there

What is defined. `begunGroup`: the segment's group as the beginning of the test leaves it.

Limits. `CloseBase` is an assumption: that it holds at a state of a run is not shown here. The statement is `D.S1 s`, as
in `closeBase_holds`; the record that the closing returns holds `spent (D.S1 s) D.m` (`close_leaves`, LeavesAt.lean),
and that `LeftFits` and `leftAt` are the same there is not shown. Neither `close_leaves` nor `closeBase_holds` is called
here (LeftClaim.lean joins them). The example shows that the premises can be met together; it does not show that either
side of `toy_iff` is true. It is one made-up example with h = 0, not the sizes of a real description: the words at the
fresh mask's message are 0, every main row is over the extension field, the mask table has one row, and no member is
sampled. Nothing is said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.LeftIs
import Johnson.Desc.K10.Honest.HoldsToy
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.First.Close (Par Rec)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase layoutOf_same closeBase_of)
open ProofFile.Honest.K10.Values (keptLen)

/-- The segment's group as the beginning of the test leaves it. -/
def begunGroup (D : BaseData) : Group := { D.G with inRun := true, rows := #[] }

variable {P : Par} {s : Rec} {D : BaseData}

/-- **The single rows that the fold returns bear the description's own layout of the group.** -/
theorem rows_layout (H : CloseBase P s D) (row : GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView) :
    (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)).layout = Own.layoutOf s.st D.G := by
  show ({ Own.layoutOf s.st D.G with k := D.Gq.k, h := D.Gq.h } : GroupLayout) = _
  rw [← H.kh.1, ← H.kh.2]

/-- **The public premises hold at the single rows that the closing returns**, from `CloseBase`. -/
theorem leftFits_of_base (H : CloseBase P s D) (row : GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView) :
    LeftFits (D.S1 s) (begunGroup D) (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)) := by
  have hE := extends_begun s.st s.frame.group D.G
  have hG' := begun_group s.st s.frame.group D.G H.there
  have hOk' : GroupOk (D.S1 s) { D.G with inRun := true, rows := #[] } :=
    H.inOrder.extends hE rfl rfl rfl rfl
  have eL := layoutOf_same H.there
  have hL' : (D.S1 s).layout s.frame.group = some (Own.layoutOf s.st D.G) := by
    show (Slice.begun s.st s.frame.group D.G).layout s.frame.group = _
    rw [layout_eq _ _ _ hG', eL,
      layoutOf_extends (G' := { D.G with inRun := true, rows := #[] }) hE H.inOrder rfl rfl rfl rfl]
  have e := rows_layout H row rE rR
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact layFacts hG' hL' hOk'
  · rw [e]
    exact H.inOrder.nodup
  · exact (Own.foldShapeFits_agrees _ _).trans H.shape

namespace Toy
open ProofFile.Honest.K10.Values.Toy (sT words sT_member)

/-- The toy example's words are 0 on the rows beyond the real ones. -/
theorem toy_padded (D : BaseData) : Padded (D.S1 sT) words := by
  have hE : Extends sT.st (D.S1 sT) := extends_begun sT.st sT.frame.group D.G
  intro o part i h
  match o, part with
  | 0, .main =>
    rw [hE.realRows (o := 0) (by decide) .main, hE.rowBits (o := 0) (by decide) .main] at h
    have h' : 3 ≤ i % 2 ^ 2 := h
    show readE (if i % 2 ^ 2 < 3 && i / 2 ^ 2 < 8 then _ else zeroE) = 0
    rw [if_neg (by simp; omega)]
    exact readE_zero
  | 0, .mask =>
    rw [hE.realRows (o := 0) (by decide) .mask, hE.rowBits (o := 0) (by decide) .mask] at h
    exact absurd (show 1 ≤ i % 2 ^ 0 from h) (by omega)
  | 1, .main => exact readE_zero
  | 1, .mask => exact readE_zero
  | 2, .main =>
    rw [hE.realRows (o := 2) (by decide) .main, hE.rowBits (o := 2) (by decide) .main] at h
    exact absurd (show 1 ≤ i % 2 ^ 0 from h) (by omega)
  | 2, .mask => exact readE_zero
  | 3, .main =>
    rw [hE.realRows (o := 3) (by decide) .main, hE.rowBits (o := 3) (by decide) .main] at h
    exact absurd (show 2 ≤ i % 2 ^ 1 from h) (by omega)
  | 3, .mask => exact readE_zero
  | _ + 4, .main => exact readE_zero
  | _ + 4, .mask => exact readE_zero

/-- **At the toy example's single rows the premises hold together.** -/
theorem toy_fits : ∃ D, CloseBase ProofFile.Honest.K10.Toy.P sT D ∧ Padded (D.S1 sT) words ∧
    ∀ (row : GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView),
      LeftFits (D.S1 sT) (begunGroup D) (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)) := by
  obtain ⟨D, H⟩ := closeBase_of sT_member
  exact ⟨D, H, toy_padded D, fun row rE rR => leftFits_of_base H row rE rR⟩

/-- `claimTrue_iff_tables`, applied there. -/
theorem toy_iff : ∃ D, CloseBase ProofFile.Honest.K10.Toy.P sT D ∧
    ∀ (row : GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (T : SwitchTarget),
      ClaimTrue (sizesAt (D.S1 sT) (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)) T)
          (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR))
          (leftAt (D.S1 sT) (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)) words) ↔
        (∀ f ∈ (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)).kept.toList,
          f.oracle ∈ (switchKept (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR))).toList) ∧
        ∑ j, vecS (stageAt (D.S1 sT) (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)))
              (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)) j *
            foldedAt (D.S1 sT) (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)) words j +
          keptVal (keptLen (D.S1 sT))
            (tablesOf (D.S1 sT) (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)).layout words).kept
            (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)).kept =
          readE (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)).target := by
  obtain ⟨D, H, hp, hf⟩ := toy_fits
  exact ⟨D, H, fun row rE rR T => claimTrue_iff_tables _ _ _ T words (hf row rE rR) hp⟩

end Toy

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.begunGroup
#print axioms ProofFile.Honest.K10.LeftIs.rows_layout
#print axioms ProofFile.Honest.K10.LeftIs.leftFits_of_base
#print axioms ProofFile.Honest.K10.LeftIs.Toy.toy_padded
#print axioms ProofFile.Honest.K10.LeftIs.Toy.toy_fits
#print axioms ProofFile.Honest.K10.LeftIs.Toy.toy_iff
